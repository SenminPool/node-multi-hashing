// Copyright (c) 2012-2013 The Cryptonote developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.
// Portions Copyright (c) 2018 The Monero developers

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include "crypto/oaes_lib.h"
#include "crypto/c_keccak.h"
#include "crypto/c_groestl.h"
#include "crypto/c_blake256.h"
#include "crypto/c_jh.h"
#include "crypto/c_skein.h"
#include "crypto/int-util.h"
#include "crypto/hash-ops.h"
#include <x86intrin.h>
#include <wmmintrin.h>
#include <sys/mman.h>

#include <wmmintrin.h>
#include <sys/mman.h>

#define MEMORY         (1 << 21) /* 2 MiB */
#define ITER           (1 << 20)
#define AES_BLOCK_SIZE  16
#define AES_KEY_SIZE    32 /*16*/
#define INIT_SIZE_BLK   8
#define INIT_SIZE_BYTE (INIT_SIZE_BLK * AES_BLOCK_SIZE)

#define VARIANT1_1(p) \
  do if (variant > 0) \
  { \
    uint8_t tmp = ((const uint8_t*)p)[11]; \
    uint8_t tmp1 = (tmp>>4)&1, tmp2 = (tmp>>5)&1, tmp3 = tmp1^tmp2; \
    uint8_t tmp0 = nonce_flag ? tmp3 : tmp1 + 1; \
    ((uint8_t*)p)[11] = (tmp & 0xef) | (tmp0<<4); \
  } while(0)

#define VARIANT1_2(p) VARIANT1_1(p)
#define VARIANT1_INIT() \
  if (variant > 0 && len < 43) \
  { \
    fprintf(stderr, "Cryptonight variants need at least 43 bytes of data"); \
    _exit(1); \
  } \
  const uint8_t nonce_flag = variant > 0 ? ((const uint8_t*)input)[39] & 0x01 : 0

#pragma pack(push, 1)
union cn_slow_hash_state {
    union hash_state hs;
    struct {
        uint8_t k[64];
        uint8_t init[INIT_SIZE_BYTE];
    };
};
#pragma pack(pop)

static void do_blake_hash(const void* input, size_t len, char* output) {
    blake256_hash((uint8_t*)output, input, len);
}

void do_groestl_hash(const void* input, size_t len, char* output) {
    groestl(input, len * 8, (uint8_t*)output);
}

static void do_jh_hash(const void* input, size_t len, char* output) {
    int r = jh_hash_n(HASH_SIZE * 8, input, 8 * len, (uint8_t*)output);
    assert(SUCCESS == r);
}

static void do_skein_hash(const void* input, size_t len, char* output) {
    int r = c_skein_hash(8 * HASH_SIZE, input, 8 * len, (uint8_t*)output);
    assert(SKEIN_SUCCESS == r);
}

static void (* const extra_hashes[4])(const void *, size_t, char *) = {
    do_blake_hash, do_groestl_hash, do_jh_hash, do_skein_hash
};

extern int aesb_single_round(const uint8_t *in, uint8_t*out, const uint8_t *expandedKey);
extern int aesb_pseudo_round(const uint8_t *in, uint8_t *out, const uint8_t *expandedKey);

static inline size_t e2i(const uint8_t* a) {
    return (*((uint64_t*) a) / AES_BLOCK_SIZE) & (MEMORY / AES_BLOCK_SIZE - 1);
}

static inline void copy_block(uint8_t* dst, const uint8_t* src) {
    ((uint64_t*) dst)[0] = ((uint64_t*) src)[0];
    ((uint64_t*) dst)[1] = ((uint64_t*) src)[1];
}

static inline void xor_blocks(uint8_t* a, const uint8_t* b) {
    ((uint64_t*) a)[0] ^= ((uint64_t*) b)[0];
    ((uint64_t*) a)[1] ^= ((uint64_t*) b)[1];
}

static inline void xor_blocks_dst(const uint8_t* a, const uint8_t* b, uint8_t* dst) {
    ((uint64_t*) dst)[0] = ((uint64_t*) a)[0] ^ ((uint64_t*) b)[0];
    ((uint64_t*) dst)[1] = ((uint64_t*) a)[1] ^ ((uint64_t*) b)[1];
}

////////////////
struct cryptonight_ctx {
    uint8_t long_state[MEMORY] __attribute((aligned(16)));
    union cn_slow_hash_state state;
    uint8_t text[INIT_SIZE_BYTE] __attribute((aligned(16)));
    uint64_t a[AES_BLOCK_SIZE >> 3] __attribute((aligned(16)));
    uint64_t b[AES_BLOCK_SIZE >> 3] __attribute((aligned(16)));
    uint8_t c[AES_BLOCK_SIZE];
    uint8_t aes_key[AES_KEY_SIZE];
    oaes_ctx* aes_ctx;
};

void cryptonight_hash(const char* input, char* output, uint32_t len, int variant) {
    struct cryptonight_ctx *ctx = alloca(sizeof(struct cryptonight_ctx));
    hash_process(&ctx->state.hs, (const uint8_t*) input, len);
    uint8_t ExpandedKey[256];
    size_t i, j;

    VARIANT1_INIT();

    oaes_key_import_data(ctx->aes_ctx, ctx->aes_key, AES_KEY_SIZE);
    for (i = 0; i < MEMORY / INIT_SIZE_BYTE; i++) {
        for (j = 0; j < INIT_SIZE_BLK; j++) {
            aesb_pseudo_round(&ctx->text[AES_BLOCK_SIZE * j],
                    &ctx->text[AES_BLOCK_SIZE * j],
                    ctx->aes_ctx->key->exp_data);
        }
        memcpy(&ctx->long_state[i * INIT_SIZE_BYTE], ctx->text, INIT_SIZE_BYTE);
    }
	
	for (i = 0; i < 2; i++) 
    {
	    ctx->a[i] = ((uint64_t *)ctx->state.k)[i] ^  ((uint64_t *)ctx->state.k)[i+4];
	    ctx->b[i] = ((uint64_t *)ctx->state.k)[i+2] ^  ((uint64_t *)ctx->state.k)[i+6];
    }

    for (i = 0; i < ITER / 2; i++) {
        /* Dependency chain: address -> read value ------+
         * written value <-+ hard function (AES or MUL) <+
         * next address  <-+
         */
        /* Iteration 1 */
        j = e2i(ctx->a);
        aesb_single_round(&ctx->long_state[j * AES_BLOCK_SIZE], ctx->c, ctx->a);
        xor_blocks_dst(ctx->c, ctx->b, &ctx->long_state[j * AES_BLOCK_SIZE]);
	VARIANT1_1((uint8_t*)&ctx->long_state[j * AES_BLOCK_SIZE]);
        /* Iteration 2 */
        mul_sum_xor_dst(ctx->c, ctx->a,
                &ctx->long_state[e2i(ctx->c) * AES_BLOCK_SIZE]);
        copy_block(ctx->b, ctx->c);
	VARIANT1_2((uint8_t*)
                &ctx->long_state[e2i(ctx->c) * AES_BLOCK_SIZE]);
    }

    memcpy(ctx->text, ctx->state.init, INIT_SIZE_BYTE);
    memcpy(ExpandedKey, &ctx->state.hs.b[32], AES_KEY_SIZE);
    ExpandAESKey256(ExpandedKey);
    
    //for (i = 0; likely(i < MEMORY); i += INIT_SIZE_BYTE)
    //    aesni_parallel_xor(&ctx->text, ExpandedKey, &ctx->long_state[i]);
    
    for (i = 0; __builtin_expect(i < MEMORY, 1); i += INIT_SIZE_BYTE) 
	{	
		xmminput[0] = _mm_xor_si128(longoutput[(i >> 4)], xmminput[0]);
		xmminput[1] = _mm_xor_si128(longoutput[(i >> 4) + 1], xmminput[1]);
		xmminput[2] = _mm_xor_si128(longoutput[(i >> 4) + 2], xmminput[2]);
		xmminput[3] = _mm_xor_si128(longoutput[(i >> 4) + 3], xmminput[3]);
		xmminput[4] = _mm_xor_si128(longoutput[(i >> 4) + 4], xmminput[4]);
		xmminput[5] = _mm_xor_si128(longoutput[(i >> 4) + 5], xmminput[5]);
		xmminput[6] = _mm_xor_si128(longoutput[(i >> 4) + 6], xmminput[6]);
		xmminput[7] = _mm_xor_si128(longoutput[(i >> 4) + 7], xmminput[7]);
		
		for(j = 0; j < 10; j++)
		{
			xmminput[0] = _mm_aesenc_si128(xmminput[0], expkey[j]);
			xmminput[1] = _mm_aesenc_si128(xmminput[1], expkey[j]);
			xmminput[2] = _mm_aesenc_si128(xmminput[2], expkey[j]);
			xmminput[3] = _mm_aesenc_si128(xmminput[3], expkey[j]);
			xmminput[4] = _mm_aesenc_si128(xmminput[4], expkey[j]);
			xmminput[5] = _mm_aesenc_si128(xmminput[5], expkey[j]);
			xmminput[6] = _mm_aesenc_si128(xmminput[6], expkey[j]);
			xmminput[7] = _mm_aesenc_si128(xmminput[7], expkey[j]);
		}
		
	}
        
    memcpy(ctx->state.init, ctx->text, INIT_SIZE_BYTE);
    hash_permutation(&ctx->state.hs);
    extra_hashes[ctx->state.hs.b[0] & 3](&ctx->state, 200, output);
    munmap(ctx, sizeof(struct cryptonight_ctx));
}


void cryptonight_fast_hash(const char* input, char* output, uint32_t len) {
    union hash_state state;
    hash_process(&state, (const uint8_t*) input, len);
    memcpy(output, &state, HASH_SIZE);
}
