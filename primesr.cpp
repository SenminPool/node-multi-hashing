#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <vector>
#include <openssl/sha.h>
#include "bignum.h"
#include "uint1024.h"

#include "primesr.h"

#define BEGIN(a)            ((char*)&(a))
#define END(a)              ((char*)&((&(a))[1]))
#define UBEGIN(a)           ((unsigned char*)&(a))
#define UEND(a)             ((unsigned char*)&((&(a))[1]))
#define ARRAYLEN(array)     (sizeof(array)/sizeof((array)[0]))

// This is needed because the foreach macro can't get over the comma in pair<t1, t2>
#define PAIRTYPE(t1, t2)    std::pair<t1, t2>

typedef unsigned int bitsType;
typedef uint256 offsetType;

template<typename T1>
inline uint256 Hash(const T1 pbegin, const T1 pend)
{
    static unsigned char pblank[1];
    uint256 hash1;
    SHA256((pbegin == pend ? pblank : (unsigned char*)&pbegin[0]), (pend - pbegin) * sizeof(pbegin[0]), (unsigned char*)&hash1);
    uint256 hash2;
    SHA256((unsigned char*)&hash1, sizeof(hash1), (unsigned char*)&hash2);
    return hash2;
}

class CBlockHeader
{
public:
    // header
    static const int CURRENT_VERSION=2;
    int nVersion;
    uint256 hashPrevBlock;
    uint256 hashMerkleRoot;
    bitsType nBits;
    int64_t nTime;
    offsetType nOffset;

    CBlockHeader()
    {
        SetNull();
    }

    void SetNull()
    {
        nVersion = CBlockHeader::CURRENT_VERSION;
        hashPrevBlock = 0;
        hashMerkleRoot = 0;
        nTime = 0;
        nBits = 0;
        nOffset = 0;
    }

    uint256 GetHash() const;
    uint256 GetHashForPoW() const;

};


class CBlock : public CBlockHeader
{
public:

    CBlock()
    {
        SetNull();
    }

    CBlock(const CBlockHeader &header)
    {
        SetNull();
        *((CBlockHeader*)this) = header;
    }

    CBlockHeader GetBlockHeader() const
    {
        CBlockHeader block;
        block.nVersion       = nVersion;
        block.hashPrevBlock  = hashPrevBlock;
        block.hashMerkleRoot = hashMerkleRoot;
        block.nTime          = nTime;
        block.nBits          = nBits;
        block.nOffset        = nOffset;
        return block;
    }
};

uint256 CBlockHeader::GetHash() const
{
    return Hash(BEGIN(nVersion), END(nOffset));
}

uint256 CBlockHeader::GetHashForPoW() const
{
    return Hash(BEGIN(nVersion), BEGIN(nOffset));
}

unsigned int generatePrimeBase( CBigNum &bnTarget, uint256 hash, bitsType compactBits )
{
    bnTarget = 1;
    bnTarget <<= 8;

    for ( int i = 0; i < 256; i++ )
    {
        bnTarget = (bnTarget << 1) + (hash.GetLow32() & 1);
        hash >>= 1;
    }
    CBigNum nBits;
    nBits.SetCompact(compactBits);

    const unsigned int significativeDigits = 265;
    unsigned int trailingZeros = nBits.getuint();
    if( trailingZeros < significativeDigits )
        return 0;
    trailingZeros -= significativeDigits;
    bnTarget <<= trailingZeros;
    return trailingZeros;
}

int CheckProofOfWork(uint256 hash, bitsType compactBits, uint256 delta)
{
    CBigNum bnTarget;
    unsigned int trailingZeros = generatePrimeBase( bnTarget, hash, compactBits );

    if (trailingZeros < 16 || trailingZeros > 20000){
        return 0;
    }

    CBigNum bigDelta = CBigNum(delta);
    bnTarget += bigDelta;

    if( (bnTarget % 210) != 97 ){
        return 0;
    }

    if( BN_is_prime_fasttest( &bnTarget, 1, NULL, NULL, NULL, 1) != 1 )
    {
        return 0;
    }

    int primes = 1;

    bnTarget += 4;
    if( BN_is_prime_fasttest( &bnTarget, 1, NULL, NULL, NULL, 1) == 1 )
    {
        primes += 1;
    }

    bnTarget += 2;
    if( BN_is_prime_fasttest( &bnTarget, 1, NULL, NULL, NULL, 1) == 1 )
    {
        primes += 1;
    }

    bnTarget += 4;
    if( BN_is_prime_fasttest( &bnTarget, 1, NULL, NULL, NULL, 1) == 1 )
    {
        primes += 1;
    }

    bnTarget += 2;
    if( BN_is_prime_fasttest( &bnTarget, 1, NULL, NULL, NULL, 1) == 1 )
    {
        primes += 1;
    }

    bnTarget += 4;
    if( BN_is_prime_fasttest( &bnTarget, 4, NULL, NULL, NULL, 1) == 1 )
    {
        primes += 1;
    }

    return primes;
}

int PrimesDifficulty(const char *input, uint32_t len)
{
   std::vector<unsigned char> blockData(input, input + len);
   CBlock* pblock = (CBlock*)&blockData[0];
   return CheckProofOfWork( pblock->GetHashForPoW(), pblock->nBits, pblock->nOffset);
}

