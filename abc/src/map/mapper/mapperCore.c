/**CFile****************************************************************

  FileName    [mapperCore.c]

  PackageName [MVSIS 1.3: Multi-valued logic synthesis system.]

  Synopsis    [Generic technology mapping engine.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 2.0. Started - June 1, 2004.]

  Revision    [$Id: mapperCore.c,v 1.7 2004/10/01 23:41:04 satrajit Exp $]

***********************************************************************/

#include "mapperInt.h"
//#include "resm.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


static Map_Node_t * Map_YocoFindNodeByAigId( Map_Man_t * p, int AigId )
{
    Map_Node_t * pNode;
    int i;
    for ( i = 0; i < p->vMapObjs->nSize; i++ )
    {
        pNode = (Map_Node_t *)p->vMapObjs->pArray[i];
        if ( Map_NodeReadAigId( pNode ) == AigId )
            return pNode;
    }
    for ( i = 0; i < p->nOutputs; i++ )
        if ( Map_NodeReadAigId( Map_Regular(p->pOutputs[i]) ) == AigId )
            return Map_Regular(p->pOutputs[i]);
    return NULL;
}

static unsigned Map_YocoSha256Rotr( unsigned x, unsigned n ) { return (x >> n) | (x << (32 - n)); }
static unsigned Map_YocoSha256Ch( unsigned x, unsigned y, unsigned z ) { return (x & y) ^ (~x & z); }
static unsigned Map_YocoSha256Maj( unsigned x, unsigned y, unsigned z ) { return (x & y) ^ (x & z) ^ (y & z); }
static unsigned Map_YocoSha256S0( unsigned x ) { return Map_YocoSha256Rotr(x, 2) ^ Map_YocoSha256Rotr(x, 13) ^ Map_YocoSha256Rotr(x, 22); }
static unsigned Map_YocoSha256S1( unsigned x ) { return Map_YocoSha256Rotr(x, 6) ^ Map_YocoSha256Rotr(x, 11) ^ Map_YocoSha256Rotr(x, 25); }
static unsigned Map_YocoSha256s0( unsigned x ) { return Map_YocoSha256Rotr(x, 7) ^ Map_YocoSha256Rotr(x, 18) ^ (x >> 3); }
static unsigned Map_YocoSha256s1( unsigned x ) { return Map_YocoSha256Rotr(x, 17) ^ Map_YocoSha256Rotr(x, 19) ^ (x >> 10); }

static void Map_YocoSha256Block( unsigned H[8], unsigned char * pData )
{
    static const unsigned K[64] = {
        0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
        0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
        0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
        0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
        0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
        0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
        0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
        0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2 };
    unsigned W[64], a, b, c, d, e, f, g, h, T1, T2;
    int i;
    for ( i = 0; i < 16; i++ )
        W[i] = ((unsigned)pData[4*i] << 24) | ((unsigned)pData[4*i+1] << 16) | ((unsigned)pData[4*i+2] << 8) | (unsigned)pData[4*i+3];
    for ( i = 16; i < 64; i++ )
        W[i] = Map_YocoSha256s1(W[i-2]) + W[i-7] + Map_YocoSha256s0(W[i-15]) + W[i-16];
    a = H[0]; b = H[1]; c = H[2]; d = H[3]; e = H[4]; f = H[5]; g = H[6]; h = H[7];
    for ( i = 0; i < 64; i++ )
    {
        T1 = h + Map_YocoSha256S1(e) + Map_YocoSha256Ch(e,f,g) + K[i] + W[i];
        T2 = Map_YocoSha256S0(a) + Map_YocoSha256Maj(a,b,c);
        h = g; g = f; f = e; e = d + T1; d = c; c = b; b = a; a = T1 + T2;
    }
    H[0] += a; H[1] += b; H[2] += c; H[3] += d; H[4] += e; H[5] += f; H[6] += g; H[7] += h;
}

static int Map_YocoSha256File( const char * pFileName, char * pHex )
{
    FILE * pFile;
    unsigned H[8] = { 0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19 };
    unsigned char Buffer[64], Final[128];
    unsigned long long nBytes = 0, nBits;
    size_t nRead, nFinal;
    int i;
    static const char * pDigits = "0123456789abcdef";
    if ( pFileName == NULL )
        return 0;
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
        return 0;
    while ( (nRead = fread( Buffer, 1, 64, pFile )) == 64 )
    {
        Map_YocoSha256Block( H, Buffer );
        nBytes += 64;
    }
    if ( ferror( pFile ) )
    {
        fclose( pFile );
        return 0;
    }
    fclose( pFile );
    nBytes += nRead;
    memset( Final, 0, sizeof(Final) );
    memcpy( Final, Buffer, nRead );
    Final[nRead] = 0x80;
    nFinal = ( nRead + 1 <= 56 ) ? 64 : 128;
    nBits = nBytes * 8;
    for ( i = 0; i < 8; i++ )
        Final[nFinal - 1 - i] = (unsigned char)(nBits >> (8 * i));
    Map_YocoSha256Block( H, Final );
    if ( nFinal == 128 )
        Map_YocoSha256Block( H, Final + 64 );
    for ( i = 0; i < 32; i++ )
    {
        unsigned char Byte = (unsigned char)(H[i/4] >> (24 - 8 * (i & 3)));
        pHex[2*i] = pDigits[Byte >> 4];
        pHex[2*i+1] = pDigits[Byte & 15];
    }
    pHex[64] = 0;
    return 1;
}

static int Map_YocoJsonReadString( char * pLine, const char * pKey, char * pValue, int nValueMax )
{
    char * p = strstr( pLine, pKey );
    int n = 0;
    if ( p == NULL )
        return 0;
    p = strchr( p, ':' );
    if ( p == NULL )
        return 0;
    p++;
    while ( *p == ' ' || *p == '\t' )
        p++;
    if ( *p != '\"' )
        return 0;
    p++;
    while ( *p && *p != '\"' )
    {
        if ( n + 1 >= nValueMax )
            return 0;
        pValue[n++] = *p++;
    }
    if ( *p != '\"' )
        return 0;
    pValue[n] = 0;
    return 1;
}

static int Map_YocoJsonReadInt( char * pLine, const char * pKey, int * pValue )
{
    char * p = strstr( pLine, pKey );
    if ( p == NULL )
        return 0;
    p = strchr( p, ':' );
    if ( p == NULL )
        return 0;
    p++;
    while ( *p == ' ' || *p == '\t' )
        p++;
    if ( *p == '-' )
        return 0;
    *pValue = atoi( p );
    return 1;
}

static int Map_YocoJsonReadLeaves( char * pLine, int * pLeaves, int nLeavesMax )
{
    char * p = strstr( pLine, "\"leaves\"" );
    int nLeaves = 0;
    if ( p == NULL )
        return -1;
    p = strchr( p, '[' );
    if ( p == NULL )
        return -1;
    p++;
    while ( *p && *p != ']' )
    {
        while ( *p == ' ' || *p == '\t' || *p == ',' )
            p++;
        if ( *p == ']' )
            break;
        if ( *p < '0' || *p > '9' )
            return -1;
        if ( nLeaves >= nLeavesMax )
            return -1;
        pLeaves[nLeaves++] = atoi( p );
        while ( *p >= '0' && *p <= '9' )
            p++;
    }
    return nLeaves;
}

static void Map_YocoSortInts( int * pValues, int nValues )
{
    int i, k, Temp;
    for ( i = 1; i < nValues; i++ )
    {
        Temp = pValues[i];
        for ( k = i; k > 0 && pValues[k-1] > Temp; k-- )
            pValues[k] = pValues[k-1];
        pValues[k] = Temp;
    }
}

static void Map_YocoStoreSuppliedCut( Map_Man_t * p, int Root, int * pLeaves, int nLeaves )
{
    int i;
    if ( p->nYocoSuppliedCuts == p->nYocoSuppliedRowsAlloc )
    {
        p->nYocoSuppliedRowsAlloc = p->nYocoSuppliedRowsAlloc ? 2 * p->nYocoSuppliedRowsAlloc : 1024;
        p->pYocoSuppliedRoots = ABC_REALLOC( int, p->pYocoSuppliedRoots, p->nYocoSuppliedRowsAlloc );
        p->pYocoSuppliedLeafCounts = ABC_REALLOC( int, p->pYocoSuppliedLeafCounts, p->nYocoSuppliedRowsAlloc );
        p->pYocoSuppliedLeaves = ABC_REALLOC( int, p->pYocoSuppliedLeaves, 6 * p->nYocoSuppliedRowsAlloc );
    }
    Map_YocoSortInts( pLeaves, nLeaves );
    p->pYocoSuppliedRoots[p->nYocoSuppliedCuts] = Root;
    p->pYocoSuppliedLeafCounts[p->nYocoSuppliedCuts] = nLeaves;
    for ( i = 0; i < nLeaves; i++ )
        p->pYocoSuppliedLeaves[6 * p->nYocoSuppliedCuts + i] = pLeaves[i];
    p->nYocoSuppliedCuts++;
}

static int Map_YocoCutMatchesRow( Map_Man_t * p, int iRow, int Root, int * pLeaves, int nLeaves )
{
    int i;
    if ( p->pYocoSuppliedRoots[iRow] != Root )
        return 0;
    if ( p->pYocoSuppliedLeafCounts[iRow] != nLeaves )
        return 0;
    for ( i = 0; i < nLeaves; i++ )
        if ( p->pYocoSuppliedLeaves[6 * iRow + i] != pLeaves[i] )
            return 0;
    return 1;
}

static int Map_YocoCutIsSupplied( Map_Man_t * p, Map_Node_t * pNode, Map_Cut_t * pCut )
{
    int Leaves[6], Root, i, r;
    if ( pCut->nLeaves == 1 )
        return 1;
    Root = Map_NodeReadAigId( pNode );
    for ( i = 0; i < pCut->nLeaves; i++ )
        Leaves[i] = Map_NodeReadAigId( pCut->ppLeaves[i] );
    Map_YocoSortInts( Leaves, pCut->nLeaves );
    for ( r = 0; r < p->nYocoSuppliedCuts; r++ )
        if ( Map_YocoCutMatchesRow( p, r, Root, Leaves, pCut->nLeaves ) )
            return 1;
    return 0;
}

static int Map_YocoCountMatchedCutsForRoot( Map_Man_t * p, Map_Node_t * pNode )
{
    Map_Cut_t * pCut;
    int nMatches = 0;
    for ( pCut = pNode->pCuts; pCut; pCut = pCut->pNext )
        if ( pCut->nLeaves > 1 && Map_YocoCutIsSupplied( p, pNode, pCut ) )
            nMatches++;
    return nMatches;
}

static void Map_YocoFilterSuppliedCuts( Map_Man_t * p )
{
    Map_Node_t * pNode;
    Map_Cut_t * pCut, * pNext, * pPrev;
    int i, nRootMatches;
    p->nYocoSuppliedMatchedCuts = 0;
    p->nYocoSuppliedFilteredCuts = 0;
    for ( i = 0; i < p->vMapObjs->nSize; i++ )
    {
        pNode = p->vMapObjs->pArray[i];
        nRootMatches = Map_YocoCountMatchedCutsForRoot( p, pNode );
        if ( nRootMatches == 0 )
            continue;
        pPrev = NULL;
        for ( pCut = pNode->pCuts; pCut; pCut = pNext )
        {
            pNext = pCut->pNext;
            if ( Map_YocoCutIsSupplied( p, pNode, pCut ) )
            {
                if ( pCut->nLeaves > 1 )
                    p->nYocoSuppliedMatchedCuts++;
                pPrev = pCut;
                continue;
            }
            if ( pPrev )
                pPrev->pNext = pNext;
            else
                pNode->pCuts = pNext;
            Map_CutFree( p, pCut );
            p->nYocoSuppliedFilteredCuts++;
        }
    }
    p->nYocoSuppliedMissingRows = p->nYocoSuppliedCuts - p->nYocoSuppliedMatchedCuts;
    if ( p->nYocoSuppliedMissingRows < 0 )
        p->nYocoSuppliedMissingRows = 0;
    p->nYocoExposedCuts = Map_MappingCountAllCuts( p );
    printf( "YOCO_SUPPLIED_CUT_FILTER {\"retained_nontrivial_cuts\":%d,\"filtered_nontrivial_cuts\":%d,\"missing_cut_rows\":%d,\"exposed_cuts\":%d,\"fallback_policy\":\"keep_all_cuts_for_roots_without_matched_supplied_cut\"}\n",
        p->nYocoSuppliedMatchedCuts, p->nYocoSuppliedFilteredCuts, p->nYocoSuppliedMissingRows, p->nYocoExposedCuts );
}

static Map_Cut_t * Map_YocoCreateElementaryCut( Map_Man_t * p, Map_Node_t * pNode )
{
    Map_Cut_t * pCut = Map_CutAlloc( p );
    pCut->nLeaves = 1;
    pCut->ppLeaves[0] = pNode;
    pCut->uTruth = 0xAAAAAAAA;
    pNode->pCuts = pCut;
    pNode->pCutBest[0] = NULL;
    pNode->pCutBest[1] = pCut;
    pCut->M[0].AreaFlow = 0.0;
    pCut->M[1].AreaFlow = 0.0;
    return pCut;
}

static int Map_YocoFindLeafIndex( Map_Node_t * pNode, Map_Node_t ** ppLeaves, int nLeaves )
{
    int i;
    for ( i = 0; i < nLeaves; i++ )
        if ( ppLeaves[i] == pNode )
            return i;
    return -1;
}

static int Map_YocoComputeTruth_rec( Map_Man_t * p, Map_Node_t * pNode, Map_Node_t ** ppLeaves, int nLeaves, unsigned uTruth[2] )
{
    unsigned uTruth0[2], uTruth1[2];
    Map_Node_t * pReg;
    int iLeaf;
    int fCompl = Map_IsComplement( pNode );
    pReg = Map_Regular( pNode );
    iLeaf = Map_YocoFindLeafIndex( pReg, ppLeaves, nLeaves );
    if ( iLeaf >= 0 )
    {
        uTruth[0] = p->uTruths[iLeaf][0];
        uTruth[1] = p->uTruths[iLeaf][1];
    }
    else if ( Map_NodeIsBuf( pReg ) )
    {
        if ( !Map_YocoComputeTruth_rec( p, pReg->p1, ppLeaves, nLeaves, uTruth ) )
            return 0;
    }
    else if ( Map_NodeIsAnd( pReg ) )
    {
        if ( !Map_YocoComputeTruth_rec( p, pReg->p1, ppLeaves, nLeaves, uTruth0 ) )
            return 0;
        if ( !Map_YocoComputeTruth_rec( p, pReg->p2, ppLeaves, nLeaves, uTruth1 ) )
            return 0;
        uTruth[0] = uTruth0[0] & uTruth1[0];
        uTruth[1] = uTruth0[1] & uTruth1[1];
    }
    else
        return 0;
    if ( fCompl )
    {
        uTruth[0] = ~uTruth[0];
        uTruth[1] = ~uTruth[1];
    }
    return 1;
}

static Map_Cut_t * Map_YocoCreateDirectCut( Map_Man_t * p, Map_Node_t * pRoot, Map_Node_t ** ppLeaves, int nLeaves )
{
    Map_Cut_t * pCut;
    int i;
    if ( nLeaves <= 0 || nLeaves > p->nVarsMax )
        return NULL;
    pCut = Map_CutAlloc( p );
    pCut->nLeaves = nLeaves;
    for ( i = 0; i < nLeaves; i++ )
        pCut->ppLeaves[i] = ppLeaves[i];
    if ( !Map_YocoComputeTruth_rec( p, pRoot, ppLeaves, nLeaves, pCut->uYocoTruth ) )
    {
        Map_CutFree( p, pCut );
        return NULL;
    }
    pCut->fYocoHasTruth = 1;
    pCut->pNext = pRoot->pCuts->pNext;
    pRoot->pCuts->pNext = pCut;
    return pCut;
}

static int Map_YocoBuildDirectCuts( Map_Man_t * p )
{
    Map_Node_t * pNode, * pRoot, * Leaves[6];
    int i, r, k;
    p->nYocoSuppliedMatchedCuts = 0;
    p->nYocoSuppliedFilteredCuts = 0;
    p->nYocoSuppliedMissingRows = 0;
    p->nYocoRawCuts = 0;
    for ( i = 0; i < p->nInputs; i++ )
        Map_YocoCreateElementaryCut( p, p->pInputs[i] );
    for ( i = 0; i < p->vMapObjs->nSize; i++ )
    {
        pNode = p->vMapObjs->pArray[i];
        if ( Map_NodeIsBuf(pNode) )
            Map_YocoCreateElementaryCut( p, pNode );
        else if ( Map_NodeIsAnd(pNode) )
        {
            Map_YocoCreateElementaryCut( p, pNode );
            Leaves[0] = Map_Regular(pNode->p1);
            Leaves[1] = Map_Regular(pNode->p2);
            if ( Leaves[0] != Leaves[1] && Map_YocoCreateDirectCut( p, pNode, Leaves, 2 ) )
                p->nYocoRawCuts++;
        }
    }
    for ( r = 0; r < p->nYocoSuppliedCuts; r++ )
    {
        pRoot = Map_YocoFindNodeByAigId( p, p->pYocoSuppliedRoots[r] );
        if ( pRoot == NULL || !Map_NodeIsAnd(pRoot) )
        {
            p->nYocoSuppliedMissingRows++;
            continue;
        }
        for ( k = 0; k < p->pYocoSuppliedLeafCounts[r]; k++ )
        {
            Leaves[k] = Map_YocoFindNodeByAigId( p, p->pYocoSuppliedLeaves[6*r + k] );
            if ( Leaves[k] == NULL )
                break;
        }
        if ( k != p->pYocoSuppliedLeafCounts[r] || !Map_YocoCreateDirectCut( p, pRoot, Leaves, p->pYocoSuppliedLeafCounts[r] ) )
        {
            p->nYocoSuppliedMissingRows++;
            continue;
        }
        p->nYocoSuppliedMatchedCuts++;
        p->nYocoRawCuts++;
    }
    p->nYocoExposedCuts = Map_MappingCountAllCuts( p );
    printf( "YOCO_SUPPLIED_CUT_DIRECT {\"supplied_constructed_cut_count\":%d,\"supplied_missing_cut_rows\":%d,\"fallback_two_input_cut_count\":%d,\"exposed_cuts\":%d}\n",
        p->nYocoSuppliedMatchedCuts, p->nYocoSuppliedMissingRows,
        p->nYocoRawCuts - p->nYocoSuppliedMatchedCuts, p->nYocoExposedCuts );
    return 1;
}

static int Map_YocoScanSuppliedCuts( Map_Man_t * p )
{
    FILE * pFile;
    char pLine[8192];
    int nLines = 0, nCuts = 0, nModel = 0, nFallback = 0, nOracle = 0, fHeader = 0;
    int nInvalidRoot = 0, nInvalidLeaf = 0, nDuplicateLeaf = 0, nRootInLeaves = 0, nParseErrors = 0;
    pFile = fopen( p->pYocoSuppliedCuts, "r" );
    if ( pFile == NULL )
    {
        printf( "YOCO supplied-cut file cannot be opened: %s\n", p->pYocoSuppliedCuts );
        return 0;
    }
    while ( fgets( pLine, sizeof(pLine), pFile ) )
    {
        char * pCur = pLine;
        while ( *pCur == ' ' || *pCur == '\t' || *pCur == '\r' || *pCur == '\n' )
            pCur++;
        if ( *pCur == 0 )
            continue;
        nLines++;
        if ( strstr( pCur, "\"schema_version\"" ) && strstr( pCur, "\"circuit\"" ) )
        {
            fHeader = 1;
            if ( !Map_YocoJsonReadString( pCur, "\"aig_sha256\"", p->pYocoHeaderAigSha256, 65 ) )
                p->pYocoHeaderAigSha256[0] = 0;
            continue;
        }
        if ( strstr( pCur, "\"root\"" ) && strstr( pCur, "\"leaves\"" ) )
        {
            int Root = -1, Leaves[6], nLeaves, i, k, fBadLeaf = 0, fDupLeaf = 0, fRootInLeaves = 0;
            if ( strstr( pCur, "\"source\": \"model\"" ) || strstr( pCur, "\"source\":\"model\"" ) )
                nModel++;
            else if ( strstr( pCur, "\"source\": \"fallback\"" ) || strstr( pCur, "\"source\":\"fallback\"" ) )
                nFallback++;
            else if ( strstr( pCur, "\"source\": \"oracle_golden\"" ) || strstr( pCur, "\"source\":\"oracle_golden\"" ) )
                nOracle++;
            if ( !Map_YocoJsonReadInt( pCur, "\"root\"", &Root ) )
            {
                nParseErrors++;
                continue;
            }
            nLeaves = Map_YocoJsonReadLeaves( pCur, Leaves, p->nVarsMax );
            if ( nLeaves <= 0 )
            {
                nParseErrors++;
                continue;
            }
            if ( Map_YocoFindNodeByAigId( p, Root ) == NULL )
                nInvalidRoot++;
            for ( i = 0; i < nLeaves; i++ )
            {
                if ( Leaves[i] == Root )
                    fRootInLeaves = 1;
                if ( Map_YocoFindNodeByAigId( p, Leaves[i] ) == NULL )
                    fBadLeaf = 1;
                for ( k = i + 1; k < nLeaves; k++ )
                    if ( Leaves[i] == Leaves[k] )
                        fDupLeaf = 1;
            }
            nInvalidLeaf += fBadLeaf;
            nDuplicateLeaf += fDupLeaf;
            nRootInLeaves += fRootInLeaves;
            if ( !fBadLeaf && !fDupLeaf && !fRootInLeaves && Map_YocoFindNodeByAigId( p, Root ) != NULL )
            {
                Map_YocoStoreSuppliedCut( p, Root, Leaves, nLeaves );
                nCuts++;
            }
        }
    }
    fclose( pFile );
    if ( nParseErrors || nInvalidRoot || nInvalidLeaf || nDuplicateLeaf || nRootInLeaves )
    {
        printf( "YOCO supplied-cut structural validation failed: parse_errors=%d invalid_roots=%d invalid_leaf_rows=%d duplicate_leaf_rows=%d root_in_leaf_rows=%d\n", nParseErrors, nInvalidRoot, nInvalidLeaf, nDuplicateLeaf, nRootInLeaves );
        return 0;
    }
    if ( !fHeader )
    {
        printf( "YOCO supplied-cut file is missing a schema header: %s\n", p->pYocoSuppliedCuts );
        return 0;
    }
    if ( p->pYocoHeaderAigSha256[0] == 0 )
    {
        printf( "YOCO supplied-cut file header is missing aig_sha256: %s\n", p->pYocoSuppliedCuts );
        return 0;
    }
    if ( !Map_YocoSha256File( p->pYocoAigFileName, p->pYocoLoadedAigSha256 ) )
    {
        printf( "YOCO supplied-cut AIG hash cannot be computed from loaded network file: %s\n", p->pYocoAigFileName ? p->pYocoAigFileName : "<none>" );
        return 0;
    }
    if ( strcmp( p->pYocoHeaderAigSha256, p->pYocoLoadedAigSha256 ) != 0 )
    {
        printf( "YOCO supplied-cut AIG hash mismatch: header=%s loaded=%s file=%s\n", p->pYocoHeaderAigSha256, p->pYocoLoadedAigSha256, p->pYocoAigFileName ? p->pYocoAigFileName : "<none>" );
        return 0;
    }
    if ( nCuts == 0 )
    {
        printf( "YOCO supplied-cut file contains no cut rows: %s\n", p->pYocoSuppliedCuts );
        return 0;
    }
    p->nYocoSuppliedCuts = nCuts;
    p->nYocoSuppliedModelCuts = nModel;
    p->nYocoSuppliedFallbackCuts = nFallback;
    p->nYocoSuppliedOracleCuts = nOracle;
    printf( "YOCO supplied-cut file accepted by ABC front end: %s\n", p->pYocoSuppliedCuts );
    printf( "YOCO_SUPPLIED_CUT_FILE {\"lines\":%d,\"cuts\":%d,\"model_cuts\":%d,\"fallback_cuts\":%d,\"oracle_cuts\":%d,\"parse_errors\":%d,\"invalid_roots\":%d,\"invalid_leaf_rows\":%d,\"duplicate_leaf_rows\":%d,\"root_in_leaf_rows\":%d,\"aig_sha256_match\":1}\n", nLines, nCuts, nModel, nFallback, nOracle, nParseErrors, nInvalidRoot, nInvalidLeaf, nDuplicateLeaf, nRootInLeaves );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Performs technology mapping for the given object graph.]

  Description [The object graph is stored in the mapping manager.
  First, the AND nodes that fanout into POs are collected in the DFS order.
  Two preprocessing steps are performed: the k-feasible cuts are computed 
  for each node and the truth tables are computed for each cut. Next, the 
  delay-optimal matches are assigned for each node, followed by several 
  iterations of area recoveryd: using area flow (global optimization) 
  and using exact area at a node (local optimization).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Map_Mapping( Map_Man_t * p )
{
    int fShowSwitching         = 0;
    int fUseAreaFlow           = 1;
    int fUseExactArea          = !p->fSwitching;
    int fUseExactAreaWithPhase = !p->fSwitching;
    abctime clk;

    if ( p->pYocoSuppliedCuts )
        p->fYocoNoDominance = 1;
    if ( p->pYocoSuppliedCuts && !Map_YocoScanSuppliedCuts( p ) )
    {
        printf( "YOCO_MAP_STATS {\"supplied_mode\":1,\"supplied_file_valid\":0,\"exhaustive_enumerated_cut_count\":0,\"exhaustive_boolean_match_count\":0,\"raw_cuts\":0,\"exposed_cuts\":0,\"selected_cuts\":0}\n" );
        return 0;
    }

    //////////////////////////////////////////////////////////////////////
    // perform pre-mapping computations
    if ( p->fVerbose )
        Map_MappingReportChoices( p ); 
    Map_MappingSetChoiceLevels( p ); // should always be called before mapping!
//    return 1;

    // compute the cuts of nodes in the DFS order
    clk = Abc_Clock();
    if ( p->pYocoSuppliedCuts )
        Map_YocoBuildDirectCuts( p );
    else
        Map_MappingCuts( p );
    p->timeCuts = Abc_Clock() - clk;
    // derive the truth tables 
    clk = Abc_Clock();
    Map_MappingTruths( p );
    p->timeTruth = Abc_Clock() - clk;
    //////////////////////////////////////////////////////////////////////
//ABC_PRT( "Truths", Abc_Clock() - clk );

    //////////////////////////////////////////////////////////////////////
    // compute the minimum-delay mapping
    clk = Abc_Clock();
    p->fMappingMode = 0;
    if ( !Map_MappingMatches( p ) )
        return 0;
    p->timeMatch = Abc_Clock() - clk;
    // compute the references and collect the nodes used in the mapping
    Map_MappingSetRefs( p );
    p->AreaBase = Map_MappingGetArea( p );
if ( p->fVerbose )
{
printf( "Delay    : %s = %8.2f  Flow = %11.1f  Area = %11.1f  %4.1f %%   ", 
                    fShowSwitching? "Switch" : "Delay", 
                    fShowSwitching? Map_MappingGetSwitching(p) : p->fRequiredGlo, 
                    Map_MappingGetAreaFlow(p), p->AreaBase, 0.0 );
ABC_PRT( "Time", p->timeMatch );
}
    //////////////////////////////////////////////////////////////////////

    if ( !p->fAreaRecovery )
    {
        if ( p->fVerbose )
            Map_MappingPrintOutputArrivals( p );
        return 1;
    }

    //////////////////////////////////////////////////////////////////////
    // perform area recovery using area flow
    clk = Abc_Clock();
    if ( fUseAreaFlow )
    {
        // compute the required times
        Map_TimeComputeRequiredGlobal( p );
        // recover area flow
        p->fMappingMode = 1;
        Map_MappingMatches( p );
        // compute the references and collect the nodes used in the mapping
        Map_MappingSetRefs( p );
        p->AreaFinal = Map_MappingGetArea( p );
if ( p->fVerbose )
{
printf( "AreaFlow : %s = %8.2f  Flow = %11.1f  Area = %11.1f  %4.1f %%   ", 
                    fShowSwitching? "Switch" : "Delay", 
                    fShowSwitching? Map_MappingGetSwitching(p) : p->fRequiredGlo, 
                    Map_MappingGetAreaFlow(p), p->AreaFinal, 
                    100.0*(p->AreaBase-p->AreaFinal)/p->AreaBase );
ABC_PRT( "Time", Abc_Clock() - clk );
}
    }
    p->timeArea += Abc_Clock() - clk;
    //////////////////////////////////////////////////////////////////////

    //////////////////////////////////////////////////////////////////////
    // perform area recovery using exact area
    clk = Abc_Clock();
    if ( fUseExactArea )
    {
        // compute the required times
        Map_TimeComputeRequiredGlobal( p );
        // recover area
        p->fMappingMode = 2;
        Map_MappingMatches( p );
        // compute the references and collect the nodes used in the mapping
        Map_MappingSetRefs( p );
        p->AreaFinal = Map_MappingGetArea( p );
if ( p->fVerbose )
{
printf( "Area     : %s = %8.2f  Flow = %11.1f  Area = %11.1f  %4.1f %%   ", 
                    fShowSwitching? "Switch" : "Delay", 
                    fShowSwitching? Map_MappingGetSwitching(p) : p->fRequiredGlo, 
                    0.0, p->AreaFinal, 
                    100.0*(p->AreaBase-p->AreaFinal)/p->AreaBase );
ABC_PRT( "Time", Abc_Clock() - clk );
}
    }
    p->timeArea += Abc_Clock() - clk;
    //////////////////////////////////////////////////////////////////////

    //////////////////////////////////////////////////////////////////////
    // perform area recovery using exact area
    clk = Abc_Clock();
    if ( fUseExactAreaWithPhase )
    {
        // compute the required times
        Map_TimeComputeRequiredGlobal( p );
        // recover area
        p->fMappingMode = 3;
        Map_MappingMatches( p );
        // compute the references and collect the nodes used in the mapping
        Map_MappingSetRefs( p );
        p->AreaFinal = Map_MappingGetArea( p );
if ( p->fVerbose )
{
printf( "Area     : %s = %8.2f  Flow = %11.1f  Area = %11.1f  %4.1f %%   ", 
                    fShowSwitching? "Switch" : "Delay", 
                    fShowSwitching? Map_MappingGetSwitching(p) : p->fRequiredGlo, 
                    0.0, p->AreaFinal, 
                    100.0*(p->AreaBase-p->AreaFinal)/p->AreaBase );
ABC_PRT( "Time", Abc_Clock() - clk );
}
    }
    p->timeArea += Abc_Clock() - clk;
    //////////////////////////////////////////////////////////////////////

    //////////////////////////////////////////////////////////////////////
    // perform area recovery using exact area
    clk = Abc_Clock();
    if ( p->fSwitching )
    {
        // compute the required times
        Map_TimeComputeRequiredGlobal( p );
        // recover switching activity
        p->fMappingMode = 4;
        Map_MappingMatches( p );
        // compute the references and collect the nodes used in the mapping
        Map_MappingSetRefs( p );
        p->AreaFinal = Map_MappingGetArea( p );
if ( p->fVerbose )
{
printf( "Switching: %s = %8.2f  Flow = %11.1f  Area = %11.1f  %4.1f %%   ", 
                    fShowSwitching? "Switch" : "Delay", 
                    fShowSwitching? Map_MappingGetSwitching(p) : p->fRequiredGlo, 
                    0.0, p->AreaFinal, 
                    100.0*(p->AreaBase-p->AreaFinal)/p->AreaBase );
ABC_PRT( "Time", Abc_Clock() - clk );
}

        // compute the required times
        Map_TimeComputeRequiredGlobal( p );
        // recover switching activity
        p->fMappingMode = 4;
        Map_MappingMatches( p );
        // compute the references and collect the nodes used in the mapping
        Map_MappingSetRefs( p );
        p->AreaFinal = Map_MappingGetArea( p );
if ( p->fVerbose )
{
printf( "Switching: %s = %8.2f  Flow = %11.1f  Area = %11.1f  %4.1f %%   ", 
                    fShowSwitching? "Switch" : "Delay", 
                    fShowSwitching? Map_MappingGetSwitching(p) : p->fRequiredGlo, 
                    0.0, p->AreaFinal, 
                    100.0*(p->AreaBase-p->AreaFinal)/p->AreaBase );
ABC_PRT( "Time", Abc_Clock() - clk );
}
    }
    p->timeArea += Abc_Clock() - clk;
    //////////////////////////////////////////////////////////////////////

    // print the arrival times of the latest outputs
    if ( p->fVerbose )
        Map_MappingPrintOutputArrivals( p );
    return 1;
}
ABC_NAMESPACE_IMPL_END

