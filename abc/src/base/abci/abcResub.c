/**CFile****************************************************************

  FileName    [abcResub.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Resubstitution manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcResub.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "bool/dec/dec.h"
#include "misc/extra/extra.h"
#include "proof/cec/cec.h"

ABC_NAMESPACE_IMPL_START

 
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ABC_RS_DIV1_MAX    150   // the max number of divisors to consider
#define ABC_RS_DIV2_MAX    500   // the max number of pair-wise divisors to consider
#define ABC_RS_SIM_WORDS    32   // 2048 deterministic global simulation patterns

typedef struct SimResub_Exp_t_ SimResub_Exp_t;
struct SimResub_Exp_t_
{
    Abc_Obj_t * pLeaf;
    int iLeft;
    int iRight;
    int Cost;
    int Level;
    word * pSim;
    unsigned * pTruth;
};

typedef struct SimResub_Work_t_ SimResub_Work_t;
struct SimResub_Work_t_
{
    SimResub_Exp_t * pExps;
    int nSize;
    int nCap;
    int nWords;
    int nSimWords;
    int nHash;
    int * pBins;
    int * pNext;
};

typedef struct Abc_ManRes_t_ Abc_ManRes_t;
struct Abc_ManRes_t_
{
    // paramers
    int                nLeavesMax; // the max number of leaves in the cone
    int                nDivsMax;   // the max number of divisors in the cone
    // resub problem dumping
    int                Log2Probs;
    int                Log2Divs;
    int                nProbs;
    FILE *             pFile;
    // representation of the cone
    Abc_Obj_t *        pRoot;      // the root of the cone
    int                nLeaves;    // the number of leaves
    int                nDivs;      // the number of all divisor (including leaves)
    int                nMffc;      // the size of MFFC
    int                nLastGain;  // the gain the number of nodes
    Vec_Ptr_t *        vDivs;      // the divisors
    // representation of the simulation info
    int                nBits;      // the number of simulation bits
    int                nWords;     // the number of unsigneds for siminfo
    Vec_Ptr_t        * vSims;      // simulation info
    unsigned         * pInfo;      // pointer to simulation info
    // observability don't-cares
    unsigned *         pCareSet;
    unsigned *         pTempSim;
    // internal divisor storage
    Vec_Ptr_t        * vDivs1UP;   // the single-node unate divisors
    Vec_Ptr_t        * vDivs1UN;   // the single-node unate divisors
    Vec_Ptr_t        * vDivs1B;    // the single-node binate divisors
    Vec_Ptr_t        * vDivs2UP0;  // the double-node unate divisors
    Vec_Ptr_t        * vDivs2UP1;  // the double-node unate divisors
    Vec_Ptr_t        * vDivs2UN0;  // the double-node unate divisors
    Vec_Ptr_t        * vDivs2UN1;  // the double-node unate divisors
    // other data
    Vec_Ptr_t        * vTemp;      // temporary array of nodes
    // runtime statistics
    abctime            timeCut;
    abctime            timeTruth;
    abctime            timeRes;
    abctime            timeDiv;
    abctime            timeMffc;
    abctime            timeSim;
    abctime            timeRes1;
    abctime            timeResD;
    abctime            timeRes2;
    abctime            timeRes3;
    abctime            timeNtk;
    abctime            timeTotal;
    // improvement statistics
    int                nUsedNodeC;
    int                nUsedNode0;
    int                nUsedNode1Or;
    int                nUsedNode1And;
    int                nUsedNode2Or;
    int                nUsedNode2And;
    int                nUsedNode2OrAnd;
    int                nUsedNode2AndOr;
    int                nUsedNode3OrAnd;
    int                nUsedNode3AndOr;
    int                nUsedNodeTotal;
    int                nTotalDivs;
    int                nTotalLeaves;
    int                nTotalGain;
    int                nNodesBeg;
    int                nNodesEnd;
    int                fUseSim;
    int                nSimCandMax;
    int                nPairMax;
    int                fPairUseful;
    int                nSuppMax;
    int                fBestCand;
    int                fFirstMatch;
    int                fUseLevel;
    int                fLimitHit;
    int                nGlobalObjs;
    int                nHashSize;
    word *             pGlobalSims;
    int *              pHashBins;
    int *              pHashNext;
    unsigned char *    pHashPhase;
    ABC_INT64_T        nStructCands;
    ABC_INT64_T        nSimCands;
    ABC_INT64_T        nSimCands0;
    ABC_INT64_T        nSimCands1;
    ABC_INT64_T        nAcceptedStruct;
    ABC_INT64_T        nAcceptedSim;
    ABC_INT64_T        nSimTargets;
    ABC_INT64_T        nLegalHashLits;
    ABC_INT64_T        nImplLits;
    ABC_INT64_T        nPairsTried;
    ABC_INT64_T        nIntermsGenerated;
    ABC_INT64_T        nSubmitted;
    ABC_INT64_T        nPassedExact;
    ABC_INT64_T        nGenCost[6];
    ABC_INT64_T        nAcceptedCost[6];
    ABC_INT64_T        nBestGain[16];
    ABC_INT64_T        nTargets0;
    ABC_INT64_T        nRejectedSim;
    ABC_INT64_T        nRejectedLegal;
    ABC_INT64_T        nRejectedLevel;
    ABC_INT64_T        nRejectedExact;
    ABC_INT64_T        nRejectedGain;
    ABC_INT64_T        nFirstNotBest;
    ABC_INT64_T        nZeroBucketsGt1;
    ABC_INT64_T        nZeroRaw;
    ABC_INT64_T        nZeroLegal;
    ABC_INT64_T        nZeroChecked;
    ABC_INT64_T        nZeroAccepted;
    ABC_INT64_T        nZeroRejectedForbidden;
    ABC_INT64_T        nZeroRejectedLevel;
    ABC_INT64_T        nZeroRejectedGain;
    ABC_INT64_T        nZeroNoMatch;
};

// external procedures
static Abc_ManRes_t* Abc_ManResubStart( int nLeavesMax, int nDivsMax );
static void          Abc_ManResubStop( Abc_ManRes_t * p );
static Dec_Graph_t * Abc_ManResubEval( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int nSteps, int fUpdateLevel, int fVerbose );
static int           Abc_NtkSimResubZeroSweep( Abc_ManRes_t * p, int fUpdateLevel, int fVerbose );
static Dec_Graph_t * Abc_ManSimResubEvalExplicit( Abc_ManRes_t * p, int nSteps, int Required );
extern int           Dec_GraphToNetworkCount( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int nSteps, int Required );
extern Gia_Man_t *   Abc_NtkToGia2( Abc_Ntk_t * p, int fUseXors );
static void          Abc_ManResubCleanup( Abc_ManRes_t * p );
static void          Abc_ManResubPrint( Abc_ManRes_t * p );

// other procedures
static int           Abc_ManResubCollectDivs( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int Required );
static int           Abc_ManResubCollectDivsSim( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int Required );
static void          Abc_ManResubBuildGlobalSim( Abc_ManRes_t * p );
static void          Abc_ManResubSimulate( Vec_Ptr_t * vDivs, int nLeaves, Vec_Ptr_t * vSims, int nLeavesMax, int nWords );
static void          Abc_ManResubPrintDivs( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves );

static void          Abc_ManResubDivsS( Abc_ManRes_t * p, int Required );
static void          Abc_ManResubDivsD( Abc_ManRes_t * p, int Required );
static Dec_Graph_t * Abc_ManResubQuit( Abc_ManRes_t * p );
static Dec_Graph_t * Abc_ManResubDivs0( Abc_ManRes_t * p );
static Dec_Graph_t * Abc_ManResubDivs1( Abc_ManRes_t * p, int Required );
static Dec_Graph_t * Abc_ManResubDivs12( Abc_ManRes_t * p, int Required );
static Dec_Graph_t * Abc_ManResubDivs2( Abc_ManRes_t * p, int Required );
static Dec_Graph_t * Abc_ManResubDivs3( Abc_ManRes_t * p, int Required );

static Vec_Ptr_t *   Abc_CutFactorLarge( Abc_Obj_t * pNode, int nLeavesMax );
static int           Abc_CutVolumeCheck( Abc_Obj_t * pNode, Vec_Ptr_t * vLeaves );

//extern abctime s_ResubTime;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs incremental resynthesis of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_NtkResubstituteInt( Abc_Ntk_t * pNtk, int nCutMax, int nStepsMax, int nMinSaved, int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose, int Log2Probs, int Log2Divs, int fUseSim, int nSimCandMax, int nPairMax, int fPairUseful, int nSuppMax, int fBestCand, int fFirstMatch, int fUseLevel )
{
    extern int           Dec_GraphUpdateNetwork( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int fUpdateLevel, int nGain );
    ProgressBar * pProgress;
    Abc_ManRes_t * pManRes;
    Abc_ManCut_t * pManCut;
    Odc_Man_t * pManOdc = NULL;
    Dec_Graph_t * pFForm;
    Vec_Ptr_t * vLeaves;
    Abc_Obj_t * pNode;
    abctime clk, clkStart = Abc_Clock();
    int i, nNodes;

    assert( Abc_NtkIsStrash(pNtk) );

    // cleanup the AIG
    Abc_AigCleanup((Abc_Aig_t *)pNtk->pManFunc);
    // start the managers
    pManCut = Abc_NtkManCutStart( nCutMax, 100000, 100000, 100000 );
    pManRes = Abc_ManResubStart( nCutMax, fUseSim ? Abc_NtkNodeNum(pNtk) + nCutMax + 1 : ABC_RS_DIV1_MAX );
    pManRes->fUseSim = fUseSim;
    pManRes->nSimCandMax = nSimCandMax;
    pManRes->nPairMax = nPairMax;
    pManRes->fPairUseful = fPairUseful;
    pManRes->nSuppMax = nSuppMax;
    pManRes->fBestCand = fBestCand;
    pManRes->fFirstMatch = fFirstMatch;
    pManRes->fUseLevel = fUseLevel;
    if ( Log2Probs && Log2Divs )
    {
        pManRes->Log2Probs = Log2Probs;
        pManRes->Log2Divs = Log2Divs;
        pManRes->nProbs = 0;
        char * pName = Extra_FileNameGeneric(Extra_FileNameWithoutPath(pNtk->pName));
        char pFileName[100]; sprintf( pFileName, "p%02dd%02dv%02d_%s.bin", Log2Probs, nCutMax, Log2Divs, pName );
        ABC_FREE( pName );
        pManRes->pFile = fopen( pFileName, "wb" );
        if ( pManRes->pFile == NULL ) {
            printf( "Cannot open output file \"%s\".\n", pFileName );
            return 1;
        }
        printf( "Collecting resub problems into binary file \"%s\" expected to take %.3f MB...\n", pFileName, 1.0*(1 << Log2Probs)*(1 << Log2Divs)*(1 << (nCutMax-3)) / (1 << 20) );
    }
    if ( nLevelsOdc > 0 )
    pManOdc = Abc_NtkDontCareAlloc( nCutMax, nLevelsOdc, fVerbose, fVeryVerbose );

    // compute the reverse levels if level update is requested
    if ( fUpdateLevel )
        Abc_NtkStartReverseLevels( pNtk, 0 );

    if ( Abc_NtkLatchNum(pNtk) ) {
        Abc_NtkForEachLatch(pNtk, pNode, i)
            pNode->pNext = (Abc_Obj_t *)pNode->pData;
    }

    // resynthesize each node once
    pManRes->nNodesBeg = Abc_NtkNodeNum(pNtk);
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart( stdout, nNodes );
    //clear markAB at the beginning
    Abc_NtkCleanMarkAB( pNtk );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // skip the constant node
//        if ( Abc_NodeIsConst(pNode) )
//            continue;
        // skip persistant nodes
        if ( Abc_NodeIsPersistant(pNode) )
            continue;
        // skip the nodes with many fanouts
        if ( Abc_ObjFanoutNum(pNode) > 1000 )
            continue;
        // stop if all nodes have been tried once
        if ( i >= nNodes )
            break;

        // compute a reconvergence-driven cut
clk = Abc_Clock();
        vLeaves = Abc_NodeFindCut( pManCut, pNode, 0 );
//        vLeaves = Abc_CutFactorLarge( pNode, nCutMax );
pManRes->timeCut += Abc_Clock() - clk;
/*
        if ( fVerbose && vLeaves )
        printf( "Node %6d : Leaves = %3d. Volume = %3d.\n", pNode->Id, Vec_PtrSize(vLeaves), Abc_CutVolumeCheck(pNode, vLeaves) );
        if ( vLeaves == NULL )
            continue;
*/
        // get the don't-cares
        if ( pManOdc )
        {
clk = Abc_Clock();
            Abc_NtkDontCareClear( pManOdc );
            Abc_NtkDontCareCompute( pManOdc, pNode, vLeaves, pManRes->pCareSet );
pManRes->timeTruth += Abc_Clock() - clk;
        }

        // evaluate this cut
clk = Abc_Clock();
        pFForm = Abc_ManResubEval( pManRes, pNode, vLeaves, nStepsMax, fUpdateLevel, fVerbose );
//        Vec_PtrFree( vLeaves );
//        Abc_ManResubCleanup( pManRes );
pManRes->timeRes += Abc_Clock() - clk;
        if ( pFForm == NULL )
            continue;
        if ( pManRes->nLastGain < nMinSaved )
        {
            Dec_GraphFree( pFForm );
            continue;
        }
        pManRes->nTotalGain += pManRes->nLastGain;
/*
        if ( pManRes->nLeaves == 4 && pManRes->nMffc == 2 && pManRes->nLastGain == 1 )
        {
            printf( "%6d :  L = %2d. V = %2d. Mffc = %2d. Divs = %3d.   Up = %3d. Un = %3d. B = %3d.\n", 
                   pNode->Id, pManRes->nLeaves, Abc_CutVolumeCheck(pNode, vLeaves), pManRes->nMffc, pManRes->nDivs, 
                   pManRes->vDivs1UP->nSize, pManRes->vDivs1UN->nSize, pManRes->vDivs1B->nSize );
            Abc_ManResubPrintDivs( pManRes, pNode, vLeaves );
        }
*/
        // acceptable replacement found, update the graph
clk = Abc_Clock();
        Dec_GraphUpdateNetwork( pNode, pFForm, fUpdateLevel, pManRes->nLastGain );
pManRes->timeNtk += Abc_Clock() - clk;
        Dec_GraphFree( pFForm );
    }
    Extra_ProgressBarStop( pProgress );
pManRes->timeTotal = Abc_Clock() - clkStart;
    pManRes->nNodesEnd = Abc_NtkNodeNum(pNtk);

    // print statistics
    if ( fVerbose )
    Abc_ManResubPrint( pManRes );

    if ( Log2Probs && Log2Divs )
    {
        fclose( pManRes->pFile );
        pManRes->pFile = NULL;
        char pFileName[100]; sprintf( pFileName, "p%02dd%02dv%02d.bin", Log2Probs, nCutMax, Log2Divs );
        printf( "Finished writing file \"%s\" containing %d (out of requested %d) resub problems,\n", pFileName, pManRes->nProbs, 1<<Log2Probs );
        printf( "each having %d divisors with support size %d (including the on-set and the off-set).  ", 1<<Log2Divs, nCutMax );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    }

    // delete the managers
    Abc_ManResubStop( pManRes );
    Abc_NtkManCutStop( pManCut );
    if ( pManOdc ) Abc_NtkDontCareFree( pManOdc );

    // clean the data field
    Abc_NtkForEachObj( pNtk, pNode, i )
        pNode->pData = NULL, pNode->fMarkC = 0;

    if ( Abc_NtkLatchNum(pNtk) ) {
        Abc_NtkForEachLatch(pNtk, pNode, i)
            pNode->pData = pNode->pNext, pNode->pNext = NULL;
    }

    // put the nodes into the DFS order and reassign their IDs
    Abc_NtkReassignIds( pNtk );
//    Abc_AigCheckFaninOrder( pNtk->pManFunc );
    // fix the levels
    if ( fUpdateLevel )
        Abc_NtkStopReverseLevels( pNtk );
    else
        Abc_NtkLevel( pNtk );
    // check
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkRefactor: The network check has failed.\n" );
        return 0;
    }
//s_ResubTime = Abc_Clock() - clkStart;
    return 1;
}




/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkResubstitute( Abc_Ntk_t * pNtk, int nCutMax, int nStepsMax, int nMinSaved, int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose, int Log2Probs, int Log2Divs )
{
    return Abc_NtkResubstituteInt( pNtk, nCutMax, nStepsMax, nMinSaved, nLevelsOdc, fUpdateLevel, fVerbose, fVeryVerbose, Log2Probs, Log2Divs, 0, 0, 0, 1, 0, 0, 0, 1 );
}

int Abc_NtkSimResubstitute( Abc_Ntk_t * pNtk, int nCutMax, int nStepsMax, int nSimCandMax, int nPairMax, int nSuppMax, int fPairUseful, int fBestCand, int fFirstMatch, int fUseLevel, int fUpdateLevel, int fVerbose )
{
    return Abc_NtkResubstituteInt( pNtk, nCutMax, nStepsMax, 1, 0, fUpdateLevel, fVerbose, 0, 0, 0, 1, nSimCandMax, nPairMax, fPairUseful, nSuppMax, fBestCand, fFirstMatch, fUseLevel );
}

int Abc_NtkSimResubstituteZero( Abc_Ntk_t * pNtk, int fUseLevel, int fUpdateLevel, int fVerbose )
{
    Abc_ManRes_t * pManRes;
    Abc_Obj_t * pNode;
    int i;
    if ( pNtk == NULL || !Abc_NtkIsStrash( pNtk ) )
        return 0;
    pManRes = Abc_ManResubStart( 0, 1 );
    pManRes->fUseLevel = fUseLevel;
    pManRes->pRoot = NULL;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        pManRes->pRoot = pNode;
        break;
    }
    if ( pManRes->pRoot == NULL )
    {
        Abc_ManResubStop( pManRes );
        return 1;
    }
    Abc_NtkSimResubZeroSweep( pManRes, fUpdateLevel, fVerbose );
    Abc_ManResubStop( pManRes );
    return 1;
}

Abc_ManRes_t * Abc_ManResubStart( int nLeavesMax, int nDivsMax )
{
    Abc_ManRes_t * p;
    unsigned * pData;
    int i, k;
    assert( sizeof(unsigned) == 4 );
    p = ABC_ALLOC( Abc_ManRes_t, 1 );
    memset( p, 0, sizeof(Abc_ManRes_t) );
    p->nLeavesMax = nLeavesMax;
    p->nDivsMax   = nDivsMax;
    p->vDivs      = Vec_PtrAlloc( p->nDivsMax );
    // allocate simulation info
    p->nBits      = (1 << p->nLeavesMax);
    p->nWords     = (p->nBits <= 32)? 1 : (p->nBits / 32);
    p->pInfo      = ABC_ALLOC( unsigned, p->nWords * (p->nDivsMax + 1) );
    memset( p->pInfo, 0, sizeof(unsigned) * p->nWords * p->nLeavesMax );
    p->vSims      = Vec_PtrAlloc( p->nDivsMax );
    for ( i = 0; i < p->nDivsMax; i++ )
        Vec_PtrPush( p->vSims, p->pInfo + i * p->nWords );
    // assign the care set
    p->pCareSet  = p->pInfo + p->nDivsMax * p->nWords;
    Abc_InfoFill( p->pCareSet, p->nWords );
    // set elementary truth tables
    for ( k = 0; k < p->nLeavesMax; k++ )
    {
        pData = (unsigned *)p->vSims->pArray[k];
        for ( i = 0; i < p->nBits; i++ )
            if ( i & (1 << k) )
                pData[i>>5] |= (1 << (i&31));
    }
    p->pTempSim   = ABC_CALLOC( unsigned, p->nWords );
    // create the remaining divisors
    p->vDivs1UP  = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs1UN  = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs1B   = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UP0 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UP1 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UN0 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UN1 = Vec_PtrAlloc( p->nDivsMax );
    p->vTemp     = Vec_PtrAlloc( p->nDivsMax );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ManResubStop( Abc_ManRes_t * p )
{
    Vec_PtrFree( p->vDivs );
    Vec_PtrFree( p->vSims );
    Vec_PtrFree( p->vDivs1UP );
    Vec_PtrFree( p->vDivs1UN );
    Vec_PtrFree( p->vDivs1B );
    Vec_PtrFree( p->vDivs2UP0 );
    Vec_PtrFree( p->vDivs2UP1 );
    Vec_PtrFree( p->vDivs2UN0 );
    Vec_PtrFree( p->vDivs2UN1 );
    Vec_PtrFree( p->vTemp );
    ABC_FREE( p->pTempSim );
    ABC_FREE( p->pInfo );
    ABC_FREE( p->pGlobalSims );
    ABC_FREE( p->pHashBins );
    ABC_FREE( p->pHashNext );
    ABC_FREE( p->pHashPhase );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ManResubPrint( Abc_ManRes_t * p )
{
    printf( "Used constants    = %6d.             ", p->nUsedNodeC );          ABC_PRT( "Cuts  ", p->timeCut );
    printf( "Used replacements = %6d.             ", p->nUsedNode0 );          ABC_PRT( "Resub ", p->timeRes );
    printf( "Used single ORs   = %6d.             ", p->nUsedNode1Or );        ABC_PRT( " Div  ", p->timeDiv );
    printf( "Used single ANDs  = %6d.             ", p->nUsedNode1And );       ABC_PRT( " Mffc ", p->timeMffc );
    printf( "Used double ORs   = %6d.             ", p->nUsedNode2Or );        ABC_PRT( " Sim  ", p->timeSim );
    printf( "Used double ANDs  = %6d.             ", p->nUsedNode2And );       ABC_PRT( " 1    ", p->timeRes1 );
    printf( "Used OR-AND       = %6d.             ", p->nUsedNode2OrAnd );     ABC_PRT( " D    ", p->timeResD );
    printf( "Used AND-OR       = %6d.             ", p->nUsedNode2AndOr );     ABC_PRT( " 2    ", p->timeRes2 );
    printf( "Used OR-2ANDs     = %6d.             ", p->nUsedNode3OrAnd );     ABC_PRT( "Truth ", p->timeTruth ); //ABC_PRT( " 3    ", p->timeRes3 );
    printf( "Used AND-2ORs     = %6d.             ", p->nUsedNode3AndOr );     ABC_PRT( "AIG   ", p->timeNtk );
    printf( "TOTAL             = %6d.             ", p->nUsedNodeC +
                                                     p->nUsedNode0 +
                                                     p->nUsedNode1Or +
                                                     p->nUsedNode1And +
                                                     p->nUsedNode2Or +
                                                     p->nUsedNode2And +
                                                     p->nUsedNode2OrAnd +
                                                     p->nUsedNode2AndOr +
                                                     p->nUsedNode3OrAnd +
                                                     p->nUsedNode3AndOr
                                                   );                          ABC_PRT( "TOTAL ", p->timeTotal );
    printf( "Total leaves   = %8d.\n", p->nTotalLeaves );
    printf( "Total divisors = %8d.\n", p->nTotalDivs );
//    printf( "Total gain     = %8d.\n", p->nTotalGain );
    printf( "Gain           = %8d. (%6.2f %%).\n", p->nNodesBeg-p->nNodesEnd, 100.0*(p->nNodesBeg-p->nNodesEnd)/p->nNodesBeg );
    if ( p->fUseSim )
    {
        printf( "SimResub: targets = %lld  legal hash literals = %lld (avg %.1f)  implication literals = %lld (avg %.1f)\n", (long long)p->nSimTargets, (long long)p->nLegalHashLits, 1.0*p->nLegalHashLits/Abc_MaxInt(1,(int)p->nSimTargets), (long long)p->nImplLits, 1.0*p->nImplLits/Abc_MaxInt(1,(int)p->nSimTargets) );
        printf( "SimResub explicit: targets0 = %lld  generated cost0/1/2/3/4/5 = %lld/%lld/%lld/%lld/%lld/%lld\n", (long long)p->nTargets0, (long long)p->nGenCost[0], (long long)p->nGenCost[1], (long long)p->nGenCost[2], (long long)p->nGenCost[3], (long long)p->nGenCost[4], (long long)p->nGenCost[5] );
        printf( "SimResub explicit: pairs tried = %lld  intermediates = %lld  submitted = %lld  passed exact = %lld\n", (long long)p->nPairsTried, (long long)p->nIntermsGenerated, (long long)p->nSubmitted, (long long)p->nPassedExact );
        printf( "SimResub explicit: accepted cost0/1/2/3/4/5 = %lld/%lld/%lld/%lld/%lld/%lld  first-not-best = %lld\n", (long long)p->nAcceptedCost[0], (long long)p->nAcceptedCost[1], (long long)p->nAcceptedCost[2], (long long)p->nAcceptedCost[3], (long long)p->nAcceptedCost[4], (long long)p->nAcceptedCost[5], (long long)p->nFirstNotBest );
        { int g; printf( "SimResub best-gain:" ); for ( g = 0; g < 15; g++ ) if ( p->nBestGain[g] ) printf( " %d=%lld", g, (long long)p->nBestGain[g] ); if ( p->nBestGain[15] ) printf( " 15+=%lld", (long long)p->nBestGain[15] ); printf( "\n" ); }
        printf( "SimResub rejected: sim = %lld  legality = %lld  level = %lld  exact = %lld  gain = %lld  limit-hit = %s\n", (long long)p->nRejectedSim, (long long)p->nRejectedLegal, (long long)p->nRejectedLevel, (long long)p->nRejectedExact, (long long)p->nRejectedGain, p->fLimitHit ? "yes" : "no" );
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ManResubCollectDivs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vInternal )
{
    // skip visited nodes
    if ( Abc_NodeIsTravIdCurrent(pNode) )
        return;
    Abc_NodeSetTravIdCurrent(pNode);
    // collect the fanins
    Abc_ManResubCollectDivs_rec( Abc_ObjFanin0(pNode), vInternal );
    Abc_ManResubCollectDivs_rec( Abc_ObjFanin1(pNode), vInternal );
    // collect the internal node
    if ( pNode->fMarkA == 0 ) 
        Vec_PtrPush( vInternal, pNode );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ManResubCollectDivs( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int Required )
{
    Abc_Obj_t * pNode, * pFanout;
    int i, k, Limit, Counter;

    Vec_PtrClear( p->vDivs1UP );
    Vec_PtrClear( p->vDivs1UN );
    Vec_PtrClear( p->vDivs1B );

    // add the leaves of the cuts to the divisors
    Vec_PtrClear( p->vDivs );
    Abc_NtkIncrementTravId( pRoot->pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pNode, i )
    {
        Vec_PtrPush( p->vDivs, pNode );
        Abc_NodeSetTravIdCurrent( pNode );        
    }

    // mark nodes in the MFFC
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i )
        pNode->fMarkA = 1;
    // collect the cone (without MFFC)
    Abc_ManResubCollectDivs_rec( pRoot, p->vDivs );
    // unmark the current MFFC
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i )
        pNode->fMarkA = 0;

    // check if the number of divisors is not exceeded
    if ( Vec_PtrSize(p->vDivs) - Vec_PtrSize(vLeaves) + Vec_PtrSize(p->vTemp) >= Vec_PtrSize(p->vSims) - p->nLeavesMax )
        return 0;

    // get the number of divisors to collect
    Limit = Vec_PtrSize(p->vSims) - p->nLeavesMax - (Vec_PtrSize(p->vDivs) - Vec_PtrSize(vLeaves) + Vec_PtrSize(p->vTemp));

    // explore the fanouts, which are not in the MFFC
    Counter = 0;
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs, pNode, i )
    {
        if ( Abc_ObjFanoutNum(pNode) > 100 )
        {
//            printf( "%d ", Abc_ObjFanoutNum(pNode) );
            continue;
        }
        // if the fanout has both fanins in the set, add it
        Abc_ObjForEachFanout( pNode, pFanout, k )
        {
            if ( Abc_NodeIsTravIdCurrent(pFanout) || Abc_ObjIsCo(pFanout) || (int)pFanout->Level > Required )
                continue;
            if ( Abc_NodeIsTravIdCurrent(Abc_ObjFanin0(pFanout)) && Abc_NodeIsTravIdCurrent(Abc_ObjFanin1(pFanout)) )
            {
                if ( Abc_ObjFanin0(pFanout) == pRoot || Abc_ObjFanin1(pFanout) == pRoot )
                    continue;
                Vec_PtrPush( p->vDivs, pFanout );
                Abc_NodeSetTravIdCurrent( pFanout );
                // quit computing divisors if there is too many of them
                if ( ++Counter == Limit )
                    goto Quits;
            }
        }
    }

Quits :
    // get the number of divisors
    p->nDivs = Vec_PtrSize(p->vDivs);

    // add the nodes in the MFFC
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i )
        Vec_PtrPush( p->vDivs, pNode );
    assert( pRoot == Vec_PtrEntryLast(p->vDivs) );

    assert( Vec_PtrSize(p->vDivs) - Vec_PtrSize(vLeaves) <= Vec_PtrSize(p->vSims) - p->nLeavesMax );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static word * Abc_ManResubGlobalSim( Abc_ManRes_t * p, Abc_Obj_t * pObj ) { return p->pGlobalSims + (ABC_PTRUINT_T)pObj->Id * ABC_RS_SIM_WORDS; }

static unsigned Abc_ManResubHashSim( word * pSim, int fCompl )
{
    unsigned Hash = 0x9e3779b9; int w; word Value;
    for ( w = 0; w < ABC_RS_SIM_WORDS; w++ ) { Value = fCompl ? ~pSim[w] : pSim[w]; Hash ^= (unsigned)Value + (unsigned)(Value >> 32) + (Hash << 6) + (Hash >> 2); }
    return Hash;
}

static int Abc_ManResubSimEqual( word * p0, word * p1, int fCompl )
{
    int w; for ( w = 0; w < ABC_RS_SIM_WORDS; w++ ) if ( p0[w] != (fCompl ? ~p1[w] : p1[w]) ) return 0; return 1;
}

static int Abc_ManResubSimImpl( word * p0, word * p1, int c0, int c1 )
{
    int w; for ( w = 0; w < ABC_RS_SIM_WORDS; w++ ) if ( (c0 ? ~p0[w] : p0[w]) & ~(c1 ? ~p1[w] : p1[w]) ) return 0; return 1;
}

static int Abc_ManResubPairUseful( word * p0, word * p1, word * pRoot )
{
    int c0, c1, fOr, w; word Temp[ABC_RS_SIM_WORDS];
    for ( fOr = 0; fOr < 2; fOr++ ) for ( c0 = 0; c0 < 2; c0++ ) for ( c1 = 0; c1 < 2; c1++ )
    {
        for ( w = 0; w < ABC_RS_SIM_WORDS; w++ ) Temp[w] = fOr ? ((c0 ? ~p0[w] : p0[w]) | (c1 ? ~p1[w] : p1[w])) : ((c0 ? ~p0[w] : p0[w]) & (c1 ? ~p1[w] : p1[w]));
        if ( Abc_ManResubSimEqual(Temp, pRoot, 0) || Abc_ManResubSimEqual(Temp, pRoot, 1) || Abc_ManResubSimImpl(Temp,pRoot,0,0) || Abc_ManResubSimImpl(pRoot,Temp,0,0) ) return 1;
    }
    return 0;
}

void Abc_ManResubBuildGlobalSim( Abc_ManRes_t * p )
{
    Abc_Obj_t * pObj; word * pSim, * p0, * p1; unsigned State = 0x31415926; int i, w, fCompl;
    int nObjs;
    if ( p->pRoot == NULL ) return;
    nObjs = Abc_NtkObjNumMax(p->pRoot->pNtk);
    if ( nObjs > p->nGlobalObjs ) { p->nGlobalObjs = nObjs; p->pGlobalSims = ABC_REALLOC(word, p->pGlobalSims, (ABC_PTRUINT_T)nObjs * ABC_RS_SIM_WORDS); p->pHashNext = ABC_REALLOC(int, p->pHashNext, nObjs); p->pHashPhase = ABC_REALLOC(unsigned char, p->pHashPhase, nObjs); }
    p->nHashSize = Abc_PrimeCudd(2*nObjs + 1); p->pHashBins = ABC_REALLOC(int, p->pHashBins, p->nHashSize);
    for ( i = 0; i < p->nHashSize; i++ ) p->pHashBins[i] = -1;
    Abc_NtkForEachNodeCi( p->pRoot->pNtk, pObj, i )
    {
        pSim = Abc_ManResubGlobalSim(p, pObj);
        if ( Abc_ObjIsCi(pObj) ) for ( w = 0; w < ABC_RS_SIM_WORDS; w++ ) { State ^= State << 13; State ^= State >> 17; State ^= State << 5; pSim[w] = ((word)State << 32) | (State * 0x9e3779b9u + w + i); }
        else { p0 = Abc_ManResubGlobalSim(p, Abc_ObjFanin0(pObj)); p1 = Abc_ManResubGlobalSim(p, Abc_ObjFanin1(pObj)); for ( w = 0; w < ABC_RS_SIM_WORDS; w++ ) pSim[w] = (Abc_ObjFaninC0(pObj) ? ~p0[w] : p0[w]) & (Abc_ObjFaninC1(pObj) ? ~p1[w] : p1[w]); }
        if ( Abc_ObjIsCi(pObj) ) { pSim[0] = ABC_CONST(0xAAAAAAAAAAAAAAAA) ^ (word)(i & 1 ? ~(word)0 : 0); pSim[1] = ABC_CONST(0xCCCCCCCCCCCCCCCC) ^ (word)(i & 2 ? ~(word)0 : 0); for ( w = 0; w < ABC_RS_SIM_WORDS; w++ ) pSim[w] &= ~((word)1), pSim[w] |= ((word)1 << 1); }
        fCompl = (pSim[0] >> 63) & 1; p->pHashPhase[pObj->Id] = fCompl;
        { unsigned h = Abc_ManResubHashSim(pSim, fCompl) % p->nHashSize; p->pHashNext[pObj->Id] = p->pHashBins[h]; p->pHashBins[h] = pObj->Id; }
    }
}

int Abc_ManResubCollectDivsSim( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int Required )
{
    Abc_Obj_t * pNode;
    int i, Limit, nBefore;
    Vec_PtrClear( p->vDivs1UP ); Vec_PtrClear( p->vDivs1UN ); Vec_PtrClear( p->vDivs1B );
    Vec_PtrClear( p->vDivs );
    Abc_NtkIncrementTravId( pRoot->pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pNode, i )
        Vec_PtrPush( p->vDivs, pNode ), Abc_NodeSetTravIdCurrent( pNode );
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i ) pNode->fMarkA = pNode->fMarkB = 1;
    Abc_ManResubCollectDivs_rec( pRoot, p->vDivs );
    nBefore = Vec_PtrSize( p->vDivs );
    Limit = Vec_PtrSize(p->vSims) - p->nLeavesMax - Vec_PtrSize(p->vTemp);
    Abc_NtkForEachNode( pRoot->pNtk, pNode, i )
    {
        if ( Vec_PtrSize(p->vDivs) >= Limit ) break;
        if ( pNode->fMarkB || Abc_ObjFanin0(pNode)->fMarkB || Abc_ObjFanin1(pNode)->fMarkB )
        {
            pNode->fMarkB = 1;
            continue;
        }
        if ( Abc_NodeIsTravIdCurrent(pNode) || pNode->fMarkA || pNode == pRoot || (int)pNode->Level > Required ) continue;
        if ( Abc_NodeIsTravIdCurrent(Abc_ObjFanin0(pNode)) && Abc_NodeIsTravIdCurrent(Abc_ObjFanin1(pNode)) )
            Vec_PtrPush( p->vDivs, pNode ), Abc_NodeSetTravIdCurrent( pNode );
    }
    Abc_NtkForEachNode( pRoot->pNtk, pNode, i ) pNode->fMarkB = 0;
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i ) pNode->fMarkA = 0;
    p->nDivs = Vec_PtrSize(p->vDivs);
    p->nSimTargets++;
    p->nLegalHashLits += 2 * (ABC_INT64_T)p->nDivs;
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i ) Vec_PtrPush( p->vDivs, pNode );
    assert( pRoot == Vec_PtrEntryLast(p->vDivs) );
    return 1;
}

void Abc_ManResubPrintDivs( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves )
{
    Abc_Obj_t * pFanin, * pNode;
    int i, k;
    // print the nodes
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs, pNode, i )
    {
        if ( i < Vec_PtrSize(vLeaves) )
        {
            printf( "%6d : %c\n", pNode->Id, 'a'+i );
            continue;
        }
        printf( "%6d : %2d = ", pNode->Id, i );
        // find the first fanin
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs, pFanin, k )
            if ( Abc_ObjFanin0(pNode) == pFanin )
                break;
        if ( k < Vec_PtrSize(vLeaves) )
            printf( "%c", 'a' + k );
        else
            printf( "%d", k );
        printf( "%s ", Abc_ObjFaninC0(pNode)? "\'" : "" );
        // find the second fanin
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs, pFanin, k )
            if ( Abc_ObjFanin1(pNode) == pFanin )
                break;
        if ( k < Vec_PtrSize(vLeaves) )
            printf( "%c", 'a' + k );
        else
            printf( "%d", k );
        printf( "%s ", Abc_ObjFaninC1(pNode)? "\'" : "" );
        if ( pNode == pRoot )
            printf( " root" );
        printf( "\n" );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Dumps one resub instance.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ManResubDumpInstance( Vec_Ptr_t * vDivs, int nLeaves, int nDivs, int nWords )
{
    Abc_Obj_t * pRoot = (Abc_Obj_t *)Vec_PtrEntryLast(vDivs);
    char pFileName[1000]; 
    sprintf( pFileName, "%s_%05d.pla", pRoot->pNtk->pName, pRoot->Id );
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL ) {
        printf( "Cannot open file \"%s\" for writing.\n", pFileName );
        return;
    }
    fprintf( pFile, "// Resub instance generated for node %d in network \"%s\" on %s\n", pRoot->Id, pRoot->pNtk->pName, Extra_TimeStamp() );
    fprintf( pFile, ".i %d\n", nDivs );
    fprintf( pFile, ".o %d\n", 1 );
    fprintf( pFile, ".p %d\n", 1 << nLeaves );    
    Abc_Obj_t * pObj; int i, n;
    for ( n = 0; n < (1 << nLeaves); n++ ) {
        Vec_PtrForEachEntryStop( Abc_Obj_t *, vDivs, pObj, i, nDivs ) {
            fprintf( pFile, "%d", Abc_InfoHasBit((unsigned *)pObj->pData, n) );
            if ( i == nLeaves-1 )
                fprintf( pFile, " " );
        }
        fprintf( pFile, " %d\n", Abc_InfoHasBit((unsigned *)pRoot->pData, n) );
    }
    fprintf( pFile, ".e\n" );    
    fclose( pFile );
    printf( "Finished dumping file \"%s\" with %d divisors and %d patterns.\n", pFileName, nDivs, (1 << nLeaves) );
}

/**Function*************************************************************

  Synopsis    [Performs simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ManResubSimulate( Vec_Ptr_t * vDivs, int nLeaves, Vec_Ptr_t * vSims, int nLeavesMax, int nWords )
{
    Abc_Obj_t * pObj;
    unsigned * puData0, * puData1, * puData;
    int i, k;
    assert( Vec_PtrSize(vDivs) - nLeaves <= Vec_PtrSize(vSims) - nLeavesMax );
    // simulate
    Vec_PtrForEachEntry( Abc_Obj_t *, vDivs, pObj, i )
    {
        if ( i < nLeaves )
        { // initialize the leaf
            pObj->pData = Vec_PtrEntry( vSims, i );
            continue;
        }
        // set storage for the node's simulation info
        pObj->pData = Vec_PtrEntry( vSims, i - nLeaves + nLeavesMax );
        // get pointer to the simulation info
        puData  = (unsigned *)pObj->pData;
        puData0 = (unsigned *)Abc_ObjFanin0(pObj)->pData;
        puData1 = (unsigned *)Abc_ObjFanin1(pObj)->pData;
        // simulate
        if ( Abc_ObjFaninC0(pObj) && Abc_ObjFaninC1(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & ~puData1[k];
        else if ( Abc_ObjFaninC0(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & puData1[k];
        else if ( Abc_ObjFaninC1(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & ~puData1[k];
        else 
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & puData1[k];
    }
    // normalize
    Vec_PtrForEachEntry( Abc_Obj_t *, vDivs, pObj, i )
    {
        puData = (unsigned *)pObj->pData;
        pObj->fPhase = (puData[0] & 1);
        if ( pObj->fPhase )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData[k];
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubQuit0( Abc_Obj_t * pRoot, Abc_Obj_t * pObj )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot;
    pGraph = Dec_GraphCreate( 1 );
    Dec_GraphNode( pGraph, 0 )->pFunc = pObj;
    eRoot = Dec_EdgeCreate( 0, pObj->fPhase );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubQuit1( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eNode0, eNode1;
    assert( Abc_ObjRegular(pObj0) != Abc_ObjRegular(pObj1) );
    pGraph = Dec_GraphCreate( 2 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular(pObj1);
    eNode0 = Dec_EdgeCreate( 0, Abc_ObjRegular(pObj0)->fPhase ^ Abc_ObjIsComplement(pObj0) );
    eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular(pObj1)->fPhase ^ Abc_ObjIsComplement(pObj1) );
    if ( fOrGate ) 
        eRoot  = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
    else
        eRoot  = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubQuit21( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, Abc_Obj_t * pObj2, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eNode0, eNode1, eNode2;
    assert( Abc_ObjRegular(pObj0) != Abc_ObjRegular(pObj1) );
    assert( Abc_ObjRegular(pObj0) != Abc_ObjRegular(pObj2) );
    assert( Abc_ObjRegular(pObj1) != Abc_ObjRegular(pObj2) );
    pGraph = Dec_GraphCreate( 3 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular(pObj1);
    Dec_GraphNode( pGraph, 2 )->pFunc = Abc_ObjRegular(pObj2);
    eNode0 = Dec_EdgeCreate( 0, Abc_ObjRegular(pObj0)->fPhase ^ Abc_ObjIsComplement(pObj0) );
    eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular(pObj1)->fPhase ^ Abc_ObjIsComplement(pObj1) );
    eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular(pObj2)->fPhase ^ Abc_ObjIsComplement(pObj2) );
    if ( fOrGate ) 
    {
        eRoot  = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
        eRoot  = Dec_GraphAddNodeOr( pGraph, eNode2, eRoot );
    }
    else
    {
        eRoot  = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
        eRoot  = Dec_GraphAddNodeAnd( pGraph, eNode2, eRoot );
    }
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubQuit2( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, Abc_Obj_t * pObj2, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, ePrev, eNode0, eNode1, eNode2;
    assert( Abc_ObjRegular(pObj0) != Abc_ObjRegular(pObj1) );
    assert( Abc_ObjRegular(pObj0) != Abc_ObjRegular(pObj2) );
    assert( Abc_ObjRegular(pObj1) != Abc_ObjRegular(pObj2) );
    pGraph = Dec_GraphCreate( 3 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular(pObj1);
    Dec_GraphNode( pGraph, 2 )->pFunc = Abc_ObjRegular(pObj2);
    eNode0 = Dec_EdgeCreate( 0, Abc_ObjRegular(pObj0)->fPhase ^ Abc_ObjIsComplement(pObj0) );
    if ( Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
    {
        eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular(pObj1)->fPhase );
        eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular(pObj2)->fPhase );
        ePrev  = Dec_GraphAddNodeOr( pGraph, eNode1, eNode2 );
    }
    else
    {
        eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular(pObj1)->fPhase ^ Abc_ObjIsComplement(pObj1) );
        eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular(pObj2)->fPhase ^ Abc_ObjIsComplement(pObj2) );
        ePrev  = Dec_GraphAddNodeAnd( pGraph, eNode1, eNode2 );
    }
    if ( fOrGate ) 
        eRoot  = Dec_GraphAddNodeOr( pGraph, eNode0, ePrev );
    else
        eRoot  = Dec_GraphAddNodeAnd( pGraph, eNode0, ePrev );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubQuit3( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, Abc_Obj_t * pObj2, Abc_Obj_t * pObj3, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, ePrev0, ePrev1, eNode0, eNode1, eNode2, eNode3;
    assert( Abc_ObjRegular(pObj0) != Abc_ObjRegular(pObj1) );
    assert( Abc_ObjRegular(pObj2) != Abc_ObjRegular(pObj3) );
    pGraph = Dec_GraphCreate( 4 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular(pObj1);
    Dec_GraphNode( pGraph, 2 )->pFunc = Abc_ObjRegular(pObj2);
    Dec_GraphNode( pGraph, 3 )->pFunc = Abc_ObjRegular(pObj3);
    if ( Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) )
    {
        eNode0 = Dec_EdgeCreate( 0, Abc_ObjRegular(pObj0)->fPhase );
        eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular(pObj1)->fPhase );
        ePrev0 = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
        if ( Abc_ObjIsComplement(pObj2) && Abc_ObjIsComplement(pObj3) )
        {
            eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular(pObj2)->fPhase );
            eNode3 = Dec_EdgeCreate( 3, Abc_ObjRegular(pObj3)->fPhase );
            ePrev1 = Dec_GraphAddNodeOr( pGraph, eNode2, eNode3 );
        }
        else
        {
            eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular(pObj2)->fPhase ^ Abc_ObjIsComplement(pObj2) );
            eNode3 = Dec_EdgeCreate( 3, Abc_ObjRegular(pObj3)->fPhase ^ Abc_ObjIsComplement(pObj3) );
            ePrev1 = Dec_GraphAddNodeAnd( pGraph, eNode2, eNode3 );
        }
    }
    else
    {
        eNode0 = Dec_EdgeCreate( 0, Abc_ObjRegular(pObj0)->fPhase ^ Abc_ObjIsComplement(pObj0) );
        eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular(pObj1)->fPhase ^ Abc_ObjIsComplement(pObj1) );
        ePrev0 = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
        if ( Abc_ObjIsComplement(pObj2) && Abc_ObjIsComplement(pObj3) )
        {
            eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular(pObj2)->fPhase );
            eNode3 = Dec_EdgeCreate( 3, Abc_ObjRegular(pObj3)->fPhase );
            ePrev1 = Dec_GraphAddNodeOr( pGraph, eNode2, eNode3 );
        }
        else
        {
            eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular(pObj2)->fPhase ^ Abc_ObjIsComplement(pObj2) );
            eNode3 = Dec_EdgeCreate( 3, Abc_ObjRegular(pObj3)->fPhase ^ Abc_ObjIsComplement(pObj3) );
            ePrev1 = Dec_GraphAddNodeAnd( pGraph, eNode2, eNode3 );
        }
    }
    if ( fOrGate ) 
        eRoot = Dec_GraphAddNodeOr( pGraph, ePrev0, ePrev1 );
    else
        eRoot = Dec_GraphAddNodeAnd( pGraph, ePrev0, ePrev1 );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}




/**Function*************************************************************

  Synopsis    [Derives single-node unate/binate divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ManResubDivsS( Abc_ManRes_t * p, int Required )
{
    int fMoreDivs = 1; // bug fix by Siang-Yun Lee
    Abc_Obj_t * pObj;
    unsigned * puData, * puDataR;
    int i, w;
    Vec_PtrClear( p->vDivs1UP );
    Vec_PtrClear( p->vDivs1UN );
    Vec_PtrClear( p->vDivs1B );
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntryStop( Abc_Obj_t *, p->vDivs, pObj, i, p->nDivs )
    {
        if ( (int)pObj->Level > Required - 1 )
            continue;

        puData = (unsigned *)pObj->pData;
        // check positive containment
        for ( w = 0; w < p->nWords; w++ )
//            if ( puData[w] & ~puDataR[w] )
            if ( puData[w] & ~puDataR[w] & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
        {
            Vec_PtrPush( p->vDivs1UP, pObj );
            continue;
        }
        if ( fMoreDivs )
        {
            for ( w = 0; w < p->nWords; w++ )
    //            if ( ~puData[w] & ~puDataR[w] )
                if ( ~puData[w] & ~puDataR[w] & p->pCareSet[w] ) // care set
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs1UP, Abc_ObjNot(pObj) );
                continue;
            }
        }
        // check negative containment
        for ( w = 0; w < p->nWords; w++ )
//            if ( ~puData[w] & puDataR[w] )
            if ( ~puData[w] & puDataR[w] & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
        {
            Vec_PtrPush( p->vDivs1UN, pObj );
            continue;
        }
        if ( fMoreDivs )
        {
            for ( w = 0; w < p->nWords; w++ )
    //            if ( puData[w] & puDataR[w] )
                if ( puData[w] & puDataR[w] & p->pCareSet[w] ) // care set
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs1UN, Abc_ObjNot(pObj) );
                continue;
            }
        }
        // add the node to binates
        Vec_PtrPush( p->vDivs1B, pObj );
    }
}

/**Function*************************************************************

  Synopsis    [Derives double-node unate/binate divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ManResubDivsD( Abc_ManRes_t * p, int Required )
{
    Abc_Obj_t * pObj0, * pObj1;
    unsigned * puData0, * puData1, * puDataR;
    int i, k, w;
    Vec_PtrClear( p->vDivs2UP0 );
    Vec_PtrClear( p->vDivs2UP1 );
    Vec_PtrClear( p->vDivs2UN0 );
    Vec_PtrClear( p->vDivs2UN1 );
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1B, pObj0, i )
    {
        if ( (int)pObj0->Level > Required - 2 )
            continue;

        puData0 = (unsigned *)pObj0->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1B, pObj1, k, i + 1 )
        {
            if ( (int)pObj1->Level > Required - 2 )
                continue;

            puData1 = (unsigned *)pObj1->pData;

            if ( p->fUseSim || Vec_PtrSize(p->vDivs2UP0) < ABC_RS_DIV2_MAX )
            {
                // get positive unate divisors
                for ( w = 0; w < p->nWords; w++ )
//                    if ( (puData0[w] & puData1[w]) & ~puDataR[w] )
                    if ( (puData0[w] & puData1[w]) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, pObj0 );
                    Vec_PtrPush( p->vDivs2UP1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( (~puData0[w] & puData1[w]) & ~puDataR[w] )
                    if ( (~puData0[w] & puData1[w]) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, Abc_ObjNot(pObj0) );
                    Vec_PtrPush( p->vDivs2UP1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( (puData0[w] & ~puData1[w]) & ~puDataR[w] )
                    if ( (puData0[w] & ~puData1[w]) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, pObj0 );
                    Vec_PtrPush( p->vDivs2UP1, Abc_ObjNot(pObj1) );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( (puData0[w] | puData1[w]) & ~puDataR[w] )
                    if ( (puData0[w] | puData1[w]) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, Abc_ObjNot(pObj0) );
                    Vec_PtrPush( p->vDivs2UP1, Abc_ObjNot(pObj1) );
                }
            }

            if ( p->fUseSim || Vec_PtrSize(p->vDivs2UN0) < ABC_RS_DIV2_MAX )
            {
                // get negative unate divisors
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ~(puData0[w] & puData1[w]) & puDataR[w] )
                    if ( ~(puData0[w] & puData1[w]) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, pObj0 );
                    Vec_PtrPush( p->vDivs2UN1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ~(~puData0[w] & puData1[w]) & puDataR[w] )
                    if ( ~(~puData0[w] & puData1[w]) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, Abc_ObjNot(pObj0) );
                    Vec_PtrPush( p->vDivs2UN1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ~(puData0[w] & ~puData1[w]) & puDataR[w] )
                    if ( ~(puData0[w] & ~puData1[w]) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, pObj0 );
                    Vec_PtrPush( p->vDivs2UN1, Abc_ObjNot(pObj1) );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ~(puData0[w] | puData1[w]) & puDataR[w] )
                    if ( ~(puData0[w] | puData1[w]) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, Abc_ObjNot(pObj0) );
                    Vec_PtrPush( p->vDivs2UN1, Abc_ObjNot(pObj1) );
                }
            }
        }
    }
//    printf( "%d %d  ", Vec_PtrSize(p->vDivs2UP0), Vec_PtrSize(p->vDivs2UN0) );
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubQuit( Abc_ManRes_t * p )
{
    Dec_Graph_t * pGraph;
    unsigned * upData;
    int w;
    upData = (unsigned *)p->pRoot->pData;
    for ( w = 0; w < p->nWords; w++ )
//        if ( upData[w] )
        if ( upData[w] & p->pCareSet[w] ) // care set
            break;
    if ( w != p->nWords )
        return NULL;
    // get constant node graph
    if ( p->pRoot->fPhase )
        pGraph = Dec_GraphCreateConst1();
    else 
        pGraph = Dec_GraphCreateConst0();
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubDivs0( Abc_ManRes_t * p )
{
    Abc_Obj_t * pObj;
    unsigned * puData, * puDataR;
    int i, w;
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntryStop( Abc_Obj_t *, p->vDivs, pObj, i, p->nDivs )
    {
        puData = (unsigned *)pObj->pData;
        for ( w = 0; w < p->nWords; w++ )
//            if ( puData[w] != puDataR[w] )
            if ( (puData[w] ^ puDataR[w]) & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
            return Abc_ManResubQuit0( p->pRoot, pObj );
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubDivs1( Abc_ManRes_t * p, int Required )
{
    Abc_Obj_t * pObj0, * pObj1;
    unsigned * puData0, * puData1, * puDataR;
    int i, k, w;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular(pObj0)->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UP, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Abc_ObjRegular(pObj1)->pData;
            if ( Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    if ( ((~puData0[w] | ~puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else if ( Abc_ObjIsComplement(pObj0) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    if ( ((~puData0[w] | puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else if ( Abc_ObjIsComplement(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    if ( ((puData0[w] | ~puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else 
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    if ( ((puData0[w] | puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            if ( w == p->nWords )
            {
                p->nUsedNode1Or++;
                return Abc_ManResubQuit1( p->pRoot, pObj0, pObj1, 1 );
            }
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular(pObj0)->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UN, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Abc_ObjRegular(pObj1)->pData;
            if ( Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] & puData1[w]) != puDataR[w] )
                    if ( ((~puData0[w] & ~puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            if ( Abc_ObjIsComplement(pObj0) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] & puData1[w]) != puDataR[w] )
                    if ( ((~puData0[w] & puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            if ( Abc_ObjIsComplement(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] & puData1[w]) != puDataR[w] )
                    if ( ((puData0[w] & ~puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] & puData1[w]) != puDataR[w] )
                    if ( ((puData0[w] & puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            if ( w == p->nWords )
            {
                p->nUsedNode1And++;
                return Abc_ManResubQuit1( p->pRoot, pObj0, pObj1, 0 );
            }
        }
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubDivs12( Abc_ManRes_t * p, int Required )
{
    Abc_Obj_t * pObj0, * pObj1, * pObj2, * pObjMax, * pObjMin0 = NULL, * pObjMin1 = NULL;
    unsigned * puData0, * puData1, * puData2, * puDataR;
    int i, k, j, w, LevelMax;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular(pObj0)->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UP, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Abc_ObjRegular(pObj1)->pData;
            Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UP, pObj2, j, k + 1 )
            {
                puData2 = (unsigned *)Abc_ObjRegular(pObj2)->pData;
                if ( Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] | ~puData1[w] | ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) && !Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] | ~puData1[w] | puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj0) && !Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] | puData1[w] | ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj0) && !Abc_ObjIsComplement(pObj1) && !Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] | puData1[w] | puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] | ~puData1[w] | ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) && !Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] | ~puData1[w] | puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement(pObj0) && !Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] | puData1[w] | ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement(pObj0) && !Abc_ObjIsComplement(pObj1) && !Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] | puData1[w] | puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else assert( 0 );
                if ( w == p->nWords )
                {
                    LevelMax = Abc_MaxInt( Abc_ObjRegular(pObj0)->Level, Abc_MaxInt(Abc_ObjRegular(pObj1)->Level, Abc_ObjRegular(pObj2)->Level) );
                    assert( LevelMax <= Required - 1 );

                    pObjMax = NULL;
                    if ( (int)Abc_ObjRegular(pObj0)->Level == LevelMax )
                        pObjMax = pObj0, pObjMin0 = pObj1, pObjMin1 = pObj2;
                    if ( (int)Abc_ObjRegular(pObj1)->Level == LevelMax )
                    {
                        if ( pObjMax ) continue;
                        pObjMax = pObj1, pObjMin0 = pObj0, pObjMin1 = pObj2;
                    }
                    if ( (int)Abc_ObjRegular(pObj2)->Level == LevelMax )
                    {
                        if ( pObjMax ) continue;
                        pObjMax = pObj2, pObjMin0 = pObj0, pObjMin1 = pObj1;
                    }

                    p->nUsedNode2Or++;
                    assert(pObjMin0);
                    assert(pObjMin1);
                    return Abc_ManResubQuit21( p->pRoot, pObjMin0, pObjMin1, pObjMax, 1 );
                }
            }
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular(pObj0)->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UN, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Abc_ObjRegular(pObj1)->pData;
            Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UN, pObj2, j, k + 1 )
            {
                puData2 = (unsigned *)Abc_ObjRegular(pObj2)->pData;
                if ( Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] & ~puData1[w] & ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) && !Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] & ~puData1[w] & puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj0) && !Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] & puData1[w] & ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj0) && !Abc_ObjIsComplement(pObj1) && !Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] & puData1[w] & puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] & ~puData1[w] & ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement(pObj0) && Abc_ObjIsComplement(pObj1) && !Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] & ~puData1[w] & puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement(pObj0) && !Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] & puData1[w] & ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement(pObj0) && !Abc_ObjIsComplement(pObj1) && !Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] & puData1[w] & puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else assert( 0 );
                if ( w == p->nWords )
                {
                    LevelMax = Abc_MaxInt( Abc_ObjRegular(pObj0)->Level, Abc_MaxInt(Abc_ObjRegular(pObj1)->Level, Abc_ObjRegular(pObj2)->Level) );
                    assert( LevelMax <= Required - 1 );

                    pObjMax = NULL;
                    if ( (int)Abc_ObjRegular(pObj0)->Level == LevelMax )
                        pObjMax = pObj0, pObjMin0 = pObj1, pObjMin1 = pObj2;
                    if ( (int)Abc_ObjRegular(pObj1)->Level == LevelMax )
                    {
                        if ( pObjMax ) continue;
                        pObjMax = pObj1, pObjMin0 = pObj0, pObjMin1 = pObj2;
                    }
                    if ( (int)Abc_ObjRegular(pObj2)->Level == LevelMax )
                    {
                        if ( pObjMax ) continue;
                        pObjMax = pObj2, pObjMin0 = pObj0, pObjMin1 = pObj1;
                    }

                    p->nUsedNode2And++;
                    assert(pObjMin0);
                    assert(pObjMin1);
                    return Abc_ManResubQuit21( p->pRoot, pObjMin0, pObjMin1, pObjMax, 0 );
                }
            }
        }
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubDivs2( Abc_ManRes_t * p, int Required )
{
    Abc_Obj_t * pObj0, * pObj1, * pObj2;
    unsigned * puData0, * puData1, * puData2, * puDataR;
    int i, k, w;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular(pObj0)->pData;
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs2UP0, pObj1, k )
        {
            pObj2 = (Abc_Obj_t *)Vec_PtrEntry( p->vDivs2UP1, k );

            puData1 = (unsigned *)Abc_ObjRegular(pObj1)->pData;
            puData2 = (unsigned *)Abc_ObjRegular(pObj2)->pData;
            if ( Abc_ObjIsComplement(pObj0) )
            {
                if ( Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] | puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] | (puData1[w] | puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj1) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (~puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] | (~puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] & ~puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] | (puData1[w] & ~puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else 
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] | (puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
            }
            else
            {
                if ( Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] | puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] | (puData1[w] | puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj1) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (~puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] | (~puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] & ~puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] | (puData1[w] & ~puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else 
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] | (puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
            }
            if ( w == p->nWords )
            {
                p->nUsedNode2OrAnd++;
                return Abc_ManResubQuit2( p->pRoot, pObj0, pObj1, pObj2, 1 );
            }
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular(pObj0)->pData;
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs2UN0, pObj1, k )
        {
            pObj2 = (Abc_Obj_t *)Vec_PtrEntry( p->vDivs2UN1, k );

            puData1 = (unsigned *)Abc_ObjRegular(pObj1)->pData;
            puData2 = (unsigned *)Abc_ObjRegular(pObj2)->pData;
            if ( Abc_ObjIsComplement(pObj0) )
            {
                if ( Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] | puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] & (puData1[w] | puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj1) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (~puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] & (~puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] & ~puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] & (puData1[w] & ~puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else 
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] & (puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
            }
            else
            {
                if ( Abc_ObjIsComplement(pObj1) && Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] | puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] & (puData1[w] | puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj1) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (~puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] & (~puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] & ~puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] & (puData1[w] & ~puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else 
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] & (puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
            }
            if ( w == p->nWords )
            {
                p->nUsedNode2AndOr++;
                return Abc_ManResubQuit2( p->pRoot, pObj0, pObj1, pObj2, 0 );
            }
        }
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubDivs3( Abc_ManRes_t * p, int Required )
{
    Abc_Obj_t * pObj0, * pObj1, * pObj2, * pObj3;
    unsigned * puData0, * puData1, * puData2, * puData3, * puDataR;
    int i, k, w = 0, Flag;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs2UP0, pObj0, i )
    {
        pObj1 = (Abc_Obj_t *)Vec_PtrEntry( p->vDivs2UP1, i );
        puData0 = (unsigned *)Abc_ObjRegular(pObj0)->pData;
        puData1 = (unsigned *)Abc_ObjRegular(pObj1)->pData;
        Flag = (Abc_ObjIsComplement(pObj0) << 3) | (Abc_ObjIsComplement(pObj1) << 2);

        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs2UP0, pObj2, k, i + 1 )
        {
            pObj3 = (Abc_Obj_t *)Vec_PtrEntry( p->vDivs2UP1, k );
            puData2 = (unsigned *)Abc_ObjRegular(pObj2)->pData;
            puData3 = (unsigned *)Abc_ObjRegular(pObj3)->pData;

            Flag = (Flag & 12) | ((int)Abc_ObjIsComplement(pObj2) << 1) | (int)Abc_ObjIsComplement(pObj3);
            assert( Flag < 16 );
            switch( Flag )
            {
            case 0: // 0000
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 1: // 0001
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 2: // 0010
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 3: // 0011
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & puData1[w]) | (puData2[w] | puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & puData1[w]) | (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;

            case 4: // 0100
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & ~puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & ~puData1[w]) | (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 5: // 0101
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & ~puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & ~puData1[w]) | (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 6: // 0110
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & ~puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & ~puData1[w]) | (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 7: // 0111
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & ~puData1[w]) | (puData2[w] | puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & ~puData1[w]) | (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;

            case 8: // 1000
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((~puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((~puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 9: // 1001
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((~puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                    if ( (((~puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 10: // 1010
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((~puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((~puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 11: // 1011
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((~puData0[w] & puData1[w]) | (puData2[w] | puData3[w])) != puDataR[w] )
                    if ( (((~puData0[w] & puData1[w]) | (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;

            case 12: // 1100
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] | puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] | puData1[w]) | (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 13: // 1101
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] | puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] | puData1[w]) | (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 14: // 1110
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] | puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] | puData1[w]) | (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 15: // 1111
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] | puData1[w]) | (puData2[w] | puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] | puData1[w]) | (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            }
            if ( w == p->nWords )
            {
                p->nUsedNode3OrAnd++;
                return Abc_ManResubQuit3( p->pRoot, pObj0, pObj1, pObj2, pObj3, 1 );
            }
        }
    }

/*
    // check negative unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs2UN0, pObj0, i )
    {
        pObj1 = Vec_PtrEntry( p->vDivs2UN1, i );
        puData0 = Abc_ObjRegular(pObj0)->pData;
        puData1 = Abc_ObjRegular(pObj1)->pData;
        Flag = (Abc_ObjIsComplement(pObj0) << 3) | (Abc_ObjIsComplement(pObj1) << 2);

        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs2UN0, pObj2, k, i + 1 )
        {
            pObj3 = Vec_PtrEntry( p->vDivs2UN1, k );
            puData2 = Abc_ObjRegular(pObj2)->pData;
            puData3 = Abc_ObjRegular(pObj3)->pData;

            Flag = (Flag & 12) | (Abc_ObjIsComplement(pObj2) << 1) | Abc_ObjIsComplement(pObj3);
            assert( Flag < 16 );
            switch( Flag )
            {
            case 0: // 0000
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & puData1[w]) & (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 1: // 0001
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & puData1[w]) & (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 2: // 0010
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & puData1[w]) & (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 3: // 0011
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & puData1[w]) & (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            case 4: // 0100
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & ~puData1[w]) & (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 5: // 0101
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & ~puData1[w]) & (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 6: // 0110
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & ~puData1[w]) & (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 7: // 0111
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & ~puData1[w]) & (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            case 8: // 1000
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((~puData0[w] & puData1[w]) & (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 9: // 1001
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((~puData0[w] & puData1[w]) & (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 10: // 1010
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((~puData0[w] & puData1[w]) & (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 11: // 1011
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((~puData0[w] & puData1[w]) & (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            case 12: // 1100
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] | puData1[w]) & (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 13: // 1101
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] | puData1[w]) & (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 14: // 1110
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] | puData1[w]) & (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 15: // 1111
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] | puData1[w]) & (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            }
            if ( w == p->nWords )
            {
                p->nUsedNode3AndOr++;
                return Abc_ManResubQuit3( p->pRoot, pObj0, pObj1, pObj2, pObj3, 0 );
            }
        }
    }
*/
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static word * SreSim(SimResub_Work_t *w,int l){return w->pExps[Abc_Lit2Var(l)].pSim;}
static unsigned * SreTruth(SimResub_Work_t *w,int l){return w->pExps[Abc_Lit2Var(l)].pTruth;}
static int SreEqW(word*a,word*b,int n,int c){int i;for(i=0;i<n;i++)if(a[i]!=(c?~b[i]:b[i]))return 0;return 1;}
static int SreEqU(unsigned*a,unsigned*b,int n,int c){int i;for(i=0;i<n;i++)if(a[i]!=(c?~b[i]:b[i]))return 0;return 1;}
static int SreImpl(word*t,word*f,int n,int c){int i;for(i=0;i<n;i++)if(t[i]&~(c?~f[i]:f[i]))return 0;return 1;}
static void SreGrow(SimResub_Work_t*w){if(w->nSize<w->nCap)return;w->nCap=w->nCap?2*w->nCap:256;w->pExps=ABC_REALLOC(SimResub_Exp_t,w->pExps,w->nCap);w->pNext=ABC_REALLOC(int,w->pNext,w->nCap);}
static unsigned SreHash(unsigned*t,int n){unsigned h=0x9e3779b9;int i;for(i=0;i<n;i++)h^=t[i]+(h<<6)+(h>>2);return h;}
static int SreFind(SimResub_Work_t*w,word*t,int cost,int lev){int i,h=SreHash((unsigned *)t,w->nSimWords)%w->nHash;for(i=w->pBins[h];i>=0;i=w->pNext[i])if(w->pExps[i].Cost<=cost&&w->pExps[i].Level<=lev&&SreEqW(w->pExps[i].pSim,t,w->nSimWords,0))return i;return -1;}
static void SreInsert(SimResub_Work_t*w,int i){int h=SreHash((unsigned *)w->pExps[i].pSim,w->nSimWords)%w->nHash;w->pNext[i]=w->pBins[h];w->pBins[h]=i;}
static int SreLeaf(SimResub_Work_t*w,Abc_ManRes_t*m,Abc_Obj_t*o){SimResub_Exp_t*e;SreGrow(w);e=w->pExps+w->nSize;memset(e,0,sizeof(*e));e->pLeaf=o;e->Level=o->Level;e->pSim=ABC_ALLOC(word,w->nSimWords);memcpy(e->pSim,Abc_ManResubGlobalSim(m,o),sizeof(word)*w->nSimWords);e->pTruth=NULL;SreInsert(w,w->nSize);return w->nSize++;}
static int SreAnd(SimResub_Work_t*w,int a,int b){SimResub_Exp_t*e;word*x=SreSim(w,a),*y=SreSim(w,b);int i;SreGrow(w);e=w->pExps+w->nSize;memset(e,0,sizeof(*e));e->iLeft=a;e->iRight=b;e->Cost=w->pExps[Abc_Lit2Var(a)].Cost+w->pExps[Abc_Lit2Var(b)].Cost+1;e->Level=1+Abc_MaxInt(w->pExps[Abc_Lit2Var(a)].Level,w->pExps[Abc_Lit2Var(b)].Level);e->pSim=ABC_ALLOC(word,w->nSimWords);for(i=0;i<w->nSimWords;i++)e->pSim[i]=(Abc_LitIsCompl(a)?~x[i]:x[i])&(Abc_LitIsCompl(b)?~y[i]:y[i]);e->pTruth=NULL;i=SreFind(w,e->pSim,e->Cost,e->Level);if(i>=0){ABC_FREE(e->pSim);return i;}SreInsert(w,w->nSize);return w->nSize++;}
static void SreStop(SimResub_Work_t*w){int i;for(i=0;i<w->nSize;i++){ABC_FREE(w->pExps[i].pSim);if(w->pExps[i].pTruth)ABC_FREE(w->pExps[i].pTruth);}ABC_FREE(w->pExps);ABC_FREE(w->pBins);ABC_FREE(w->pNext);}
static void SreLeaves(SimResub_Work_t*w,int l,Vec_Ptr_t*v){SimResub_Exp_t*e=w->pExps+Abc_Lit2Var(l);if(!e->Cost){if(Vec_PtrFind(v,e->pLeaf)<0)Vec_PtrPush(v,e->pLeaf);return;}SreLeaves(w,e->iLeft,v);SreLeaves(w,e->iRight,v);}
static Dec_Edge_t SreGraph_rec(SimResub_Work_t*w,int l,Dec_Graph_t*g,Vec_Ptr_t*v){SimResub_Exp_t*e=w->pExps+Abc_Lit2Var(l);Dec_Edge_t a,b,r;if(!e->Cost)return Dec_EdgeCreate(Vec_PtrFind(v,e->pLeaf),Abc_LitIsCompl(l));a=SreGraph_rec(w,e->iLeft,g,v);b=SreGraph_rec(w,e->iRight,g,v);r=Dec_GraphAddNodeAnd(g,a,b);r.fCompl^=Abc_LitIsCompl(l);return r;}
static Dec_Graph_t*SreGraph(SimResub_Work_t*w,int l){Vec_Ptr_t*v=Vec_PtrAlloc(8);Dec_Graph_t*g;Abc_Obj_t*o;Dec_Edge_t r;int i;SreLeaves(w,l,v);g=Dec_GraphCreate(Vec_PtrSize(v));Vec_PtrForEachEntry(Abc_Obj_t*,v,o,i)Dec_GraphNode(g,i)->pFunc=o,Dec_GraphNode(g,i)->Level=o->Level;r=SreGraph_rec(w,l,g,v);Dec_GraphSetRoot(g,r);Vec_PtrFree(v);return g;}
static int SreSupp(SimResub_Work_t*w,int l){Vec_Ptr_t*v=Vec_PtrAlloc(8);int n;SreLeaves(w,l,v);n=Vec_PtrSize(v);Vec_PtrFree(v);return n;}
static void SreMarkTfo_rec( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i;
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    Abc_ObjForEachFanout( pObj, pFanout, i )
        if ( Abc_ObjIsNode(pFanout) )
            SreMarkTfo_rec( pFanout );
}
static int SreLegalGlobalObj( Abc_ManRes_t * p, Vec_Ptr_t * vInside, Abc_Obj_t * pRoot, Abc_Obj_t * pObj, Gia_Man_t * pGiaSrc, int Required )
{
    int iObj = Abc_Lit2Var(pObj->iTemp);
    if ( pObj == pRoot )
        return 0;
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return 0;
    if ( Vec_PtrFind(vInside, pObj) >= 0 )
        return 0;
    if ( p->fUseLevel && (int)pObj->Level > Required )
        return 0;
    if ( p->nSuppMax )
    {
        int Supp = Gia_ManSuppSize( pGiaSrc, &iObj, 1 );
        if ( Supp > p->nSuppMax )
            return 0;
    }
    return 1;
}

static int SreZeroLegalGlobalObj( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Abc_Obj_t * pObj, int Required )
{
    if ( pObj == pRoot )
        return 0;
    if ( Abc_NodeIsTravIdPrevious(pObj) )
        return 0;
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return 0;
    if ( p->fUseLevel && (int)pObj->Level > Required )
        return 0;
    return 1;
}

static void SreZeroDumpBuckets( Abc_ManRes_t * p, int nMax )
{
    Abc_Ntk_t * pNtk = p->pRoot->pNtk;
    Abc_Obj_t * pNode, * pObj;
    word * s, * ps;
    int i, j, h, nPrinted = 0, nSize, fCompl;
    printf( "SimResub-Zero: first %d nontrivial hash buckets\n", nMax );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        s = Abc_ManResubGlobalSim( p, pNode );
        fCompl = (s[0] >> 63) & 1;
        h = Abc_ManResubHashSim( s, fCompl ) % p->nHashSize;
        nSize = 0;
        for ( j = p->pHashBins[h]; j >= 0; j = p->pHashNext[j] )
            nSize++;
        if ( nSize <= 1 )
            continue;
        printf( "  bucket %5d target %6d %-12s size=%d :", h, pNode->Id, Abc_ObjName(pNode), nSize );
        for ( j = p->pHashBins[h]; j >= 0; j = p->pHashNext[j] )
        {
            pObj = Abc_NtkObj( pNtk, j );
            if ( pObj == NULL )
                continue;
            ps = Abc_ManResubGlobalSim( p, pObj );
            if ( !(SreEqW( ps, s, ABC_RS_SIM_WORDS, 0 ) || SreEqW( ps, s, ABC_RS_SIM_WORDS, 1 )) )
                continue;
            printf( " %d%s", pObj->Id, SreEqW( ps, s, ABC_RS_SIM_WORDS, 0 ) ? "+" : "-" );
        }
        printf( "\n" );
        if ( ++nPrinted >= nMax )
            break;
    }
    if ( !nPrinted )
        printf( "  none\n" );
}

static int SreZeroCandidateCost( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Abc_Obj_t * pObj, int fCompl, int Required, Dec_Graph_t ** ppBest, int * pBestAdded )
{
    Dec_Graph_t * pGraph;
    int nAdded, fSave = pObj->fPhase;
    pObj->fPhase = fCompl;
    pGraph = Abc_ManResubQuit0( pRoot, pObj );
    pObj->fPhase = fSave;
    nAdded = Dec_GraphToNetworkCount( pRoot, pGraph, p->nMffc, p->fUseLevel ? Required : ABC_INFINITY );
    if ( nAdded < 0 )
    {
        Dec_GraphFree( pGraph );
        p->nZeroRejectedLevel++;
        return 0;
    }
    p->nZeroChecked++;
    if ( nAdded >= p->nMffc )
    {
        Dec_GraphFree( pGraph );
        p->nZeroRejectedGain++;
        return 0;
    }
    if ( nAdded < *pBestAdded )
    {
        if ( *ppBest )
            Dec_GraphFree( *ppBest );
        *ppBest = pGraph;
        *pBestAdded = nAdded;
    }
    else
        Dec_GraphFree( pGraph );
    return 1;
}

static int Abc_NtkSimResubZeroSweep( Abc_ManRes_t * p, int fUpdateLevel, int fVerbose )
{
    Abc_Ntk_t * pNtk = p->pRoot->pNtk;
    Abc_Obj_t * pNode, * pObj;
    Dec_Graph_t * pBestGraph;
    word * s, * ps;
    abctime clk = Abc_Clock();
    int Required, i, j, h, fCompl, fChanged, nSize, nAdded, nPasses = 0, nTargets = 0, fPhase;
    assert( Abc_NtkIsStrash( pNtk ) );
    p->nNodesBeg = Abc_NtkNodeNum( pNtk );
    if ( fUpdateLevel )
        Abc_NtkStartReverseLevels( pNtk, 0 );
    Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
    while ( 1 )
    {
        fChanged = 0;
        Abc_ManResubBuildGlobalSim( p );
        Abc_NtkForEachNode( pNtk, pNode, i )
        {
            if ( Abc_NodeIsPersistant( pNode ) )
                continue;
            if ( Abc_ObjFanoutNum( pNode ) > 1000 )
                continue;
            p->pRoot = pNode;
            nTargets++;
            p->nMffc = Abc_NodeMffcLabelAig( pNode );
            if ( p->nMffc <= 0 )
                continue;
            Abc_NtkIncrementTravId( pNtk );
            SreMarkTfo_rec( pNode );
            Required = fUpdateLevel ? Abc_ObjRequiredLevel( pNode ) : ABC_INFINITY;
            s = Abc_ManResubGlobalSim( p, pNode );
            fCompl = (s[0] >> 63) & 1;
            h = Abc_ManResubHashSim( s, fCompl ) % p->nHashSize;
            nSize = 0;
            for ( j = p->pHashBins[h]; j >= 0; j = p->pHashNext[j] )
                nSize++;
            if ( nSize > 1 )
                p->nZeroBucketsGt1++;
            pBestGraph = NULL;
            nAdded = ABC_INFINITY;
            fPhase = 0;
            for ( j = p->pHashBins[h]; j >= 0; j = p->pHashNext[j] )
            {
                pObj = Abc_NtkObj( pNtk, j );
                if ( pObj == NULL )
                    continue;
                ps = Abc_ManResubGlobalSim( p, pObj );
                if ( !SreEqW( ps, s, ABC_RS_SIM_WORDS, 0 ) && !SreEqW( ps, s, ABC_RS_SIM_WORDS, 1 ) )
                {
                    p->nZeroNoMatch++;
                    continue;
                }
                p->nZeroRaw++;
                if ( !SreZeroLegalGlobalObj( p, pNode, pObj, Required ) )
                {
                    p->nZeroRejectedForbidden++;
                    continue;
                }
                p->nZeroLegal++;
                fPhase = SreEqW( ps, s, ABC_RS_SIM_WORDS, 1 );
                if ( !SreZeroCandidateCost( p, pNode, pObj, fPhase, Required, &pBestGraph, &nAdded ) )
                    continue;
            }
            if ( pBestGraph )
            {
                int nGain = p->nMffc - nAdded;
                Dec_GraphUpdateNetwork( pNode, pBestGraph, fUpdateLevel, nGain );
                Dec_GraphFree( pBestGraph );
                p->nZeroAccepted++;
                fChanged = 1;
                if ( fVerbose )
                    printf( "SimResub-Zero: accepted target %d gain=%d size=%d\n", pNode->Id, nGain, nAdded );
                break;
            }
        }
        nPasses++;
        if ( !fChanged )
            break;
        Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
    }
    p->nNodesEnd = Abc_NtkNodeNum( pNtk );
    p->timeTotal = Abc_Clock() - clk;
    if ( fVerbose )
    {
        printf( "SimResub-Zero: passes = %d  targets = %d  buckets>1 = %lld\n", nPasses, nTargets, (long long)p->nZeroBucketsGt1 );
        printf( "SimResub-Zero: raw = %lld  legal = %lld  checked = %lld  accepted = %lld\n", (long long)p->nZeroRaw, (long long)p->nZeroLegal, (long long)p->nZeroChecked, (long long)p->nZeroAccepted );
        printf( "SimResub-Zero: rejects forbidden = %lld  level = %lld  gain = %lld  no-match = %lld\n", (long long)p->nZeroRejectedForbidden, (long long)p->nZeroRejectedLevel, (long long)p->nZeroRejectedGain, (long long)p->nZeroNoMatch );
        printf( "SimResub-Zero: nodes %d -> %d\n", p->nNodesBeg, p->nNodesEnd );
    }
    if ( !p->nZeroAccepted )
        SreZeroDumpBuckets( p, 20 );
    if ( fUpdateLevel )
        Abc_NtkStopReverseLevels( pNtk );
    return 1;
}

static int SreBuildExpr_rec( SimResub_Work_t * w, Gia_Man_t * pGiaSrc, Gia_Man_t * pGiaNew, int l )
{
    SimResub_Exp_t * e = w->pExps + Abc_Lit2Var(l);
    if ( !e->Cost )
    {
        Gia_Obj_t * pObj = Gia_ManObj( pGiaSrc, Abc_Lit2Var( e->pLeaf->iTemp ) );
        return Abc_LitNotCond( pObj->Value, Abc_LitIsCompl(l) );
    }
    else
    {
        int iLit0 = SreBuildExpr_rec( w, pGiaSrc, pGiaNew, e->iLeft );
        int iLit1 = SreBuildExpr_rec( w, pGiaSrc, pGiaNew, e->iRight );
        int iLit  = Gia_ManAppendAnd( pGiaNew, iLit0, iLit1 );
        return Abc_LitNotCond( iLit, Abc_LitIsCompl(l) );
    }
}
static int SreExactValidate( Abc_ManRes_t * p, SimResub_Work_t * w, Gia_Man_t * pGiaSrc, Gia_Man_t * pGiaTgt, int l )
{
    Cec_ParCec_t Pars, * pPars = &Pars;
    Gia_Man_t * pGiaCand, * pMiter;
    int iLit, RetValue;
    Cec_ManCecSetDefaultParams( pPars );
    pPars->fSilent = 1;
    pGiaCand = Gia_ManDup( pGiaSrc );
    iLit = SreBuildExpr_rec( w, pGiaSrc, pGiaCand, l );
    Gia_ManAppendCo( pGiaCand, iLit );
    pMiter = Gia_ManMiter( pGiaCand, pGiaTgt, 0, 1, 0, 0, 0 );
    if ( pMiter == NULL )
    {
        Gia_ManStop( pGiaCand );
        return 0;
    }
    RetValue = Cec_ManVerify( pMiter, pPars );
    Gia_ManStop( pMiter );
    Gia_ManStop( pGiaCand );
    return RetValue == 1;
}
static int SreTry(Abc_ManRes_t*p,SimResub_Work_t*w,int l,Gia_Man_t*pGiaSrc,Gia_Man_t*pGiaTgt,int Req,Dec_Graph_t**best,int*bestC,int*first){Dec_Graph_t*g;int c=w->pExps[Abc_Lit2Var(l)].Cost,r;p->nGenCost[c]++;p->nSubmitted++;if(p->nSuppMax&&SreSupp(w,l)>p->nSuppMax){p->nRejectedLegal++;return 0;}if(!SreExactValidate(p,w,pGiaSrc,pGiaTgt,l)){p->nRejectedExact++;return 0;}p->nPassedExact++;g=SreGraph(w,l);r=Dec_GraphToNetworkCount(p->pRoot,g,c,p->fUseLevel?Req:ABC_INFINITY);if(r<0){p->nRejectedLevel++;Dec_GraphFree(g);return 1;}if(r>=p->nMffc){p->nRejectedGain++;Dec_GraphFree(g);return 1;}if(*first<0)*first=r;if(r<*bestC){if(*best)Dec_GraphFree(*best);*best=g;*bestC=r;}else Dec_GraphFree(g);return 2;}
static Dec_Graph_t*Abc_ManSimResubEvalExplicit(Abc_ManRes_t*p,int nSteps,int Req){SimResub_Work_t w={0};Abc_Obj_t*o;Vec_Ptr_t*vGlobals=Vec_PtrAlloc(Abc_NtkObjNumMax(p->pRoot->pNtk));Vec_Ptr_t*vImp=Vec_PtrAlloc(Abc_NtkObjNumMax(p->pRoot->pNtk));int* pMap=ABC_ALLOC(int,Abc_NtkObjNumMax(p->pRoot->pNtk));Gia_Man_t * pGiaSrc, * pGiaTgt;unsigned*t=ABC_ALLOC(unsigned,p->nWords);word*s=Abc_ManResubGlobalSim(p,p->pRoot);Dec_Graph_t*best=NULL;int bestC=ABC_INFINITY,first=-1,i,j,c,a,b,z,n0,nGen=0,q;ABC_INT64_T old0=p->nGenCost[0], oldSubmitted=p->nSubmitted;int h, fComplRoot;memset(pMap,-1,sizeof(int)*Abc_NtkObjNumMax(p->pRoot->pNtk));w.nWords=p->nWords;w.nSimWords=ABC_RS_SIM_WORDS;w.nHash=Abc_PrimeCudd(10007);w.pBins=ABC_ALLOC(int,w.nHash);for(q=0;q<w.nHash;q++)w.pBins[q]=-1;for(q=0;q<p->nWords;q++)t[q]=p->pRoot->fPhase?~((unsigned*)p->pRoot->pData)[q]:((unsigned*)p->pRoot->pData)[q];pGiaSrc = Abc_NtkToGia2( p->pRoot->pNtk, 0 );if ( pGiaSrc == NULL ){ABC_FREE(t);Vec_PtrFree(vGlobals);Vec_PtrFree(vImp);ABC_FREE(pMap);Abc_NtkForEachObj( p->pRoot->pNtk, o, i ) o->iTemp = -1;return NULL;}Abc_NtkIncrementTravId( p->pRoot->pNtk );SreMarkTfo_rec( p->pRoot );Abc_NtkForEachNodeCi( p->pRoot->pNtk, o, i ){if ( !SreLegalGlobalObj( p, p->vTemp, p->pRoot, o, pGiaSrc, Req ) ) continue;Vec_PtrPush( vGlobals, o );pMap[o->Id] = Vec_PtrSize(vGlobals)-1;}p->nLegalHashLits += (ABC_INT64_T)Vec_PtrSize(vGlobals) * 2;
Vec_PtrForEachEntry( Abc_Obj_t *, vGlobals, o, i ){word * ps = Abc_ManResubGlobalSim( p, o );if ( SreImpl( s, ps, ABC_RS_SIM_WORDS, 0 ) || SreImpl( s, ps, ABC_RS_SIM_WORDS, 1 ) ) Vec_PtrPush( vImp, o );}p->nImplLits += (ABC_INT64_T)Vec_PtrSize(vImp) * 2;for(i=0;i<Vec_PtrSize(vGlobals);i++)SreLeaf(&w,p,(Abc_Obj_t*)Vec_PtrEntry(vGlobals,i));pGiaTgt = Gia_ManDup( pGiaSrc );Gia_ManAppendCo( pGiaTgt, Gia_ManObj( pGiaSrc, Abc_Lit2Var(p->pRoot->iTemp) )->Value );fComplRoot = (s[0] >> 63) & 1;h = Abc_ManResubHashSim( s, fComplRoot ) % p->nHashSize;for ( i = p->pHashBins[h]; i >= 0; i = p->pHashNext[i] ){int idx = pMap[i];if ( idx < 0 ) continue;o = (Abc_Obj_t *)Vec_PtrEntry( vGlobals, idx );if ( SreEqW( Abc_ManResubGlobalSim(p,o), s, w.nSimWords, 0 ) || SreEqW( Abc_ManResubGlobalSim(p,o), s, w.nSimWords, 1 ) ){if ( SreEqW( Abc_ManResubGlobalSim(p,o), s, w.nSimWords, 0 ) ) SreTry(p,&w,Abc_Var2Lit(idx,0),pGiaSrc,pGiaTgt,Req,&best,&bestC,&first); else SreTry(p,&w,Abc_Var2Lit(idx,1),pGiaSrc,pGiaTgt,Req,&best,&bestC,&first);}}if(p->nGenCost[0]>old0)p->nTargets0++;for(c=1;c<=nSteps;c++){n0=w.nSize;for(i=0;i<n0;i++)for(j=i;j<n0;j++)if(w.pExps[i].Cost+w.pExps[j].Cost+1==c)for(a=0;a<2;a++)for(b=0;b<2;b++){word x[ABC_RS_SIM_WORDS];for(q=0;q<w.nSimWords;q++)x[q]=(a?~w.pExps[i].pSim[q]:w.pExps[i].pSim[q])&(b?~w.pExps[j].pSim[q]:w.pExps[j].pSim[q]);p->nPairsTried++;if(p->fPairUseful&&!SreImpl(s,x,w.nSimWords,0)&&!SreImpl(s,x,w.nSimWords,1)){p->nRejectedSim++;continue;}if(p->nPairMax&&++nGen>p->nPairMax){p->fLimitHit=1;goto done;}z=SreAnd(&w,Abc_Var2Lit(i,a),Abc_Var2Lit(j,b));p->nIntermsGenerated++;for(q=0;q<2;q++)if(SreEqW(w.pExps[z].pSim,s,w.nSimWords,q)){SreTry(p,&w,Abc_Var2Lit(z,q),pGiaSrc,pGiaTgt,Req,&best,&bestC,&first);if(p->fFirstMatch&&best)goto done;if(p->nSimCandMax&&p->nSubmitted-oldSubmitted>=p->nSimCandMax){p->fLimitHit=1;goto done;}}}if(best&&bestC<=c)break;}done:if(best){p->nAcceptedCost[bestC]++;p->nAcceptedSim++;p->nLastGain=p->nMffc-bestC;p->nBestGain[Abc_MinInt(p->nLastGain,15)]++;if(first>=0&&first!=bestC)p->nFirstNotBest++;}SreStop(&w);Gia_ManStop(pGiaTgt);Gia_ManStop(pGiaSrc);ABC_FREE(t);Vec_PtrFree(vGlobals);Vec_PtrFree(vImp);ABC_FREE(pMap);Abc_NtkForEachObj( p->pRoot->pNtk, o, i ) o->iTemp = -1;return best;}
void Abc_ManResubCleanup( Abc_ManRes_t * p )
{
    Abc_Obj_t * pObj;
    int i;
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs, pObj, i )
        pObj->pData = NULL;
    Vec_PtrClear( p->vDivs );
    p->pRoot = NULL;
}

/**Function*************************************************************

  Synopsis    [Evaluates resubstution of one cut.]

  Description [Returns the graph to add if any.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Abc_ManResubEval( Abc_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int nSteps, int fUpdateLevel, int fVerbose )
{
    extern int Abc_NodeMffcInside( Abc_Obj_t * pNode, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vInside );
    Dec_Graph_t * pGraph;
    int Required;
    abctime clk;

    Required = fUpdateLevel? Abc_ObjRequiredLevel(pRoot) : ABC_INFINITY;

    assert( nSteps >= 0 );
    assert( nSteps <= (p->fUseSim ? 5 : 3) );
    p->pRoot = pRoot;
    if ( p->fUseSim ) Abc_ManResubBuildGlobalSim( p );
    p->nLeaves = Vec_PtrSize(vLeaves);
    p->nLastGain = -1;

    // collect the MFFC
clk = Abc_Clock();
    p->nMffc = Abc_NodeMffcInside( pRoot, vLeaves, p->vTemp );
p->timeMffc += Abc_Clock() - clk;
    assert( p->nMffc > 0 );

    // collect the divisor nodes
clk = Abc_Clock();
    if ( !(p->fUseSim ? Abc_ManResubCollectDivsSim(p, pRoot, vLeaves, Required) : Abc_ManResubCollectDivs(p, pRoot, vLeaves, Required)) )
        return NULL;
    p->timeDiv += Abc_Clock() - clk;

    p->nTotalDivs   += p->nDivs;
    p->nTotalLeaves += p->nLeaves;

    // simulate the nodes
clk = Abc_Clock();
    Abc_ManResubSimulate( p->vDivs, p->nLeaves, p->vSims, p->nLeavesMax, p->nWords );
p->timeSim += Abc_Clock() - clk;
    if ( p->fUseSim )
        return Abc_ManSimResubEvalExplicit( p, nSteps, Required );

    if ( p->pFile && Vec_PtrSize(vLeaves) != p->nLeavesMax && p->nProbs < (1 << p->Log2Probs) ) 
    {
        Abc_Obj_t * pObj; int i, w, Count = 0;
        unsigned * pFunc = (unsigned *)pRoot->pData;
        int Limit = Abc_MinInt( Vec_PtrSize(p->vDivs), (1 << p->Log2Divs) - 2 );
        Vec_PtrForEachEntryStop( Abc_Obj_t *, p->vDivs, pObj, i, Limit )
            Count += fwrite( (unsigned *)pObj->pData, 1, sizeof(unsigned) * p->nWords, p->pFile );
        // write constant zeros
        memset( p->pTempSim, 0, sizeof(unsigned) * p->nWords );
        for ( ; i < (1 << p->Log2Divs) - 2; i++ ) 
            Count += fwrite( p->pTempSim, 1, sizeof(unsigned) * p->nWords, p->pFile );
        // write offset
        for ( w = 0; w < p->nWords; w++ )
            p->pTempSim[w] = p->pCareSet[w] & ~pFunc[w];
        Count += fwrite( p->pTempSim, 1, sizeof(unsigned) * p->nWords, p->pFile );
        // write onset
        for ( w = 0; w < p->nWords; w++ )
            p->pTempSim[w] = p->pCareSet[w] & pFunc[w];
        Count += fwrite( p->pTempSim, 1, sizeof(unsigned) * p->nWords, p->pFile );
        assert( Count == (1 << p->Log2Divs) * (1 << (p->nLeavesMax-3)) );
        p->nProbs++;
        //printf( "Finished dumping node %d.  Written %d bytes of data (expected %d bytes).\n", pRoot->Id, Count, (1 << p->Log2Divs) * (1 << (p->nLeavesMax-3)) );
        //printf( "%d ", Vec_PtrSize(p->vDivs) );
        return NULL;
    }

clk = Abc_Clock();
    // consider constants
    if ( (pGraph = Abc_ManResubQuit( p )) )
    {
        p->nUsedNodeC++;
        p->nLastGain = p->nMffc;
        return pGraph;
    }

    // consider equal nodes
    if ( (pGraph = Abc_ManResubDivs0( p )) )
    {
p->timeRes1 += Abc_Clock() - clk;
        p->nUsedNode0++;
        p->nLastGain = p->nMffc;
        return pGraph;
    }
    if ( nSteps == 0 || p->nMffc == 1 )
    {
p->timeRes1 += Abc_Clock() - clk;
        return NULL;
    }

    // get the one level divisors
    Abc_ManResubDivsS( p, Required );

//    if ( Vec_PtrSize(vLeaves) >= 6 )
//        Abc_ManResubDumpInstance( p->vDivs, Vec_PtrSize(vLeaves), p->nDivs, p->nWords );

    // consider one node
    if ( (pGraph = Abc_ManResubDivs1( p, Required )) )
    {
p->timeRes1 += Abc_Clock() - clk;
        p->nLastGain = p->nMffc - 1;
        return pGraph;
    }
p->timeRes1 += Abc_Clock() - clk;
    if ( nSteps == 1 || p->nMffc == 2 )
        return NULL;

clk = Abc_Clock();
    // consider triples
    if ( (pGraph = Abc_ManResubDivs12( p, Required )) )
    {
p->timeRes2 += Abc_Clock() - clk;
        p->nLastGain = p->nMffc - 2;
        return pGraph;
    }
p->timeRes2 += Abc_Clock() - clk;

    // get the two level divisors
clk = Abc_Clock();
    Abc_ManResubDivsD( p, Required );
p->timeResD += Abc_Clock() - clk;

    // consider two nodes
clk = Abc_Clock();
    if ( (pGraph = Abc_ManResubDivs2( p, Required )) )
    {
p->timeRes2 += Abc_Clock() - clk;
        p->nLastGain = p->nMffc - 2;
        return pGraph;
    }
p->timeRes2 += Abc_Clock() - clk;
    if ( nSteps == 2 || p->nMffc == 3 )
        return NULL;

    // consider two nodes
clk = Abc_Clock();
    if ( (pGraph = Abc_ManResubDivs3( p, Required )) )
    {
p->timeRes3 += Abc_Clock() - clk;
        p->nLastGain = p->nMffc - 3;
        return pGraph;
    }
p->timeRes3 += Abc_Clock() - clk;
    if ( nSteps == 3 || p->nLeavesMax == 4 )
        return NULL;
    return NULL;
}




/**Function*************************************************************

  Synopsis    [Computes the volume and checks if the cut is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CutVolumeCheck_rec( Abc_Obj_t * pObj )
{
    // quit if the node is visited (or if it is a leaf)
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return 0;
    Abc_NodeSetTravIdCurrent(pObj);
    // report the error
    if ( Abc_ObjIsCi(pObj) )
        printf( "Abc_CutVolumeCheck() ERROR: The set of nodes is not a cut!\n" );
    // count the number of nodes in the leaves
    return 1 + Abc_CutVolumeCheck_rec( Abc_ObjFanin0(pObj) ) +
        Abc_CutVolumeCheck_rec( Abc_ObjFanin1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Computes the volume and checks if the cut is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CutVolumeCheck( Abc_Obj_t * pNode, Vec_Ptr_t * vLeaves )
{
    Abc_Obj_t * pObj;
    int i;
    // mark the leaves
    Abc_NtkIncrementTravId( pNode->pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pObj, i )
        Abc_NodeSetTravIdCurrent( pObj ); 
    // traverse the nodes starting from the given one and count them
    return Abc_CutVolumeCheck_rec( pNode );
}

/**Function*************************************************************

  Synopsis    [Computes the factor cut of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_CutFactor_rec( Abc_Obj_t * pObj, Vec_Ptr_t * vLeaves )
{
    if ( pObj->fMarkA )
        return;
    if ( Abc_ObjIsCi(pObj) || (Abc_ObjFanoutNum(pObj) > 1 && !Abc_NodeIsMuxControlType(pObj)) )
    {
        Vec_PtrPush( vLeaves, pObj );
        pObj->fMarkA = 1;
        return;
    }
    Abc_CutFactor_rec( Abc_ObjFanin0(pObj), vLeaves );
    Abc_CutFactor_rec( Abc_ObjFanin1(pObj), vLeaves );
}

/**Function*************************************************************

  Synopsis    [Computes the factor cut of the node.]

  Description [Factor-cut is the cut at a node in terms of factor-nodes.
  Factor-nodes are roots of the node trees (MUXes/EXORs are counted as single nodes).
  Factor-cut is unique for the given node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_CutFactor( Abc_Obj_t * pNode )
{
    Vec_Ptr_t * vLeaves;
    Abc_Obj_t * pObj;
    int i;
    assert( !Abc_ObjIsCi(pNode) );
    vLeaves  = Vec_PtrAlloc( 10 );
    Abc_CutFactor_rec( Abc_ObjFanin0(pNode), vLeaves );
    Abc_CutFactor_rec( Abc_ObjFanin1(pNode), vLeaves );
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pObj, i )
        pObj->fMarkA = 0;
    return vLeaves;
}

/**Function*************************************************************

  Synopsis    [Cut computation.]

  Description [This cut computation works as follows: 
  It starts with the factor cut at the node. If the factor-cut is large, quit.
  It supports the set of leaves of the cut under construction and labels all nodes
  in the cut under construction, including the leaves.
  It computes the factor-cuts of the leaves and checks if it is easible to add any of them.
  If it is, it randomly chooses one feasible and continues.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_CutFactorLarge( Abc_Obj_t * pNode, int nLeavesMax )
{
    Vec_Ptr_t * vLeaves, * vFactors, * vFact, * vNext;
    Vec_Int_t * vFeasible;
    Abc_Obj_t * pLeaf, * pTemp;
    int i, k, Counter, RandLeaf;
    int BestCut, BestShare;
    assert( Abc_ObjIsNode(pNode) );
    // get one factor-cut
    vLeaves = Abc_CutFactor( pNode );
    if ( Vec_PtrSize(vLeaves) > nLeavesMax )
    {
        Vec_PtrFree(vLeaves);
        return NULL;
    }
    if ( Vec_PtrSize(vLeaves) == nLeavesMax )
        return vLeaves;
    // initialize the factor cuts for the leaves
    vFactors = Vec_PtrAlloc( nLeavesMax );
    Abc_NtkIncrementTravId( pNode->pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pLeaf, i )
    {
        Abc_NodeSetTravIdCurrent( pLeaf ); 
        if ( Abc_ObjIsCi(pLeaf) )
            Vec_PtrPush( vFactors, NULL );
        else
            Vec_PtrPush( vFactors, Abc_CutFactor(pLeaf) );
    }
    // construct larger factor cuts
    vFeasible = Vec_IntAlloc( nLeavesMax );
    while ( 1 )
    {
        BestCut = -1, BestShare = -1;
        // find the next feasible cut to add
        Vec_IntClear( vFeasible );
        Vec_PtrForEachEntry( Vec_Ptr_t *, vFactors, vFact, i )
        {
            if ( vFact == NULL )
                continue;
            // count the number of unmarked leaves of this factor cut
            Counter = 0;
            Vec_PtrForEachEntry( Abc_Obj_t *, vFact, pTemp, k )
                Counter += !Abc_NodeIsTravIdCurrent(pTemp);
            // if the number of new leaves is smaller than the diff, it is feasible
            if ( Counter <= nLeavesMax - Vec_PtrSize(vLeaves) + 1 )
            {
                Vec_IntPush( vFeasible, i );
                if ( BestCut == -1 || BestShare < Vec_PtrSize(vFact) - Counter )
                    BestCut = i, BestShare = Vec_PtrSize(vFact) - Counter;
            }
        }
        // quit if there is no feasible factor cuts
        if ( Vec_IntSize(vFeasible) == 0 )
            break;
        // randomly choose one leaf and get its factor cut
//        RandLeaf = Vec_IntEntry( vFeasible, rand() % Vec_IntSize(vFeasible) );
        // choose the cut that has most sharing with the other cuts
        RandLeaf = BestCut;

        pLeaf = (Abc_Obj_t *)Vec_PtrEntry( vLeaves, RandLeaf );
        vNext = (Vec_Ptr_t *)Vec_PtrEntry( vFactors, RandLeaf );
        // unmark this leaf
        Abc_NodeSetTravIdPrevious( pLeaf ); 
        // remove this cut from the leaves and factor cuts
        for ( i = RandLeaf; i < Vec_PtrSize(vLeaves)-1; i++ )
        {
            Vec_PtrWriteEntry( vLeaves,  i, Vec_PtrEntry(vLeaves, i+1) );
            Vec_PtrWriteEntry( vFactors, i, Vec_PtrEntry(vFactors,i+1) );
        }
        Vec_PtrShrink( vLeaves,  Vec_PtrSize(vLeaves) -1 );
        Vec_PtrShrink( vFactors, Vec_PtrSize(vFactors)-1 );
        // add new leaves, compute their factor cuts
        Vec_PtrForEachEntry( Abc_Obj_t *, vNext, pLeaf, i )
        {
            if ( Abc_NodeIsTravIdCurrent(pLeaf) )
                continue;
            Abc_NodeSetTravIdCurrent( pLeaf ); 
            Vec_PtrPush( vLeaves, pLeaf );
            if ( Abc_ObjIsCi(pLeaf) )
                Vec_PtrPush( vFactors, NULL );
            else
                Vec_PtrPush( vFactors, Abc_CutFactor(pLeaf) );
        }
        Vec_PtrFree( vNext );
        assert( Vec_PtrSize(vLeaves) <= nLeavesMax );
        if ( Vec_PtrSize(vLeaves) == nLeavesMax )
            break;
    }

    // remove temporary storage
    Vec_PtrForEachEntry( Vec_Ptr_t *, vFactors, vFact, i )
        if ( vFact ) Vec_PtrFree( vFact );
    Vec_PtrFree( vFactors );
    Vec_IntFree( vFeasible );
    return vLeaves;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

