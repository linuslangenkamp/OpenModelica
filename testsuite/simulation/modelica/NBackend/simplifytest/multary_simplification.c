/* Main Simulation File */

#if defined(__cplusplus)
extern "C" {
#endif

#include "multary_simplification_model.h"
#include "simulation/solver/events.h"

#define prefixedName_performSimulation multary_simplification_performSimulation
#define prefixedName_updateContinuousSystem multary_simplification_updateContinuousSystem
#include <simulation/solver/perform_simulation.c.inc>

#define prefixedName_performQSSSimulation multary_simplification_performQSSSimulation
#include <simulation/solver/perform_qss_simulation.c.inc>


/* dummy VARINFO and FILEINFO */
const FILE_INFO dummyFILE_INFO = omc_dummyFileInfo;
const VAR_INFO dummyVAR_INFO = omc_dummyVarInfo;

int multary_simplification_input_function(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH


  TRACE_POP
  return 0;
}

int multary_simplification_input_function_init(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH


  TRACE_POP
  return 0;
}

int multary_simplification_input_function_updateStartValues(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH


  TRACE_POP
  return 0;
}

int multary_simplification_inputNames(DATA *data, char ** names){
  TRACE_PUSH


  TRACE_POP
  return 0;
}

int multary_simplification_data_function(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH

  TRACE_POP
  return 0;
}

int multary_simplification_dataReconciliationInputNames(DATA *data, char ** names){
  TRACE_PUSH


  TRACE_POP
  return 0;
}

int multary_simplification_output_function(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH


  TRACE_POP
  return 0;
}

int multary_simplification_setc_function(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH


  TRACE_POP
  return 0;
}


/*
equation index: 1
type: SIMPLE_ASSIGN
z = 8.0 + time
*/
void multary_simplification_eqFunction_1(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH
  const int equationIndexes[2] = {1,1};
  data->localData[0]->realVars[0] /* z variable */ = 8.0 + data->localData[0]->timeValue;
  TRACE_POP
}

OMC_DISABLE_OPT
int multary_simplification_functionDAE(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH
  int equationIndexes[1] = {0};
#if !defined(OMC_MINIMAL_RUNTIME)
  if (measure_time_flag) rt_tick(SIM_TIMER_DAE);
#endif

  data->simulationInfo->needToIterate = 0;
  data->simulationInfo->discreteCall = 1;
  multary_simplification_functionLocalKnownVars(data, threadData);
  multary_simplification_eqFunction_1(data, threadData);
  data->simulationInfo->discreteCall = 0;

#if !defined(OMC_MINIMAL_RUNTIME)
  if (measure_time_flag) rt_accumulate(SIM_TIMER_DAE);
#endif
  TRACE_POP
  return 0;
}


int multary_simplification_functionLocalKnownVars(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH


  TRACE_POP
  return 0;
}


int multary_simplification_functionODE(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH
#if !defined(OMC_MINIMAL_RUNTIME)
  if (measure_time_flag) rt_tick(SIM_TIMER_FUNCTION_ODE);
#endif


  data->simulationInfo->callStatistics.functionODE++;

  multary_simplification_functionLocalKnownVars(data, threadData);
  /* no ODE systems */

#if !defined(OMC_MINIMAL_RUNTIME)
  if (measure_time_flag) rt_accumulate(SIM_TIMER_FUNCTION_ODE);
#endif

  TRACE_POP
  return 0;
}

/* forward the main in the simulation runtime */
extern int _main_SimulationRuntime(int argc, char**argv, DATA *data, threadData_t *threadData);

#include "multary_simplification_12jac.h"
#include "multary_simplification_13opt.h"

struct OpenModelicaGeneratedFunctionCallbacks multary_simplification_callback = {
   (int (*)(DATA *, threadData_t *, void *)) multary_simplification_performSimulation,    /* performSimulation */
   (int (*)(DATA *, threadData_t *, void *)) multary_simplification_performQSSSimulation,    /* performQSSSimulation */
   multary_simplification_updateContinuousSystem,    /* updateContinuousSystem */
   multary_simplification_callExternalObjectDestructors,    /* callExternalObjectDestructors */
   NULL,    /* initialNonLinearSystem */
   NULL,    /* initialLinearSystem */
   NULL,    /* initialMixedSystem */
   #if !defined(OMC_NO_STATESELECTION)
   multary_simplification_initializeStateSets,
   #else
   NULL,
   #endif    /* initializeStateSets */
   multary_simplification_initializeDAEmodeData,
   multary_simplification_functionODE,
   multary_simplification_functionAlgebraics,
   multary_simplification_functionDAE,
   multary_simplification_functionLocalKnownVars,
   multary_simplification_input_function,
   multary_simplification_input_function_init,
   multary_simplification_input_function_updateStartValues,
   multary_simplification_data_function,
   multary_simplification_output_function,
   multary_simplification_setc_function,
   multary_simplification_function_storeDelayed,
   multary_simplification_function_storeSpatialDistribution,
   multary_simplification_function_initSpatialDistribution,
   multary_simplification_updateBoundVariableAttributes,
   multary_simplification_functionInitialEquations,
   1, /* useHomotopy - 0: local homotopy (equidistant lambda), 1: global homotopy (equidistant lambda), 2: new global homotopy approach (adaptive lambda), 3: new local homotopy approach (adaptive lambda)*/
   NULL,
   multary_simplification_functionRemovedInitialEquations,
   multary_simplification_updateBoundParameters,
   multary_simplification_checkForAsserts,
   multary_simplification_function_ZeroCrossingsEquations,
   multary_simplification_function_ZeroCrossings,
   multary_simplification_function_updateRelations,
   multary_simplification_zeroCrossingDescription,
   multary_simplification_relationDescription,
   multary_simplification_function_initSample,
   multary_simplification_INDEX_JAC_A,
   multary_simplification_INDEX_JAC_B,
   multary_simplification_INDEX_JAC_C,
   multary_simplification_INDEX_JAC_D,
   multary_simplification_INDEX_JAC_F,
   multary_simplification_initialAnalyticJacobianA,
   multary_simplification_initialAnalyticJacobianB,
   multary_simplification_initialAnalyticJacobianC,
   multary_simplification_initialAnalyticJacobianD,
   multary_simplification_initialAnalyticJacobianF,
   multary_simplification_functionJacA_column,
   multary_simplification_functionJacB_column,
   multary_simplification_functionJacC_column,
   multary_simplification_functionJacD_column,
   multary_simplification_functionJacF_column,
   multary_simplification_linear_model_frame,
   multary_simplification_linear_model_datarecovery_frame,
   multary_simplification_mayer,
   multary_simplification_lagrange,
   multary_simplification_pickUpBoundsForInputsInOptimization,
   multary_simplification_setInputData,
   multary_simplification_getTimeGrid,
   multary_simplification_symbolicInlineSystem,
   multary_simplification_function_initSynchronous,
   multary_simplification_function_updateSynchronous,
   multary_simplification_function_equationsSynchronous,
   multary_simplification_inputNames,
   multary_simplification_dataReconciliationInputNames,
   NULL,
   NULL,
   NULL,
   -1

};

static const MMC_DEFSTRUCTLIT(_OMC_LIT_RESOURCES,0,MMC_ARRAY_TAG) {}};
void multary_simplification_setupDataStruc(DATA *data, threadData_t *threadData)
{
  assertStreamPrint(threadData,0!=data, "Error while initialize Data");
  threadData->localRoots[LOCAL_ROOT_SIMULATION_DATA] = data;
  data->callback = &multary_simplification_callback;
  OpenModelica_updateUriMapping(threadData, MMC_REFSTRUCTLIT(_OMC_LIT_RESOURCES));
  data->modelData->modelName = "multary_simplification";
  data->modelData->modelFilePrefix = "multary_simplification";
  data->modelData->resultFileName = NULL;
  data->modelData->modelDir = "";
  data->modelData->modelGUID = "{5b01ebf9-34ba-4ad2-a438-1e47d480b451}";
  #if defined(OPENMODELICA_XML_FROM_FILE_AT_RUNTIME)
  data->modelData->initXMLData = NULL;
  data->modelData->modelDataXml.infoXMLData = NULL;
  #else
  #if defined(_MSC_VER) /* handle joke compilers */
  {
  /* for MSVC we encode a string like char x[] = {'a', 'b', 'c', '\0'} */
  /* because the string constant limit is 65535 bytes */
  static const char contents_init[] =
    #include "multary_simplification_init.c"
    ;
  static const char contents_info[] =
    #include "multary_simplification_info.c"
    ;
    data->modelData->initXMLData = contents_init;
    data->modelData->modelDataXml.infoXMLData = contents_info;
  }
  #else /* handle real compilers */
  data->modelData->initXMLData =
  #include "multary_simplification_init.c"
    ;
  data->modelData->modelDataXml.infoXMLData =
  #include "multary_simplification_info.c"
    ;
  #endif /* defined(_MSC_VER) */
  #endif /* defined(OPENMODELICA_XML_FROM_FILE_AT_RUNTIME) */
  data->modelData->runTestsuite = 0;

  data->modelData->nStates = 0;
  data->modelData->nVariablesReal = 1;
  data->modelData->nDiscreteReal = 0;
  data->modelData->nVariablesInteger = 0;
  data->modelData->nVariablesBoolean = 0;
  data->modelData->nVariablesString = 0;
  data->modelData->nParametersReal = 0;
  data->modelData->nParametersInteger = 0;
  data->modelData->nParametersBoolean = 0;
  data->modelData->nParametersString = 0;
  data->modelData->nInputVars = 0;
  data->modelData->nOutputVars = 0;

  data->modelData->nAliasReal = 0;
  data->modelData->nAliasInteger = 0;
  data->modelData->nAliasBoolean = 0;
  data->modelData->nAliasString = 0;

  data->modelData->nZeroCrossings = 0;
  data->modelData->nSamples = 0;
  data->modelData->nRelations = 0;
  data->modelData->nMathEvents = 0;
  data->modelData->nExtObjs = 0;

  data->modelData->modelDataXml.fileName = "multary_simplification_info.json";
  data->modelData->modelDataXml.modelInfoXmlLength = 0;
  data->modelData->modelDataXml.nFunctions = 0;
  data->modelData->modelDataXml.nProfileBlocks = 0;
  data->modelData->modelDataXml.nEquations = 2;
  data->modelData->nMixedSystems = 0;
  data->modelData->nLinearSystems = 0;
  data->modelData->nNonLinearSystems = 0;
  data->modelData->nStateSets = 0;
  data->modelData->nJacobians = 5;
  data->modelData->nOptimizeConstraints = 0;
  data->modelData->nOptimizeFinalConstraints = 0;

  data->modelData->nDelayExpressions = 0;

  data->modelData->nClocks = 0;
  data->modelData->nSubClocks = 0;

  data->modelData->nSpatialDistributions = 0;

  data->modelData->nSensitivityVars = 0;
  data->modelData->nSensitivityParamVars = 0;
  data->modelData->nSetcVars = 0;
  data->modelData->ndataReconVars = 0;
  data->modelData->linearizationDumpLanguage =
  OMC_LINEARIZE_DUMP_LANGUAGE_MODELICA;
}

static int rml_execution_failed()
{
  fflush(NULL);
  fprintf(stderr, "Execution failed!\n");
  fflush(NULL);
  return 1;
}

#if defined(threadData)
#undef threadData
#endif
/* call the simulation runtime main from our main! */
int main(int argc, char**argv)
{
  int res;
  DATA data;
  MODEL_DATA modelData;
  SIMULATION_INFO simInfo;
  data.modelData = &modelData;
  data.simulationInfo = &simInfo;
  measure_time_flag = 0;
  compiledInDAEMode = 0;
  compiledWithSymSolver = 0;
  MMC_INIT(0);
  omc_alloc_interface.init();
  {
    MMC_TRY_TOP()

    MMC_TRY_STACK()

    multary_simplification_setupDataStruc(&data, threadData);
    res = _main_SimulationRuntime(argc, argv, &data, threadData);

    MMC_ELSE()
    rml_execution_failed();
    fprintf(stderr, "Stack overflow detected and was not caught.\nSend us a bug report at https://trac.openmodelica.org/OpenModelica/newticket\n    Include the following trace:\n");
    printStacktraceMessages();
    fflush(NULL);
    return 1;
    MMC_CATCH_STACK()

    MMC_CATCH_TOP(return rml_execution_failed());
  }

  fflush(NULL);
  EXIT(res);
  return res;
}

#ifdef __cplusplus
}
#endif


