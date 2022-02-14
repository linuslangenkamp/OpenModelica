/* Algebraic */
#include "multary_simplification_model.h"

#ifdef __cplusplus
extern "C" {
#endif


/* forwarded equations */
extern void multary_simplification_eqFunction_1(DATA* data, threadData_t *threadData);

static void functionAlg_system0(DATA *data, threadData_t *threadData)
{
  multary_simplification_eqFunction_1(data, threadData);
  threadData->lastEquationSolved = 1;
}
/* for continuous time variables */
int multary_simplification_functionAlgebraics(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH

#if !defined(OMC_MINIMAL_RUNTIME)
  if (measure_time_flag) rt_tick(SIM_TIMER_ALGEBRAICS);
#endif
  data->simulationInfo->callStatistics.functionAlgebraics++;

  functionAlg_system0(data, threadData);

  multary_simplification_function_savePreSynchronous(data, threadData);

#if !defined(OMC_MINIMAL_RUNTIME)
  if (measure_time_flag) rt_accumulate(SIM_TIMER_ALGEBRAICS);
#endif

  TRACE_POP
  return 0;
}

#ifdef __cplusplus
}
#endif
