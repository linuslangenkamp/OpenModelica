/*
 * This file belongs to the OpenModelica Run-Time System
 *
 * Copyright (c) 1998-2026, Open Source Modelica Consortium (OSMC), c/o Linköpings
 * universitet, Department of Computer and Information Science, SE-58183 Linköping, Sweden. All rights
 * reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF THE BSD NEW LICENSE OR THE
 * AGPL VERSION 3 LICENSE OR THE OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.8. ANY
 * USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES RECIPIENT'S
 * ACCEPTANCE OF THE BSD NEW LICENSE OR THE OSMC PUBLIC LICENSE OR THE AGPL
 * VERSION 3, ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the OSMC (Open Source Modelica Consortium) Public License
 * (OSMC-PL) are obtained from OSMC, either from the above address, from the URLs:
 * http://www.openmodelica.org or https://github.com/OpenModelica/ or
 * http://www.ida.liu.se/projects/OpenModelica, and in the OpenModelica distribution. GNU
 * AGPL version 3 is obtained from: https://www.gnu.org/licenses/licenses.html#GPL. The BSD NEW
 * License is obtained from: http://www.opensource.org/licenses/BSD-3-Clause.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY
 * SET FORTH IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF
 * OSMC-PL.
 *
 */

/*! \file nonlinearSolverHybrd.c
 *
 *
 */

#ifdef __cplusplus
extern "C" {
#endif

#include <math.h>
#include <stdlib.h>
#include <string.h> /* memcpy */

#include "../simulation_info_json.h"
#include "../jacobian_util.h"
#include "../../util/omc_error.h"
#include "../../util/varinfo.h"
#include "model_help.h"
#include "../../gc/omc_gc.h"
#include "../../meta/meta_modelica.h"

#include "nonlinearSystem.h"
#include "nonlinearSolverHybrd.h"

extern double enorm_(integer *n, double *x);

static void wrapper_fvec_hybrj(const integer *n_p, const double *x, double *f, double *fjac, const integer *ldjac, integer *iflag, void *userData);

/**
 * @brief Allocate memory for non-linear hybrid solver.
 *
 * @param size            Size of non-linear system.
 * @param userData        Information about the non-linear system (number, Jacobian, data, threadData, ...)
 * @return DATA_HYBRD*    Pointer to allocated hybrid data.
 */
DATA_HYBRD* allocateHybrdData(size_t size, NLS_USERDATA* userData)
{
  DATA_HYBRD* hybrdData = (DATA_HYBRD*) malloc(sizeof(DATA_HYBRD));
  assertStreamPrint(NULL, hybrdData != NULL, "allocationHybrdData() failed!");

  hybrdData->initialized = FALSE;

  hybrdData->n = size;
  hybrdData->x = (double*) malloc((size+1)*sizeof(double));
  hybrdData->fvec = (double*) calloc(size, sizeof(double));
  hybrdData->xtol = 1e-12;
  hybrdData->maxfev = size*10000;
  hybrdData->ml = size - 1;
  hybrdData->mu = size - 1;
  hybrdData->diag = (double*) malloc(size*sizeof(double));
  for (size_t i = 0; i < size; i++) hybrdData->diag[i] = 1.0;
  hybrdData->mode = 2;
  hybrdData->factor = 100.0;
  hybrdData->nprint = -1;
  hybrdData->info = 0;
  hybrdData->nfev = 0;
  hybrdData->njev = 0;
  hybrdData->fjac = (double*) calloc((size*(size+1)), sizeof(double));
  hybrdData->ldfjac = size;
  hybrdData->r__ = (double*) malloc(((size*(size+1))/2)*sizeof(double));
  hybrdData->lr = (size*(size + 1)) / 2;
  hybrdData->qtf = (double*) malloc(size*sizeof(double));
  hybrdData->wa1 = (double*) malloc(size*sizeof(double));
  hybrdData->wa2 = (double*) malloc(size*sizeof(double));
  hybrdData->wa3 = (double*) malloc(size*sizeof(double));
  hybrdData->wa4 = (double*) malloc(size*sizeof(double));

  hybrdData->numberOfIterations = 0;
  hybrdData->numberOfFunctionEvaluations = 0;

  hybrdData->userData = userData;

  return hybrdData;
}

/**
 * @brief Free hybrid solver data.
 *
 * @param hybrdData   Pointer to hybrid data.
 */
void freeHybrdData(DATA_HYBRD* hybrdData)
{
  free(hybrdData->x);
  free(hybrdData->fvec);
  free(hybrdData->diag);
  free(hybrdData->fjac);
  free(hybrdData->r__);
  free(hybrdData->qtf);
  free(hybrdData->wa1);
  free(hybrdData->wa2);
  free(hybrdData->wa3);
  free(hybrdData->wa4);

  freeNlsUserData(hybrdData->userData);

  free(hybrdData);
  return;
}

/*! \fn printVector
 *
 *  \param [in]  [vector]
 *  \param [in]  [size]
 *  \param [in]  [logLevel]
 *  \param [in]  [name]
 *
 *  \author wbraun
 */
static void printVector(const double *vector, const integer size, const int logLevel, const char *name)
{
  int i;
  if (!OMC_ACTIVE_STREAM(logLevel)) return;
  infoStreamPrint(logLevel, 1, "%s", name);
  for(i=0; i<size; i++)
    infoStreamPrint(logLevel, 0, "[%2d] %20.12g", i, vector[i]);
  messageClose(logLevel);
}

/**
 * @brief Residual and Jacobian function.
 *
 * @param n               Size of arrays x and f.
 * @param x               Scaled iteration variables.
 * @param f               Scaled residual vector.
 *                        Set to residual vector on exit, if iflag=1.
 *                        Needs to be set as input, if iflag=2.
 * @param fjac            Scaled Jacobian.
 * @param ldjac           Leading dimension of Jacobian.
 * @param iflag           Flag signaling if residual or Jacobian should be evaluated.
 *                        iflag = 1 ==> Residual evaluation
 *                        iflag = 2 ==> Jacobian evaluation
 * @param userDataIn      User data. Get's typecasted to NLS_USERDATA
 */
static void wrapper_fvec_hybrj(const integer *n_p, const double *x, double *f, double *fjac, const integer *ldjac, integer *iflag, void *userDataIn)
{
  int n = *n_p;
  int result = 0;
  NLS_USERDATA* userData = (NLS_USERDATA*) userDataIn;
  DATA* data = userData->data;
  NONLINEAR_SYSTEM_DATA* systemData = userData->nlsData;
  DATA_HYBRD* hybrdData = (DATA_HYBRD*)(systemData->solverData);
  modelica_boolean continuous = data->simulationInfo->solveContinuous;

  switch(*iflag)
  {
  case 1:
    /* debug output */
    if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_RES)) {
      infoStreamPrint(OMC_LOG_NLS_RES, 0, "-- residual function call %d --", (int)hybrdData->nfev);
      printVector(x, n, OMC_LOG_NLS_RES, "scaled iteration variables");
    }

    /* call residual function */
#if defined(OMC_MINIMAL_RUNTIME) || defined(OMC_FMI_RUNTIME)
    MemPoolState mem_pool_state = omc_util_get_pool_state();
#endif
    result = nlsResidual(userData, x, f, (const int*) iflag);
#if defined(OMC_MINIMAL_RUNTIME) || defined(OMC_FMI_RUNTIME)
    omc_util_restore_pool_state(mem_pool_state);
#endif
    if (result) *iflag = -1;

    /* debug output */
    if (!result && OMC_ACTIVE_STREAM(OMC_LOG_NLS_RES)) {
      printVector(f, n, OMC_LOG_NLS_RES, "scaled residuals");
      infoStreamPrint(OMC_LOG_NLS_RES, 0, "-- end of residual function call %d --", (int)hybrdData->nfev);
    }

    hybrdData->numberOfFunctionEvaluations++;
    break;
  case 2:
    /* set residual function continuous for jacobian calculation */
    if(continuous)
      data->simulationInfo->solveContinuous = FALSE;

    if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_RES))
      infoStreamPrint(OMC_LOG_NLS_RES, 0, "-- begin calculating jacobian --");

    /* performance measurement */
    rt_ext_tp_tick(&systemData->jacobianTimeClock);

    result = nlsJacobian(userData, x, fjac, FALSE, NLS_JACOBIAN_AUTO);
    if (result) *iflag = -1;

    if (OMC_ACTIVE_STREAM(OMC_LOG_NLS_RES))
      infoStreamPrint(OMC_LOG_NLS_RES, 0, "-- end calculating jacobian --");
    /* reset residual function again */
    if(continuous)
      data->simulationInfo->solveContinuous = TRUE;

    /* performance measurement and statistics */
    systemData->jacobianTime += rt_ext_tp_tock(&(systemData->jacobianTimeClock));
    if (!result) systemData->numberOfJEval++;

    break;

  default:
    throwStreamPrint(NULL, "Well, this is embarrasing. The non-linear solver should never call this case.%d", (int)*iflag);
    break;
  }
}

/**
 * @brief Solve non-linear system with hybrid method.
 *
 * @param data                Runtime data struct.
 * @param threadData          Thread data for error handling.
 * @param nlsData             Pointer to non-linear system data.
 * @return NLS_SOLVER_STATUS  Return NLS_SOLVED on success and NLS_FAILED otherwise.
 */
NLS_SOLVER_STATUS solveHybrd(DATA *data, threadData_t *threadData, NONLINEAR_SYSTEM_DATA* nlsData)
{
  DATA_HYBRD* hybrdData = (DATA_HYBRD*)nlsData->solverData;
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  int eqSystemNumber = nlsData->equationIndex;

  int i;
  integer iflag = 1;
  double xerror_scaled;
  NLS_SOLVER_STATUS success = NLS_FAILED;
  modelica_boolean catchedError;
  double local_tol = 1e-12;
  double initial_factor = hybrdData->factor;
  int nfunc_evals = 0;
  modelica_boolean continuous = TRUE;
  int nonContinuousCase = 0;

  int giveUp = 0;
  int retries = 0;
  int retries2 = 0;
  int retries3 = 0;
  int assertCalled = 0;
  int assertRetries = 0;
  int assertMessage = 0;

  modelica_boolean* relationsPreBackup;

  relationsPreBackup = (modelica_boolean*) malloc(data->modelData->nRelations*sizeof(modelica_boolean));

  hybrdData->numberOfFunctionEvaluations = 0;

  // Initialize lambda variable
  if (nlsData->homotopySupport) {
    hybrdData->x[hybrdData->n] = 1.0;
  }
  else {
    hybrdData->x[hybrdData->n] = 0.0;
  }

  /* debug output */
  if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V))
  {
    int indexes[2] = {1,eqSystemNumber};
    infoStreamPrintWithEquationIndexes(OMC_LOG_NLS_V, omc_dummyFileInfo, 1, indexes,
      "Start solving Non-Linear System %d (size %d) at time %g with Hybrd Solver",
      eqSystemNumber, (int) nlsData->size, data->localData[0]->timeValue);

    messageClose(OMC_LOG_NLS_V);
  }

  /* set x vector */
  if(data->simulationInfo->discreteCall)
    memcpy(hybrdData->x, scaling->z, hybrdData->n*(sizeof(double)));
  else
    memcpy(hybrdData->x, scaling->zExtrapolation, hybrdData->n*(sizeof(double)));

  nlsPrintInitialGuess(hybrdData->userData, hybrdData->x, hybrdData->n, OMC_LOG_NLS_V);
  nlsPrintScaleFactors(hybrdData->userData, hybrdData->n, OMC_LOG_NLS_V);

  /* start solving loop */
  while(!giveUp && !success)
  {
    /* constrain x */
    for(i=0; i<hybrdData->n; i++)
      hybrdData->x[i] = fmax(scaling->zMin[i], fmin(hybrdData->x[i], scaling->zMax[i]));

    printVector(hybrdData->x, hybrdData->n, OMC_LOG_NLS_V, "scaled iteration variables");

    /* set residual function continuous */
    data->simulationInfo->solveContinuous = continuous;

    giveUp = 1;

    /* try */
    {
      catchedError = TRUE;
#ifndef OMC_EMCC
      MMC_TRY_INTERNAL(simulationJumpBuffer)
#endif
      hybrj_(wrapper_fvec_hybrj, &hybrdData->n, hybrdData->x,
          hybrdData->fvec, hybrdData->fjac, &hybrdData->ldfjac, &hybrdData->xtol,
          &hybrdData->maxfev, hybrdData->diag, &hybrdData->mode, &hybrdData->factor,
          &hybrdData->nprint, &hybrdData->info, &hybrdData->nfev, &hybrdData->njev, hybrdData->r__,
          &hybrdData->lr, hybrdData->qtf, hybrdData->wa1, hybrdData->wa2,
          hybrdData->wa3, hybrdData->wa4, hybrdData->userData);

      catchedError = FALSE;
#ifndef OMC_EMCC
      MMC_CATCH_INTERNAL(simulationJumpBuffer)
#endif
      /* catch */
      if (catchedError)
      {
        if (!assertMessage)
        {
          if (OMC_ACTIVE_WARNING_STREAM(OMC_LOG_STDOUT))
          {
            if(data->simulationInfo->initial)
              warningStreamPrint(OMC_LOG_STDOUT, 1, "While solving non-linear system an assertion failed during initialization.");
            else
              warningStreamPrint(OMC_LOG_STDOUT, 1, "While solving non-linear system an assertion failed at time %g.", data->localData[0]->timeValue);
            warningStreamPrint(OMC_LOG_STDOUT, 0, "The non-linear solver tries to solve the problem that could take some time.");
            warningStreamPrint(OMC_LOG_STDOUT, 0, "It could help to provide better start-values for the iteration variables.");
            if (!OMC_ACTIVE_STREAM(OMC_LOG_NLS_V))
              warningStreamPrint(OMC_LOG_STDOUT, 0, "For more information simulate with -lv LOG_NLS_V");
            messageCloseWarning(OMC_LOG_STDOUT);
          }
          assertMessage = 1;
        }

        hybrdData->info = -1;
        xerror_scaled = 1;
        assertCalled = 1;
      }
    }

    if (!catchedError && assertCalled) {
      infoStreamPrint(OMC_LOG_NLS_V, 0, "After assertions failed, found a solution for which assertions did not fail.");
      memcpy(scaling->zOld, hybrdData->x, hybrdData->n*sizeof(double));
    }
    if (!catchedError) {
      assertRetries = 0;
      assertCalled = 0;
    }

    /* reset residual function continuous */
    data->simulationInfo->solveContinuous = !continuous;

    /* check for proper inputs */
    if(hybrdData->info == 0) {
      printErrorEqSyst(IMPROPER_INPUT, modelInfoGetEquation(&data->modelData->modelDataXml, eqSystemNumber),
                       data->localData[0]->timeValue);
    }

    if(hybrdData->info != -1)
    {
      /* evaluate with discontinuities */
      if(data->simulationInfo->discreteCall){
        catchedError = TRUE;

        data->simulationInfo->solveContinuous = FALSE;

        /* try */
#ifndef OMC_EMCC
        MMC_TRY_INTERNAL(simulationJumpBuffer)
#endif
        wrapper_fvec_hybrj(&hybrdData->n, hybrdData->x, hybrdData->fvec, hybrdData->fjac, &hybrdData->ldfjac,
                           &iflag, hybrdData->userData);
        catchedError = FALSE;
#ifndef OMC_EMCC
        MMC_CATCH_INTERNAL(simulationJumpBuffer)
#endif
        /* catch */
        if (catchedError)
        {
          warningStreamPrint(OMC_LOG_STDOUT, 0, "Non-Linear Solver try to handle a problem with a called assert.");

          hybrdData->info = -1;
          xerror_scaled = 1;
          assertCalled = 1;
        }

        updateRelationsPre(data);
      }
    }

    if(hybrdData->info != -1)
    {
      xerror_scaled = enorm_(&hybrdData->n, hybrdData->fvec);
    }

    /* reset non-contunuousCase */
    if(nonContinuousCase && xerror_scaled > local_tol)
    {
      memcpy(data->simulationInfo->relationsPre, relationsPreBackup, sizeof(modelica_boolean)*data->modelData->nRelations);
      nonContinuousCase = 0;
    }

    if(hybrdData->info < 4 && xerror_scaled > local_tol)
      hybrdData->info = 4;

    if (hybrdData->info >= 2 && hybrdData->info <= 5) {
      nlsPrintStatus(hybrdData->userData, hybrdData->x, hybrdData->fvec, hybrdData->n, nfunc_evals + hybrdData->nfev,
                     xerror_scaled, OMC_LOG_NLS_V);
    }

    /* solution found */
    if(hybrdData->info == 1 || xerror_scaled <= local_tol)
    {
      success = NLS_SOLVED;
      nfunc_evals += hybrdData->nfev;
      if (OMC_ACTIVE_STREAM(OMC_LOG_NLS_V)){
        infoStreamPrint(OMC_LOG_NLS_V, 1, "System solved");
        infoStreamPrint(OMC_LOG_NLS_V, 0, "%d retries\n%d restarts", retries, retries2+retries3);
        messageClose(OMC_LOG_NLS_V);
      }
      /* take the solution */
      memcpy(scaling->z, hybrdData->x, hybrdData->n*(sizeof(double)));

      /* try */
      {
        catchedError = TRUE;
#ifndef OMC_EMCC
        MMC_TRY_INTERNAL(simulationJumpBuffer)
#endif
        wrapper_fvec_hybrj(&hybrdData->n, hybrdData->x, hybrdData->fvec, hybrdData->fjac, &hybrdData->ldfjac,
                           &iflag, hybrdData->userData);
        catchedError = FALSE;
#ifndef OMC_EMCC
        MMC_CATCH_INTERNAL(simulationJumpBuffer)
#endif
        /* catch */
        if (catchedError) {
          warningStreamPrint(OMC_LOG_STDOUT, 0, "Non-Linear Solver try to handle a problem with a called assert.");

          hybrdData->info = 4;
          xerror_scaled = 1;
          assertCalled = 1;
          success = NLS_FAILED;
          giveUp = 0;
        }
      }
    }
    else if((hybrdData->info == 4 || hybrdData->info == 5) && assertRetries < 1+hybrdData->n && assertCalled)
    {
      /* case only used, when the Modelica code called an assert
       * then, we try to modify start values to avoid the assert call.*/
      int i;

      memcpy(hybrdData->x, scaling->zOld, hybrdData->n*(sizeof(double)));

      /* set all zero values to nominal values */
      if(assertRetries < 1)
      {
        for(i=0; i<hybrdData->n; i++)
        {
          if(scaling->z[i] == 0)
          {
            scaling->z[i] = scaling->zNominal[i];
            hybrdData->x[i] = scaling->zNominal[i];
          }
        }
      }
      /* change initial guess values one by one */
      else if(assertRetries < hybrdData->n+1)
      {
        i = assertRetries-1;
        hybrdData->x[i] += 0.01*scaling->zNominal[i];
      }

      giveUp = 0;
      nfunc_evals += hybrdData->nfev;
      assertRetries++;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V))
      {
        infoStreamPrint(OMC_LOG_NLS_V, 0, " - try to handle a problem with a called assert vary initial value a bit. (Retry: %d)",assertRetries);
      }
    }
    else if((hybrdData->info == 4 || hybrdData->info == 5) && retries < 3)
    {
      /* first try to decrease factor */

      /* set x vector */
      if(data->simulationInfo->discreteCall)
        memcpy(hybrdData->x, scaling->z, hybrdData->n*(sizeof(double)));
      else
        memcpy(hybrdData->x, scaling->zExtrapolation, hybrdData->n*(sizeof(double)));

      hybrdData->factor = hybrdData->factor / 10.0;

      retries++;
      giveUp = 0;
      nfunc_evals += hybrdData->nfev;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V))
      {
        infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t decreasing initial step bound to %f.", hybrdData->factor);
      }
    }
    else if((hybrdData->info == 4 || hybrdData->info == 5) && retries < 4)
    {
      /* try to vary the initial values */

      for(i = 0; i < hybrdData->n; i++)
        hybrdData->x[i] += scaling->zNominal[i] * 0.1;

      hybrdData->factor = initial_factor;
      retries++;
      giveUp = 0;
      nfunc_evals += hybrdData->nfev;

      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V))
      {
        infoStreamPrint(OMC_LOG_NLS_V, 0, "iteration making no progress:\t vary solution point by 1%%.");
      }
    }
    else if((hybrdData->info == 4 || hybrdData->info == 5) && retries < 5  && data->simulationInfo->discreteCall)
    {
      /* try to solve non-continuous
       * work-a-round: since other wise some model does
       * stuck in event iteration. e.g.: Modelica.Mechanics.Rotational.Examples.HeatLosses
       */

      memcpy(hybrdData->x, scaling->zOld, hybrdData->n*(sizeof(double)));
      retries++;

      /* try to solve a discontinuous system */
      continuous = FALSE;

      nonContinuousCase = 1;
      memcpy(relationsPreBackup, data->simulationInfo->relationsPre, sizeof(modelica_boolean)*data->modelData->nRelations);

      giveUp = 0;
      nfunc_evals += hybrdData->nfev;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V)) {
        infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t try to solve a discontinuous system.");
      }
    /* Then try with old values (instead of extrapolating )*/
    } else if((hybrdData->info == 4 || hybrdData->info == 5) && retries2 < 1) {
      /* set x vector */
      memcpy(hybrdData->x, scaling->zOld, hybrdData->n*(sizeof(double)));

      continuous = TRUE;
      hybrdData->factor = initial_factor;

      retries = 0;
      retries2++;
      giveUp = 0;
      nfunc_evals += hybrdData->nfev;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V)) {
        infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t use old values instead extrapolated.");
      }
    /* try to vary the initial values */
    } else if((hybrdData->info == 4 || hybrdData->info == 5) && retries2 < 2) {
      /* set x vector */
      if(data->simulationInfo->discreteCall)
        memcpy(hybrdData->x, scaling->z, hybrdData->n*(sizeof(double)));
      else
        memcpy(hybrdData->x, scaling->zExtrapolation, hybrdData->n*(sizeof(double)));
      for(i = 0; i < hybrdData->n; i++) {
        hybrdData->x[i] *= 1.01;
      };

      retries = 0;
      retries2++;
      giveUp = 0;
      nfunc_evals += hybrdData->nfev;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V)) {
        infoStreamPrint(OMC_LOG_NLS_V, 0,
            " - iteration making no progress:\t vary initial point by adding 1%%.");
      }
    /* try to vary the initial values */
    } else if((hybrdData->info == 4 || hybrdData->info == 5) && retries2 < 3) {
      /* set x vector */
      if(data->simulationInfo->discreteCall)
        memcpy(hybrdData->x, scaling->z, hybrdData->n*(sizeof(double)));
      else
        memcpy(hybrdData->x, scaling->zExtrapolation, hybrdData->n*(sizeof(double)));
      for(i = 0; i < hybrdData->n; i++) {
        hybrdData->x[i] *= 0.99;
      };

      retries = 0;
      retries2++;
      giveUp = 0;
      nfunc_evals += hybrdData->nfev;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V)) {
        infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t vary initial point by -1%%.");
      }
    /* try to vary the initial values */
    } else if((hybrdData->info == 4 || hybrdData->info == 5) && retries2 < 4) {
      /* set x vector */
      memcpy(hybrdData->x, scaling->zNominal, hybrdData->n*(sizeof(double)));
      retries = 0;
      retries2++;
      giveUp = 0;
      nfunc_evals += hybrdData->nfev;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V)) {
        infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t try nominal values as initial point.");
      }
    /* try to reduce the tolerance a bit */
    } else if((hybrdData->info == 4 || hybrdData->info == 5) && retries3 < 6) {
      /* set x vector */
      if(data->simulationInfo->discreteCall)
        memcpy(hybrdData->x, scaling->z, hybrdData->n*(sizeof(double)));
      else
        memcpy(hybrdData->x, scaling->zExtrapolation, hybrdData->n*(sizeof(double)));

      /* reduce tolarance */
      local_tol = local_tol*10;

      hybrdData->factor = initial_factor;
      hybrdData->mode = 2;

      retries = 0;
      retries2 = 0;
      retries3++;

      giveUp = 0;
      nfunc_evals += hybrdData->nfev;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V)) {
        infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t reduce the tolerance slightly to %e.", local_tol);
      }
    } else if(hybrdData->info >= 2 && hybrdData->info <= 5) {

      /* while the initialization it's ok to every time a solution */
      if(!data->simulationInfo->initial){
        printErrorEqSyst(ERROR_AT_TIME, modelInfoGetEquation(&data->modelData->modelDataXml, eqSystemNumber), data->localData[0]->timeValue);
      }
      if (OMC_ACTIVE_STREAM(OMC_LOG_NLS_V)) {
        infoStreamPrint(OMC_LOG_NLS_V, 0, "### No Solution! ###\n after %d restarts", retries*retries2*retries3);
      }
      /* take the best approximation */
      memcpy(scaling->z, hybrdData->x, hybrdData->n*(sizeof(double)));

      giveUp = 1;
      success = NLS_FAILED;
      break;
    }
  }

  /* reset some solving data */
  hybrdData->factor = initial_factor;
  hybrdData->mode = 2;

  /* write statistics */
  nlsData->numberOfFEval += hybrdData->numberOfFunctionEvaluations;
  /* iteration in hybrid are equal to the nfev numbers */
  nlsData->numberOfIterations += nfunc_evals;

  free(relationsPreBackup);

  return success;
}

#ifdef __cplusplus
}
#endif
