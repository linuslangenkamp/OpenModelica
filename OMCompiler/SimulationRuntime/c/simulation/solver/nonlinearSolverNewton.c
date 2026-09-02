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

/*! \file nonlinearSolverNewton.c
 */

#ifdef __cplusplus
extern "C" {
#endif

#include <math.h>
#include <stdlib.h>
#include <string.h> /* memcpy */

#include "../simulation_info_json.h"
#include "util/omc_error.h"

#include "util/varinfo.h"
#include "model_help.h"

#include "nonlinearSystem.h"
#include "nonlinearSolverNewton.h"
#include "newtonIteration.h"

#include "external_input.h"

/* Private function prototypes */

int wrapper_fvec_newton(int n, double* x, double* fvec, NLS_USERDATA* userData, int fj);

/* External function prototypes */

extern double enorm_(int *n, double *x);
extern int dgesv_(int *n, int *nrhs, doublereal *a, int *lda, int *ipiv, doublereal *b, int *ldb, int *info);


/**
 * @brief Calculate residual f(x) or Jacobian J(x).
 *
 * @param n         Size of vector x.
 * @param x         Scaled iteration variables.
 *                  Also used as work array, but will be reverted before function exits.
 * @param fvec      Scaled residual values.
 *                  Will be computed if fj = 1.
 *                  Will be used to compute Jacobian if fj = 0.
 * @param userData  Pointer to Newton user data.
 * @param fj        Decides whether the function values or the jacobian matrix shall be calculated.
 *                  fj = 1: calculate function values
 *                  fj = 0: calculate jacobian matrix
 * @return int      Zero on success, non-zero on a recoverable callback failure.
 */
int wrapper_fvec_newton(int n, double* x, double* fvec, NLS_USERDATA* userData, int fj)
{
  NONLINEAR_SYSTEM_DATA* nlsData = userData->nlsData;
  DATA_NEWTON* solverData = (DATA_NEWTON*)(nlsData->solverData);
  int flag = 1;
  int result;

  if (fj) {
    result = nlsResidual(userData, x, fvec, &flag);
  } else {
    /* performance measurement */
    rt_ext_tp_tick(&nlsData->jacobianTimeClock);

    result = nlsJacobian(userData, x, solverData->fjac, FALSE, NLS_JACOBIAN_AUTO);
    /* performance measurement and statistics */
    nlsData->jacobianTime += rt_ext_tp_tock(&(nlsData->jacobianTimeClock));
    if (!result) nlsData->numberOfJEval++;
  }
  return result;
}

/**
 * @brief Solve non-linear system with Newton method.
 *
 * @param data                Runtime data struct.
 * @param threadData          Thread data for error handling.
 * @param nlsData             Pointer to non-linear system data.
 * @return NLS_SOLVER_STATUS  Return NLS_SOLVED on success and NLS_FAILED otherwise.
 */
NLS_SOLVER_STATUS solveNewton(DATA *data, threadData_t *threadData, NONLINEAR_SYSTEM_DATA* nlsData)
{
  DATA_NEWTON* solverData = (DATA_NEWTON*)(nlsData->solverData);
  NLS_SCALING_DATA *scaling = nlsData->scaling;

  int eqSystemNumber = 0;
  int i;
  double xerror_scaled = -1;
  NLS_SOLVER_STATUS success = NLS_FAILED;
  int nfunc_evals = 0;
  double local_tol = solverData->ftol;
  const double relaxed_tol = nlsRelaxedTolerance(data, local_tol);

  int giveUp = 0;
  int retries = 0;
  int retries2 = 0;
  int nonContinuousCase = 0;
  modelica_boolean *relationsPreBackup = NULL;
  int casualTearingSet = nlsData->strictTearingFunctionCall != NULL;

  /*
   * We are given the number of the non-linear system.
   * We want to look it up among all equations.
   */
  eqSystemNumber = nlsData->equationIndex;

  relationsPreBackup = (modelica_boolean*) malloc(data->modelData->nRelations*sizeof(modelica_boolean));

  solverData->nfev = 0;

  /* try to calculate jacobian only once at the beginning of the iteration */
  solverData->calculate_jacobian = 0;

  // Initialize lambda variable
  if (nlsData->homotopySupport) {
    solverData->x[solverData->n] = 1.0;
    solverData->x_new[solverData->n] = 1.0;
  }
  else {
    solverData->x[solverData->n] = 0.0;
    solverData->x_new[solverData->n] = 0.0;
  }

  /* debug output */
  if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V))
  {
    int indexes[2] = {1, eqSystemNumber};
    infoStreamPrintWithEquationIndexes(OMC_LOG_NLS_V, omc_dummyFileInfo, 1, indexes,
      "Start solving Non-Linear System %d (size %d) at time %g with Newton Solver",
      eqSystemNumber, (int) nlsData->size, data->localData[0]->timeValue);

    messageClose(OMC_LOG_NLS_V);
  }

  /* set x vector */
  if(data->simulationInfo->discreteCall) {
    memcpy(solverData->x, scaling->z, solverData->n*(sizeof(double)));
  } else {
    memcpy(solverData->x, scaling->zExtrapolation, solverData->n*(sizeof(double)));
  }
  nlsPrintInitialGuess(solverData->userData, solverData->x, solverData->n, OMC_LOG_NLS_V);
  nlsPrintScaleFactors(solverData->userData, solverData->n, OMC_LOG_NLS_V);
  solverData->time = data->localData[0]->timeValue;
  solverData->initial = data->simulationInfo->initial;

  /* start solving loop */
  while(!giveUp && success != NLS_SOLVED)
  {

    giveUp = 1;
    solverData->newtonStrategy = data->simulationInfo->newtonStrategy;
    _omc_newton((genericResidualFunc*)wrapper_fvec_newton, solverData, solverData->userData);

    /* check for proper inputs */
    if(solverData->info == 0)
      printErrorEqSyst(IMPROPER_INPUT, modelInfoGetEquation(&data->modelData->modelDataXml,eqSystemNumber), data->localData[0]->timeValue);

    /* reset non-contunuousCase */
    if(nonContinuousCase && xerror_scaled > local_tol)
    {
      memcpy(data->simulationInfo->relationsPre, relationsPreBackup, sizeof(modelica_boolean)*data->modelData->nRelations);
      nonContinuousCase = 0;
    }

    /* check for error  */
    xerror_scaled = enorm_(&solverData->n, solverData->fvec);

    /* solution found */
    if(xerror_scaled <= local_tol && solverData->info > 0)
    {
      success = NLS_SOLVED;
      nfunc_evals += solverData->nfev;
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V))
      {
        infoStreamPrint(OMC_LOG_NLS_V, 1, "System solved");
        infoStreamPrint(OMC_LOG_NLS_V, 0, "%d restarts", retries);
        nlsPrintStatus(solverData->userData, solverData->x, solverData->fvec, solverData->n, nfunc_evals,
                       xerror_scaled, OMC_LOG_NLS_V);
        messageClose(OMC_LOG_NLS_V);
      }

      /* take the solution */
      memcpy(scaling->z, solverData->x, solverData->n*(sizeof(double)));

      /* Then try with old values (instead of extrapolating )*/
    }
    // If this is the casual tearing set (only exists for dynamic tearing), break after first try
    else if(retries < 1 && casualTearingSet)
    {
      giveUp = 1;
      infoStreamPrint(OMC_LOG_NLS_V, 0, "### No Solution for the casual tearing set at the first try! ###");
    }
    else if(retries < 1)
    {
      memcpy(solverData->x, scaling->zOld, solverData->n*(sizeof(double)));

      retries++;
      giveUp = 0;
      nfunc_evals += solverData->nfev;
      infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t try old values.");
      /* try to vary the initial values */

      /* evaluate jacobian in every step now */
      solverData->calculate_jacobian = 1;
    }
    else if(retries < 2)
    {
      for(i = 0; i < solverData->n; i++)
        solverData->x[i] += scaling->zNominal[i] * 0.01;
      retries++;
      giveUp = 0;
      nfunc_evals += solverData->nfev;
      infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t vary solution point by 1%%.");
      /* try to vary the initial values */
    }
    else if(retries < 3)
    {
      for(i = 0; i < solverData->n; i++)
        solverData->x[i] = scaling->zNominal[i];
      retries++;
      giveUp = 0;
      nfunc_evals += solverData->nfev;
      infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t try nominal values as initial solution.");
    }
    else if(retries < 4  && data->simulationInfo->discreteCall)
    {
      /* try to solve non-continuous
       * work-a-round: since other wise some model does
       * stuck in event iteration. e.g.: Modelica.Mechanics.Rotational.Examples.HeatLosses
       */

      memcpy(solverData->x, scaling->zOld, solverData->n*(sizeof(double)));
      retries++;

      /* try to solve a discontinuous system */
      nonContinuousCase = 1;
      memcpy(relationsPreBackup, data->simulationInfo->relationsPre, sizeof(modelica_boolean)*data->modelData->nRelations);

      giveUp = 0;
      nfunc_evals += solverData->nfev;
      infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t try to solve a discontinuous system.");
    }
    else if(local_tol < relaxed_tol)
    {
      memcpy(solverData->x, scaling->zOld, solverData->n*(sizeof(double)));
      /* reduce tolarance */
      local_tol = fmin(local_tol*10, relaxed_tol);

      retries = 0;
      retries2++;
      giveUp = 0;
      nfunc_evals += solverData->nfev;
      infoStreamPrint(OMC_LOG_NLS_V, 0, " - iteration making no progress:\t reduce the tolerance slightly to %e.", local_tol);
    }
    else
    {
      printErrorEqSyst(ERROR_AT_TIME, modelInfoGetEquation(&data->modelData->modelDataXml,eqSystemNumber), data->localData[0]->timeValue);
      if(OMC_ACTIVE_STREAM(OMC_LOG_NLS_V))
      {
        infoStreamPrint(OMC_LOG_NLS_V, 0, "### No Solution! ###\n after %d restarts", retries);
        nlsPrintStatus(solverData->userData, solverData->x, solverData->fvec, solverData->n, nfunc_evals,
                       xerror_scaled, OMC_LOG_NLS_V);
      }
    }
  }

  free(relationsPreBackup);

  /* write statistics */
  nlsData->numberOfFEval = solverData->numberOfFunctionEvaluations;
  nlsData->numberOfIterations = solverData->numberOfIterations;

  return success;
}
