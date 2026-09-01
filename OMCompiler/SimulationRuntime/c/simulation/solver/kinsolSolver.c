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

/*! \file kinsolSolver.c
 */

#include "kinsolSolver.h"

#include "nonlinearSystem.h"
#include "omc_config.h"
#include "omc_math.h"
#include "../options.h"
#include "../simulation_info_json.h"
#include "sundials_util.h"
#include "util/omc_error.h"

#ifdef WITH_SUNDIALS

#include "events.h"
#include "model_help.h"
#include "openmodelica.h"
#include "openmodelica_func.h"
#include "util/read_matlab4.h"
#include "util/varinfo.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Function prototypes */
static int nlsKinsolResiduals(N_Vector x, N_Vector f, void* userData);
static int nlsKinsolJacobian(N_Vector vecX, N_Vector vecFX, SUNMatrix Jac, void* userData, N_Vector tmp1, N_Vector tmp2);
static int nlsKinsolDenseDerivativeTest(DATA *data, NONLINEAR_SYSTEM_DATA *nlsData, NLS_KINSOL_DATA *kinsolData,
                                        const modelica_real *x, SUNMatrix Jsym, SolverCaller caller);
static void finishSparseColPtr(SUNMatrix A, int nnz);
static void nlsKinsolJacSumSparse(SUNMatrix A);
static void nlsKinsolJacSumDense(SUNMatrix A);

/**
 * @brief Set KINSOL configuration.
 *
 * @param kinsolData    Kinsol data with configuration settings.
 */
static void nlsKinsolConfigSetup(NLS_KINSOL_DATA *kinsolData) {
  /* Variables */
  int flag;

  /* configuration */
  flag = KINSetFuncNormTol(kinsolData->kinsolMemory,
                           kinsolData->fnormtol); /* Set function-norm stopping tolerance */
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetFuncNormTol");
  flag = KINSetScaledStepTol(kinsolData->kinsolMemory,
                             kinsolData->scsteptol); /* Set scaled-step stopping tolerance */
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetScaledStepTol");

  flag = KINSetNumMaxIters(kinsolData->kinsolMemory,
                           100 * kinsolData->size); /* Set max. number of nonlinear iterations */
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetNumMaxIters");

  flag = KINSetMaxSetupCalls(kinsolData->kinsolMemory, 10);
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetMaxSetupCalls");

  kinsolData->kinsolStrategy = KIN_LINESEARCH; /* Newton with globalization strategy to solve nonlinear systems */

  flag = KINSetNoInitSetup(kinsolData->kinsolMemory, SUNFALSE); /* TODO: This is the default value. Is there a point in calling this function? */
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetNoInitSetup");

  kinsolData->retries = 0;
  kinsolData->countResCalls = 0;
  kinsolData->maxstepfactor = maxStepFactor;
  kinsolData->jacobianMethod = NLS_JACOBIAN_AUTO;
}

/**
 * @brief Initialize KINSOL data.
 *
 * Allocate memory for KINSOL data and Jacobian.
 *
 * @param kinsolData          KINSOL data.
 */
void initKinsolMemory(NLS_KINSOL_DATA *kinsolData) {
  int flag;
  int size = kinsolData->size;
  NONLINEAR_SYSTEM_DATA *nlsData = kinsolData->userData->nlsData;
  const SPARSE_PATTERN *sparsePattern = nlsJacobianPattern(kinsolData->userData);

  /* Free KINSOL memory block */
  if (kinsolData->kinsolMemory != NULL || kinsolData->J != NULL) {
    errorStreamPrint(OMC_LOG_STDOUT, 0,
                     "KINSOL: Already allocated kinsol memory. Loosing memory!");
  }

  /* Create KINSOL memory block. The SUNDIALS context was created by
   * nlsKinsolAllocate, which has to happen before any SUNDIALS object. */
  kinsolData->kinsolMemory = KINCreate(kinsolData->sunctx);
  if (kinsolData->kinsolMemory == NULL) {
    errorStreamPrint(OMC_LOG_STDOUT, 0,
                     "KINSOL: In function KINCreate: An error occurred.");
  }

  flag = KINSetUserData(kinsolData->kinsolMemory, (void*)kinsolData->userData);
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetUserData");

  /* Initialize KINSOL object */
  flag = KINInit(kinsolData->kinsolMemory, nlsKinsolResiduals,
                 kinsolData->initialGuess);
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINInit");

  /* Create matrix object */
  if (kinsolData->linearSolverMethod == NLS_LS_DEFAULT ||
      kinsolData->linearSolverMethod == NLS_LS_LAPACK) {
    kinsolData->J = SUNDenseMatrix(size, size, kinsolData->sunctx);
  } else if (kinsolData->linearSolverMethod == NLS_LS_KLU) {
    assertStreamPrint(kinsolData->userData->threadData, sparsePattern != NULL, "KINSOL with KLU requires a nonlinear Jacobian sparsity pattern");
    kinsolData->nnz = sparsePattern->nnz;
    kinsolData->J = SUNSparseMatrix(size, size, kinsolData->nnz, SUN_CSC_MAT, kinsolData->sunctx);
  }

  /* Create linear solver object */
  if (kinsolData->linearSolverMethod == NLS_LS_DEFAULT ||
      kinsolData->linearSolverMethod == NLS_LS_TOTALPIVOT) {
    kinsolData->linSol = SUNLinSol_Dense(kinsolData->y, kinsolData->J, kinsolData->sunctx);
    if (kinsolData->linSol == NULL) {
      throwStreamPrint(NULL, "KINSOL: In function SUNLinSol_Dense: Input incompatible.");
    }
  } else if (kinsolData->linearSolverMethod == NLS_LS_LAPACK) {
    kinsolData->linSol = SUNLinSol_LapackDense(kinsolData->y, kinsolData->J, kinsolData->sunctx);
    if (kinsolData->linSol == NULL) {
      throwStreamPrint(NULL, "KINSOL: In function SUNLinSol_LapackDense: Input incompatible.");
    }
  } else if (kinsolData->linearSolverMethod == NLS_LS_KLU) {
    kinsolData->linSol = SUNLinSol_KLU(kinsolData->y, kinsolData->J, kinsolData->sunctx);
    if (kinsolData->linSol == NULL) {
      throwStreamPrint(NULL, "KINSOL: In function SUNLinSol_KLU: Input incompatible.");
    }
  } else {
    throwStreamPrint(NULL, "KINSOL: Unknown linear solver method.");
  }
  /* Log used solver */
  infoStreamPrint(OMC_LOG_NLS, 0, "KINSOL: Using linear solver method %s", NLS_LS_METHOD_NAME[kinsolData->linearSolverMethod]);

  /* Set linear solver */
  flag = KINSetLinearSolver(kinsolData->kinsolMemory, kinsolData->linSol,
                            kinsolData->J);
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KINLS_FLAG, "KINSetLinearSolver");

  flag = KINSetJacFn(kinsolData->kinsolMemory, nlsKinsolJacobian);
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KINLS_FLAG, "KINSetJacFn");

  /* Configuration */
  nlsKinsolConfigSetup(kinsolData);
}

/**
 * @brief Allocate memory for kinsol solver data and initialize KINSOL solver.
 *
 * @param size                  Size of non-linear problem.
 * @param userData              Pointer to set NLS user data.
 * @param attemptRetry          True if KINSOL should retry with different settings after solution failed.
 * @return NLS_KINSOL_DATA*     Pointer to allocated KINSOL data.
 */
NLS_KINSOL_DATA* nlsKinsolAllocate(int size, NLS_USERDATA* userData, modelica_boolean attemptRetry) {
  /* Allocate system data */
  NLS_KINSOL_DATA *kinsolData = (NLS_KINSOL_DATA *)calloc(1, sizeof(NLS_KINSOL_DATA));

  kinsolData->size = size;
  kinsolData->linearSolverMethod = userData->nlsData->nlsLinearSolver;
  kinsolData->jacobianMethod = NLS_JACOBIAN_AUTO;
  kinsolData->solved = NLS_FAILED;
  kinsolData->userData = userData;

  if (SUNContext_Create(SUN_COMM_NULL, &kinsolData->sunctx) != SUN_SUCCESS) {
    throwStreamPrint(NULL, "KINSOL: In function SUNContext_Create: An error occurred.");
  }
  sundialsSilenceLogger(kinsolData->sunctx);

  /* Set error handler */
  if (SUNContext_PushErrHandler(kinsolData->sunctx, kinsolErrorHandlerFunction, kinsolData) != SUN_SUCCESS) {
    throwStreamPrint(NULL, "KINSOL: In function SUNContext_PushErrHandler: An error occurred.");
  }

  kinsolData->fnormtol = newtonFTol;  /* function tolerance */
  kinsolData->scsteptol = newtonXTol; /* step tolerance */

  kinsolData->maxstepfactor = maxStepFactor; /* step tolerance */
  kinsolData->attemptRetry = attemptRetry;

  kinsolData->initialGuess = N_VNew_Serial(size, kinsolData->sunctx);
  kinsolData->scale = N_VNew_Serial(size, kinsolData->sunctx);
  N_VConst(1.0, kinsolData->scale);

  kinsolData->y = N_VNew_Serial(size, kinsolData->sunctx);
  kinsolData->J = NULL;

  kinsolData->kinsolMemory = NULL;

  initKinsolMemory(kinsolData);

  return kinsolData;
}

/**
 * @brief Deallocates memory for KINSOL solver.
 *
 * Free memory that was allocated with `nlsKinsolAllocate`.
 *
 * @param kinsolData    Pointer to KINSOL data.
 */
void nlsKinsolFree(NLS_KINSOL_DATA* kinsolData) {
  KINFree((void *)&kinsolData->kinsolMemory);

  N_VDestroy_Serial(kinsolData->initialGuess);
  N_VDestroy_Serial(kinsolData->scale);

  /* Free linear solver data */
  SUNLinSolFree(kinsolData->linSol);
  SUNMatDestroy(kinsolData->J);
  N_VDestroy_Serial(kinsolData->y);

  /* The context has to outlive every SUNDIALS object created with it */
  SUNContext_Free(&kinsolData->sunctx);

  freeNlsUserData(kinsolData->userData);
  free(kinsolData);

  return;
}

/**
 * @brief Residual function for non-linear problem.
 *
 * @param x         The current value of the variable vector.
 * @param f         Output vector.
 * @param userData  Pointer to Kinsol user data.
 * @return int      Return 0 on success, return 1 on recoverable error.
 */
static int nlsKinsolResiduals(N_Vector x, N_Vector f, void* userData) {
  double *xdata = NV_DATA_S(x);
  double *fdata = NV_DATA_S(f);

  NLS_USERDATA* kinsolUserData = (NLS_USERDATA*)userData;
  NONLINEAR_SYSTEM_DATA* nlsData = kinsolUserData->nlsData;
  NLS_KINSOL_DATA* kinsolData = (NLS_KINSOL_DATA*)nlsData->solverData;
  threadData_t *threadData = kinsolUserData->threadData;
  volatile int iflag = 1 /* recoverable error */;
  int result;

  /* Update statistics */
  kinsolData->countResCalls++;

#ifndef OMC_EMCC
  MMC_TRY_INTERNAL(simulationJumpBuffer)
#endif

  result = nlsResidual(kinsolUserData, xdata, fdata, (const int*) &iflag);
  iflag = result ? 1 : 0;

#ifndef OMC_EMCC
  MMC_CATCH_INTERNAL(simulationJumpBuffer)
#endif

  return iflag;
}

/** Common scaled Jacobian adapter for KINSOL dense and CSC matrices. */
static int nlsKinsolJacobian(N_Vector vecX, N_Vector vecFX, SUNMatrix Jac, void* userData, N_Vector tmp1, N_Vector tmp2)
{
  NLS_USERDATA *kinsolUserData = (NLS_USERDATA*) userData;
  DATA *data = kinsolUserData->data;
  NONLINEAR_SYSTEM_DATA *nlsData = kinsolUserData->nlsData;
  NLS_KINSOL_DATA *kinsolData = (NLS_KINSOL_DATA*) nlsData->solverData;
  const modelica_boolean sparse = SUNMatGetID(Jac) == SUNMATRIX_SPARSE;
  const SPARSE_PATTERN *pattern = nlsJacobianPattern(kinsolUserData);
  modelica_integer column;
  unsigned int nz;
  int result;

  if (!sparse && SUNMatGetID(Jac) != SUNMATRIX_DENSE) return -1;

  rt_ext_tp_tick(&nlsData->jacobianTimeClock);
  result = nlsJacobian(kinsolUserData, NV_DATA_S(vecX), sparse ? SM_DATA_S(Jac) : SM_DATA_D(Jac), sparse,
                       kinsolData->jacobianMethod);
  nlsData->jacobianTime += rt_ext_tp_tock(&nlsData->jacobianTimeClock);
  if (result) return 1;

  if (sparse) {
    assertStreamPrint(kinsolUserData->threadData, pattern != NULL, "KINSOL sparse Jacobian has no sparsity pattern");
    assertStreamPrint(kinsolUserData->threadData, pattern->nnz <= (unsigned int) SM_NNZ_S(Jac), "KINSOL sparse Jacobian capacity is too small");

    for (column = 0; column <= kinsolData->size; column++) {
      SM_INDEXPTRS_S(Jac)[column] = pattern->leadindex[column];
    }

    for (nz = 0; nz < pattern->nnz; nz++) {
      SM_INDEXVALS_S(Jac)[nz] = pattern->index[nz];
    }

    finishSparseColPtr(Jac, pattern->nnz);
  }

  nlsData->numberOfJEval++;

  if (OMC_ACTIVE_STREAM(OMC_LOG_NLS_JAC)) {
    infoStreamPrint(OMC_LOG_NLS_JAC, 1, "KINSOL: scaled %s Jacobian.", sparse ? "sparse" : "dense");
    if (sparse) {
      SUNSparseMatrix_Print(Jac, stdout);
      nlsKinsolJacSumSparse(Jac);
    } else {
      SUNDenseMatrix_Print(Jac, stdout);
      nlsKinsolJacSumDense(Jac);
    }
    messageClose(OMC_LOG_NLS_JAC);
  }

  if (sparse && omc_useStream[OMC_LOG_NLS_DERIVATIVE_TEST]) {
    nlsKinsolDenseDerivativeTest(data, nlsData, kinsolData, NV_DATA_S(vecX), Jac, KINSOL_JAC_EVAL);
  }
  if (sparse && omc_useStream[OMC_LOG_NLS_JAC_SUMS]) {
    nlsJacobianRowColSums(data, nlsData, Jac, KINSOL_JAC_EVAL, TRUE);
  }
  if (omc_useStream[OMC_LOG_NLS_SVD] || omc_useStream[OMC_LOG_NLS_SVD_V]) {
    svd_compute(data, nlsData, sparse ? SM_DATA_S(Jac) : SM_DATA_D(Jac), sparse ? pattern : NULL, TRUE, KINSOL_JAC_EVAL);
  }

  return 0;
}

/**
 * @brief Finish sparse matrix by fixing colprts.
 *
 * Last value of indexptrs should always be nnz.
 * Search for empty columns which would mean the matrix is singular.
 *
 * @param A   CSC matrix
 */
static void finishSparseColPtr(SUNMatrix A, int nnz) {
  int i;

  /* TODO: Remove this check for performance reasons? */
  if (SM_SPARSETYPE_S(A) != SUN_CSC_MAT) {
    errorStreamPrint(OMC_LOG_STDOUT, 0,
                     "KINSOL: In function finishSparseColPtr: Wrong sparse format of SUNMatrix A.");
  }

  /* Set last value of indexptrs to nnz */
  SM_INDEXPTRS_S(A)[SM_COLUMNS_S(A)] = nnz;

  /* Check for empty columns */
  for (i = 1; i < SM_COLUMNS_S(A) + 1; i++) {
    if (SM_INDEXPTRS_S(A)[i] == SM_INDEXPTRS_S(A)[i - 1]) {
      warningStreamPrint(OMC_LOG_STDOUT, 0,
                         "KINSOL: Jacobian column %d singular. See OMC_LOG_NLS for "
                         "more information.",
                         i);
      SM_INDEXPTRS_S(A)[i] = SM_INDEXPTRS_S(A)[i - 1];
    }
  }
}

/**
 * @brief Perform derivative test comparing symbolic and numerical Jacobians for KINSOL
 *
 * Compares the symbolic Jacobian (sparse CSC format) with a numerically approximated
 * dense Jacobian, checking for numerical and structural anomalies. The numerical
 * Jacobian is computed through the common nonlinear Jacobian API.
 *
 * @param data              Runtime data structure
 * @param nlsData           Nonlinear system data
 * @param kinsolData        KINSOL solver data structure
 * @param x                 Current solver-coordinate iterate
 * @param Jsym              Symbolic Jacobian in sparse CSC format
 * @param caller            Location from which the test was requested
 *
 * @return int              1 derivative test failed and no error
 *                          0 derivative test successful and no error
 *                         -1 internal error
 */
static int nlsKinsolDenseDerivativeTest(DATA *data, NONLINEAR_SYSTEM_DATA *nlsData, NLS_KINSOL_DATA *kinsolData,
                                        const modelica_real *x, SUNMatrix Jsym, SolverCaller caller)
{
  int row, col, nz, numericalErrorCount, structuralErrorCount;
  const int size = nlsData->size;
  int ret = 0;

  modelica_real symValue, numValue, absError, relError;
  modelica_real maxError = 0.0;

  modelica_boolean errorFound;

  sunindextype nnz = SUNSparseMatrix_NNZ(Jsym);
  sunindextype columns = SUNSparseMatrix_Columns(Jsym);
  sunindextype rows = SUNSparseMatrix_Rows(Jsym);

  sunindextype *colPointers = SM_INDEXPTRS_S(Jsym);
  sunindextype *rowIndices = SM_INDEXVALS_S(Jsym);
  sunrealtype *symValues = SM_DATA_S(Jsym);

  SUNMatrix Jnum = SUNDenseMatrix(size, size, kinsolData->sunctx);

  // set tolerances
  modelica_real Atol = omc_flag[FLAG_NLS_JAC_TEST_ATOL] ? atof(omc_flagValue[FLAG_NLS_JAC_TEST_ATOL]) : 100 * DBL_EPSILON;
  modelica_real Rtol = omc_flag[FLAG_NLS_JAC_TEST_RTOL] ? atof(omc_flagValue[FLAG_NLS_JAC_TEST_RTOL]) : 1e-4;

  // Compute the finite-difference Jacobian at the current iterate.
  SUNMatZero(Jnum);
  const int jacobianResult = nlsJacobian(kinsolData->userData, x, SM_DATA_D(Jnum), FALSE, NLS_JACOBIAN_NUMERICAL);
  if (jacobianResult) {
    SUNMatDestroy(Jnum);
    return -1;
  }

  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 1, "%s: Derivative test (atol=%.5e, rtol=%.5e, scaled, Caller: %s):",
                  SolverCaller_callerString(caller), Atol, Rtol, SolverCaller_toString(caller));
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 1, "Matrix Info");
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "NLS index = " OMC_INT_FORMAT, nlsData->equationIndex);
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "Columns   = " OMC_INT_FORMAT, columns);
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "Rows      = " OMC_INT_FORMAT, rows);
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "NNZ       = " OMC_INT_FORMAT, nnz);
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "Curr Time = %-11.5e", data->localData[0]->timeValue);

  messageClose(OMC_LOG_NLS_DERIVATIVE_TEST);

  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 1, "Anomalies");

  nz = 0;
  numericalErrorCount = 0;
  structuralErrorCount = 0;

  for (col = 0; col < size; col++)
  {
    errorFound = FALSE;

    for (row = 0; row < size; row++)
    {
      numValue = SM_ELEMENT_D(Jnum, row, col);

      if (colPointers[col] <= nz && nz < colPointers[col+1] && rowIndices[nz] == row)
      {
        // structural non-zero -> compare values
        symValue = symValues[nz++];
        absError = fabs(symValue - numValue);
        relError = (absError < Atol) ? 0.0 : absError / fmax(fabs(numValue), fabs(symValue));

        if (relError > maxError)
        {
            maxError = relError;
        }

        if (relError > Rtol)
        {
          // tolerance exceeded -> numerical error
          if (!errorFound)
          {
            infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 1, "Column / Variable: %i, Name: %s",
            col + 1, modelInfoGetEquation(&data->modelData->modelDataXml, nlsData->equationIndex).vars[col]);
            infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "%-12s %-6s %-6s %-15s  %-15s  %-8s",
                            "Type", "Col", "Row", "Symbolic", "Numerical", "RelError");
            errorFound = TRUE;
          }
          infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "%-12s %-6d %-6d %+15.8e  %+15.8e  %+13.8e",
                          "Numerical", col + 1, row + 1, symValue, numValue, relError);
          numericalErrorCount++;
        }
      }
      else if (fabs(numValue) > Atol)
      {
        // structural error with tolerance exceeded -> non-zero in numerical Jacobian but zero in symbolic
        if (!errorFound)
        {
          infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 1, "Column / Variable: %i, Name: %s",
                          col + 1, modelInfoGetEquation(&data->modelData->modelDataXml, nlsData->equationIndex).vars[col]);
          infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "%-12s %-6s %-6s %-15s  %-15s  %-8s",
                          "Type", "Col", "Row", "Symbolic", "Numerical", "RelError");
          errorFound = TRUE;
        }
        infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "%-12s %-6d %-6d %+15.8e  %+15.8e  %+13.8e",
                        "Structural", col + 1, row + 1, 0.0, numValue, 1.0);
        structuralErrorCount++;
      }
    }

    if (errorFound)
    {
      messageClose(OMC_LOG_NLS_DERIVATIVE_TEST);
    }
  }
  messageClose(OMC_LOG_NLS_DERIVATIVE_TEST);

  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 1, "Summary");
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "Numerical errors:  %d (value mismatch w.r.t. reference)", numericalErrorCount);
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "Structural errors: %d (non-zero not in sparsity pattern)", structuralErrorCount);
  infoStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "Max relative error: %.3e", maxError);

  if (numericalErrorCount + structuralErrorCount > 0)
  {
    warningStreamPrint(OMC_LOG_NLS_DERIVATIVE_TEST, 0, "Derivative test failed (%d numerical, %d structural errors)",
                       numericalErrorCount, structuralErrorCount);
    ret = 1;
  }
  messageClose(OMC_LOG_NLS_DERIVATIVE_TEST);

  SUNMatDestroy(Jnum);

  messageClose(OMC_LOG_NLS_DERIVATIVE_TEST);

  return ret;
}

/**
 * @brief Check for zero columns of matrix and print absolute sums.
 *
 * Compute absolute sum for each column and print the result.
 * Report a warning if it is zero, since the matrix is singular in that case.
 *
 * @param A       Dense matrix stored columnwise
 */
static void nlsKinsolJacSumDense(SUNMatrix A) {
  /* Variables */
  int i, j;
  double sum;

  for (i = 0; i < SM_ROWS_D(A); ++i) {
    sum = 0.0;
    for (j = 0; j < SM_COLUMNS_D(A); ++j) {
      sum += fabs(SM_ELEMENT_D(A, j, i));
    }

    if (sum == 0.0) { /* TODO: Don't check for equality(!), maybe use DBL_EPSILON */
      warningStreamPrint(OMC_LOG_NLS_V, 0,
                         "KINSOL: Column %d of Jacobian is zero. Jacobian is singular.",
                         i);
    } else {
      infoStreamPrint(OMC_LOG_NLS_JAC, 0, "Column %d of Jacobian absolute sum = %g",
                      i, sum);
    }
  }
}

/**
 * @brief Check for zero columns of matrix and print absolute sums.
 *
 * Compute absolute sum for each column and print the result.
 * Report a warning if it is zero, since the matrix is singular in that case.
 *
 * @param A       CSC matrix
 */
static void nlsKinsolJacSumSparse(SUNMatrix A) {
  /* Variables */
  int i, j;
  double sum;

  /* Check format of A */
  if (SM_SPARSETYPE_S(A) != SUN_CSC_MAT) {
    errorStreamPrint(OMC_LOG_STDOUT, 0,
                     "KINSOL: In function nlsKinsolJacSumSparse: Wrong sparse format "
                     "of SUNMatrix A.");
  }

  /* Check sums of each column of A */
  for (i = 0; i < SM_COLUMNS_S(A); ++i) {
    sum = 0.0;
    for (j = SM_INDEXPTRS_S(A)[i]; j < SM_INDEXPTRS_S(A)[i + 1]; ++j) {
      sum += fabs(SM_DATA_S(A)[j]);
    }

    if (sum == 0.0) { /* TODO: Don't check for equality(!), maybe use DBL_EPSILON */
      warningStreamPrint(OMC_LOG_NLS_V, 0,
                         "KINSOL: Column %d of Jacobian is zero. Jacobian is singular.",
                         i);
    } else {
      infoStreamPrint(OMC_LOG_NLS_JAC, 0, "Column %d of Jacobian absolute sum = %g",
                      i, sum);
    }
  }
}

/**
 * @brief Set maximum scaled length of Newton step.
 *
 * The KINSOL scaling vector is unity because the problem is already expressed
 * in common NLS solver coordinates.
 *
 * @param kinsolData
 * @param maxstepfactor
 */
static void nlsKinsolSetMaxNewtonStep(NLS_KINSOL_DATA *kinsolData, double maxstepfactor) {
  /* Variables */
  int flag;

  kinsolData->mxnstepin = sqrt((double) kinsolData->size) * maxstepfactor;

  /* Set maximum step size */
  flag = KINSetMaxNewtonStep(kinsolData->kinsolMemory, kinsolData->mxnstepin);
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetMaxNewtonStep");
}

/**
 * @brief Set initial guess for KINSOL
 *
 * Depending on mode extrapolate start value or use old value for
 * initialization.
 *
 * @param data
 * @param kinsolData
 * @param nlsData
 * @param mode          Has to be `INITIAL_EXTRAPOLATION` for extrapolation or
 * `INITIAL_OLDVALUES` for using old values.
 */
static void nlsKinsolResetInitial(DATA *data, NLS_KINSOL_DATA *kinsolData, NONLINEAR_SYSTEM_DATA *nlsData,
                                  initialMode mode) {
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  double *xStart = NV_DATA_S(kinsolData->initialGuess);
  const double *xSource;

  switch (mode) {
  case INITIAL_EXTRAPOLATION:
    xSource = data->simulationInfo->discreteCall ? scaling->z : scaling->zExtrapolation;
    break;
  case INITIAL_OLDVALUES:
    xSource = scaling->zOld;
    break;
  default:
    throwStreamPrint(kinsolData->userData->threadData, "KINSOL: Unknown initial-guess mode %d", (int) mode);
    return;
  }

  memcpy(xStart, xSource, kinsolData->size * sizeof(double));
}

/**
 * @brief Print KINSOL configuration.
 *
 * Only prints if stream `LOG_NLS_V` is active.
 *
 * @param kinsolData
 */
static void nlsKinsolConfigPrint(NLS_KINSOL_DATA *kinsolData) {
  nlsPrintInitialGuess(kinsolData->userData, NV_DATA_S(kinsolData->initialGuess), kinsolData->size, OMC_LOG_NLS_V);
  nlsPrintScaleFactors(kinsolData->userData, kinsolData->size, OMC_LOG_NLS_V);

  infoStreamPrint(OMC_LOG_NLS_V, 0, "KINSOL scaled-residual tolerance: %g", kinsolData->fnormtol);
  infoStreamPrint(OMC_LOG_NLS_V, 0, "KINSOL scaled-step tolerance: %g", kinsolData->scsteptol);
  infoStreamPrint(OMC_LOG_NLS_V, 0, "KINSOL max iterations %d", 100 * kinsolData->size);
  infoStreamPrint(OMC_LOG_NLS_V, 0, "KINSOL strategy %d", kinsolData->kinsolStrategy);
  infoStreamPrint(OMC_LOG_NLS_V, 0, "KINSOL current retry %d", kinsolData->retries);
  infoStreamPrint(OMC_LOG_NLS_V, 0, "KINSOL max scaled step %g", kinsolData->mxnstepin);
  infoStreamPrint(OMC_LOG_NLS_V, 0, "KINSOL linear solver %d", kinsolData->linearSolverMethod);
}

static modelica_boolean nlsKinsolConfigureRetry(DATA *data, NONLINEAR_SYSTEM_DATA *nlsData,
                                                NLS_KINSOL_DATA *kinsolData)
{
  switch (kinsolData->retries) {
  case 0:
    /* Retry the current iterate with a fresh setup. */
    break;
  case 1:
    nlsKinsolResetInitial(data, kinsolData, nlsData, INITIAL_OLDVALUES);
    kinsolData->kinsolStrategy = KIN_LINESEARCH;
    break;
  case 2:
    nlsKinsolResetInitial(data, kinsolData, nlsData, INITIAL_EXTRAPOLATION);
    kinsolData->kinsolStrategy = KIN_NONE;
    break;
  case 3:
    nlsKinsolResetInitial(data, kinsolData, nlsData, INITIAL_EXTRAPOLATION);
    KINSetMaxSetupCalls(kinsolData->kinsolMemory, 1);
    kinsolData->kinsolStrategy = KIN_LINESEARCH;
    break;
  case 4:
    nlsKinsolResetInitial(data, kinsolData, nlsData, INITIAL_OLDVALUES);
    KINSetMaxSetupCalls(kinsolData->kinsolMemory, 1);
    kinsolData->kinsolStrategy = KIN_LINESEARCH;
    break;
  default:
    return FALSE;
  }
  return TRUE;
}

/**
 * @brief Try to handle errors of KINSol().
 *
 * @param errorCode           Error code from KINSOL.
 * @param data                Pointer to data struct.
 * @param nlsData             Non-linear solver data.
 * @param kinsolData          Kinsol data.
 * @return modelica_boolean   Return true, if it is possible to retry KINSol().
 */
static modelica_boolean nlsKinsolErrorHandler(int errorCode, DATA *data,
                                              NONLINEAR_SYSTEM_DATA *nlsData,
                                              NLS_KINSOL_DATA *kinsolData) {
  int flag;             /* KIN_* and KINLS_* codes, which are plain macros */
  SUNErrCode sunFlag;   /* SUNLinearSolver codes, which are not */
  long outL;

  flag = KINSetNoInitSetup(kinsolData->kinsolMemory, SUNFALSE);
  checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetNoInitSetup");

  switch (errorCode) {
  case KIN_MEM_NULL:
    throwStreamPrint(NULL, "KINSOL: Memory NULL ERROR %d\n", errorCode);
    return FALSE;
    break;
  case KIN_ILL_INPUT:
    throwStreamPrint(NULL, "KINSOL: Ill input ERROR %d\n", errorCode);
    return FALSE;
    break;
  case KIN_NO_MALLOC:
    throwStreamPrint(NULL, "KINSOL: Memory issue ERROR %d\n", errorCode);
    return FALSE;
    break;
  /* Just retry with new initial guess */
  case KIN_MXNEWT_5X_EXCEEDED:
    warningStreamPrint(
        OMC_LOG_NLS_V, 0,
        "Newton step exceed the maximum step size several times. Try again "
        "after increasing maximum step size.\n");
    kinsolData->maxstepfactor *= 1e5;
    nlsKinsolSetMaxNewtonStep(kinsolData, kinsolData->maxstepfactor);
    return TRUE;
    break;
  /* Just retry without line search */
  case KIN_LINESEARCH_NONCONV:
    warningStreamPrint(
        OMC_LOG_NLS_V, 0,
        "kinsols line search did not convergence. Try without.\n");
    kinsolData->kinsolStrategy = KIN_NONE;
    kinsolData->retries--;
    return TRUE;
    break;
  /* Maybe happened because of an out-dated factorization, so just retry */
  case KIN_LSOLVE_FAIL:
    warningStreamPrint(OMC_LOG_NLS_V, 0,
                       "KINSOL: Matrix need new factorization. Try again.\n");
    if (kinsolData->linearSolverMethod == NLS_LS_KLU && nlsJacobianPattern(kinsolData->userData)) {
      /* Complete symbolic and numeric factorizations */
      sunFlag = SUNLinSol_KLUReInit(kinsolData->linSol, kinsolData->J,
                                    kinsolData->nnz, SUNKLU_REINIT_PARTIAL);
      checkReturnFlag_SUNDIALS(sunFlag, SUNDIALS_SUNLS_FLAG, "SUNLinSol_KLUReInit");
      return TRUE;
    }
    break;
  case KIN_MAXITER_REACHED:
  case KIN_REPTD_SYSFUNC_ERR:
    warningStreamPrint(OMC_LOG_NLS_V, 0,
                       "KINSOL: Runs into issues retry with different configuration.\n");
    break;
  case KIN_LINIT_FAIL:
    errorStreamPrint(OMC_LOG_STDOUT, 0,
                     "KINSOL: The linear solver's initialization function failed.\n");
    return FALSE;
  case KIN_LSETUP_FAIL:
    /* In case something goes wrong with the symbolic jacobian try the numerical */
    warningStreamPrint(OMC_LOG_NLS_V, 0,
                       "KINSOL: The kinls setup routine (lsetup) encountered an error. "
                       "Retry with numerical Jacobian.\n");
    kinsolData->jacobianMethod = NLS_JACOBIAN_NUMERICAL;
    break;
  case KIN_LINESEARCH_BCFAIL:
    KINGetNumBetaCondFails(kinsolData->kinsolMemory, &outL);
    warningStreamPrint(
        OMC_LOG_NLS_V, 0,
        "kinsols runs into issues with beta-condition fails: %ld\n", outL);
    break;
  default:
    errorStreamPrint(OMC_LOG_STDOUT, 0,
                     "kinsol has a serious solving issue ERROR %d\n",
                     errorCode);
    return FALSE;
    break;
  }

  return nlsKinsolConfigureRetry(data, nlsData, kinsolData);
}

/**
 * @brief Solve non-linear system with KINSol
 *
 * @param data                Runtime data struct.
 * @param threadData          Thread data for error handling.
 * @param nlsData             Pointer to non-linear system data.
 * @return NLS_SOLVER_STATUS  Return NLS_SOLVED on success and NLS_FAILED otherwise.
 */
NLS_SOLVER_STATUS nlsKinsolSolve(DATA* data, threadData_t* threadData, NONLINEAR_SYSTEM_DATA* nlsData) {

  NLS_KINSOL_DATA *kinsolData = (NLS_KINSOL_DATA *)nlsData->solverData;
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  int eqSystemNumber = nlsData->equationIndex;
  int indexes[2] = {1, eqSystemNumber};

  int flag;
  long nFEval;
  modelica_boolean success = FALSE;
  modelica_boolean retry = TRUE;
  NLS_SOLVER_STATUS candidateStatus = NLS_FAILED;
  NLS_SOLVER_STATUS bestStatus = NLS_FAILED;
  double *xStart = NV_DATA_S(kinsolData->initialGuess);

  infoStreamPrintWithEquationIndexes(OMC_LOG_NLS_V, omc_dummyFileInfo, 1, indexes,
    "Start solving Non-Linear System %d (size %d) at time %g with Kinsol Solver",
    eqSystemNumber, (int) nlsData->size, data->localData[0]->timeValue);

  kinsolData->fnormtol = scaling->convergence.fTol;
  kinsolData->scsteptol = scaling->convergence.xTol;
  if (kinsolData->attemptRetry) {
    nlsKinsolConfigSetup(kinsolData);
  } else {
    flag = KINSetFuncNormTol(kinsolData->kinsolMemory, kinsolData->fnormtol);
    checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetFuncNormTol");
    flag = KINSetScaledStepTol(kinsolData->kinsolMemory, kinsolData->scsteptol);
    checkReturnFlag_SUNDIALS(flag, SUNDIALS_KIN_FLAG, "KINSetScaledStepTol");
    kinsolData->countResCalls = 0;
    kinsolData->retries = 0;
    kinsolData->jacobianMethod = NLS_JACOBIAN_AUTO;
    kinsolData->maxstepfactor = maxStepFactor;
  }
  nlsKinsolResetInitial(data, kinsolData, nlsData, INITIAL_EXTRAPOLATION);
  nlsKinsolSetMaxNewtonStep(kinsolData, kinsolData->maxstepfactor);
  kinsolData->jacobianMethod = NLS_JACOBIAN_AUTO;

  /* Solve nonlinear system with KINSol() */
  kinsolData->retries = 0;
  do {
    /* Dump configuration */
    nlsKinsolConfigPrint(kinsolData);

    flag = KINSol(kinsolData->kinsolMemory,    /* KINSol memory block */
                  kinsolData->initialGuess,    /* initial guess on input; solution vector */
                  kinsolData->kinsolStrategy,  /* global strategy choice */
                  kinsolData->scale,           /* native KINSOL variable scaling (unity) */
                  kinsolData->scale);          /* native KINSOL residual scaling (unity) */

    if (flag < 0 && kinsolData->attemptRetry) {
      warningStreamPrint(OMC_LOG_NLS, 0, "KINSol finished with errorCode %d.", flag);
    } else {
      infoStreamPrint(OMC_LOG_NLS_V, 0, "KINSol finished with errorCode %d.", flag);
    }
    candidateStatus = nlsValidateCandidate(kinsolData->userData, xStart, NULL,
                                           flag == KIN_STEP_LT_STPTOL, "KINSOL");
    success = candidateStatus == NLS_SOLVED;
    if (candidateStatus == NLS_RETRY) bestStatus = NLS_RETRY;

    /* KINSOL return values are termination reasons. The common validator decides acceptance. */
    if (!success && flag < 0) {
      retry = kinsolData->attemptRetry && nlsKinsolErrorHandler(flag, data, nlsData, kinsolData);
    } else if (!success) {
      retry = kinsolData->attemptRetry && nlsKinsolConfigureRetry(data, nlsData, kinsolData);
    } else {
      retry = FALSE;
    }
    kinsolData->retries++;

    /* write statistics */
    KINGetNumNonlinSolvIters(kinsolData->kinsolMemory, &nFEval);
    nlsData->numberOfIterations += nFEval;
    nlsData->numberOfFEval = kinsolData->countResCalls;

    infoStreamPrint(OMC_LOG_NLS_V, 0, "Next try? success = %d, retry = %d, retries = %d = %s\n",
                    success, retry, kinsolData->retries,
                    !success && retry && kinsolData->retries < RETRY_MAX ? "true" : "false");
  } while (!success && retry && kinsolData->retries < RETRY_MAX);

  kinsolData->solved = success ? NLS_SOLVED : bestStatus;

  messageClose(OMC_LOG_NLS_V);

  return kinsolData->solved;
}

#else /* WITH_SUNDIALS */

void* nlsKinsolAllocate(int size, void* userData, int attemptRetry) {

  throwStreamPrint(NULL, "No sundials/kinsol support activated.");
  return 0;
}

int nlsKinsolFree(void* kinsolData) {

  throwStreamPrint(NULL, "No sundials/kinsol support activated.");
  return 0;
}

int nlsKinsolSolve(void *data, threadData_t *threadData, void* nlsData) {

  throwStreamPrint(threadData, "No sundials/kinsol support activated.");
  return 0;
}

#endif /* WITH_SUNDIALS */
