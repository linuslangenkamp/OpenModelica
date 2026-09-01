/*
 * This file belongs to the OpenModelica Run-Time System
 *
 * Copyright (c) 1998-2026, Open Source Modelica Consortium (OSMC)
 *
 * Distributed under the OSMC Public License (OSMC-PL), BSD 3-Clause, or
 * GNU AGPL version 3.
 */

#include "nonlinearScaling.h"

#include <float.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

#include "../jacobian_util.h"
#include "../options.h"
#include "../../meta/meta_modelica.h"
#include "../../util/omc_error.h"
#include "../../util/simulation_options.h"
#include "model_help.h"
#include "nonlinearSystem.h"

static const size_t NLS_SCALING_VECTOR_COUNT = 13;

static inline modelica_real clampTolerance(modelica_real value, modelica_real lower, modelica_real upper)
{
  return fmin(upper, fmax(lower, value));
}

static modelica_boolean finiteVector(const modelica_real *values, modelica_integer size)
{
  modelica_integer i;
  for (i = 0; i < size; i++) {
    if (!isfinite(values[i])) return FALSE;
  }
  return TRUE;
}

modelica_real nlsMaxNorm(const modelica_real *values, modelica_integer size)
{
  modelica_integer i;
  modelica_real norm = 0.0;
  for (i = 0; i < size; i++) {
    if (!isfinite(values[i])) return INFINITY;
    norm = fmax(norm, fabs(values[i]));
  }
  return norm;
}

modelica_real nlsRelativeStepNorm(const modelica_real *z, const modelica_real *zPrevious, modelica_integer size)
{
  modelica_integer i;
  modelica_real norm = 0.0;
  if (!zPrevious) return NAN;
  for (i = 0; i < size; i++) {
    const modelica_real denominator = fmax(1.0, fabs(z[i]));
    const modelica_real step = fabs(z[i] - zPrevious[i]) / denominator;
    if (!isfinite(step)) return INFINITY;
    norm = fmax(norm, step);
  }
  return norm;
}

static int residualSafe(NLS_USERDATA *userData, const modelica_real *z, modelica_real *g, const int *iflag)
{
  threadData_t *threadData = userData->threadData;
  volatile int result = 1;
#ifndef OMC_EMCC
  MMC_TRY_INTERNAL(simulationJumpBuffer)
#endif
  result = nlsResidual(userData, z, g, iflag);
#ifndef OMC_EMCC
  MMC_CATCH_INTERNAL(simulationJumpBuffer)
#endif
  return result;
}

static void prepareConvergencePolicy(NLS_USERDATA *userData)
{
  NLS_CONVERGENCE_DATA *convergence = &userData->nlsData->scaling->convergence;
  modelica_real baseTol = userData->data->simulationInfo->tolerance;
  modelica_real derivedTol;

  if (!isfinite(baseTol) || baseTol <= 0.0) baseTol = 1e-5;
  derivedTol = clampTolerance(0.1 * baseTol, 1e-12, 1e-6);
  convergence->fTol = omc_flag[FLAG_NEWTON_FTOL] ? newtonFTol : derivedTol;
  convergence->xTol = omc_flag[FLAG_NEWTON_XTOL] ? newtonXTol : derivedTol;
  if (!isfinite(convergence->fTol) || convergence->fTol <= 0.0) convergence->fTol = derivedTol;
  if (!isfinite(convergence->xTol) || convergence->xTol <= 0.0) convergence->xTol = derivedTol;
  convergence->relaxedFTol = clampTolerance(baseTol, convergence->fTol, fmax(convergence->fTol, 1e-4));
  convergence->residualNorm = INFINITY;
  convergence->stepNorm = INFINITY;

  infoStreamPrint(OMC_LOG_NLS_V, 0,
                  "NLS tolerances: residual=%g, step=%g, retry=%g (simulation tolerance=%g)",
                  convergence->fTol, convergence->xTol, convergence->relaxedFTol, baseTol);
}

const SPARSE_PATTERN *nlsJacobianPattern(const NLS_USERDATA *userData)
{
  const JACOBIAN *jacobian = userData->analyticJacobian;
  if (jacobian && !jacobian->isRowEval && jacobian->sparsePattern) {
    return jacobian->sparsePattern;
  }
  return userData->nlsData->sparsePattern;
}

void nlsScalingAllocate(NONLINEAR_SYSTEM_DATA *nlsData, const JACOBIAN *analyticJacobian)
{
  NLS_SCALING_DATA *scaling = (NLS_SCALING_DATA*) calloc(1, sizeof(*scaling));
  const SPARSE_PATTERN *pattern = analyticJacobian && !analyticJacobian->isRowEval ? analyticJacobian->sparsePattern : nlsData->sparsePattern;
  const size_t size = nlsData->size;
  const size_t analyticSize = analyticJacobian ? analyticJacobian->sizeRows * analyticJacobian->sizeCols : 0;
  const size_t denseSize = size * size;
  size_t jacobianCapacity = pattern ? pattern->nnz : denseSize;
  modelica_real *memory;

  if ((nlsData->homotopySupport || (analyticJacobian && analyticJacobian->isRowEval)) && jacobianCapacity < denseSize) {
    jacobianCapacity = denseSize;
  }
  if (analyticJacobian && analyticJacobian->isRowEval && jacobianCapacity < analyticSize) jacobianCapacity = analyticSize;

  assertStreamPrint(NULL, scaling != NULL, "Failed to allocate nonlinear scaling data");
  scaling->size = size;
  scaling->method = NLS_SCALING_JACOBIAN;
  scaling->activeMethod = NLS_SCALING_JACOBIAN;
  scaling->jacobianCapacity = jacobianCapacity;
  memory = (modelica_real*) malloc((NLS_SCALING_VECTOR_COUNT * size + jacobianCapacity) * sizeof(modelica_real));
  assertStreamPrint(NULL, memory != NULL, "Failed to allocate nonlinear scaling work memory");

  scaling->z = memory;
  scaling->zOld = scaling->z + size;
  scaling->zExtrapolation = scaling->zOld + size;
  scaling->zNominal = scaling->zExtrapolation + size;
  scaling->zMin = scaling->zNominal + size;
  scaling->zMax = scaling->zMin + size;
  scaling->xScale = scaling->zMax + size;
  scaling->fScale = scaling->xScale + size;
  scaling->xPhysical = scaling->fScale + size;
  scaling->zWork = scaling->xPhysical + size;
  scaling->fWork = scaling->zWork + size;
  scaling->fBase = scaling->fWork + size;
  scaling->fdStep = scaling->fBase + size;
  scaling->jacobianWork = scaling->fdStep + size;
  nlsData->scaling = scaling;
}

void nlsScalingSetMethod(NONLINEAR_SYSTEM_DATA *nlsData, NLS_SCALING_METHOD method)
{
  assertStreamPrint(NULL, nlsData->scaling != NULL, "Nonlinear system has no scaling data");
  assertStreamPrint(NULL, !nlsData->scaling->prepared, "Cannot change nonlinear scaling while a solve is active");
  nlsData->scaling->method = method;
  nlsData->scaling->activeMethod = method;
}

static inline void scaleVariables(const NLS_SCALING_DATA *scaling, const modelica_real *x, modelica_real *z,
                                  modelica_integer size)
{
  modelica_integer i;
  for (i = 0; i < size; i++) z[i] = x[i] * scaling->xScale[i];
}

static inline void unscaleVariables(const NLS_SCALING_DATA *scaling, const modelica_real *z, modelica_real *x,
                                    modelica_integer size)
{
  modelica_integer i;
  for (i = 0; i < size; i++) x[i] = z[i] / scaling->xScale[i];
}

static inline modelica_real nlsScalingBound(modelica_real value, modelica_real scale)
{
  modelica_real scaled;
  if (value == DBL_MAX || value == -DBL_MAX) return value;
  scaled = value * scale;
  return isinf(scaled) ? copysign(DBL_MAX, scaled) : scaled;
}

static void nlsScalingUpdateSolverData(NONLINEAR_SYSTEM_DATA *nlsData)
{
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  modelica_integer i;

  scaleVariables(scaling, nlsData->nlsx, scaling->z, nlsData->size);
  scaleVariables(scaling, nlsData->nlsxOld, scaling->zOld, nlsData->size);
  scaleVariables(scaling, nlsData->nlsxExtrapolation, scaling->zExtrapolation, nlsData->size);
  scaleVariables(scaling, nlsData->nominal, scaling->zNominal, nlsData->size);
  for (i = 0; i < nlsData->size; i++) {
    scaling->zMin[i] = nlsScalingBound(nlsData->min[i], scaling->xScale[i]);
    scaling->zMax[i] = nlsScalingBound(nlsData->max[i], scaling->xScale[i]);
  }
}

void nlsScalingFinish(NONLINEAR_SYSTEM_DATA *nlsData)
{
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  if (!scaling || !scaling->prepared) return;
  unscaleVariables(scaling, scaling->z, nlsData->nlsx, nlsData->size);
  unscaleVariables(scaling, scaling->zOld, nlsData->nlsxOld, nlsData->size);
  unscaleVariables(scaling, scaling->zExtrapolation, nlsData->nlsxExtrapolation, nlsData->size);
  scaling->prepared = FALSE;
}

modelica_real nlsScalingPhysicalX(const NONLINEAR_SYSTEM_DATA *nlsData, modelica_integer index, modelica_real z)
{
  return z / nlsData->scaling->xScale[index];
}

modelica_real nlsScalingPhysicalResidual(const NONLINEAR_SYSTEM_DATA *nlsData, modelica_integer index, modelica_real g)
{
  return g / nlsData->scaling->fScale[index];
}

void nlsScalingFree(NONLINEAR_SYSTEM_DATA *nlsData)
{
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  if (!scaling) return;
  free(scaling->z);
  free(scaling);
  nlsData->scaling = NULL;
}

int nlsResidual(NLS_USERDATA *userData, const modelica_real *z, modelica_real *g, const int *iflag)
{
  NONLINEAR_SYSTEM_DATA *nlsData = userData->nlsData;
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  RESIDUAL_USERDATA residualUserData = {userData->data, userData->threadData, userData->solverData};
  modelica_integer i;
  int result = 0;

  assertStreamPrint(userData->threadData, scaling && scaling->prepared, "Nonlinear scaling must be prepared before residual evaluation");

  if (!finiteVector(z, nlsData->size) || !finiteVector(scaling->xScale, nlsData->size) ||
      !finiteVector(scaling->fScale, scaling->equations)) {
    infoStreamPrint(OMC_LOG_NLS_V, 0, "Rejecting non-finite nonlinear variables or scale factors.");
    return 1;
  }
  for (i = 0; i < nlsData->size; i++) {
    if (scaling->xScale[i] <= 0.0 || (i < scaling->equations && scaling->fScale[i] <= 0.0)) return 1;
  }

  unscaleVariables(scaling, z, scaling->xPhysical, nlsData->size);
  if (!finiteVector(scaling->xPhysical, nlsData->size)) {
    infoStreamPrint(OMC_LOG_NLS_V, 0, "Rejecting non-finite physical nonlinear variables.");
    return 1;
  }
  if (nlsData->strictTearingFunctionCall) {
    assertStreamPrint(userData->threadData, nlsData->residualFuncConstraints != NULL,
                      "Nonlinear system with dynamic tearing has no causal residual function");
    result = nlsData->residualFuncConstraints(&residualUserData, scaling->xPhysical, g, iflag);
  } else {
    nlsData->residualFunc(&residualUserData, scaling->xPhysical, g, iflag);
  }
  if (result || !finiteVector(g, scaling->equations)) return result ? result : 1;
  for (i = 0; i < scaling->equations; i++) {
    g[i] *= scaling->fScale[i];
    if (!isfinite(g[i])) return 1;
  }
  return result;
}

NLS_SOLVER_STATUS nlsValidateCandidate(NLS_USERDATA *userData, const modelica_real *z,
                                      const modelica_real *zPrevious, modelica_boolean stepConverged,
                                      const char *solverName)
{
  NONLINEAR_SYSTEM_DATA *nlsData = userData->nlsData;
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  NLS_CONVERGENCE_DATA *convergence = &scaling->convergence;
  DATA *data = userData->data;
  const modelica_boolean solveContinuous = data->simulationInfo->solveContinuous;
  int iflag = 1;
  int result;

  convergence->residualNorm = INFINITY;
  convergence->stepNorm = nlsRelativeStepNorm(z, zPrevious, scaling->unknowns);
  if (stepConverged && !zPrevious) convergence->stepNorm = convergence->xTol;
  if (!finiteVector(z, nlsData->size)) {
    infoStreamPrint(OMC_LOG_NLS_V, 0, "%s candidate contains non-finite values.", solverName);
    return NLS_FAILED;
  }

  data->simulationInfo->solveContinuous = data->simulationInfo->discreteCall ? FALSE : TRUE;
  result = residualSafe(userData, z, scaling->fWork, &iflag);
  data->simulationInfo->solveContinuous = solveContinuous;
  if (result) {
    infoStreamPrint(OMC_LOG_NLS_V, 0, "%s candidate failed final residual or constraint evaluation.", solverName);
    return NLS_FAILED;
  }

  convergence->residualNorm = nlsMaxNorm(scaling->fWork, scaling->equations);
  infoStreamPrint(OMC_LOG_NLS_V, 0, "%s final scaled max residual = %.16g, relative step = %.16g",
                  solverName, convergence->residualNorm, convergence->stepNorm);
  if (!isfinite(convergence->residualNorm) || (zPrevious && !isfinite(convergence->stepNorm))) return NLS_FAILED;
  if (convergence->residualNorm <= convergence->fTol) {
    memcpy(scaling->z, z, nlsData->size * sizeof(modelica_real));
    return NLS_SOLVED;
  }
  if ((stepConverged || (zPrevious && convergence->stepNorm <= convergence->xTol)) &&
      convergence->residualNorm <= convergence->relaxedFTol) {
    infoStreamPrint(OMC_LOG_NLS_V, 0,
                    "%s candidate satisfies the step criterion and the integrator-level residual budget.", solverName);
    memcpy(scaling->z, z, nlsData->size * sizeof(modelica_real));
    return NLS_SOLVED;
  }
  if (convergence->residualNorm <= convergence->relaxedFTol) {
    infoStreamPrint(OMC_LOG_NLS_V, 0,
                    "%s produced a finite candidate within retry tolerance, but not the requested accuracy.", solverName);
    return NLS_RETRY;
  }
  if (stepConverged || (zPrevious && convergence->stepNorm <= convergence->xTol)) {
    infoStreamPrint(OMC_LOG_NLS_V, 0, "%s stagnated before satisfying the residual tolerance.", solverName);
  }
  return NLS_FAILED;
}

static void scaleAnalyticJacobian(const NLS_USERDATA *userData, modelica_real *jacobian, modelica_boolean sparse)
{
  const NLS_SCALING_DATA *scaling = userData->nlsData->scaling;
  const JACOBIAN *analytic = userData->analyticJacobian;
  const SPARSE_PATTERN *pattern = nlsJacobianPattern(userData);
  const modelica_integer columns = !sparse && analytic ? analytic->sizeCols : scaling->unknowns;
  modelica_integer column, row;
  unsigned int nz;

  if (scaling->activeMethod == NLS_SCALING_IDENTITY) return;
  if (sparse) {
    for (column = 0; column < scaling->unknowns; column++) {
      for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
        row = pattern->index[nz];
        jacobian[nz] *= scaling->fScale[row] / scaling->xScale[column];
      }
    }
  } else {
    for (column = 0; column < columns; column++) {
      for (row = 0; row < scaling->equations; row++) {
        jacobian[column * scaling->equations + row] *= scaling->fScale[row] / scaling->xScale[column];
      }
    }
  }
}

static int finiteDifferenceDirection(const NLS_SCALING_DATA *scaling, const modelica_real *z,
                                     modelica_integer column, modelica_real magnitude)
{
  if (isfinite(scaling->zMax[column]) && z[column] + magnitude > scaling->zMax[column]) return -1;
  if (isfinite(scaling->zMin[column]) && z[column] - magnitude < scaling->zMin[column]) return 1;
  return 1;
}

static modelica_real finiteDifferenceStep(const NLS_SCALING_DATA *scaling, const modelica_real *z,
                                          modelica_integer column, modelica_real magnitude, int direction)
{
  modelica_real step = magnitude;
  modelica_real room;
  if (direction > 0 && isfinite(scaling->zMax[column])) {
    room = scaling->zMax[column] - z[column];
    if (room <= 0.0) return 0.0;
    step = fmin(step, 0.5 * room);
  } else if (direction < 0 && isfinite(scaling->zMin[column])) {
    room = z[column] - scaling->zMin[column];
    if (room <= 0.0) return 0.0;
    step = fmin(step, 0.5 * room);
  }
  step = direction * step;
  return isfinite(step) && step != 0.0 && z[column] + step != z[column] ? step : 0.0;
}

static int numericalJacobianColumn(NLS_USERDATA *userData, modelica_integer column, modelica_real magnitude,
                                   modelica_real *jacobian, modelica_boolean sparse)
{
  NLS_SCALING_DATA *scaling = userData->nlsData->scaling;
  const SPARSE_PATTERN *pattern = nlsJacobianPattern(userData);
  const modelica_real zBase = scaling->zWork[column];
  const int preferred = finiteDifferenceDirection(scaling, scaling->zWork, column, magnitude);
  int iflag = 1;
  int reduction, directionIndex;
  modelica_integer row;
  unsigned int nz;

  for (reduction = 0; reduction < 4; reduction++) {
    const modelica_real reducedMagnitude = ldexp(magnitude, -reduction);
    for (directionIndex = 0; directionIndex < 2; directionIndex++) {
      const int direction = directionIndex ? -preferred : preferred;
      const modelica_real step = finiteDifferenceStep(scaling, scaling->zWork, column, reducedMagnitude, direction);
      modelica_boolean valid = TRUE;
      if (step == 0.0) continue;
      scaling->zWork[column] = zBase + step;
      if (residualSafe(userData, scaling->zWork, scaling->fWork, &iflag) == 0) {
        if (sparse) {
          for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
            row = pattern->index[nz];
            if (!isfinite((scaling->fWork[row] - scaling->fBase[row]) / step)) valid = FALSE;
          }
          if (valid) {
            for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
              row = pattern->index[nz];
              jacobian[nz] = (scaling->fWork[row] - scaling->fBase[row]) / step;
            }
          }
        } else {
          for (row = 0; row < scaling->equations; row++) {
            if (!isfinite((scaling->fWork[row] - scaling->fBase[row]) / step)) valid = FALSE;
          }
          if (valid) {
            for (row = 0; row < scaling->equations; row++) {
              jacobian[column * scaling->equations + row] = (scaling->fWork[row] - scaling->fBase[row]) / step;
            }
          }
        }
        scaling->zWork[column] = zBase;
        if (valid) return 0;
      } else {
        scaling->zWork[column] = zBase;
      }
    }
  }
  scaling->zWork[column] = zBase;
  return 1;
}

static int numericalJacobian(NLS_USERDATA *userData, const modelica_real *z, modelica_real *jacobian, modelica_boolean sparse)
{
  NONLINEAR_SYSTEM_DATA *nlsData = userData->nlsData;
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  const SPARSE_PATTERN *pattern = nlsJacobianPattern(userData);
  modelica_integer color, column, row;
  unsigned int nz;
  int iflag = 1;
  int result;
  const modelica_real delta = sqrt(20.0 * DBL_EPSILON);

  assertStreamPrint(userData->threadData, scaling != NULL, "Numerical nonlinear Jacobian requires scaling work memory");
  memcpy(scaling->zWork, z, nlsData->size * sizeof(modelica_real));
  result = residualSafe(userData, scaling->zWork, scaling->fBase, &iflag);
  if (result) return result;

  if (!sparse) {
    for (column = 0; column < scaling->unknowns; column++) {
      const modelica_real magnitude = delta * (fabs(scaling->zWork[column]) + 1.0);
      if (numericalJacobianColumn(userData, column, magnitude, jacobian, FALSE)) goto fail;
    }
  } else {
    assertStreamPrint(userData->threadData, pattern != NULL, "Sparse numerical nonlinear Jacobian has no sparsity pattern");
    for (color = 0; color < (modelica_integer) pattern->maxColors; color++) {
      modelica_boolean colorDone = FALSE;
      int reduction, directionIndex;
      for (reduction = 0; reduction < 4 && !colorDone; reduction++) {
        for (directionIndex = 0; directionIndex < 2 && !colorDone; directionIndex++) {
          modelica_boolean valid = TRUE;
          for (column = 0; column < scaling->unknowns; column++) {
            if ((modelica_integer) pattern->colorCols[column] - 1 == color) {
              const modelica_real magnitude = ldexp(delta * (fabs(scaling->zWork[column]) + 1.0), -reduction);
              const int preferred = finiteDifferenceDirection(scaling, scaling->zWork, column, magnitude);
              scaling->fdStep[column] = finiteDifferenceStep(scaling, scaling->zWork, column, magnitude,
                                                              directionIndex ? -preferred : preferred);
              if (scaling->fdStep[column] == 0.0) valid = FALSE;
              scaling->zWork[column] += scaling->fdStep[column];
            }
          }
          result = valid ? residualSafe(userData, scaling->zWork, scaling->fWork, &iflag) : 1;
          for (column = 0; column < scaling->unknowns; column++) {
            if ((modelica_integer) pattern->colorCols[column] - 1 == color) scaling->zWork[column] -= scaling->fdStep[column];
          }
          if (!result) {
            for (column = 0; column < scaling->unknowns && valid; column++) {
              if ((modelica_integer) pattern->colorCols[column] - 1 == color) {
                for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
                  row = pattern->index[nz];
                  if (!isfinite((scaling->fWork[row] - scaling->fBase[row]) / scaling->fdStep[column])) valid = FALSE;
                }
              }
            }
            if (valid) {
              for (column = 0; column < scaling->unknowns; column++) {
                if ((modelica_integer) pattern->colorCols[column] - 1 == color) {
                  for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
                    row = pattern->index[nz];
                    jacobian[nz] = (scaling->fWork[row] - scaling->fBase[row]) / scaling->fdStep[column];
                  }
                }
              }
              colorDone = TRUE;
            }
          }
        }
      }
      if (!colorDone) {
        /* A recoverable failure in one column must not discard the complete color. */
        for (column = 0; column < scaling->unknowns; column++) {
          if ((modelica_integer) pattern->colorCols[column] - 1 == color) {
            const modelica_real magnitude = delta * (fabs(scaling->zWork[column]) + 1.0);
            if (numericalJacobianColumn(userData, column, magnitude, jacobian, TRUE)) goto fail;
          }
        }
      }
    }
  }

  /* Restore generated variables and inner equations to z. */
  memcpy(scaling->zWork, z, nlsData->size * sizeof(modelica_real));
  return residualSafe(userData, scaling->zWork, scaling->fWork, &iflag);

fail:
  memcpy(scaling->zWork, z, nlsData->size * sizeof(modelica_real));
  residualSafe(userData, scaling->zWork, scaling->fWork, &iflag);
  return 1;
}

int nlsJacobian(NLS_USERDATA *userData, const modelica_real *z, modelica_real *jacobian, modelica_boolean sparse,
                NLS_JACOBIAN_METHOD method)
{
  NONLINEAR_SYSTEM_DATA *nlsData = userData->nlsData;
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  JACOBIAN *analytic = userData->analyticJacobian;
  const SPARSE_PATTERN *pattern = nlsJacobianPattern(userData);
  int iflag = 1;

  assertStreamPrint(userData->threadData, scaling != NULL && scaling->prepared, "Nonlinear scaling must be prepared before Jacobian evaluation");
  assertStreamPrint(userData->threadData, !sparse || pattern != NULL, "Sparse nonlinear Jacobian has no sparsity pattern");

  if (method == NLS_JACOBIAN_AUTO && analytic && analytic->evalColumn &&
      analytic->sizeRows == scaling->equations && analytic->sizeCols >= scaling->unknowns && analytic->sizeCols <= scaling->size) {
    const modelica_boolean gatherRows = sparse && analytic->isRowEval;
    const modelica_boolean trimColumns = !sparse && analytic->sizeCols > scaling->unknowns;
    modelica_real *values = gatherRows || trimColumns ? scaling->jacobianWork : jacobian;
    const size_t valueCount = sparse && !gatherRows ? pattern->nnz : scaling->equations * analytic->sizeCols;
    modelica_integer column;
    unsigned int nz;

    const int result = nlsResidual(userData, z, scaling->fBase, &iflag);
    if (result) return result;
    evalJacobian(userData->data, userData->threadData, analytic, NULL, values, gatherRows || !sparse);
    if (!finiteVector(values, valueCount)) return 1;
    scaleAnalyticJacobian(userData, values, gatherRows || trimColumns ? FALSE : sparse);
    if (!finiteVector(values, valueCount)) return 1;
    if (gatherRows) {
      for (column = 0; column < scaling->unknowns; column++) {
        for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
          jacobian[nz] = values[column * scaling->equations + pattern->index[nz]];
        }
      }
    } else if (trimColumns && values != jacobian) {
      memcpy(jacobian, values, scaling->equations * scaling->unknowns * sizeof(modelica_real));
    }
    if (!finiteVector(jacobian, sparse ? pattern->nnz : scaling->equations * scaling->unknowns)) return 1;
    return 0;
  }

  return numericalJacobian(userData, z, jacobian, sparse);
}

void nlsScalingPrepare(NLS_USERDATA *userData, const modelica_real *xReference, modelica_integer equations, modelica_integer unknowns)
{
  NONLINEAR_SYSTEM_DATA *nlsData = userData->nlsData;
  NLS_SCALING_DATA *scaling = nlsData->scaling;
  threadData_t *threadData = userData->threadData;
  const SPARSE_PATTERN *pattern;
  modelica_boolean sparse;
  size_t required;
  modelica_integer column, row;
  unsigned int nz;
  volatile modelica_boolean failed = TRUE;

  assertStreamPrint(threadData, scaling != NULL, "Nonlinear system has no scaling data");
  assertStreamPrint(threadData, !scaling->prepared, "Nonlinear scaling is already prepared");
  assertStreamPrint(threadData, equations > 0 && unknowns > 0 && nlsData->size > 0 && nlsData->size <= scaling->size &&
                    equations <= scaling->size && unknowns <= scaling->size,
                    "Invalid nonlinear scaling dimensions");

  scaling->equations = equations;
  scaling->unknowns = unknowns;
  scaling->prepared = TRUE;
  scaling->activeMethod = omc_flag[FLAG_NO_SCALING] ? NLS_SCALING_IDENTITY : scaling->method;
  prepareConvergencePolicy(userData);

  for (column = 0; column < unknowns; column++) {
    double scale = 1.0;
    if ((scaling->activeMethod == NLS_SCALING_NOMINAL || scaling->activeMethod == NLS_SCALING_JACOBIAN) &&
        column < nlsData->size) {
      const double nominal = fabs(nlsData->nominal[column]);
      const double reference = fabs(xReference[column]);
      double characteristic = isfinite(nominal) && nominal > 0.0 ? nominal : 0.0;
      if (isfinite(reference) && reference > characteristic) characteristic = reference;
      if (characteristic <= 0.0) characteristic = 1.0;
      scale = 1.0 / characteristic;
      if (!isfinite(scale) || scale <= 0.0) scale = 1.0;
    }
    scaling->xScale[column] = scale;
  }
  for (column = unknowns; column < scaling->size; column++) scaling->xScale[column] = 1.0;
  for (row = 0; row < scaling->size; row++) scaling->fScale[row] = 1.0;
  nlsScalingUpdateSolverData(nlsData);

  switch (scaling->activeMethod) {
  case NLS_SCALING_IDENTITY:
  case NLS_SCALING_NOMINAL:
    return;

  case NLS_SCALING_RESIDUAL:
  case NLS_SCALING_JACOBIAN:
    pattern = nlsJacobianPattern(userData);
    sparse = unknowns == nlsData->size && pattern && !(userData->analyticJacobian && userData->analyticJacobian->isRowEval);
    required = sparse ? pattern->nnz : equations * unknowns;
    assertStreamPrint(threadData, required <= scaling->jacobianCapacity, "Nonlinear scaling Jacobian work array is too small");

    scaleVariables(scaling, xReference, scaling->zWork, nlsData->size);
#ifndef OMC_EMCC
    MMC_TRY_INTERNAL(simulationJumpBuffer)
#endif
    if (nlsJacobian(userData, scaling->zWork, scaling->jacobianWork, sparse, NLS_JACOBIAN_AUTO) == 0) {
      failed = FALSE;
    }
#ifndef OMC_EMCC
    MMC_CATCH_INTERNAL(simulationJumpBuffer)
#endif
    if (failed) {
      warningStreamPrint(OMC_LOG_NLS, 0, "Could not evaluate the reference Jacobian; using nominal scaling only.");
      scaling->activeMethod = NLS_SCALING_NOMINAL;
      return;
    }

    for (row = 0; row < equations; row++) scaling->fScale[row] = fabs(scaling->fBase[row]);
    if (sparse) {
      for (column = 0; column < unknowns; column++) {
        for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
          row = pattern->index[nz];
          scaling->fScale[row] = fmax(scaling->fScale[row], fabs(scaling->jacobianWork[nz]));
        }
      }
    } else {
      for (column = 0; column < unknowns; column++) {
        for (row = 0; row < equations; row++) {
          scaling->fScale[row] = fmax(scaling->fScale[row], fabs(scaling->jacobianWork[column * equations + row]));
        }
      }
    }
    for (row = 0; row < equations; row++) {
      const modelica_real characteristic = scaling->fScale[row];
      if (!isfinite(characteristic)) {
        warningStreamPrint(OMC_LOG_NLS, 0, "Non-finite characteristic for nonlinear residual row %d; using nominal scaling only.",
                           (int) row + 1);
        scaling->activeMethod = NLS_SCALING_NOMINAL;
        for (row = 0; row < scaling->size; row++) scaling->fScale[row] = 1.0;
        return;
      }
      if (characteristic == 0.0) {
        /* A zero residual with a zero derivative is a redundant local equation. */
        scaling->fScale[row] = 1.0;
        infoStreamPrint(OMC_LOG_NLS_V, 0, "Nonlinear residual row %d is locally constant zero; using unit row scale.",
                        (int) row + 1);
      } else {
        scaling->fScale[row] = characteristic < 1.0 / DBL_MAX ? DBL_MAX : 1.0 / characteristic;
      }
    }
    return;
  }

  throwStreamPrint(threadData, "Unknown nonlinear scaling method %d", scaling->activeMethod);
}
