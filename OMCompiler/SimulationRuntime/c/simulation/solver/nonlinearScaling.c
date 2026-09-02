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
#include "nonlinearSystem.h"

static const size_t NLS_SCALING_VECTOR_COUNT = 13;
static const modelica_real NLS_RESIDUAL_SCALE_FLOOR = 1e-12;

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

  unscaleVariables(scaling, z, scaling->xPhysical, nlsData->size);
  if (nlsData->strictTearingFunctionCall) {
    assertStreamPrint(userData->threadData, nlsData->residualFuncConstraints != NULL,
                      "Nonlinear system with dynamic tearing has no causal residual function");
    result = nlsData->residualFuncConstraints(&residualUserData, scaling->xPhysical, g, iflag);
  } else {
    nlsData->residualFunc(&residualUserData, scaling->xPhysical, g, iflag);
  }
  if (result) return result;
  for (i = 0; i < scaling->equations; i++) g[i] *= scaling->fScale[i];
  return result;
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

static inline double finiteDifferenceStep(const NONLINEAR_SYSTEM_DATA *nlsData, const NLS_SCALING_DATA *scaling,
                                          const modelica_real *z, modelica_integer column, double delta)
{
  double step = delta * (fabs(z[column]) + 1.0);
  if (column < nlsData->size && isfinite(scaling->zMax[column]) && z[column] + step >= scaling->zMax[column]) step = -step;
  return step;
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
  const double delta = sqrt(20.0 * DBL_EPSILON);

  assertStreamPrint(userData->threadData, scaling != NULL, "Numerical nonlinear Jacobian requires scaling work memory");
  if (z != scaling->zWork) {
    memcpy(scaling->zWork, z, nlsData->size * sizeof(modelica_real));
  }
  result = nlsResidual(userData, scaling->zWork, scaling->fBase, &iflag);
  if (result) return result;

  if (!sparse) {
    for (column = 0; column < scaling->unknowns; column++) {
      const double zBase = scaling->zWork[column];
      const double step = finiteDifferenceStep(nlsData, scaling, scaling->zWork, column, delta);
      scaling->zWork[column] += step;
      result = nlsResidual(userData, scaling->zWork, scaling->fWork, &iflag);
      if (result) {
        scaling->zWork[column] = zBase;
        nlsResidual(userData, scaling->zWork, scaling->fWork, &iflag);
        return result;
      }
      for (row = 0; row < scaling->equations; row++) {
        jacobian[column * scaling->equations + row] = (scaling->fWork[row] - scaling->fBase[row]) / step;
      }
      scaling->zWork[column] = zBase;
    }
  } else {
    assertStreamPrint(userData->threadData, pattern != NULL, "Sparse numerical nonlinear Jacobian has no sparsity pattern");
    for (color = 0; color < (modelica_integer) pattern->maxColors; color++) {
      for (column = 0; column < scaling->unknowns; column++) {
        if ((modelica_integer) pattern->colorCols[column] - 1 == color) {
          scaling->fdStep[column] = finiteDifferenceStep(nlsData, scaling, scaling->zWork, column, delta);
          scaling->zWork[column] += scaling->fdStep[column];
        }
      }
      result = nlsResidual(userData, scaling->zWork, scaling->fWork, &iflag);
      for (column = 0; column < scaling->unknowns; column++) {
        if ((modelica_integer) pattern->colorCols[column] - 1 == color) {
          if (!result) {
            for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
              row = pattern->index[nz];
              jacobian[nz] = (scaling->fWork[row] - scaling->fBase[row]) / scaling->fdStep[column];
            }
          }
          scaling->zWork[column] -= scaling->fdStep[column];
        }
      }
      if (result) {
        nlsResidual(userData, scaling->zWork, scaling->fWork, &iflag);
        return result;
      }
    }
  }

  /* Restore generated variables and inner equations to z. */
  return nlsResidual(userData, scaling->zWork, scaling->fWork, &iflag);
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
    modelica_integer column;
    unsigned int nz;

    const int result = nlsResidual(userData, z, scaling->fBase, &iflag);
    if (result) return result;
    evalJacobian(userData->data, userData->threadData, analytic, NULL, values, gatherRows || !sparse);
    scaleAnalyticJacobian(userData, values, gatherRows || trimColumns ? FALSE : sparse);
    if (gatherRows) {
      for (column = 0; column < scaling->unknowns; column++) {
        for (nz = pattern->leadindex[column]; nz < pattern->leadindex[column + 1]; nz++) {
          jacobian[nz] = values[column * scaling->equations + pattern->index[nz]];
        }
      }
    } else if (trimColumns && values != jacobian) {
      memcpy(jacobian, values, scaling->equations * scaling->unknowns * sizeof(modelica_real));
    }
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

  for (column = 0; column < unknowns; column++) {
    double scale = 1.0;
    if (scaling->activeMethod != NLS_SCALING_IDENTITY && column < nlsData->size) {
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

    for (row = 0; row < equations; row++) {
      scaling->fScale[row] = NLS_RESIDUAL_SCALE_FLOOR;
    }
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
      scaling->fScale[row] = isfinite(scaling->fScale[row]) ? 1.0 / scaling->fScale[row] : 1.0;
    }
    return;
  }

  throwStreamPrint(threadData, "Unknown nonlinear scaling method %d", scaling->activeMethod);
}
