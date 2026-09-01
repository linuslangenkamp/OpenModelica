/*
 * This file belongs to the OpenModelica Run-Time System
 *
 * Copyright (c) 1998-2026, Open Source Modelica Consortium (OSMC)
 *
 * Distributed under the OSMC Public License (OSMC-PL), BSD 3-Clause, or
 * GNU AGPL version 3.
 */

#ifndef OMC_NONLINEAR_SCALING_H
#define OMC_NONLINEAR_SCALING_H

#include "../../simulation_data.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef enum NLS_SCALING_METHOD {
  NLS_SCALING_IDENTITY = 0,
  NLS_SCALING_NOMINAL,
  NLS_SCALING_RESIDUAL,
  NLS_SCALING_JACOBIAN
} NLS_SCALING_METHOD;

typedef enum NLS_JACOBIAN_METHOD {
  NLS_JACOBIAN_AUTO = 0,
  NLS_JACOBIAN_NUMERICAL
} NLS_JACOBIAN_METHOD;

typedef struct NLS_CONVERGENCE_DATA {
  modelica_real fTol;
  modelica_real xTol;
  modelica_real relaxedFTol;
  modelica_real residualNorm;
  modelica_real stepNorm;
} NLS_CONVERGENCE_DATA;

struct NLS_SCALING_DATA {
  /* Solver-coordinate view of NONLINEAR_SYSTEM_DATA. */
  modelica_real *z;
  modelica_real *zOld;
  modelica_real *zExtrapolation;
  modelica_real *zNominal;
  modelica_real *zMin;
  modelica_real *zMax;
  modelica_real *xScale;
  modelica_real *fScale;

  /* Work memory owned by the common residual and Jacobian callbacks. */
  modelica_real *xPhysical;
  modelica_real *zWork;
  modelica_real *fWork;
  modelica_real *fBase;
  modelica_real *fdStep;
  modelica_real *jacobianWork;

  modelica_integer size;
  modelica_integer equations;
  modelica_integer unknowns;
  size_t jacobianCapacity;
  NLS_SCALING_METHOD method;
  NLS_SCALING_METHOD activeMethod;
  NLS_CONVERGENCE_DATA convergence;
  modelica_boolean prepared;
};

void nlsScalingAllocate(NONLINEAR_SYSTEM_DATA *nlsData, const JACOBIAN *analyticJacobian);
void nlsScalingFree(NONLINEAR_SYSTEM_DATA *nlsData);
void nlsScalingSetMethod(NONLINEAR_SYSTEM_DATA *nlsData, NLS_SCALING_METHOD method);
void nlsScalingPrepare(NLS_USERDATA *userData, const modelica_real *xReference, modelica_integer equations, modelica_integer unknowns);
void nlsScalingFinish(NONLINEAR_SYSTEM_DATA *nlsData);
modelica_real nlsScalingPhysicalX(const NONLINEAR_SYSTEM_DATA *nlsData, modelica_integer index, modelica_real z);
modelica_real nlsScalingPhysicalResidual(const NONLINEAR_SYSTEM_DATA *nlsData, modelica_integer index, modelica_real g);
modelica_real nlsMaxNorm(const modelica_real *values, modelica_integer size);
modelica_real nlsRelativeStepNorm(const modelica_real *z, const modelica_real *zPrevious, modelica_integer size);
NLS_SOLVER_STATUS nlsValidateCandidate(NLS_USERDATA *userData, const modelica_real *z,
                                      const modelica_real *zPrevious, modelica_boolean stepConverged,
                                      const char *solverName);

int nlsResidual(NLS_USERDATA *userData, const modelica_real *z, modelica_real *g, const int *iflag);
int nlsJacobian(NLS_USERDATA *userData, const modelica_real *z, modelica_real *jacobian, modelica_boolean sparse,
                NLS_JACOBIAN_METHOD method);

const SPARSE_PATTERN *nlsJacobianPattern(const NLS_USERDATA *userData);

#ifdef __cplusplus
}
#endif

#endif
