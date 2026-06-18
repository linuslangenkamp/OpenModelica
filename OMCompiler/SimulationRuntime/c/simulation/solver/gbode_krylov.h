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
 */

#ifndef GBODE_KRYLOV_H
#define GBODE_KRYLOV_H

#ifdef __cplusplus
extern "C" {
#endif

typedef int (*gbode_krylov_matvec_func)(void *userData, const double *x, double *y);
typedef int (*gbode_krylov_precond_func)(void *userData, const double *x, double *y);
typedef double (*gbode_krylov_norm_func)(void *userData, const double *x);

typedef struct GBODE_KRYLOV_WORK GBODE_KRYLOV_WORK;

typedef struct GBODE_KRYLOV_CALLBACKS
{
  void *userData;
  gbode_krylov_matvec_func matvec;
  gbode_krylov_precond_func preconditioner;
  gbode_krylov_norm_func norm;
} GBODE_KRYLOV_CALLBACKS;

typedef struct GBODE_KRYLOV_OPTIONS
{
  int maxIterations;
  double linearTolerance;
  double maxRelativeResidual;
} GBODE_KRYLOV_OPTIONS;

typedef struct GBODE_KRYLOV_STATS
{
  int status;
  int iterations;
  int restarts;
  int matvecs;
  int exactResiduals;
  double initialResidual;
  double finalResidual;
  double estimatedResidual;
  double targetResidual;
} GBODE_KRYLOV_STATS;

enum GBODE_KRYLOV_STATUS
{
  GBODE_KRYLOV_SUCCESS = 0,
  GBODE_KRYLOV_MAX_ITERATIONS = 1,
  GBODE_KRYLOV_INVALID_INPUT = -1,
  GBODE_KRYLOV_MATVEC_FAILED = -2,
  GBODE_KRYLOV_BREAKDOWN = -3
};

GBODE_KRYLOV_WORK *gbodeKrylovCreateReal(int size, int restart);
void gbodeKrylovFree(GBODE_KRYLOV_WORK *work);

int gbodeKrylovGMRESSolveReal(GBODE_KRYLOV_WORK *work,
                              const GBODE_KRYLOV_CALLBACKS *callbacks,
                              const GBODE_KRYLOV_OPTIONS *options,
                              const double *rhs,
                              /* output only; the GMRES initial guess is zero */
                              double *x,
                              GBODE_KRYLOV_STATS *stats);

#ifdef __cplusplus
}
#endif

#endif /* GBODE_KRYLOV_H */
