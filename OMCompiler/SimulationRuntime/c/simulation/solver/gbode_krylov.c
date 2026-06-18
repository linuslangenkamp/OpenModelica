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

#include "gbode_krylov.h"

#include <float.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

extern void daxpy_(const int *n,
                   const double *alpha,
                   const double *x, const int *incX,
                   double *y, const int *incY);

extern void dscal_(const int *n,
                   const double *alpha,
                   double *x, const int *incX);

extern double ddot_(const int *n,
                    const double *x, const int *incX,
                    const double *y, const int *incY);

extern double dnrm2_(const int *n,
                     const double *x, const int *incX);

struct GBODE_KRYLOV_WORK
{
  int size;
  int restart;
  double *rhs;
  double *x_base;
  double *x_candidate;
  double *residual;
  double *w;
  double *V;
  double *Z;
  double *H;
  double *cs;
  double *sn;
  double *g;
  double *y;
};

static const int INT_ONE = 1;
static const double DBL_ONE = 1.0;
static const double DBL_MINUS_ONE = -1.0;

static int gbodeKrylovMinInt(int a, int b)
{
  return a < b ? a : b;
}

static void gbodeKrylovInitStats(GBODE_KRYLOV_STATS *stats)
{
  if (stats)
  {
    stats->status = GBODE_KRYLOV_INVALID_INPUT;
    stats->iterations = 0;
    stats->restarts = 0;
    stats->matvecs = 0;
    stats->exactResiduals = 0;
    stats->initialResidual = 0.0;
    stats->finalResidual = 0.0;
    stats->estimatedResidual = 0.0;
    stats->targetResidual = 0.0;
  }
}

static int gbodeKrylovSolveUpper(const double *H,
                                 const double *g,
                                 double *y,
                                 int ldh,
                                 int active_cols)
{
  for (int i = 0; i < active_cols; i++)
  {
    y[i] = 0.0;
  }

  for (int i = active_cols - 1; i >= 0; i--)
  {
    double sum = g[i];
    for (int j = i + 1; j < active_cols; j++)
    {
      sum -= H[i + j * ldh] * y[j];
    }

    const double diag = H[i + i * ldh];
    if (fabs(diag) <= DBL_EPSILON)
    {
      return GBODE_KRYLOV_BREAKDOWN;
    }

    y[i] = sum / diag;
  }

  return GBODE_KRYLOV_SUCCESS;
}

static int gbodeKrylovUpdateCandidate(GBODE_KRYLOV_WORK *work, int ldh, int active_cols)
{
  int status = gbodeKrylovSolveUpper(work->H, work->g, work->y, ldh, active_cols);
  if (status != GBODE_KRYLOV_SUCCESS)
  {
    return status;
  }

  memcpy(work->x_candidate, work->x_base, work->size * sizeof(double));
  for (int k = 0; k < active_cols; k++)
  {
    daxpy_(&work->size, &work->y[k], &work->Z[k * work->size], &INT_ONE, work->x_candidate, &INT_ONE);
  }

  return GBODE_KRYLOV_SUCCESS;
}

static int gbodeKrylovComputeResidual(GBODE_KRYLOV_WORK *work,
                                      const GBODE_KRYLOV_CALLBACKS *callbacks,
                                      const double *x,
                                      GBODE_KRYLOV_STATS *stats,
                                      double *scaled_norm)
{
  int ret = callbacks->matvec(callbacks->userData, x, work->residual);
  if (ret != 0)
  {
    return GBODE_KRYLOV_MATVEC_FAILED;
  }
  if (stats)
  {
    stats->matvecs++;
    stats->exactResiduals++;
  }

  dscal_(&work->size, &DBL_MINUS_ONE, work->residual, &INT_ONE);
  daxpy_(&work->size, &DBL_ONE, work->rhs, &INT_ONE, work->residual, &INT_ONE);

  *scaled_norm = callbacks->norm(callbacks->userData, work->residual);
  return isfinite(*scaled_norm) ? GBODE_KRYLOV_SUCCESS : GBODE_KRYLOV_BREAKDOWN;
}

GBODE_KRYLOV_WORK *gbodeKrylovCreateReal(int size, int restart)
{
  if (size <= 0 || restart <= 0)
  {
    return NULL;
  }

  GBODE_KRYLOV_WORK *work = (GBODE_KRYLOV_WORK *) calloc(1, sizeof(GBODE_KRYLOV_WORK));
  if (!work)
  {
    return NULL;
  }

  work->size = size;
  work->restart = gbodeKrylovMinInt(size, restart);

  const int n = work->size;
  const int m = work->restart;
  work->rhs = (double *) malloc(n * sizeof(double));
  work->x_base = (double *) malloc(n * sizeof(double));
  work->x_candidate = (double *) malloc(n * sizeof(double));
  work->residual = (double *) malloc(n * sizeof(double));
  work->w = (double *) malloc(n * sizeof(double));
  work->V = (double *) malloc((m + 1) * n * sizeof(double));
  work->Z = (double *) malloc(m * n * sizeof(double));
  work->H = (double *) malloc((m + 1) * m * sizeof(double));
  work->cs = (double *) malloc(m * sizeof(double));
  work->sn = (double *) malloc(m * sizeof(double));
  work->g = (double *) malloc((m + 1) * sizeof(double));
  work->y = (double *) malloc(m * sizeof(double));

  if (!work->rhs || !work->x_base || !work->x_candidate || !work->residual || !work->w ||
      !work->V || !work->Z || !work->H || !work->cs || !work->sn || !work->g || !work->y)
  {
    gbodeKrylovFree(work);
    return NULL;
  }

  return work;
}

void gbodeKrylovFree(GBODE_KRYLOV_WORK *work)
{
  if (!work)
  {
    return;
  }

  free(work->rhs);
  free(work->x_base);
  free(work->x_candidate);
  free(work->residual);
  free(work->w);
  free(work->V);
  free(work->Z);
  free(work->H);
  free(work->cs);
  free(work->sn);
  free(work->g);
  free(work->y);
  free(work);
}

int gbodeKrylovGMRESSolveReal(GBODE_KRYLOV_WORK *work,
                              const GBODE_KRYLOV_CALLBACKS *callbacks,
                              const GBODE_KRYLOV_OPTIONS *options,
                              const double *rhs,
                              double *x,
                              GBODE_KRYLOV_STATS *stats)
{
  gbodeKrylovInitStats(stats);

  if (!work || !callbacks || !callbacks->matvec || !callbacks->norm || !options || !rhs || !x ||
      options->maxIterations <= 0 || options->linearTolerance < 0.0 || !isfinite(options->linearTolerance))
  {
    return GBODE_KRYLOV_INVALID_INPUT;
  }

  const int n = work->size;
  const int m = work->restart;
  const int ldh = m + 1;
  double max_relative_residual = options->maxRelativeResidual;
  if (!(max_relative_residual > 0.0 && max_relative_residual < 1.0))
  {
    max_relative_residual = 0.9;
  }

  memcpy(work->rhs, rhs, n * sizeof(double));
  memset(x, 0, n * sizeof(double));
  memcpy(work->residual, work->rhs, n * sizeof(double));

  double scaled_residual = callbacks->norm(callbacks->userData, work->residual);
  if (!isfinite(scaled_residual))
  {
    if (stats) stats->status = GBODE_KRYLOV_BREAKDOWN;
    return GBODE_KRYLOV_BREAKDOWN;
  }

  if (stats)
  {
    stats->initialResidual = scaled_residual;
    stats->finalResidual = scaled_residual;
    stats->estimatedResidual = scaled_residual;
  }

  if (scaled_residual <= DBL_EPSILON)
  {
    if (stats)
    {
      stats->status = GBODE_KRYLOV_SUCCESS;
      stats->targetResidual = options->linearTolerance;
    }
    return GBODE_KRYLOV_SUCCESS;
  }

  const double linear_tolerance = options->linearTolerance;
  if (stats)
  {
    stats->targetResidual = linear_tolerance;
  }

  int total_iterations = 0;
  int restart_count = 0;
  int status = GBODE_KRYLOV_SUCCESS;

  while (total_iterations < options->maxIterations)
  {
    const double beta = dnrm2_(&n, work->residual, &INT_ONE);
    if (beta <= DBL_EPSILON)
    {
      status = GBODE_KRYLOV_BREAKDOWN;
      break;
    }

    memcpy(work->x_base, x, n * sizeof(double));
    memset(work->H, 0, (m + 1) * m * sizeof(double));
    memset(work->cs, 0, m * sizeof(double));
    memset(work->sn, 0, m * sizeof(double));
    memset(work->g, 0, (m + 1) * sizeof(double));

    memcpy(work->V, work->residual, n * sizeof(double));
    const double beta_inv = 1.0 / beta;
    dscal_(&n, &beta_inv, work->V, &INT_ONE);
    work->g[0] = beta;

    const int inner_iterations = gbodeKrylovMinInt(m, options->maxIterations - total_iterations);
    const double restart_scaled_residual = scaled_residual;

    for (int j = 0; j < inner_iterations; j++)
    {
      double *vj = &work->V[j * n];
      double *zj = &work->Z[j * n];

      if (callbacks->preconditioner)
      {
        status = callbacks->preconditioner(callbacks->userData, vj, zj);
        if (status != 0)
        {
          status = GBODE_KRYLOV_MATVEC_FAILED;
          goto finish;
        }
      }
      else
      {
        memcpy(zj, vj, n * sizeof(double));
      }

      status = callbacks->matvec(callbacks->userData, zj, work->w);
      if (status != 0)
      {
        status = GBODE_KRYLOV_MATVEC_FAILED;
        goto finish;
      }
      if (stats) stats->matvecs++;

      for (int i = 0; i <= j; i++)
      {
        double *vi = &work->V[i * n];
        work->H[i + j * ldh] = ddot_(&n, vi, &INT_ONE, work->w, &INT_ONE);
        const double minus_h = -work->H[i + j * ldh];
        daxpy_(&n, &minus_h, vi, &INT_ONE, work->w, &INT_ONE);
      }

      const double next_norm = dnrm2_(&n, work->w, &INT_ONE);
      work->H[j + 1 + j * ldh] = next_norm;
      if (next_norm > DBL_EPSILON)
      {
        double *vnext = &work->V[(j + 1) * n];
        memcpy(vnext, work->w, n * sizeof(double));
        const double inv_next_norm = 1.0 / next_norm;
        dscal_(&n, &inv_next_norm, vnext, &INT_ONE);
      }

      for (int i = 0; i < j; i++)
      {
        const double h0 = work->H[i + j * ldh];
        const double h1 = work->H[i + 1 + j * ldh];
        work->H[i + j * ldh] = work->cs[i] * h0 + work->sn[i] * h1;
        work->H[i + 1 + j * ldh] = -work->sn[i] * h0 + work->cs[i] * h1;
      }

      const double h0 = work->H[j + j * ldh];
      const double h1 = work->H[j + 1 + j * ldh];
      const double denom = hypot(h0, h1);
      if (denom <= DBL_EPSILON)
      {
        status = GBODE_KRYLOV_BREAKDOWN;
        goto finish;
      }

      work->cs[j] = h0 / denom;
      work->sn[j] = h1 / denom;
      work->H[j + j * ldh] = denom;
      work->H[j + 1 + j * ldh] = 0.0;

      const double gj = work->g[j];
      work->g[j] = work->cs[j] * gj;
      work->g[j + 1] = -work->sn[j] * gj;

      total_iterations++;
      const double estimated_scaled_residual = restart_scaled_residual * fabs(work->g[j + 1]) / beta;
      if (stats)
      {
        stats->iterations = total_iterations;
        stats->finalResidual = estimated_scaled_residual;
        stats->estimatedResidual = estimated_scaled_residual;
      }

      if (estimated_scaled_residual <= linear_tolerance || next_norm <= DBL_EPSILON || j + 1 == inner_iterations)
      {
        status = gbodeKrylovUpdateCandidate(work, ldh, j + 1);
        if (status != GBODE_KRYLOV_SUCCESS)
        {
          goto finish;
        }

        status = gbodeKrylovComputeResidual(work, callbacks, work->x_candidate, stats, &scaled_residual);
        if (status != GBODE_KRYLOV_SUCCESS)
        {
          goto finish;
        }

        if (stats)
        {
          stats->finalResidual = scaled_residual;
        }

        memcpy(x, work->x_candidate, n * sizeof(double));
        if (scaled_residual <= linear_tolerance)
        {
          status = GBODE_KRYLOV_SUCCESS;
          goto finish;
        }

        if (next_norm <= DBL_EPSILON)
        {
          status = GBODE_KRYLOV_BREAKDOWN;
          goto finish;
        }

        restart_count++;
        if (stats)
        {
          stats->restarts = restart_count;
        }
        break;
      }
    }
  }

  status = GBODE_KRYLOV_MAX_ITERATIONS;

finish:
  if (stats)
  {
    stats->status = status;
  }
  return status;
}
