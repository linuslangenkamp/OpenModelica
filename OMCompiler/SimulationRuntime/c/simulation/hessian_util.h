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

/*! File hessian_util.h
 */

#ifndef OMC_HESSIAN_UTIL_H
#define OMC_HESSIAN_UTIL_H

#include "jacobian_util.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct HESSIAN HESSIAN;
typedef struct LOWER_TRIANGULAR_SPARSITY LOWER_TRIANGULAR_SPARSITY;

typedef LOWER_TRIANGULAR_SPARSITY* (*hessian_sparsity_func_ptr)(DATA *data, threadData_t *threadData);
typedef int (*hessian_hvp_func_ptr)(DATA *data, threadData_t *threadData, HESSIAN *hessian);

/*! Lower-triangular Hessian sparsity in CSC form.
 *  Optional color arrays group columns for compressed HVP evaluation. */
struct LOWER_TRIANGULAR_SPARSITY
{
  unsigned int size;            /*!< Number of Hessian rows/columns. */
  unsigned int nnz;             /*!< Number of stored lower-triangular entries. */
  unsigned int *leadindex;      /*!< Column pointer array of length size + 1. */
  unsigned int *index;          /*!< Row indices for stored entries. */
  unsigned int maxColors;       /*!< Number of color groups. */
  unsigned int *colorLeadindex; /*!< Color pointer array of length maxColors + 1. */
  unsigned int *colorIndex;     /*!< Column indices grouped by color. */
};

/*! Generated static information for one Hessian callback.
 *  The generated model owns the function pointers; runtime owns work arrays. */
typedef struct HESSIAN_INFO
{
  const char *name;                    /*!< Unique generated Hessian name. */
  unsigned int sizeRows;               /*!< Number of lambda seed variables. */
  unsigned int sizeCols;               /*!< Number of direction/result variables. */
  unsigned int sizeTmpVars;            /*!< Number of temporary work variables. */
  hessian_sparsity_func_ptr sparsity;  /*!< Generated sparsity allocator. */
  hessian_hvp_func_ptr hvp;            /*!< Generated Hessian-vector product callback. */
} HESSIAN_INFO;

/*! Runtime work object for one Hessian evaluation.
 *  Holds seed vectors, temporaries, results and generated sparsity. */
struct HESSIAN
{
  const HESSIAN_INFO *info;             /*!< Static generated Hessian metadata. */
  unsigned int sizeRows;                /*!< Number of lambda seed variables. */
  unsigned int sizeCols;                /*!< Number of direction/result variables. */
  unsigned int sizeTmpVars;             /*!< Number of temporary work variables. */
  LOWER_TRIANGULAR_SPARSITY *sparsity;  /*!< Lower-triangular sparsity and coloring. */
  modelica_real *lambdaVars;            /*!< Reverse seed vector lambda. */
  modelica_real *directionVars;         /*!< Forward direction vector v. */
  modelica_real *tmpVars;               /*!< Temporary work vector. */
  modelica_real *resultVars;            /*!< HVP result vector h. */
};

/*! Allocate lower-triangular sparsity storage.
 *  The returned object must be released with freeLowerTriangularSparsity. */
LOWER_TRIANGULAR_SPARSITY* allocLowerTriangularSparsity(unsigned int size, unsigned int nnz);

/*! Free lower-triangular sparsity storage.
 *  Safe to call with NULL. */
void freeLowerTriangularSparsity(LOWER_TRIANGULAR_SPARSITY *sparsity);

/*! Initialize runtime work arrays for one Hessian.
 *  Also creates and colors the generated lower-triangular sparsity. */
int initHessian(DATA *data, threadData_t *threadData, const HESSIAN_INFO *info, HESSIAN *hessian);

/*! Free all work arrays owned by a HESSIAN object.
 *  Resets the object to zero after releasing memory. */
void freeHessian(HESSIAN *hessian);

/*! Clear mutable HVP work arrays before one callback evaluation.
 *  Lambda and direction seeds are intentionally preserved. */
void resetHessianWork(HESSIAN *hessian);

/*! Evaluate one Hessian-vector product with current seeds.
 *  The generated callback writes hessian->resultVars. */
int evalHessianHVP(DATA *data, threadData_t *threadData, HESSIAN *hessian);

/*! Evaluate the stored lower-triangular Hessian by coloring.
 *  Values are written in sparsity->index/leadindex order. */
int evalHessian(DATA *data, threadData_t *threadData, HESSIAN *hessian, modelica_real *values);

/*! Compute color groups for a lower-triangular sparsity pattern.
 *  Uses ColPack when available and a safe one-column fallback otherwise. */
void colorLowerTriangularSparsity(LOWER_TRIANGULAR_SPARSITY *sparsity);

#ifdef __cplusplus
}
#endif

#endif
