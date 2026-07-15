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

struct LOWER_TRIANGULAR_SPARSITY
{
  unsigned int size;
  unsigned int nnz;
  unsigned int *leadindex;
  unsigned int *index;
  unsigned int maxColors;
  unsigned int *colorLeadindex;
  unsigned int *colorIndex;
};

typedef struct HESSIAN_INFO
{
  const char *name;
  unsigned int sizeRows;
  unsigned int sizeCols;
  unsigned int sizeTmpVars;
  hessian_sparsity_func_ptr sparsity;
  hessian_hvp_func_ptr hvp;
} HESSIAN_INFO;

struct HESSIAN
{
  const HESSIAN_INFO *info;
  unsigned int sizeRows;
  unsigned int sizeCols;
  unsigned int sizeTmpVars;
  LOWER_TRIANGULAR_SPARSITY *sparsity;
  modelica_real *lambdaVars;
  modelica_real *directionVars;
  modelica_real *tmpVars;
  modelica_real *resultVars;
};

LOWER_TRIANGULAR_SPARSITY* allocLowerTriangularSparsity(unsigned int size, unsigned int nnz);
void freeLowerTriangularSparsity(LOWER_TRIANGULAR_SPARSITY *sparsity);
int initHessian(DATA *data, threadData_t *threadData, const HESSIAN_INFO *info, HESSIAN *hessian);
void freeHessian(HESSIAN *hessian);
void resetHessianWork(HESSIAN *hessian);
int evalHessianHVP(DATA *data, threadData_t *threadData, HESSIAN *hessian);
int evalHessian(DATA *data, threadData_t *threadData, HESSIAN *hessian, modelica_real *values);
void colorLowerTriangularSparsity(LOWER_TRIANGULAR_SPARSITY *sparsity);

#ifdef __cplusplus
}
#endif

#endif
