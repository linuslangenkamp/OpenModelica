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

#include "hessian_util.h"
#include "jacobian_util.h"

#include <stdlib.h>
#include <string.h>

LOWER_TRIANGULAR_SPARSITY* allocLowerTriangularSparsity(unsigned int size, unsigned int nnz)
{
  LOWER_TRIANGULAR_SPARSITY *sparsity = (LOWER_TRIANGULAR_SPARSITY*)calloc(1, sizeof(LOWER_TRIANGULAR_SPARSITY));
  if (sparsity == NULL)
  {
    return NULL;
  }

  sparsity->size = size;
  sparsity->nnz = nnz;
  sparsity->leadindex = (unsigned int*)calloc(size + 1, sizeof(unsigned int));
  sparsity->index = (unsigned int*)calloc((nnz > 0 ? nnz : 1), sizeof(unsigned int));

  if (sparsity->leadindex == NULL || sparsity->index == NULL)
  {
    freeLowerTriangularSparsity(sparsity);
    return NULL;
  }

  return sparsity;
}

void freeLowerTriangularSparsity(LOWER_TRIANGULAR_SPARSITY *sparsity)
{
  if (sparsity == NULL)
  {
    return;
  }

  free(sparsity->leadindex);
  free(sparsity->index);
  free(sparsity->colorLeadindex);
  free(sparsity->colorIndex);
  free(sparsity);
}

int initHessian(DATA *data, threadData_t *threadData, const HESSIAN_INFO *info, HESSIAN *hessian)
{
  if (info == NULL || hessian == NULL || info->hvp == NULL || info->sparsity == NULL)
  {
    return 1;
  }

  memset(hessian, 0, sizeof(HESSIAN));
  hessian->info = info;
  hessian->sizeRows = info->sizeRows;
  hessian->sizeCols = info->sizeCols;
  hessian->sizeTmpVars = info->sizeTmpVars;
  hessian->sparsity = info->sparsity(data, threadData);

  if (hessian->sparsity == NULL)
  {
    memset(hessian, 0, sizeof(HESSIAN));
    return 1;
  }
  if (hessian->sizeCols > 0 && (hessian->sparsity->maxColors == 0 || hessian->sparsity->colorLeadindex == NULL || hessian->sparsity->colorIndex == NULL))
  {
    freeHessian(hessian);
    return 1;
  }

  hessian->lambdaVars = (modelica_real*)calloc((hessian->sizeRows > 0 ? hessian->sizeRows : 1), sizeof(modelica_real));
  hessian->directionVars = (modelica_real*)calloc((hessian->sizeCols > 0 ? hessian->sizeCols : 1), sizeof(modelica_real));
  hessian->tmpVars = (modelica_real*)calloc((hessian->sizeTmpVars > 0 ? hessian->sizeTmpVars : 1), sizeof(modelica_real));
  hessian->resultVars = (modelica_real*)calloc((hessian->sizeCols > 0 ? hessian->sizeCols : 1), sizeof(modelica_real));

  if (hessian->lambdaVars == NULL || hessian->directionVars == NULL || hessian->tmpVars == NULL || hessian->resultVars == NULL)
  {
    freeHessian(hessian);
    return 1;
  }

  return 0;
}

void freeHessian(HESSIAN *hessian)
{
  if (hessian == NULL)
  {
    return;
  }

  free(hessian->lambdaVars);
  free(hessian->directionVars);
  free(hessian->tmpVars);
  free(hessian->resultVars);
  freeLowerTriangularSparsity(hessian->sparsity);
  memset(hessian, 0, sizeof(HESSIAN));
}

void resetHessianWork(HESSIAN *hessian)
{
  if (hessian == NULL)
  {
    return;
  }

  if (hessian->resultVars != NULL && hessian->sizeCols > 0)
  {
    memset(hessian->resultVars, 0, hessian->sizeCols * sizeof(modelica_real));
  }
  if (hessian->tmpVars != NULL && hessian->sizeTmpVars > 0)
  {
    memset(hessian->tmpVars, 0, hessian->sizeTmpVars * sizeof(modelica_real));
  }
}

int evalHessianHVP(DATA *data, threadData_t *threadData, HESSIAN *hessian)
{
  if (hessian == NULL || hessian->info == NULL || hessian->info->hvp == NULL)
  {
    return 1;
  }

  resetHessianWork(hessian);
  return hessian->info->hvp(data, threadData, hessian);
}

int evalHessian(DATA *data, threadData_t *threadData, HESSIAN *hessian, modelica_real *values)
{
  unsigned int color, columnIndex, column, nz, row;
  LOWER_TRIANGULAR_SPARSITY *sparsity;
  int status;

  if (hessian == NULL || values == NULL || hessian->sparsity == NULL)
  {
    return 1;
  }

  sparsity = hessian->sparsity;
  if (sparsity->maxColors > 0 && (sparsity->colorLeadindex == NULL || sparsity->colorIndex == NULL))
  {
    return 1;
  }

  memset(values, 0, sparsity->nnz * sizeof(modelica_real));

  if (hessian->directionVars != NULL && hessian->sizeCols > 0)
  {
    memset(hessian->directionVars, 0, hessian->sizeCols * sizeof(modelica_real));
  }

  for (color = 0; color < sparsity->maxColors; color++)
  {
    for (columnIndex = sparsity->colorLeadindex[color]; columnIndex < sparsity->colorLeadindex[color + 1]; columnIndex++)
    {
      column = sparsity->colorIndex[columnIndex];
      if (column < hessian->sizeCols)
      {
        hessian->directionVars[column] = 1.0;
      }
    }

    status = evalHessianHVP(data, threadData, hessian);
    if (status != 0)
    {
      return status;
    }

    for (columnIndex = sparsity->colorLeadindex[color]; columnIndex < sparsity->colorLeadindex[color + 1]; columnIndex++)
    {
      column = sparsity->colorIndex[columnIndex];
      if (column < hessian->sizeCols)
      {
        for (nz = sparsity->leadindex[column]; nz < sparsity->leadindex[column + 1]; nz++)
        {
          row = sparsity->index[nz];
          values[nz] = hessian->resultVars[row];
        }
        hessian->directionVars[column] = 0.0;
      }
    }
  }

  return 0;
}
