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
 */

#include "hessian_util.h"

#include <cstdlib>
#include <vector>

#ifdef OMC_HAVE_COLPACK
#ifdef TRUE
#undef TRUE
#endif

#ifdef FALSE
#undef FALSE
#endif

#include <ColPackHeaders.h>
#include <algorithm>
#include <set>
#endif

static void clearHessianColorGroups(LOWER_TRIANGULAR_SPARSITY *sparsity)
{
  if (sparsity == NULL)
  {
    return;
  }

  free(sparsity->colorLeadindex);
  free(sparsity->colorIndex);
  sparsity->colorLeadindex = NULL;
  sparsity->colorIndex = NULL;
  sparsity->maxColors = 0;
}

static void setHessianColorGroups(LOWER_TRIANGULAR_SPARSITY *sparsity, const std::vector<unsigned int> &columnColors, unsigned int maxColors)
{
  std::vector<unsigned int> positions;
  unsigned int col, color;

  if (sparsity == NULL)
  {
    return;
  }

  clearHessianColorGroups(sparsity);
  if (sparsity->size == 0 || maxColors == 0)
  {
    return;
  }

  sparsity->colorLeadindex = (unsigned int*)calloc(maxColors + 1, sizeof(unsigned int));
  sparsity->colorIndex = (unsigned int*)calloc(sparsity->size, sizeof(unsigned int));
  if (sparsity->colorLeadindex == NULL || sparsity->colorIndex == NULL)
  {
    clearHessianColorGroups(sparsity);
    return;
  }

  for (col = 0; col < sparsity->size && col < columnColors.size(); col++)
  {
    color = columnColors[col];
    if (color > 0 && color <= maxColors)
    {
      sparsity->colorLeadindex[color]++;
    }
  }

  sparsity->colorLeadindex[0] = 0;
  for (color = 0; color < maxColors; color++)
  {
    sparsity->colorLeadindex[color + 1] += sparsity->colorLeadindex[color];
  }

  positions.assign(sparsity->colorLeadindex, sparsity->colorLeadindex + maxColors);
  for (col = 0; col < sparsity->size && col < columnColors.size(); col++)
  {
    color = columnColors[col];
    if (color > 0 && color <= maxColors)
    {
      sparsity->colorIndex[positions[color - 1]++] = col;
    }
  }
  sparsity->maxColors = maxColors;
}

static void fallbackHessianColoring(LOWER_TRIANGULAR_SPARSITY *sparsity)
{
  std::vector<unsigned int> columnColors;
  unsigned int i;

  if (sparsity == NULL)
  {
    return;
  }

  columnColors.resize(sparsity->size);
  for (i = 0; i < sparsity->size; i++)
  {
    columnColors[i] = i + 1;
  }
  setHessianColorGroups(sparsity, columnColors, sparsity->size);
}

extern "C" void colorLowerTriangularSparsity(LOWER_TRIANGULAR_SPARSITY *sparsity)
{
#ifdef OMC_HAVE_COLPACK
  unsigned int col, nz, row, i, j;
  unsigned int maxColor = 0;
  std::vector<std::set<unsigned int> > adjacency;
  std::vector<unsigned int> columnColors;
  unsigned int **adolcPattern = NULL;
  unsigned int allocatedRows = 0;

  if (sparsity == NULL || sparsity->size == 0)
  {
    fallbackHessianColoring(sparsity);
    return;
  }

  try
  {
    adjacency.resize(sparsity->size);
    for (col = 0; col < sparsity->size; col++)
    {
      for (nz = sparsity->leadindex[col]; nz < sparsity->leadindex[col + 1]; nz++)
      {
        row = sparsity->index[nz];
        if (row < sparsity->size && row != col)
        {
          adjacency[col].insert(row);
          adjacency[row].insert(col);
        }
      }
    }

    adolcPattern = new unsigned int*[sparsity->size];
    for (i = 0; i < sparsity->size; i++)
    {
      adolcPattern[i] = new unsigned int[adjacency[i].size() + 1];
      allocatedRows++;
      adolcPattern[i][0] = static_cast<unsigned int>(adjacency[i].size());
      j = 1;
      for (std::set<unsigned int>::const_iterator it = adjacency[i].begin(); it != adjacency[i].end(); ++it)
      {
        adolcPattern[i][j++] = *it;
      }
    }

    ColPack::GraphColoringInterface coloring(SRC_MEM_ADOLC, adolcPattern, static_cast<int>(sparsity->size));
    coloring.Coloring("DISTANCE_TWO_LARGEST_FIRST", "DISTANCE_TWO");

    std::vector<int> colors;
    coloring.GetVertexColors(colors);
    if (colors.size() < sparsity->size)
    {
      throw 1;
    }

    columnColors.resize(sparsity->size);
    for (i = 0; i < sparsity->size; i++)
    {
      if (colors[i] < 0)
      {
        columnColors[i] = 0;
      }
      else
      {
        columnColors[i] = static_cast<unsigned int>(colors[i]) + 1;
        maxColor = std::max(maxColor, columnColors[i]);
      }
    }
    for (i = 0; i < sparsity->size; i++)
    {
      if (columnColors[i] == 0)
      {
        columnColors[i] = ++maxColor;
      }
    }
    setHessianColorGroups(sparsity, columnColors, maxColor);

    for (i = 0; i < allocatedRows; i++)
    {
      delete[] adolcPattern[i];
    }
    delete[] adolcPattern;
    return;
  }
  catch (...)
  {
    if (adolcPattern != NULL)
    {
      for (i = 0; i < allocatedRows; i++)
      {
        delete[] adolcPattern[i];
      }
      delete[] adolcPattern;
    }
    fallbackHessianColoring(sparsity);
    return;
  }
#else
  fallbackHessianColoring(sparsity);
#endif
}
