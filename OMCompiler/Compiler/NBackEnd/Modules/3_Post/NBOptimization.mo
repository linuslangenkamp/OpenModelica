/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2026, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF AGPL VERSION 3 LICENSE OR
 * THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.8.
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
 * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GNU AGPL
 * VERSION 3, ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the OSMC (Open Source Modelica Consortium)
 * Public License (OSMC-PL) are obtained from OSMC, either from the above
 * address, from the URLs:
 * http://www.openmodelica.org or
 * https://github.com/OpenModelica/ or
 * http://www.ida.liu.se/projects/OpenModelica,
 * and in the OpenModelica distribution.
 *
 * GNU AGPL version 3 is obtained from:
 * https://www.gnu.org/licenses/licenses.html#GPL
 *
 * This program is distributed WITHOUT ANY WARRANTY; without
 * even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

encapsulated package NBOptimization
"file:        NBOptimization.mo
 package:     NBOptimization
 description: New-backend dynamic optimization artifact construction.
              This module owns GDOP-specific function-row and differentiation
              variable selection. It delegates derivative construction to the
              shared Jacobian/AD infrastructure.
"

public
  import BackendDAE = NBackendDAE;
  import Module = NBModule;
  import NBVariable;

protected
  // OF imports
  import Absyn.Path;

  // NF imports
  import ComponentRef = NFComponentRef;
  import NFFunction.Function;
  import Variable = NFVariable;

  // Backend imports
  import Adjacency = NBAdjacency;
  import BJacobian = NBJacobian;
  import BVariable = NBVariable;
  import Hessian = NBHessian;
  import Jacobian = NBackendDAE.BackendDAE;
  import NBEquation.{EquationPointers, EqData};
  import NBJacobian.JacobianType;
  import Partition = NBPartition;
  import StrongComponent = NBStrongComponent;
  import NBVariable.VarData;
  import NBVariable.VariablePointers;

  // Util imports
  import Error;
  import Flags;
  import StringUtil;
  import UnorderedMap;
  import UnorderedSet;
  import Util;

  type CrefLst = list<ComponentRef>;

public
  function main
    "Create optional GDOP artifacts for MOO after the standard Jacobian pass."
    extends Module.wrapper;
    input NBPartition.Kind kind;
  protected
    constant Module.jacobianInterface func = BJacobian.getModule();
    VariablePointers knowns;
    list<BackendDAE> optParts = {};
    list<BackendDAE> eventOptParts = {};
    BackendDAE.OptimizationFormulation formulation;
    list<Partition.Partition> parts;
    Option<list<Partition.Partition>> daeParts;
    Pointer<Integer> optIndex = Pointer.create(1);
  algorithm
    if not enabled() then
      return;
    end if;

    bdae := match bdae
      case BackendDAE.MAIN(varData = BVariable.VAR_DATA_SIM(knowns = knowns))
        algorithm
          if Flags.isSet(Flags.JAC_DUMP) then
            print(StringUtil.headline_1("[symjacdump] Creating optimization artifacts:") + "\n");
          end if;

          if kind == NBPartition.Kind.DAE and isSome(bdae.dae) then
            formulation := BackendDAE.OptimizationFormulation.DAE;
            daeParts := bdae.dae;
            (daeParts, optParts) := applyToOptionalPartitions(daeParts, knowns, formulation, func, bdae.funcMap, optIndex);
            bdae.dae := daeParts;
          else
            formulation := BackendDAE.OptimizationFormulation.ODE;
            parts := bdae.ode;
            (parts, optParts) := applyToPartitions(parts, knowns, formulation, func, bdae.funcMap, optIndex);
            bdae.ode := parts;
            parts := bdae.ode_event;
            (parts, eventOptParts) := applyToPartitions(parts, knowns, formulation, func, bdae.funcMap, optIndex);
            bdae.ode_event := parts;
            for optPart in listReverse(optParts) loop
              eventOptParts := optPart :: eventOptParts;
            end for;
            optParts := eventOptParts;
          end if;

          bdae.optimizationData := SOME(BackendDAE.OPTIMIZATION_DATA(
            problem     = BackendDAE.OptimizationProblem.GDOP,
            formulation = formulation,
            partitions  = optParts
          ));
      then bdae;

      else bdae;
    end match;
  end main;

protected
  function enabled
    output Boolean b;
  algorithm
    b := Flags.getConfigBool(Flags.MOO_DYNAMIC_OPTIMIZATION) or Flags.getConfigBool(Flags.MOO_GDOP);
  end enabled;

  function applyToOptionalPartitions
    input output Option<list<Partition.Partition>> partitions;
    input VariablePointers knowns;
    input BackendDAE.OptimizationFormulation formulation;
    input Module.jacobianInterface func;
    input UnorderedMap<Path, Function> funcMap;
    input Pointer<Integer> optIndex;
    output list<BackendDAE> optParts = {};
  protected
    list<Partition.Partition> parts;
  algorithm
    if isSome(partitions) then
      parts := Util.getOption(partitions);
      (parts, optParts) := applyToPartitions(parts, knowns, formulation, func, funcMap, optIndex);
      partitions := SOME(parts);
    end if;
  end applyToOptionalPartitions;

  function applyToPartitions
    input output list<Partition.Partition> partitions;
    input VariablePointers knowns;
    input BackendDAE.OptimizationFormulation formulation;
    input Module.jacobianInterface func;
    input UnorderedMap<Path, Function> funcMap;
    input Pointer<Integer> optIndex;
    output list<BackendDAE> optParts = {};
  protected
    Partition.Partition part;
    Option<BackendDAE> optPart;
    list<Partition.Partition> newParts = {};
  algorithm
    for p in partitions loop
      (part, optPart) := partOptimization(p, knowns, formulation, func, funcMap, optIndex);
      newParts := part :: newParts;
      if isSome(optPart) then
        optParts := Util.getOption(optPart) :: optParts;
      end if;
    end for;

    partitions := listReverse(newParts);
    optParts := listReverse(optParts);
  end applyToPartitions;

  function partOptimization
    input output Partition.Partition part;
    input VariablePointers allKnowns;
    input BackendDAE.OptimizationFormulation formulation;
    input Module.jacobianInterface func;
    input UnorderedMap<Path, Function> funcMap;
    input Pointer<Integer> optIndex;
    output Option<BackendDAE> optPart = NONE();
  protected
    constant Boolean staticAsContinuous = true;
    VariablePointers differentiationVars, lfgFunctionVars, mrfFunctionVars, r0FunctionVars, innerVars;
    Option<Jacobian> lfgJacobian, mrfJacobian, r0Jacobian;
    Option<Jacobian> lfgHessian, mrfHessian, r0Hessian;
    String suffix, name, lfgName, mrfName, r0Name;
  algorithm
    if not Partition.Partition.isODEorDAE(part) then
      return;
    end if;

    differentiationVars := getDifferentiationVars(part, allKnowns, formulation);
    lfgFunctionVars := VariablePointers.fromList(getLfgFunctionVars(part, formulation), part.unknowns.scalarized);
    mrfFunctionVars := VariablePointers.fromList(getMrfFunctionVars(part), part.unknowns.scalarized);
    r0FunctionVars  := VariablePointers.fromList(getR0FunctionVars(part),  part.unknowns.scalarized);
    innerVars := getInnerVars(part, differentiationVars, lfgFunctionVars, mrfFunctionVars, r0FunctionVars);
    suffix := intString(Pointer.access(optIndex));
    Pointer.update(optIndex, Pointer.access(optIndex) + 1);
    name := "OPT_" + suffix;
    lfgName := "OPT_LFG_" + suffix;
    mrfName := "OPT_MRF_" + suffix;
    r0Name  := "OPT_R0_" + suffix;

    lfgJacobian := createJacobian(
      lfgName, JacobianType.OPT_LFG, lfgFunctionVars, differentiationVars,
      BVariable.isLfgVariable, part, func, funcMap, staticAsContinuous);

    mrfJacobian := createJacobian(
      mrfName, JacobianType.OPT_MRF, mrfFunctionVars, differentiationVars,
      BVariable.isMrfVariable, part, func, funcMap, staticAsContinuous);

    r0Jacobian := createJacobian(
      r0Name, JacobianType.OPT_R0, r0FunctionVars, differentiationVars,
      BVariable.isR0Variable, part, func, funcMap, staticAsContinuous);

    lfgHessian := createHessian(
      lfgName, JacobianType.OPT_LFG, lfgFunctionVars, differentiationVars,
      BVariable.isLfgVariable, part, funcMap, formulation, staticAsContinuous);

    mrfHessian := createHessian(
      mrfName, JacobianType.OPT_MRF, mrfFunctionVars, differentiationVars,
      BVariable.isMrfVariable, part, funcMap, formulation, staticAsContinuous);

    r0Hessian := createHessian(
      r0Name, JacobianType.OPT_R0, r0FunctionVars, differentiationVars,
      BVariable.isR0Variable, part, funcMap, formulation, staticAsContinuous);

    part := setOptimizationJacobians(part, lfgJacobian, mrfJacobian, r0Jacobian);

    if isSome(lfgJacobian) or isSome(mrfJacobian) or isSome(r0Jacobian) or isSome(lfgHessian) or isSome(mrfHessian) or isSome(r0Hessian) then
      optPart := SOME(BackendDAE.OPTIMIZATION_PARTITION_DATA(
        name                  = name,
        formulation           = formulation,
        differentiationVars   = differentiationVars,
        innerVars             = innerVars,
        lfgFunctionVars       = lfgFunctionVars,
        mrfFunctionVars       = mrfFunctionVars,
        r0FunctionVars        = r0FunctionVars,
        lfgJacobian           = lfgJacobian,
        mrfJacobian           = mrfJacobian,
        r0Jacobian            = r0Jacobian,
        lfgHessian            = lfgHessian,
        mrfHessian            = mrfHessian,
        r0Hessian             = r0Hessian
      ));
    end if;
  end partOptimization;

  function createJacobian
    input String name;
    input JacobianType jacType;
    input VariablePointers functionVars;
    input VariablePointers differentiationVars;
    input BVariable.checkVar variableFilter;
    input Partition.Partition part;
    input Module.jacobianInterface func;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    output Option<Jacobian> jacobian;
  protected
    VariablePointers seedCandidates, partialCandidates;
    list<Pointer<Variable>> rows;
  algorithm
    rows := VariablePointers.toList(functionVars);
    if listEmpty(rows) then
      jacobian := NONE();
      return;
    end if;

    partialCandidates := VariablePointers.fromList(
      listAppend(rows, VariablePointers.toList(part.unknowns)),
      part.unknowns.scalarized);
    seedCandidates := VariablePointers.fromList(
      list(var for var guard(variableFilter(var)) in VariablePointers.toList(differentiationVars)),
      partialCandidates.scalarized);

    if VariablePointers.size(seedCandidates) == 0 then
      jacobian := NONE();
      return;
    end if;

    jacobian := func(
      name                = name,
      jacType             = jacType,
      seedCandidates      = seedCandidates,
      partialCandidates   = partialCandidates,
      equations           = part.equations,
      strongComponents    = part.strongComponents,
      full                = part.adjacencyMatrix,
      funcMap             = funcMap,
      staticAsContinuous  = staticAsContinuous);
  end createJacobian;

  function createHessian
    "Create an ODE HVP program for lambda^T * functionVars in direction v.
     DAE residual Hessians are intentionally left for a later interface."
    input String hessianName;
    input JacobianType jacType;
    input VariablePointers functionVars;
    input VariablePointers differentiationVars;
    input BVariable.checkVar variableFilter;
    input Partition.Partition part;
    input UnorderedMap<Path, Function> funcMap;
    input BackendDAE.OptimizationFormulation formulation;
    input Boolean staticAsContinuous;
    output Option<Jacobian> hessian = NONE();
  protected
    VariablePointers seedVars, innerVars;
    BJacobian.SparsityPattern lowerSparsity;
    Option<Hessian.Hessian> hvp;
  algorithm
    // DAE residual HVPs need a separate value/residual interface. Keep that future work explicit.
    if formulation == BackendDAE.OptimizationFormulation.DAE or isNone(part.strongComponents) then
      return;
    end if;

    if VariablePointers.size(functionVars) == 0 then
      return;
    end if;

    seedVars := VariablePointers.fromList(
      list(var for var guard(variableFilter(var)) in VariablePointers.toList(differentiationVars)),
      differentiationVars.scalarized);

    if VariablePointers.size(seedVars) == 0 then
      return;
    end if;

    innerVars := VariablePointers.fromList(
      excludeVariables(
        VariablePointers.toList(part.unknowns),
        listAppend(VariablePointers.toList(functionVars), VariablePointers.toList(seedVars))),
      part.unknowns.scalarized);

    hvp := Hessian.forFunctionVariables(
      functionVars          = functionVars,
      differentiationVars   = seedVars,
      innerVars             = innerVars,
      equations             = part.equations,
      comps                 = Util.getOption(part.strongComponents),
      full                  = part.adjacencyMatrix,
      funcMap               = funcMap,
      name                  = hessianName,
      jacType               = jacType,
      staticAsContinuous    = staticAsContinuous
    );

    if isSome(hvp) then
      lowerSparsity := hessianSparsity(Util.getOption(hvp), jacType, staticAsContinuous);
      hessian := SOME(hessianToBackend(Util.getOption(hvp), hessianName + "_HVP", lowerSparsity));
    end if;
  end createHessian;

  function hessianToBackend
    "Lower the NBHessian result to the backend HESSIAN container.
     The lambda and direction seed vectors stay separate from here on."
    input Hessian.Hessian hessian;
    input String name;
    input BJacobian.SparsityPattern lowerSparsity;
    output Jacobian backendHessian;
  protected
    VarData varData;
  algorithm
    backendHessian := match hessian
      case Hessian.Hessian.HESSIAN()
        algorithm
          varData := VarData.VAR_DATA_JAC(
            variables     = hessian.variables,
            unknowns      = hessian.unknowns,
            auxiliaries   = hessian.auxiliaries,
            aliasVars     = VariablePointers.empty(),
            diffVars      = hessian.directionVars,
            dependencies  = hessian.unknowns,
            resultVars    = hessian.resultVars,
            tmpVars       = hessian.tmpVars,
            seedVars      = VariablePointers.fromList(
              listAppend(VariablePointers.toList(hessian.lambdaVars), VariablePointers.toList(hessian.directionVars)),
              hessian.lambdaVars.scalarized)
          );
        then BackendDAE.HESSIAN(
          varData       = varData,
          eqData        = EqData.EQ_DATA_EMPTY(),
          name          = name,
          jacType       = hessian.jacType,
          lambdaVars    = hessian.lambdaVars,
          directionVars = hessian.directionVars,
          resultVars    = hessian.resultVars,
          tmpVars       = hessian.tmpVars,
          sparsityPattern = lowerSparsity,
          comps         = hessian.comps
        );
    end match;
  end hessianToBackend;

  function hessianSparsity
    "Create lower-triangular Hessian sparsity from the generated HVP program.
     Falls back to dense lower storage when loop dependencies are opaque."
    input Hessian.Hessian hessian;
    input JacobianType jacType;
    input Boolean staticAsContinuous;
    output BJacobian.SparsityPattern lowerSparsity;
  protected
    VariablePointers partialCandidates;
  algorithm
    partialCandidates := VariablePointers.fromList(
      listAppend(VariablePointers.toList(hessian.resultVars), VariablePointers.toList(hessian.tmpVars)),
      hessian.variables.scalarized);

    if hasAlgebraicLoop(hessian.comps) then
      lowerSparsity := denseLowerHessianSparsity(hessian.directionVars, hessian.resultVars);
      return;
    end if;

    lowerSparsity := BJacobian.SparsityPattern.createForRows(
      seedCandidates      = hessian.directionVars,
      partialCandidates   = partialCandidates,
      rowCandidates       = hessian.resultVars,
      strongComponents    = SOME(hessian.comps),
      jacType             = jacType,
      staticAsContinuous  = staticAsContinuous);

    lowerSparsity := lowerTriangularHessianSparsity(lowerSparsity, hessian.directionVars, hessian.resultVars);

    if lowerSparsity.nnz == 0 and VariablePointers.size(hessian.directionVars) > 0 and VariablePointers.size(hessian.resultVars) > 0 then
      lowerSparsity := denseLowerHessianSparsity(hessian.directionVars, hessian.resultVars);
    end if;
  end hessianSparsity;

  function hasAlgebraicLoop
    "Conservative marker for HVP sparsity. Loop-solve dependencies are not yet
     resolved strongly enough to export a structural lower pattern safely."
    input array<StrongComponent> comps;
    output Boolean found = false;
  algorithm
    for i in 1:arrayLength(comps) loop
      if componentHasAlgebraicLoop(comps[i]) then
        found := true;
        return;
      end if;
    end for;
  end hasAlgebraicLoop;

  function componentHasAlgebraicLoop
    input StrongComponent comp;
    output Boolean found;
  algorithm
    found := match comp
      case StrongComponent.ALGEBRAIC_LOOP() then true;
      case StrongComponent.ENTWINED_COMPONENT() then List.any(comp.entwined_slices, componentHasAlgebraicLoop);
      case StrongComponent.ALIAS() then componentHasAlgebraicLoop(comp.original);
      else false;
    end match;
  end componentHasAlgebraicLoop;

  function lowerTriangularHessianSparsity
    "Restrict an HVP dependency pattern to the lower triangular Hessian storage.
     The HVP itself is a full matrix-vector product, but the exported Hessian
     buffer stores only entries H(i,j) with i >= j."
    input BJacobian.SparsityPattern pattern;
    input VariablePointers directionVars;
    input VariablePointers resultVars;
    output BJacobian.SparsityPattern lowerSparsity;
  protected
    list<ComponentRef> directionCrefs, resultCrefs, deps, rowDeps, colDeps;
    list<BJacobian.SparsityPatternCol> cols = {};
    list<BJacobian.SparsityPatternRow> rows = {};
    UnorderedMap<ComponentRef, CrefLst> colDepsMap;
    Integer colIdx, rowIdx, nnz = 0;
    ComponentRef colCref, rowCref;
  algorithm
    directionCrefs := VariablePointers.getScalarVarNames(directionVars, false);
    resultCrefs := VariablePointers.getScalarVarNames(resultVars, false);
    colDepsMap := UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(pattern.col_wise_pattern)));

    for col in pattern.col_wise_pattern loop
      (colCref, deps) := col;
      UnorderedMap.add(colCref, deps, colDepsMap);
    end for;

    colIdx := 0;
    for colCref in directionCrefs loop
      deps := if UnorderedMap.contains(colCref, colDepsMap) then UnorderedMap.getSafe(colCref, colDepsMap, sourceInfo()) else {};
      rowIdx := 0;
      colDeps := {};
      for rowCref in resultCrefs loop
        if rowIdx >= colIdx and List.isMemberOnTrue(rowCref, deps, ComponentRef.isEqual) then
          colDeps := rowCref :: colDeps;
        end if;
        rowIdx := rowIdx + 1;
      end for;
      colDeps := listReverse(colDeps);
      nnz := nnz + listLength(colDeps);
      cols := (colCref, colDeps) :: cols;
      colIdx := colIdx + 1;
    end for;
    cols := listReverse(cols);

    rowIdx := 0;
    for rowCref in resultCrefs loop
      colIdx := 0;
      rowDeps := {};
      for colCref in directionCrefs loop
        deps := if UnorderedMap.contains(colCref, colDepsMap) then UnorderedMap.getSafe(colCref, colDepsMap, sourceInfo()) else {};
        if colIdx <= rowIdx and List.isMemberOnTrue(rowCref, deps, ComponentRef.isEqual) then
          rowDeps := colCref :: rowDeps;
        end if;
        colIdx := colIdx + 1;
      end for;
      rows := (rowCref, listReverse(rowDeps)) :: rows;
      rowIdx := rowIdx + 1;
    end for;
    rows := listReverse(rows);

    lowerSparsity := BJacobian.SparsityPattern.SPARSITY_PATTERN(
      col_wise_pattern = cols,
      row_wise_pattern = rows,
      seed_vars        = directionCrefs,
      partial_vars     = resultCrefs,
      nnz              = nnz);
  end lowerTriangularHessianSparsity;

  function denseLowerHessianSparsity
    "Conservative fallback used when the generic sparsity collector cannot resolve
     dependencies through generated HVP loop solves."
    input VariablePointers directionVars;
    input VariablePointers resultVars;
    output BJacobian.SparsityPattern lowerSparsity;
  protected
    list<ComponentRef> directionCrefs, resultCrefs, rowDeps, colDeps;
    list<BJacobian.SparsityPatternCol> cols = {};
    list<BJacobian.SparsityPatternRow> rows = {};
    Integer colIdx, rowIdx, nnz = 0;
    ComponentRef colCref, rowCref;
  algorithm
    directionCrefs := VariablePointers.getScalarVarNames(directionVars, false);
    resultCrefs := VariablePointers.getScalarVarNames(resultVars, false);

    colIdx := 0;
    for colCref in directionCrefs loop
      rowIdx := 0;
      colDeps := {};
      for rowCref in resultCrefs loop
        if rowIdx >= colIdx then
          colDeps := rowCref :: colDeps;
        end if;
        rowIdx := rowIdx + 1;
      end for;
      colDeps := listReverse(colDeps);
      nnz := nnz + listLength(colDeps);
      cols := (colCref, colDeps) :: cols;
      colIdx := colIdx + 1;
    end for;
    cols := listReverse(cols);

    rowIdx := 0;
    for rowCref in resultCrefs loop
      colIdx := 0;
      rowDeps := {};
      for colCref in directionCrefs loop
        if colIdx <= rowIdx then
          rowDeps := colCref :: rowDeps;
        end if;
        colIdx := colIdx + 1;
      end for;
      rows := (rowCref, listReverse(rowDeps)) :: rows;
      rowIdx := rowIdx + 1;
    end for;
    rows := listReverse(rows);

    lowerSparsity := BJacobian.SparsityPattern.SPARSITY_PATTERN(
      col_wise_pattern = cols,
      row_wise_pattern = rows,
      seed_vars        = directionCrefs,
      partial_vars     = resultCrefs,
      nnz              = nnz);
  end denseLowerHessianSparsity;

  function setOptimizationJacobians
    input output Partition.Partition part;
    input Option<Jacobian> lfgJacobian;
    input Option<Jacobian> mrfJacobian;
    input Option<Jacobian> r0Jacobian;
  algorithm
    part.association := match part.association
      local
        Partition.Association ass;

      case ass as Partition.Association.CONTINUOUS()
        algorithm
          ass.LFG_jacobian := lfgJacobian;
          ass.MRF_jacobian := mrfJacobian;
          ass.R0_jacobian  := r0Jacobian;
      then ass;

      else
        algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed for non-continuous optimization partition."});
        then fail();
    end match;
  end setOptimizationJacobians;

  function getDifferentiationVars
    "GDOP columns: states and optimizable inputs/parameters, including optimizable time parameters."
    input Partition.Partition part;
    input VariablePointers allKnowns;
    input BackendDAE.OptimizationFormulation formulation;
    output VariablePointers differentiationVars;
  protected
    VariablePointers unknowns;
    list<Pointer<Variable>> derivativeVars, stateVars, optimizableVars;
  algorithm
    unknowns := match (formulation, part.daeUnknowns)
      case (BackendDAE.OptimizationFormulation.DAE, SOME(unknowns)) then unknowns;
      else part.unknowns;
    end match;

    derivativeVars := list(var for var guard(BVariable.isStateDerivative(var)) in VariablePointers.toList(unknowns));
    stateVars := list(Util.getOption(BVariable.getVarState(var)) for var in derivativeVars);
    optimizableVars := list(var for var guard(BVariable.isOptimizable(var)) in VariablePointers.toList(allKnowns));
    differentiationVars := VariablePointers.fromList(listAppend(stateVars, optimizableVars), part.unknowns.scalarized);
  end getDifferentiationVars;

  function getLfgFunctionVars
    input Partition.Partition part;
    input BackendDAE.OptimizationFormulation formulation;
    output list<Pointer<Variable>> vars;
  protected
    list<Pointer<Variable>> lagrangeVars = {}, derivativeVars = {}, pathVars = {};
  algorithm
    if formulation == BackendDAE.OptimizationFormulation.DAE then
      vars := list(var for var guard(BVariable.isResidual(var)) in VariablePointers.toList(part.unknowns));
      return;
    end if;

    for var in VariablePointers.toList(part.unknowns) loop
      if BVariable.isLagrange(var) then
        lagrangeVars := var :: lagrangeVars;
      elseif BVariable.isStateDerivative(var) then
        derivativeVars := var :: derivativeVars;
      elseif BVariable.isPathConstraint(var) then
        pathVars := var :: pathVars;
      end if;
    end for;
    vars := listAppend(listReverse(lagrangeVars), listAppend(listReverse(derivativeVars), listReverse(pathVars)));
  end getLfgFunctionVars;

  function getMrfFunctionVars
    input Partition.Partition part;
    output list<Pointer<Variable>> vars;
  protected
    list<Pointer<Variable>> mayerVars = {}, finalVars = {};
  algorithm
    for var in VariablePointers.toList(part.unknowns) loop
      if BVariable.isMayer(var) then
        mayerVars := var :: mayerVars;
      elseif BVariable.isFinalConstraint(var) then
        finalVars := var :: finalVars;
      end if;
    end for;
    vars := listAppend(listReverse(mayerVars), listReverse(finalVars));
  end getMrfFunctionVars;

  function getR0FunctionVars
    input Partition.Partition part;
    output list<Pointer<Variable>> vars = {};
  algorithm
    for var in VariablePointers.toList(part.unknowns) loop
      if BVariable.isInitialConstraint(var) then
        vars := var :: vars;
      end if;
    end for;
    vars := listReverse(vars);
  end getR0FunctionVars;

  function getInnerVars
    input Partition.Partition part;
    input VariablePointers differentiationVars;
    input VariablePointers lfgFunctionVars;
    input VariablePointers mrfFunctionVars;
    input VariablePointers r0FunctionVars;
    output VariablePointers innerVars;
  protected
    list<Pointer<Variable>> excluded;
  algorithm
    excluded := listAppend(
      VariablePointers.toList(differentiationVars),
      listAppend(
        VariablePointers.toList(lfgFunctionVars),
        listAppend(VariablePointers.toList(mrfFunctionVars), VariablePointers.toList(r0FunctionVars))));

    innerVars := VariablePointers.fromList(
      excludeVariables(VariablePointers.toList(part.unknowns), excluded),
      part.unknowns.scalarized);
  end getInnerVars;

  function excludeVariables
    input list<Pointer<Variable>> candidates;
    input list<Pointer<Variable>> excluded;
    output list<Pointer<Variable>> filtered = {};
  protected
    UnorderedSet<ComponentRef> excludedCrefs = UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(excluded)));
    ComponentRef cref;
  algorithm
    for var in excluded loop
      UnorderedSet.add(BVariable.getVarName(var), excludedCrefs);
    end for;

    for var in candidates loop
      cref := BVariable.getVarName(var);
      if not UnorderedSet.contains(cref, excludedCrefs) then
        filtered := var :: filtered;
      end if;
    end for;

    filtered := listReverse(filtered);
  end excludeVariables;

  annotation(__OpenModelica_Interface="backend");
end NBOptimization;
