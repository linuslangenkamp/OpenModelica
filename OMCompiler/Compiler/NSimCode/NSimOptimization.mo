/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2026, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

encapsulated package NSimOptimization
"file:        NSimOptimization.mo
 package:     NSimOptimization
 description: Lowers new-backend dynamic optimization artifacts to NSimCode.
"

public
  // NF imports
  import ComponentRef = NFComponentRef;
  import Variable = NFVariable;

  // Backend imports
  import BackendDAE = NBackendDAE;
  import NBEquation.EqData;
  import Jacobian = NBJacobian;
  import NBJacobian.JacobianType;
  import StrongComponent = NBStrongComponent;
  import NBVariable.{VariablePointers, VarData};

  // SimCode imports
  import SimCode = NSimCode;
  import NSimHessian.SimHessian;
  import NSimJacobian.SimJacobian;
  import NSimVar.SimVar;

  // Util imports
  import Error;
  import UnorderedMap;
  import Util;

  function createJacobians
    "Create the SimCode OPT Jacobians from explicit backend optimization data."
    input Option<BackendDAE> optimizationData;
    output SimJacobian simJacLfg;
    output SimJacobian simJacMrf;
    output SimJacobian simJacR0;
    output list<SimHessian> simHessians = {};
    input output SimCode.SimCodeIndices simCodeIndices;
    input UnorderedMap<ComponentRef, SimVar> simcode_map;
  protected
    list<BackendDAE> lfgJacobians = {}, mrfJacobians = {}, r0Jacobians = {};
    list<BackendDAE> lfgHessians = {}, mrfHessians = {}, r0Hessians = {};
    Option<SimHessian> simHessian;
    BackendDAE data;
    list<BackendDAE> optParts;
  algorithm
    if isSome(optimizationData) then
      data := Util.getOption(optimizationData);
      optParts := match data
        case BackendDAE.OPTIMIZATION_DATA() then data.partitions;
        else {};
      end match;

      for optPart in optParts loop
        () := match optPart
          case BackendDAE.OPTIMIZATION_PARTITION_DATA()
            algorithm
              if isSome(optPart.lfgJacobian) then
                lfgJacobians := Util.getOption(optPart.lfgJacobian) :: lfgJacobians;
              end if;
              if isSome(optPart.mrfJacobian) then
                mrfJacobians := Util.getOption(optPart.mrfJacobian) :: mrfJacobians;
              end if;
              if isSome(optPart.r0Jacobian) then
                r0Jacobians := Util.getOption(optPart.r0Jacobian) :: r0Jacobians;
              end if;
              if isSome(optPart.lfgHessian) then
                lfgHessians := Util.getOption(optPart.lfgHessian) :: lfgHessians;
              end if;
              if isSome(optPart.mrfHessian) then
                mrfHessians := Util.getOption(optPart.mrfHessian) :: mrfHessians;
              end if;
              if isSome(optPart.r0Hessian) then
                r0Hessians := Util.getOption(optPart.r0Hessian) :: r0Hessians;
              end if;
          then ();
          else ();
        end match;
      end for;
    end if;

    (simJacLfg, simCodeIndices) := createOne(listReverse(lfgJacobians), "OPT_LFG", simCodeIndices, simcode_map);
    (simJacMrf, simCodeIndices) := createOne(listReverse(mrfJacobians), "OPT_MRF", simCodeIndices, simcode_map);
    (simJacR0,  simCodeIndices) := createOne(listReverse(r0Jacobians),  "OPT_R0",  simCodeIndices, simcode_map);

    (simHessian, simCodeIndices) := createOneHessian(listReverse(lfgHessians), "OPT_LFG_HVP", simCodeIndices, simcode_map);
    if isSome(simHessian) then
      simHessians := Util.getOption(simHessian) :: simHessians;
    end if;
    (simHessian, simCodeIndices) := createOneHessian(listReverse(mrfHessians), "OPT_MRF_HVP", simCodeIndices, simcode_map);
    if isSome(simHessian) then
      simHessians := Util.getOption(simHessian) :: simHessians;
    end if;
    (simHessian, simCodeIndices) := createOneHessian(listReverse(r0Hessians), "OPT_R0_HVP", simCodeIndices, simcode_map);
    if isSome(simHessian) then
      simHessians := Util.getOption(simHessian) :: simHessians;
    end if;
    simHessians := listReverse(simHessians);
  end createJacobians;

protected
  function createOne
    input list<BackendDAE> jacobians;
    input String name;
    output SimJacobian simJacobian;
    input output SimCode.SimCodeIndices simCodeIndices;
    input UnorderedMap<ComponentRef, SimVar> simcode_map;
  protected
    BackendDAE combinedJacobian;
    Option<SimJacobian> simJacobianOpt;
  algorithm
    if listEmpty(jacobians) then
      (simJacobian, simCodeIndices) := SimJacobian.empty(name, simCodeIndices);
    else
      combinedJacobian := Jacobian.combine(jacobians, name);
      (simJacobianOpt, simCodeIndices) := SimJacobian.create(combinedJacobian, simCodeIndices, simcode_map);
      if isSome(simJacobianOpt) then
        simJacobian := Util.getOption(simJacobianOpt);
      else
        (simJacobian, simCodeIndices) := SimJacobian.empty(name, simCodeIndices);
      end if;
    end if;
  end createOne;

  function createOneHessian
    input list<BackendDAE> hessians;
    input String name;
    output Option<SimHessian> simHessian = NONE();
    input output SimCode.SimCodeIndices simCodeIndices;
    input UnorderedMap<ComponentRef, SimVar> simcode_map;
  protected
    BackendDAE combinedHessian;
  algorithm
    if listEmpty(hessians) then
      return;
    end if;

    combinedHessian := combineHessians(hessians, name);
    (simHessian, simCodeIndices) := SimHessian.create(combinedHessian, simCodeIndices, simcode_map);
  end createOneHessian;

  function combineHessians
    input list<BackendDAE> hessians;
    input String name;
    output BackendDAE hessian;
  protected
    JacobianType jacType = JacobianType.NLS;
    list<Pointer<Variable>> variables = {}, unknowns = {}, auxiliaries = {};
    list<Pointer<Variable>> resultVars = {}, tmpVars = {}, lambdaVars = {}, directionVars = {};
    list<StrongComponent> comps = {};
    list<Jacobian.SparsityPatternCol> col_wise_pattern = {};
    list<Jacobian.SparsityPatternRow> row_wise_pattern = {};
    list<ComponentRef> seed_vars = {};
    list<ComponentRef> partial_vars = {};
    Integer nnz = 0;
    VarData varData;
    Jacobian.SparsityPattern sparsityPattern;
  algorithm
    if listLength(hessians) == 1 then
      hessian := listHead(hessians);
      hessian := match hessian
        case BackendDAE.HESSIAN()
          algorithm
            hessian.name := name;
        then hessian;
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
        then fail();
      end match;
      return;
    end if;

    for h in hessians loop
      () := match h
        local
          Jacobian.SparsityPattern tmpPattern;

        case BackendDAE.HESSIAN(varData = varData as VarData.VAR_DATA_JAC())
          algorithm
            jacType       := h.jacType;
            variables     := listAppend(VariablePointers.toList(varData.variables), variables);
            unknowns      := listAppend(VariablePointers.toList(varData.unknowns), unknowns);
            auxiliaries   := listAppend(VariablePointers.toList(varData.auxiliaries), auxiliaries);
            resultVars    := listAppend(VariablePointers.toList(h.resultVars), resultVars);
            tmpVars       := listAppend(VariablePointers.toList(h.tmpVars), tmpVars);
            lambdaVars    := listAppend(VariablePointers.toList(h.lambdaVars), lambdaVars);
            directionVars := listAppend(VariablePointers.toList(h.directionVars), directionVars);
            comps         := listAppend(arrayList(h.comps), comps);
            tmpPattern    := h.sparsityPattern;
            col_wise_pattern := listAppend(tmpPattern.col_wise_pattern, col_wise_pattern);
            row_wise_pattern := listAppend(tmpPattern.row_wise_pattern, row_wise_pattern);
            seed_vars        := listAppend(tmpPattern.seed_vars, seed_vars);
            partial_vars     := listAppend(tmpPattern.partial_vars, partial_vars);
            nnz              := nnz + tmpPattern.nnz;
        then ();
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
        then fail();
      end match;
    end for;

    varData := VarData.VAR_DATA_JAC(
      variables     = VariablePointers.fromList(variables),
      unknowns      = VariablePointers.fromList(unknowns),
      auxiliaries   = VariablePointers.fromList(auxiliaries),
      aliasVars     = VariablePointers.empty(),
      diffVars      = VariablePointers.fromList(directionVars),
      dependencies  = VariablePointers.fromList(unknowns),
      resultVars    = VariablePointers.fromList(resultVars),
      tmpVars       = VariablePointers.fromList(tmpVars),
      seedVars      = VariablePointers.fromList(listAppend(lambdaVars, directionVars))
    );

    sparsityPattern := Jacobian.SparsityPattern.SPARSITY_PATTERN(
      col_wise_pattern = col_wise_pattern,
      row_wise_pattern = row_wise_pattern,
      seed_vars        = seed_vars,
      partial_vars     = partial_vars,
      nnz              = nnz);

    hessian := BackendDAE.HESSIAN(
      varData       = varData,
      eqData        = EqData.EQ_DATA_EMPTY(),
      name          = name,
      jacType       = jacType,
      lambdaVars    = VariablePointers.fromList(lambdaVars),
      directionVars = VariablePointers.fromList(directionVars),
      resultVars    = VariablePointers.fromList(resultVars),
      tmpVars       = VariablePointers.fromList(tmpVars),
      sparsityPattern = sparsityPattern,
      comps         = listArray(comps)
    );
  end combineHessians;

  annotation(__OpenModelica_Interface="backend");
end NSimOptimization;
