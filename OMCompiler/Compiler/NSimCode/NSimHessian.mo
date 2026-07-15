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

encapsulated package NSimHessian
"file:        NSimHessian.mo
 package:     NSimHessian
 description: Lowers new-backend symbolic Hessian-vector products to SimCode.
"

public
  // NF imports
  import ComponentRef = NFComponentRef;

  // Backend imports
  import BackendDAE = NBackendDAE;
  import Jacobian = NBJacobian;
  import NBPartition;
  import NBVariable.VariablePointers;

  // SimCode imports
  import SimCode = NSimCode;
  import SimCodeUtil = NSimCodeUtil;
  import SimGenericCall = NSimGenericCall;
  import NSimCode.Identifier;
  import SimStrongComponent = NSimStrongComponent;
  import NSimVar.{SimVar, VarType};

  // Old SimCode imports
  import OldSimCode = SimCode;

  // Util imports
  import Error;
  import Flags;
  import List;
  import Pointer;
  import StringUtil;
  import UnorderedMap;
  import Util;

  uniontype SimHessian
    record SIM_HESSIAN
      String name;
      list<SimStrongComponent.Block> equations;
      list<SimVar> lambdaVars;
      list<SimVar> directionVars;
      list<SimVar> resultVars;
      list<SimVar> tmpVars;
      OldSimCode.SparsityPattern lowerSparsity;
      list<SimGenericCall> generic_loop_calls;
      Option<UnorderedMap<ComponentRef, SimVar>> lambda_map;
      Option<UnorderedMap<ComponentRef, SimVar>> direction_map;
      Option<UnorderedMap<ComponentRef, SimVar>> result_map;
      Option<UnorderedMap<ComponentRef, SimVar>> tmp_map;
    end SIM_HESSIAN;

    function toString
      input SimHessian simHessian;
      output String str = "";
    algorithm
      str := match simHessian
        case SIM_HESSIAN() algorithm
          str := StringUtil.headline_2("SimCode Hessian-vector product " + simHessian.name) + "\n";
          str := str + "lambdaVars: " + intString(listLength(simHessian.lambdaVars)) + "\n";
          str := str + "directionVars: " + intString(listLength(simHessian.directionVars)) + "\n";
          str := str + "resultVars: " + intString(listLength(simHessian.resultVars)) + "\n";
          str := str + "tmpVars: " + intString(listLength(simHessian.tmpVars)) + "\n";
        then str;
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
        then fail();
      end match;
    end toString;

    function create
      input BackendDAE hessian;
      output Option<SimHessian> simHessian;
      input output SimCode.SimCodeIndices indices;
      input UnorderedMap<ComponentRef, SimVar> simcode_map;
    algorithm
      _ := simcode_map;
      simHessian := match hessian
        local
          UnorderedMap<ComponentRef, SimVar> dummy_sim_map = UnorderedMap.new<SimVar>(ComponentRef.hash, ComponentRef.isEqual);
          UnorderedMap<ComponentRef, SimStrongComponent.Block> dummy_eqn_map = UnorderedMap.new<SimStrongComponent.Block>(ComponentRef.hash, ComponentRef.isEqual);
          SimStrongComponent.Block hessianEqn;
          list<SimStrongComponent.Block> equations = {};
          list<SimVar> lambdaVars, directionVars, resultVars, tmpVars;
          UnorderedMap<Identifier, Integer> sim_map;
          UnorderedMap<ComponentRef, Integer> local_idx_map;
          list<SimGenericCall> generic_loop_calls;
          OldSimCode.SparsityPattern lowerSparsity;

        case BackendDAE.HESSIAN()
          algorithm
            sim_map := indices.generic_call_map;
            indices.generic_call_map := UnorderedMap.new<Integer>(Identifier.hash, Identifier.isEqual);

            for i in arrayLength(hessian.comps):-1:1 loop
              (hessianEqn, indices, _) := SimStrongComponent.Block.fromStrongComponent(hessian.comps[i], indices, NBPartition.Kind.JAC, dummy_sim_map, dummy_eqn_map);
              equations := hessianEqn :: equations;
            end for;

            generic_loop_calls := list(SimGenericCall.fromIdentifier(tpl) for tpl in UnorderedMap.toList(indices.generic_call_map));
            indices.generic_call_map := sim_map;

            lambdaVars    := createSimVars(hessian.lambdaVars);
            directionVars := createSimVars(hessian.directionVars);
            resultVars    := createSimVars(hessian.resultVars);
            tmpVars       := createSimVars(hessian.tmpVars);

            local_idx_map := createIndexMap(directionVars, resultVars);
            lowerSparsity := createSparsityPattern(hessian.sparsityPattern.col_wise_pattern, local_idx_map);

            simHessian := SOME(SIM_HESSIAN(
              name                = hessian.name,
              equations           = equations,
              lambdaVars          = lambdaVars,
              directionVars       = directionVars,
              resultVars          = resultVars,
              tmpVars             = tmpVars,
              lowerSparsity       = lowerSparsity,
              generic_loop_calls  = generic_loop_calls,
              lambda_map          = SOME(createMap(lambdaVars)),
              direction_map       = SOME(createMap(directionVars)),
              result_map          = SOME(createMap(resultVars)),
              tmp_map             = SOME(createMap(tmpVars))
            ));
        then simHessian;

        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
        then fail();
      end match;
    end create;

    function convert
      input SimHessian simHessian;
      output OldSimCode.HessianMatrix oldHessian;
    algorithm
      oldHessian := match simHessian
        case SIM_HESSIAN() then OldSimCode.HESSIAN_MATRIX(
          name                = simHessian.name,
          equations           = SimStrongComponent.Block.convertList(simHessian.equations),
          lambdaVars          = SimVar.convertList(simHessian.lambdaVars),
          directionVars       = SimVar.convertList(simHessian.directionVars),
          resultVars          = SimVar.convertList(simHessian.resultVars),
          tmpVars             = SimVar.convertList(simHessian.tmpVars),
          lowerSparsity       = simHessian.lowerSparsity,
          generic_loop_calls  = list(SimGenericCall.convert(gc) for gc in simHessian.generic_loop_calls),
          lambdaHT            = Util.applyOption(simHessian.lambda_map, SimCodeUtil.convertSimCodeMap),
          directionHT         = Util.applyOption(simHessian.direction_map, SimCodeUtil.convertSimCodeMap),
          resultHT            = Util.applyOption(simHessian.result_map, SimCodeUtil.convertSimCodeMap),
          tmpHT               = Util.applyOption(simHessian.tmp_map, SimCodeUtil.convertSimCodeMap)
        );
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
        then fail();
      end match;
    end convert;
  end SimHessian;

protected
  function createSimVars
    input VariablePointers variables;
    output list<SimVar> simVars;
  protected
    VariablePointers vars;
    Pointer<list<SimVar>> simVars_ptr = Pointer.create({});
  algorithm
    vars := variables;
    if Flags.getConfigBool(Flags.SIM_CODE_SCALARIZE) then
      vars := VariablePointers.scalarize(vars);
    end if;
    VariablePointers.map(vars, function SimVar.traverseCreate(
      acc         = simVars_ptr,
      indices_ptr = Pointer.create(SimCode.EMPTY_SIM_CODE_INDICES()),
      varType     = VarType.SIMULATION));
    simVars := listReverse(Pointer.access(simVars_ptr));
  end createSimVars;

  function createMap
    input list<SimVar> variables;
    output UnorderedMap<ComponentRef, SimVar> map;
  algorithm
    map := UnorderedMap.new<SimVar>(ComponentRef.hash, ComponentRef.isEqual, listLength(variables));
    SimCodeUtil.addListSimCodeMap(variables, map);
  end createMap;

  function createIndexMap
    input list<SimVar> directionVars;
    input list<SimVar> resultVars;
    output UnorderedMap<ComponentRef, Integer> local_idx_map;
  protected
    ComponentRef cref;
  algorithm
    local_idx_map := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, listLength(directionVars) + listLength(resultVars));
    for var in directionVars loop
      cref := SimVar.getName(var);
      UnorderedMap.add(cref, var.index, local_idx_map);
    end for;
    for var in resultVars loop
      cref := SimVar.getName(var);
      UnorderedMap.add(cref, var.index, local_idx_map);
    end for;
  end createIndexMap;

  function createSparsityPattern
    input list<Jacobian.SparsityPatternCol> cols;
    input UnorderedMap<ComponentRef, Integer> local_idx_map;
    output OldSimCode.SparsityPattern simPattern = {};
  protected
    ComponentRef cref;
    list<ComponentRef> dependencies;
    list<Integer> dep_indices;
  algorithm
    for col in cols loop
      (cref, dependencies) := col;
      if not UnorderedMap.contains(cref, local_idx_map) then
        Error.addCompilerWarning(
          getInstanceName() + ": column cref not found in Hessian local_idx_map: " +
          ComponentRef.toString(cref) + "\n\tAvailable keys: " + stringDelimitList(List.map(UnorderedMap.keyList(local_idx_map), ComponentRef.toString), ", "));
        fail();
      end if;

      dep_indices := {};
      for dep in dependencies loop
        if not UnorderedMap.contains(dep, local_idx_map) then
          Error.addCompilerWarning(
            getInstanceName() + ": dependency cref not found in Hessian local_idx_map: " +
            ComponentRef.toString(dep) + "\n\tWhile processing column: " + ComponentRef.toString(cref) +
            "\n\tAvailable keys: " + stringDelimitList(List.map(UnorderedMap.keyList(local_idx_map), ComponentRef.toString), ", "));
          fail();
        end if;
        dep_indices := UnorderedMap.getOrFail(dep, local_idx_map) :: dep_indices;
      end for;
      simPattern := (UnorderedMap.getOrFail(cref, local_idx_map), List.sort(dep_indices, intGt)) :: simPattern;
    end for;
    simPattern := List.sort(simPattern, Util.compareTupleIntGt);
  end createSparsityPattern;

  annotation(__OpenModelica_Interface="nbackend");
end NSimHessian;
