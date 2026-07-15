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

encapsulated package NBHessian
"file:        NBHessian.mo
 package:     NBHessian
 description: Prototype utilities for symbolic Hessian-vector products.
"

public
  import NBEquation;
  import NBVariable;
  import NBJacobian.JacobianType;

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
  import NBAdjoint;
  import NBEquation.EquationPointers;
  import NBForward;
  import NBVariable.VariablePointers;
  import StrongComponent = NBStrongComponent;

  // Util imports
  import Flags;
  import StringUtil;
  import UnorderedMap;

public
  type HessianType = enumeration(FORWARD_OVER_REVERSE, NONE);

  uniontype Hessian
    record HESSIAN
      String name;
      HessianType hessianType;
      JacobianType jacType;

      VariablePointers variables;
      VariablePointers unknowns;
      VariablePointers auxiliaries;

      VariablePointers resultVars       "HVP result variables h";
      VariablePointers tmpVars          "all internal tangent / adjoint / forward-over-reverse variables";
      VariablePointers lambdaVars       "fixed reverse seed lambda";
      VariablePointers directionVars    "forward direction seed v";

      array<StrongComponent> comps;
    end HESSIAN;

    function toString
      input Hessian hessian;
      output String str;
    protected
      list<StrongComponent> comps;
    algorithm
      str := match hessian
        case HESSIAN() algorithm
          str := StringUtil.headline_1("Hessian " + hessian.name) + "\n";
          str := str + "type: " + hessianTypeString(hessian.hessianType) + "\n";
          str := str + "jacType: " + BJacobian.jacobianTypeString(hessian.jacType) + "\n\n";

          str := str + BVariable.VariablePointers.toString(hessian.lambdaVars, "Lambda seed variables") + "\n";
          str := str + BVariable.VariablePointers.toString(hessian.directionVars, "Direction seed variables") + "\n";
          str := str + BVariable.VariablePointers.toString(hessian.resultVars, "HVP result variables") + "\n";
          str := str + BVariable.VariablePointers.toString(hessian.tmpVars, "HVP temporary variables") + "\n";

          comps := arrayList(hessian.comps);
          str := str + StringUtil.headline_2("Hessian components") + "\n";
          for comp in comps loop
            str := str + StrongComponent.toString(comp) + "\n";
          end for;
        then str;
      end match;
    end toString;
  end Hessian;

  partial function hessianInterface
    input String name;
    input JacobianType jacType;
    input VariablePointers seedCandidates;
    input VariablePointers partialCandidates;
    input EquationPointers equations;
    input Option<array<StrongComponent>> strongComponents;
    input Option<Adjacency.Matrix> full;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    output Option<Hessian> hessian;
  end hessianInterface;

  function getModule
    output hessianInterface func;
  algorithm
    func := symbolicForwardOverReverse;
  end getModule;

  function none
    extends hessianInterface;
  algorithm
    hessian := NONE();
  end none;

protected
  uniontype ForwardOverReverseProgram
    "Local Hessian composition: tangent(primal), reverse(primal), tangent(reverse)."
    record FORWARD_OVER_REVERSE_PROGRAM
      String name;

      UnorderedMap<ComponentRef, ComponentRef> directionMap;
      UnorderedMap<ComponentRef, ComponentRef> reverseMap;
      UnorderedMap<ComponentRef, ComponentRef> forwardReverseMap;

      list<StrongComponent> tangentComps;
      list<StrongComponent> reverseComps;
      list<StrongComponent> forwardReverseComps;
      list<StrongComponent> comps;

      list<Pointer<Variable>> lambdaVars;
      list<Pointer<Variable>> directionVars;
      list<Pointer<Variable>> resultVars;
      list<Pointer<Variable>> tmpVars;
      list<Pointer<Variable>> unknownVars;
      list<Pointer<Variable>> auxiliaryVars;
      list<Pointer<Variable>> variables;
    end FORWARD_OVER_REVERSE_PROGRAM;

    function toString
      input ForwardOverReverseProgram program;
      output String str = "";
    algorithm
      str := match program
        case FORWARD_OVER_REVERSE_PROGRAM() algorithm
          str := StringUtil.headline_1("Forward-over-reverse Hessian program " + program.name) + "\n";
          str := str + mapToString("Direction map", program.directionMap);
          str := str + mapToString("Reverse map", program.reverseMap);
          str := str + mapToString("Forward-over-reverse map", program.forwardReverseMap);

          str := str + StringUtil.headline_2("Tangent components") + "\n";
          for comp in program.tangentComps loop
            str := str + StrongComponent.toString(comp) + "\n";
          end for;

          str := str + StringUtil.headline_2("Reverse components") + "\n";
          for comp in program.reverseComps loop
            str := str + StrongComponent.toString(comp) + "\n";
          end for;

          str := str + StringUtil.headline_2("Forward-over-reverse components") + "\n";
          for comp in program.forwardReverseComps loop
            str := str + StrongComponent.toString(comp) + "\n";
          end for;
        then str;
      end match;
    end toString;
  end ForwardOverReverseProgram;

  function hessianTypeString
    input HessianType hessianType;
    output String str;
  algorithm
    str := match hessianType
      case HessianType.FORWARD_OVER_REVERSE then "[HVP-FORWARD-OVER-REVERSE]";
      case HessianType.NONE                 then "[HVP-NONE]";
                                          else "[HVP-ERR]";
    end match;
  end hessianTypeString;

  function printGeneration
    input String name;
    input ForwardOverReverseProgram program;
    input Hessian hessian;
  algorithm
    print(StringUtil.headline_1("[symhessdump] " + name + " forward-over-reverse Hessian-vector product") + "\n");
    print(ForwardOverReverseProgram.toString(program));
    print(Hessian.toString(hessian));
  end printGeneration;

  function fromForwardOverReverseProgram
    input String newName;
    input JacobianType jacType;
    input ForwardOverReverseProgram program;
    output Hessian hessianValue;
  algorithm
    hessianValue := Hessian.HESSIAN(
      name          = newName,
      hessianType   = HessianType.FORWARD_OVER_REVERSE,
      jacType       = jacType,
      variables     = VariablePointers.fromList(program.variables),
      unknowns      = VariablePointers.fromList(program.unknownVars),
      auxiliaries   = VariablePointers.fromList(program.auxiliaryVars),
      resultVars    = VariablePointers.fromList(program.resultVars),
      tmpVars       = VariablePointers.fromList(program.tmpVars),
      lambdaVars    = VariablePointers.fromList(program.lambdaVars),
      directionVars = VariablePointers.fromList(program.directionVars),
      comps         = listArray(program.comps)
    );

    if Flags.isSet(Flags.JAC_DUMP) then
      printGeneration(newName, program, hessianValue);
    end if;
  end fromForwardOverReverseProgram;

public
  function symbolicForwardOverReverse
    "Symbolic Hessian-vector product generation.

     Builds a separate Hessian prototype structure. No Jacobian structure,
     sparsity pattern, or code-generation integration is created here.

     Runtime/generated order:
       1. tangent pass of primal strong components
       2. reverse pass of primal strong components in lambda direction
       3. forward pass of generated reverse components in v direction
    "
    extends hessianInterface;
  protected
    String newName = name + "_HVP";
    Pointer<Integer> idx = Pointer.create(0);
    ForwardOverReverseProgram program;
  algorithm
    _ := equations;
    _ := full;

    program := createForwardOverReverseFiltered(
      newName,
      newName + "_REV",
      BJacobian.getTmpFilterFunction(jacType),
      seedCandidates,
      partialCandidates,
      strongComponents,
      funcMap,
      staticAsContinuous,
      idx
    );

    hessian := SOME(fromForwardOverReverseProgram(
      newName,
      jacType,
      program
    ));
  end symbolicForwardOverReverse;

  function forFunctionVariables
    "Create an HVP program for lambda^T * functionVars(differentiationVars).

     functionVars are the mathematical rows F seeded by lambda.
     differentiationVars are the x variables with direction seeds v and HVP
     results h.
     innerVars are backend-dependent variables solved inside the strong
     components that must receive tangents and adjoints, but are not rows of F.
    "
    input VariablePointers functionVars;
    input VariablePointers differentiationVars;
    input VariablePointers innerVars;
    input EquationPointers equations;
    input array<StrongComponent> comps;
    input Option<Adjacency.Matrix> full;
    input UnorderedMap<Path, Function> funcMap;
    input String name;
    input JacobianType jacType = JacobianType.NLS;
    input Boolean staticAsContinuous;
    output Option<Hessian> hessian;
  protected
    String newName = name;
    Pointer<Integer> idx = Pointer.create(0);
    ForwardOverReverseProgram program;
  algorithm
    _ := equations;
    _ := full;

    program := createForwardOverReverse(
      newName,
      differentiationVars,
      functionVars,
      innerVars,
      SOME(comps),
      funcMap,
      staticAsContinuous,
      idx
    );

    hessian := SOME(fromForwardOverReverseProgram(
      newName,
      jacType,
      program
    ));
  end forFunctionVariables;

  function forStrongComponents
    "Convenience wrapper for direct strong-component HVP generation."
    input VariablePointers seedCandidates;
    input VariablePointers partialCandidates;
    input EquationPointers equations;
    input array<StrongComponent> comps;
    input Option<Adjacency.Matrix> full;
    input UnorderedMap<Path, Function> funcMap;
    input String name;
    input JacobianType jacType = JacobianType.NLS;
    input Boolean staticAsContinuous;
    output Option<Hessian> hessian;
  protected
    constant hessianInterface func = symbolicForwardOverReverse;
  algorithm
    hessian := func(
      name                = name,
      jacType             = jacType,
      seedCandidates      = seedCandidates,
      partialCandidates   = partialCandidates,
      equations           = equations,
      strongComponents    = SOME(comps),
      full                = full,
      funcMap             = funcMap,
      staticAsContinuous  = staticAsContinuous
    );
  end forStrongComponents;

protected
  function createForwardOverReverse
    "Create tangent(reverse(primal)) for lambda^T * functionVars(differentiationVars)."
    input String name;
    input VariablePointers differentiationVars;
    input VariablePointers functionVars;
    input VariablePointers innerVars;
    input Option<array<StrongComponent>> strongComponents;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    output ForwardOverReverseProgram program;
  protected
    NBAdjoint.Program reverseProgram;
  algorithm
    reverseProgram := NBAdjoint.create(
      name,
      differentiationVars,
      functionVars,
      innerVars,
      strongComponents,
      funcMap,
      staticAsContinuous,
      idx,
      NBForward.Allocation.FRESH
    );

    program := createForwardOverReverseFromAdjoint(
      name,
      differentiationVars,
      funcMap,
      staticAsContinuous,
      idx,
      reverseProgram
    );
  end createForwardOverReverse;

  function createForwardOverReverseFiltered
    "Create tangent(reverse(primal)) using the Jacobian row-filter convention."
    input String name;
    input String reverseName;
    input BVariable.checkVar rowFilter;
    input VariablePointers seedCandidates;
    input VariablePointers partialCandidates;
    input Option<array<StrongComponent>> strongComponents;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    output ForwardOverReverseProgram program;
  protected
    NBAdjoint.Program reverseProgram;
    list<Pointer<Variable>> functionVars, innerVars;
  algorithm
    (functionVars, innerVars) := List.splitOnTrue(VariablePointers.toList(partialCandidates), rowFilter);

    reverseProgram := NBAdjoint.create(
      reverseName,
      seedCandidates,
      VariablePointers.fromList(functionVars, partialCandidates.scalarized),
      VariablePointers.fromList(innerVars, partialCandidates.scalarized),
      strongComponents,
      funcMap,
      staticAsContinuous,
      idx
    );

    program := createForwardOverReverseFromAdjoint(
      name,
      seedCandidates,
      funcMap,
      staticAsContinuous,
      idx,
      reverseProgram
    );
  end createForwardOverReverseFiltered;

  function createForwardOverReverseFromAdjoint
    "Differentiate an already generated adjoint program in a forward direction."
    input String name;
    input VariablePointers differentiationVars;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input NBAdjoint.Program reverseProgram;
    output ForwardOverReverseProgram program;
  protected
    list<StrongComponent> comps;

    list<Pointer<Variable>> tmpVars;
    list<Pointer<Variable>> unknownVars;
    list<Pointer<Variable>> auxiliaryVars;
    list<Pointer<Variable>> variables;

    NBForward.Program tangentProgram;
    NBForward.Program forwardReverseProgram;
  algorithm
    tangentProgram := NBForward.create(
      name = "TAN_" + name,
      differentiationVars = differentiationVars,
      functionVars = VariablePointers.fromList({}, differentiationVars.scalarized),
      innerVars = VariablePointers.fromList(listAppend(reverseProgram.seedBaseVars, reverseProgram.tmpBaseVars), differentiationVars.scalarized),
      strongComponents = SOME(listArray(reverseProgram.primalComps)),
      funcMap = funcMap,
      staticAsContinuous = staticAsContinuous,
      idx = idx,
      allocation = NBForward.Allocation.FRESH,
      seedName = name + "_V",
      tmpName = "TAN_" + name,
      cleanupAlgorithms = true
    );

    forwardReverseProgram := NBForward.create(
      name = "FOR_" + name,
      differentiationVars = VariablePointers.fromList({}, differentiationVars.scalarized),
      functionVars = VariablePointers.fromList(reverseProgram.resultVars, reverseProgram.scalarized),
      innerVars = VariablePointers.fromList(reverseProgram.tmpVars, reverseProgram.scalarized),
      strongComponents = NONE(),
      funcMap = funcMap,
      staticAsContinuous = staticAsContinuous,
      idx = idx,
      allocation = NBForward.Allocation.FRESH,
      baseProgram = SOME(reverseProgram),
      initialMap = SOME(tangentProgram.diffMap),
      resultName = "HVP_" + name,
      tmpName = "FOR_" + name,
      cleanupAlgorithms = true
    );

    comps := listAppend(tangentProgram.comps, listAppend(reverseProgram.comps, forwardReverseProgram.comps));

    tmpVars := listAppend(
      tangentProgram.tmpVars,
      listAppend(
        reverseProgram.resultVars,
        listAppend(reverseProgram.tmpVars, forwardReverseProgram.tmpVars)
      )
    );

    unknownVars := listAppend(forwardReverseProgram.resultVars, tmpVars);
    auxiliaryVars := listAppend(reverseProgram.seedVars, tangentProgram.seedVars);
    variables := listAppend(unknownVars, auxiliaryVars);

    program := ForwardOverReverseProgram.FORWARD_OVER_REVERSE_PROGRAM(
      name                = name,
      directionMap        = tangentProgram.diffMap,
      reverseMap          = reverseProgram.diffMap,
      forwardReverseMap   = forwardReverseProgram.diffMap,
      tangentComps        = tangentProgram.comps,
      reverseComps        = reverseProgram.comps,
      forwardReverseComps = forwardReverseProgram.comps,
      comps               = comps,
      lambdaVars          = reverseProgram.seedVars,
      directionVars       = tangentProgram.seedVars,
      resultVars          = forwardReverseProgram.resultVars,
      tmpVars             = tmpVars,
      unknownVars         = unknownVars,
      auxiliaryVars       = auxiliaryVars,
      variables           = variables
    );
  end createForwardOverReverseFromAdjoint;

  function mapToString
    input String title;
    input UnorderedMap<ComponentRef, ComponentRef> map;
    output String str;
  algorithm
    str := StringUtil.headline_3(title) + "\n";
    str := str + UnorderedMap.toString(map, ComponentRef.toString, ComponentRef.toString, "\n  ", " -> ") + "\n";
  end mapToString;

  annotation(__OpenModelica_Interface="nbackend");
end NBHessian;
