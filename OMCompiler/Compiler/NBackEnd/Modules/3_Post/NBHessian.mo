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
 description: Symbolic Hessian-vector product construction.
"

public
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
  import NBProgram;
  import NBVariable.VariablePointers;
  import StrongComponent = NBStrongComponent;

  // Util imports
  import Flags;
  import StringUtil;
  import UnorderedMap;

public
  uniontype Hessian
    "Symbolic Hessian-vector product program before lowering to BackendDAE."
    record HESSIAN
      String       name    "unique HVP name";
      JacobianType jacType "corresponding function block type";

      VariablePointers variables   "all generated HVP variables";
      VariablePointers unknowns    "generated HVP unknowns";
      VariablePointers auxiliaries "generated HVP auxiliaries";

      VariablePointers resultVars    "HVP result variables h";
      VariablePointers tmpVars       "all internal tangent / adjoint / forward-over-reverse variables";
      VariablePointers lambdaVars    "fixed reverse seed lambda";
      VariablePointers directionVars "forward direction seed v";

      array<StrongComponent> comps "ordered HVP components";
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

protected
  function printGeneration
    input String name;
    input Hessian hessian;
  algorithm
    print(StringUtil.headline_1("[symhessdump] " + name + " forward-over-reverse Hessian-vector product") + "\n");
    print(Hessian.toString(hessian));
  end printGeneration;

public
  function symbolicForwardOverReverse
    "Symbolic Hessian-vector product generation.

     Builds a separate Hessian structure. No Jacobian structure,
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
    BVariable.checkVar rowFilter = BJacobian.getTmpFilterFunction(jacType);
    list<Pointer<Variable>> functionVars, innerVars;
    Hessian hessianValue;
  algorithm
    _ := equations;
    _ := full;

    (functionVars, innerVars) := List.splitOnTrue(VariablePointers.toList(partialCandidates), rowFilter);

    hessianValue := createForwardOverReverse(
      newName,
      jacType,
      seedCandidates,
      VariablePointers.fromList(functionVars, partialCandidates.scalarized),
      VariablePointers.fromList(innerVars, partialCandidates.scalarized),
      strongComponents,
      funcMap,
      staticAsContinuous,
      idx
    );

    hessian := SOME(hessianValue);
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
    Hessian hessianValue;
  algorithm
    _ := equations;
    _ := full;

    hessianValue := createForwardOverReverse(
      newName,
      jacType,
      differentiationVars,
      functionVars,
      innerVars,
      SOME(comps),
      funcMap,
      staticAsContinuous,
      idx
    );

    hessian := SOME(hessianValue);
  end forFunctionVariables;

protected
  function createForwardOverReverse
    "Create forward(reverse(primal)) for lambda^T * functionVars(differentiationVars).
     Returns the flattened HVP structure consumed by lowering/code generation."
    input String name;
    input JacobianType jacType;
    input VariablePointers differentiationVars;
    input VariablePointers functionVars;
    input VariablePointers innerVars;
    input Option<array<StrongComponent>> strongComponents;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    output Hessian hessianValue;
  protected
    NBProgram.Program primalProgram;
    NBProgram.Program adjointProgram;
    NBProgram.Program program;
    NBProgram.Flat flat;
    list<Pointer<Variable>> directionVars;
  algorithm
    primalProgram := NBProgram.fromStrongComponents(
      name,
      differentiationVars,
      functionVars,
      innerVars,
      strongComponents,
      funcMap,
      staticAsContinuous,
      idx,
      NBProgram.defaultOptions(name, NBProgram.Allocation.FRESH)
    );

    adjointProgram := NBAdjoint.create(primalProgram, name);
    adjointProgram := NBProgram.withOptions(
      adjointProgram,
      NBProgram.options(
        NBProgram.Allocation.FRESH,
        name + "_V",
        "HVP_" + name,
        "FOR_" + name,
        cleanupAlgorithms = true)
    );
    program := NBForward.create(adjointProgram);

    flat := NBProgram.flatten(program);
    directionVars := NBProgram.lookupMappedVariables(
      NBProgram.uniqueVariables(VariablePointers.toList(differentiationVars)),
      program.diffMap
    );

    hessianValue := Hessian.HESSIAN(
      name          = name,
      jacType       = jacType,
      variables     = VariablePointers.fromList(flat.variables),
      unknowns      = VariablePointers.fromList(flat.unknowns),
      auxiliaries   = VariablePointers.fromList(flat.auxiliaries),
      resultVars    = VariablePointers.fromList(flat.resultVars),
      tmpVars       = VariablePointers.fromList(flat.tmpVars),
      lambdaVars    = VariablePointers.fromList(adjointProgram.seedVars),
      directionVars = VariablePointers.fromList(directionVars),
      comps         = listArray(flat.comps)
    );

    if Flags.isSet(Flags.JAC_DUMP) then
      printGeneration(name, hessianValue);
    end if;
  end createForwardOverReverse;

  annotation(__OpenModelica_Interface="nbackend");
end NBHessian;
