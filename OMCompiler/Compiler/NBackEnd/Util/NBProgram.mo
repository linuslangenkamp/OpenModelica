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

encapsulated package NBProgram
"file:        NBProgram.mo
 package:     NBProgram
 description: Shared staged backend program representation for symbolic AD.
"

public
  import NBVariable;

protected
  // OF imports
  import Absyn.Path;

  // NF imports
  import ComponentRef = NFComponentRef;
  import NFFunction.Function;
  import Variable = NFVariable;

  // Backend imports
  import NBVariable.VariablePointers;
  import StrongComponent = NBStrongComponent;

  // Util imports
  import Error;
  import UnorderedMap;
  import Util;

public
  type Kind = enumeration(
    PRIMAL,
    FORWARD,
    ADJOINT
  );

  type Allocation = enumeration(
    REUSE "Use NBVariable seed/pDer partner variables",
    FRESH "Always allocate a fresh role-named derivative variable"
  );

  uniontype Names
    record NAMES
      String seed;
      String result;
      String tmp;
      Boolean cleanup;
    end NAMES;
  end Names;

  uniontype Program
    record PROGRAM
      String name;
      Kind kind;
      Integer level;
      Option<Program> source;
      list<Program> dependencies;
      list<Pointer<Variable>> sourceVars;

      UnorderedMap<ComponentRef, ComponentRef> diffMap;
      list<StrongComponent> primalComps;
      list<StrongComponent> comps;
      Boolean scalarized;

      list<Pointer<Variable>> domainVars;
      list<Pointer<Variable>> rangeVars;
      list<Pointer<Variable>> innerVars;

      list<Pointer<Variable>> seedVars;
      list<Pointer<Variable>> resultVars;
      list<Pointer<Variable>> tmpVars;

      list<Pointer<Variable>> seedBaseVars;
      list<Pointer<Variable>> resultBaseVars;
      list<Pointer<Variable>> tmpBaseVars;

      UnorderedMap<Path, Function> funcMap;
      Boolean staticAsContinuous;
      Pointer<Integer> idx;
      Allocation allocation;
      Names names;
    end PROGRAM;
  end Program;

  uniontype Flat
    record FLAT
      list<StrongComponent> comps;
      list<Pointer<Variable>> variables;
      list<Pointer<Variable>> unknowns;
      list<Pointer<Variable>> auxiliaries;
      list<Pointer<Variable>> resultVars;
      list<Pointer<Variable>> tmpVars;
      list<Pointer<Variable>> seedVars;
    end FLAT;
  end Flat;

  function defaultNames
    input String name;
    output Names names = Names.NAMES(name, name, name, false);
  end defaultNames;

  function fromStrongComponents
    input String name;
    input VariablePointers domainVars;
    input VariablePointers rangeVars;
    input VariablePointers innerVars;
    input Option<array<StrongComponent>> strongComponents;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input Allocation allocation = Allocation.FRESH;
    input Names names = defaultNames(name);
    output Program program;
  protected
    list<StrongComponent> comps;
  algorithm
    if isSome(strongComponents) then
      comps := list(comp for comp guard(not StrongComponent.isDiscrete(comp)) in Util.getOption(strongComponents));
    else
      Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed because no strong components were given."});
      fail();
    end if;

    program := PROGRAM(
      name           = name,
      kind           = Kind.PRIMAL,
      level          = 0,
      source         = NONE(),
      dependencies   = {},
      sourceVars     = {},
      diffMap        = UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual),
      primalComps    = comps,
      comps          = comps,
      scalarized     = domainVars.scalarized,
      domainVars     = VariablePointers.toList(domainVars),
      rangeVars      = VariablePointers.toList(rangeVars),
      innerVars      = VariablePointers.toList(innerVars),
      seedVars       = {},
      resultVars     = {},
      tmpVars        = {},
      seedBaseVars   = {},
      resultBaseVars = {},
      tmpBaseVars    = {},
      funcMap        = funcMap,
      staticAsContinuous = staticAsContinuous,
      idx            = idx,
      allocation     = allocation,
      names          = names
    );
  end fromStrongComponents;

  function make
    input String name;
    input Kind kind;
    input Integer level;
    input Option<Program> source;
    input list<Program> dependencies;
    input list<Pointer<Variable>> sourceVars;
    input UnorderedMap<ComponentRef, ComponentRef> diffMap;
    input list<StrongComponent> primalComps;
    input list<StrongComponent> comps;
    input Boolean scalarized;
    input list<Pointer<Variable>> domainVars;
    input list<Pointer<Variable>> rangeVars;
    input list<Pointer<Variable>> innerVars;
    input list<Pointer<Variable>> seedVars;
    input list<Pointer<Variable>> resultVars;
    input list<Pointer<Variable>> tmpVars;
    input list<Pointer<Variable>> seedBaseVars;
    input list<Pointer<Variable>> resultBaseVars;
    input list<Pointer<Variable>> tmpBaseVars;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input Allocation allocation;
    input Names names;
    output Program program;
  algorithm
    program := PROGRAM(
      name, kind, level, source, dependencies, sourceVars, diffMap, primalComps, comps, scalarized,
      domainVars, rangeVars, innerVars, seedVars, resultVars, tmpVars,
      seedBaseVars, resultBaseVars, tmpBaseVars, funcMap, staticAsContinuous,
      idx, allocation, names);
  end make;

  function names
    input String seed;
    input String result;
    input String tmp;
    input Boolean cleanup = false;
    output Names outNames = Names.NAMES(seed, result, tmp, cleanup);
  end names;

  function setNames
    input output Program program;
    input Names names;
  algorithm
    program.names := names;
  end setNames;

  function flatten
    input Program program;
    output Flat flat;
  protected
    list<String> seen;
  algorithm
    (flat, seen) := flattenWork(program, {});
  end flatten;

protected
  function flattenWork
    input Program program;
    input list<String> seenIn;
    output Flat flat;
    output list<String> seenOut;
  protected
    list<StrongComponent> depComps;
    list<Pointer<Variable>> depResults, depTmps, depSeeds;
    list<Pointer<Variable>> resultVars, tmpVars, seedVars, unknowns, auxiliaries, variables;
    String id;
  algorithm
    id := programId(program);
    if stringListContains(id, seenIn) then
      flat := Flat.FLAT({}, {}, {}, {}, {}, {}, {});
      seenOut := seenIn;
      return;
    end if;

    seenOut := id :: seenIn;
    (depComps, depResults, depTmps, depSeeds, seenOut) := flattenDependencies(program.dependencies, seenOut);

    resultVars  := program.resultVars;
    tmpVars     := listAppend(depResults, listAppend(depTmps, program.tmpVars));
    seedVars    := listAppend(depSeeds, program.seedVars);
    unknowns    := listAppend(resultVars, tmpVars);
    auxiliaries := seedVars;
    variables   := listAppend(unknowns, auxiliaries);

    flat := Flat.FLAT(
      comps       = listAppend(depComps, program.comps),
      variables   = variables,
      unknowns    = unknowns,
      auxiliaries = auxiliaries,
      resultVars  = resultVars,
      tmpVars     = tmpVars,
      seedVars    = seedVars
    );
  end flattenWork;

  function flattenDependencies
    input list<Program> dependencies;
    input list<String> seenIn;
    output list<StrongComponent> comps = {};
    output list<Pointer<Variable>> resultVars = {};
    output list<Pointer<Variable>> tmpVars = {};
    output list<Pointer<Variable>> seedVars = {};
    output list<String> seenOut;
  protected
    Flat flat;
  algorithm
    seenOut := seenIn;
    for dep in listReverse(dependencies) loop
      (flat, seenOut) := flattenWork(dep, seenOut);
      comps      := listAppend(flat.comps, comps);
      resultVars := listAppend(flat.resultVars, resultVars);
      tmpVars    := listAppend(flat.tmpVars, tmpVars);
      seedVars   := listAppend(flat.seedVars, seedVars);
    end for;
  end flattenDependencies;

  function programId
    input Program program;
    output String id;
  algorithm
    id := kindString(program.kind) + ":" + program.name + ":" + intString(program.level);
  end programId;

  function kindString
    input Kind kind;
    output String str;
  algorithm
    str := match kind
      case Kind.PRIMAL  then "P";
      case Kind.FORWARD then "F";
      case Kind.ADJOINT then "A";
    end match;
  end kindString;

  function stringListContains
    input String str;
    input list<String> strings;
    output Boolean contains = false;
  algorithm
    for candidate in strings loop
      if candidate == str then
        contains := true;
        return;
      end if;
    end for;
  end stringListContains;

  annotation(__OpenModelica_Interface="nbackend");
end NBProgram;
