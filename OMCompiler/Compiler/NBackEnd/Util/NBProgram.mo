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
  import NFBackendExtension.{BackendInfo, VariableKind};
  import NFInstNode.InstNode;
  import NFFunction.Function;
  import Variable = NFVariable;

  // Backend imports
  import BVariable = NBVariable;
  import NBVariable.VariablePointers;
  import StrongComponent = NBStrongComponent;

  // Util imports
  import Error;
  import UnorderedMap;
  import Util;

public
  type Kind = enumeration(
    PRIMAL  "Original backend program F(x)",
    FORWARD "Forward-mode derivative program",
    ADJOINT "Reverse-mode adjoint program for lambda^T * F(x)"
  );

  type Allocation = enumeration(
    REUSE "Use NBVariable seed/pDer partner variables",
    FRESH "Always allocate a fresh role-named derivative variable"
  );

  type VariableRole = enumeration(
    SEED           "Input seed of a derivative stage",
    RESULT         "Output variable of a forward derivative stage",
    TMP            "Temporary variable of a forward derivative stage",
    ADJOINT_RESULT "Output adjoint accumulator of a reverse derivative stage",
    ADJOINT_TMP    "Temporary adjoint variable of a reverse derivative stage"
  );

  uniontype Options
    record OPTIONS
      Allocation allocation        "How derivative variables are allocated";
      String     seedPrefix        "Prefix/name context for seed variables";
      String     resultPrefix      "Prefix/name context for derivative result variables";
      String     tmpPrefix         "Prefix/name context for derivative temporary variables";
      Boolean    cleanupAlgorithms "Drop non-derivative assignments from differentiated algorithms";
    end OPTIONS;
  end Options;

  uniontype VariableSets
    "Variables introduced by one AD transformation.

     domain/range/inner describe the mathematical program represented by the
     new stage. seed/result/tmp are the variables introduced by this stage.
     The *BaseVars lists remember the source variables used for naming those
     introduced variables, which is needed for readable nested derivatives."
    record VARIABLE_SETS
      list<Pointer<Variable>> domainVars     "Mathematical input variables of the transformed program";
      list<Pointer<Variable>> rangeVars      "Mathematical output variables of the transformed program";
      list<Pointer<Variable>> innerVars      "Internal variables needed while evaluating the transformed program";
      list<Pointer<Variable>> seedVars       "Seed variables introduced by this transformation";
      list<Pointer<Variable>> resultVars     "Result variables introduced by this transformation";
      list<Pointer<Variable>> tmpVars        "Temporary variables introduced by this transformation";
      list<Pointer<Variable>> seedBaseVars   "Source variables used to create seedVars";
      list<Pointer<Variable>> resultBaseVars "Source variables used to name resultVars";
      list<Pointer<Variable>> tmpBaseVars    "Source variables used to create tmpVars";
    end VARIABLE_SETS;
  end VariableSets;

  uniontype Program
    "Staged backend program used by symbolic AD.

     domainVars are the mathematical input variables of the represented
     program. rangeVars are the represented outputs. innerVars are continuous
     backend variables that are needed while evaluating the program but are
     not part of the mathematical range.

     seedVars, resultVars and tmpVars are variables introduced by the current
     AD stage. The corresponding *BaseVars lists remember which source
     variables were named by those AD variables; this lets a later stage name
     forward-over-reverse results after the original variables instead of the
     intermediate adjoints.

     sourceVars lists variables from source whose tangents must be available
     when this program is differentiated again. dependencies are staged
     programs that must execute before this program when flattened."
    record PROGRAM
      String                  name         "Stable name used for diagnostics and generated variable names";
      Kind                    kind         "Kind of staged program";
      Integer                 level        "Derivative nesting depth used to identify flattened dependencies";
      Option<Program>         source       "Program this stage was derived from, if any";
      list<Program>           dependencies "Programs that must execute before this stage";
      list<Pointer<Variable>> sourceVars   "Source variables whose tangents are required when differentiating this stage again";

      UnorderedMap<ComponentRef, ComponentRef> diffMap     "Map from source component references to derivative component references";
      list<StrongComponent>                    primalComps "Original primal strong components for this staged computation";
      list<StrongComponent>                    comps       "Strong components that evaluate this stage";
      Boolean                                  scalarized  "Whether the variable pointer sets use scalarized component references";

      list<Pointer<Variable>> domainVars "Mathematical inputs of this staged program";
      list<Pointer<Variable>> rangeVars  "Mathematical outputs of this staged program";
      list<Pointer<Variable>> innerVars  "Internal variables required by this staged program";

      list<Pointer<Variable>> seedVars   "Seed variables introduced by this stage";
      list<Pointer<Variable>> resultVars "Derivative result variables introduced by this stage";
      list<Pointer<Variable>> tmpVars    "Derivative temporary variables introduced by this stage";

      list<Pointer<Variable>> seedBaseVars   "Source variables used to create seedVars";
      list<Pointer<Variable>> resultBaseVars "Source variables used to name resultVars";
      list<Pointer<Variable>> tmpBaseVars    "Source variables used to create tmpVars";

      UnorderedMap<Path, Function> funcMap            "Known functions needed by differentiation";
      Boolean                      staticAsContinuous "Treat static variables as differentiable continuous variables";
      Pointer<Integer>             idx                "Fresh variable/equation index shared by generated derivative stages";
      Options                      options            "Naming, allocation and cleanup options for later transformations";
    end PROGRAM;
  end Program;

  uniontype Flat
    "Executable flattened view of a staged program and its dependencies."
    record FLAT
      list<StrongComponent>    comps       "Dependency components followed by the final program components";
      list<Pointer<Variable>> variables   "All generated variables needed by the flattened program";
      list<Pointer<Variable>> unknowns    "Generated unknowns, i.e. results plus temporaries";
      list<Pointer<Variable>> auxiliaries "Generated auxiliaries, currently the seed variables";
      list<Pointer<Variable>> resultVars  "Result variables of the final program only";
      list<Pointer<Variable>> tmpVars     "Temporary variables from dependencies and the final program";
      list<Pointer<Variable>> seedVars    "Seed variables from dependencies and the final program";
    end FLAT;
  end Flat;

  function defaultOptions
    "Default AD options for one staged program name.
     Uses the same name context for seeds, results and temporaries."
    input String name;
    input Allocation allocation = Allocation.FRESH;
    output Options options = Options.OPTIONS(allocation, name, name, name, false);
  end defaultOptions;

  function options
    "Create explicit AD naming/allocation options.
     Use this when nested derivatives need separate seed/result/tmp names."
    input Allocation allocation;
    input String seedPrefix;
    input String resultPrefix;
    input String tmpPrefix;
    input Boolean cleanupAlgorithms = false;
    output Options outOptions = Options.OPTIONS(allocation, seedPrefix, resultPrefix, tmpPrefix, cleanupAlgorithms);
  end options;

  function fromStrongComponents
    "Create the primal staged program from backend strong components.
     Discrete strong components are ignored because AD only handles active code."
    input String name;
    input VariablePointers domainVars;
    input VariablePointers rangeVars;
    input VariablePointers innerVars;
    input Option<array<StrongComponent>> strongComponents;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input Options options = defaultOptions(name);
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
      options        = options
    );
  end fromStrongComponents;

  function withOptions
    "Update naming/allocation options for subsequent transformations.
     Existing components and variables are left unchanged."
    input output Program program;
    input Options options;
  algorithm
    program.options := options;
  end withOptions;

  function variableSets
    "Bundle variables produced by one transformation.
     Keeps fromTransform small without exposing the raw Program constructor."
    input list<Pointer<Variable>> domainVars;
    input list<Pointer<Variable>> rangeVars;
    input list<Pointer<Variable>> innerVars;
    input list<Pointer<Variable>> seedVars = {};
    input list<Pointer<Variable>> resultVars = {};
    input list<Pointer<Variable>> tmpVars = {};
    input list<Pointer<Variable>> seedBaseVars = {};
    input list<Pointer<Variable>> resultBaseVars = {};
    input list<Pointer<Variable>> tmpBaseVars = {};
    output VariableSets vars = VariableSets.VARIABLE_SETS(
      domainVars, rangeVars, innerVars, seedVars, resultVars, tmpVars,
      seedBaseVars, resultBaseVars, tmpBaseVars);
  end variableSets;

  function fromTransform
    "Create a derivative stage derived from sourceProgram.
     The caller supplies generated components, dependencies and variable sets."
    input Program sourceProgram;
    input Kind kind;
    input list<Program> dependencies;
    input list<Pointer<Variable>> sourceVars;
    input UnorderedMap<ComponentRef, ComponentRef> diffMap;
    input list<StrongComponent> comps;
    input VariableSets vars;
    output Program program;
  algorithm
    () := match vars
      case VariableSets.VARIABLE_SETS() algorithm
        program := PROGRAM(
          name           = sourceProgram.name,
          kind           = kind,
          level          = sourceProgram.level + 1,
          source         = SOME(sourceProgram),
          dependencies   = dependencies,
          sourceVars     = sourceVars,
          diffMap        = diffMap,
          primalComps    = sourceProgram.primalComps,
          comps          = comps,
          scalarized     = sourceProgram.scalarized,
          domainVars     = vars.domainVars,
          rangeVars      = vars.rangeVars,
          innerVars      = vars.innerVars,
          seedVars       = vars.seedVars,
          resultVars     = vars.resultVars,
          tmpVars        = vars.tmpVars,
          seedBaseVars   = vars.seedBaseVars,
          resultBaseVars = vars.resultBaseVars,
          tmpBaseVars    = vars.tmpBaseVars,
          funcMap        = sourceProgram.funcMap,
          staticAsContinuous = sourceProgram.staticAsContinuous,
          idx            = sourceProgram.idx,
          options        = sourceProgram.options
        );
      then ();
    end match;
  end fromTransform;

  function fromSourceTangent
    "Create a primal-looking source program whose forward derivative provides
     the tangents needed by a later derivative stage."
    input Program sourceProgram;
    input String name;
    input list<Pointer<Variable>> requiredVars;
    input Options options;
    output Program program;
  algorithm
    program := PROGRAM(
      name           = name,
      kind           = Kind.PRIMAL,
      level          = sourceProgram.level,
      source         = NONE(),
      dependencies   = {},
      sourceVars     = {},
      diffMap        = UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual),
      primalComps    = sourceProgram.primalComps,
      comps          = sourceProgram.comps,
      scalarized     = sourceProgram.scalarized,
      domainVars     = sourceProgram.domainVars,
      rangeVars      = {},
      innerVars      = requiredVars,
      seedVars       = {},
      resultVars     = {},
      tmpVars        = {},
      seedBaseVars   = {},
      resultBaseVars = {},
      tmpBaseVars    = {},
      funcMap        = sourceProgram.funcMap,
      staticAsContinuous = sourceProgram.staticAsContinuous,
      idx            = sourceProgram.idx,
      options        = options
    );
  end fromSourceTangent;

  function mapVariables
    "Map base variables to derivative variables for one AD role."
    input list<Pointer<Variable>> baseVars;
    input String name;
    input VariableRole role;
    input Options options;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input UnorderedMap<ComponentRef, ComponentRef> mapIn;
    input list<Pointer<Variable>> newVarsIn = {};
    output UnorderedMap<ComponentRef, ComponentRef> mapOut;
    output list<Pointer<Variable>> newVarsOut;
  protected
    list<Pointer<Variable>> localVars = {};
    Pointer<Variable> newVar;
    ComponentRef newCref;
    Boolean created;
  algorithm
    mapOut := mapIn;

    for baseVar in baseVars loop
      (mapOut, newVar, newCref, created) := mapVariable(
        baseVar,
        name,
        role,
        options,
        staticAsContinuous,
        idx,
        mapOut
      );

      if created and not ComponentRef.isEmpty(newCref) then
        localVars := newVar :: localVars;
      end if;
    end for;

    newVarsOut := listAppend(newVarsIn, listReverse(localVars));
  end mapVariables;

  function getNamingVars
    "Choose source variables used to name derivative result variables.
     A non-empty base list must match the source variable count."
    input list<Pointer<Variable>> sourceVars;
    input list<Pointer<Variable>> baseVars;
    output list<Pointer<Variable>> namingVars;
  algorithm
    if listEmpty(baseVars) then
      namingVars := sourceVars;
    elseif listLength(sourceVars) == listLength(baseVars) then
      namingVars := baseVars;
    else
      Error.addMessage(Error.INTERNAL_ERROR, {
        getInstanceName() + " got mismatching source and naming variables."
      });
      fail();
    end if;
  end getNamingVars;

  function mapVariablesWithNaming
    "Map source variables while naming created variables from another list.
     Used for nested derivatives whose result names should refer to base vars."
    input list<Pointer<Variable>> sourceVars;
    input Option<list<Pointer<Variable>>> namingVarsOpt;
    input String name;
    input VariableRole role;
    input Options options;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input UnorderedMap<ComponentRef, ComponentRef> mapIn;
    output UnorderedMap<ComponentRef, ComponentRef> mapOut;
    output list<Pointer<Variable>> tangentVars;
  protected
    list<Pointer<Variable>> srcRest;
    list<Pointer<Variable>> namingRest;
    Pointer<Variable> sourceVar;
    Pointer<Variable> namingVar;
    Pointer<Variable> tangentVar;
    ComponentRef tangentCref;
    Boolean mapped;
  algorithm
    mapOut := mapIn;
    tangentVars := {};

    namingRest := match namingVarsOpt
      case SOME(namingRest) algorithm
        if listLength(sourceVars) <> listLength(namingRest) then
          Error.addMessage(Error.INTERNAL_ERROR, {
            getInstanceName() + " got mismatching source and naming variables."
          });
          fail();
        end if;
      then namingRest;

      else sourceVars;
    end match;

    srcRest := sourceVars;
    while not listEmpty(srcRest) loop
      sourceVar :: srcRest := srcRest;
      namingVar :: namingRest := namingRest;

      (mapOut, tangentVar, tangentCref, mapped) := mapVariableWithNaming(
        sourceVar,
        namingVar,
        name,
        role,
        options,
        staticAsContinuous,
        idx,
        mapOut
      );

      if mapped and not ComponentRef.isEmpty(tangentCref) then
        tangentVars := tangentVar :: tangentVars;
      end if;
    end while;

    tangentVars := listReverse(tangentVars);
  end mapVariablesWithNaming;

  function flatten
    "Flatten a staged program and dependencies into executable order.
     The final resultVars stay separate from dependency temporaries."
    input Program program;
    output Flat flat;
  protected
    list<String> seen;
  algorithm
    (flat, seen) := flattenWork(program, {});
  end flatten;

protected
  function mapVariableWithNaming
    input Pointer<Variable> sourceVar;
    input Pointer<Variable> namingVar;
    input String name;
    input VariableRole role;
    input Options options;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input UnorderedMap<ComponentRef, ComponentRef> mapIn;
    output UnorderedMap<ComponentRef, ComponentRef> mapOut;
    output Pointer<Variable> newVar;
    output ComponentRef newCref;
    output Boolean mapped;
  protected
    ComponentRef sourceCref;
    ComponentRef sourceParentCref;
    ComponentRef diffParentCref;
    Pointer<Variable> sourceParent;
    Pointer<Variable> namingParent;
    Pointer<Variable> diffParent;
    Option<ComponentRef> existing;
  algorithm
    mapOut := mapIn;
    mapped := false;
    newVar := sourceVar;
    newCref := ComponentRef.EMPTY();

    if not BVariable.isContinuous(sourceVar, staticAsContinuous) then
      return;
    end if;

    sourceCref := BVariable.getVarName(sourceVar);
    existing := UnorderedMap.get(sourceCref, mapOut);
    if isSome(existing) then
      newCref := Util.getOption(existing);
      newVar := BVariable.getVarPointer(newCref, sourceInfo());
      mapped := true;
      return;
    end if;

    (newCref, newVar) := makeVariable(namingVar, name, role, options, idx);
    UnorderedMap.add(sourceCref, newCref, mapOut);
    mapped := true;

    () := match (BVariable.getParent(sourceVar), BVariable.getParent(namingVar))
      case (SOME(sourceParent), SOME(namingParent)) algorithm
        sourceParentCref := BVariable.getVarName(sourceParent);
        diffParent := match UnorderedMap.get(sourceParentCref, mapOut)
          case SOME(diffParentCref) then BVariable.getVarPointer(diffParentCref, sourceInfo());
          else algorithm
            (diffParentCref, diffParent) := makeVariable(namingParent, name, role, options, idx);
            UnorderedMap.add(sourceParentCref, diffParentCref, mapOut);
          then diffParent;
        end match;

        BVariable.addRecordChild(diffParent, newVar);
        newVar := BVariable.setParent(newVar, diffParent);
      then ();

      else ();
    end match;
  end mapVariableWithNaming;

  function mapVariable
    input Pointer<Variable> baseVar;
    input String name;
    input VariableRole role;
    input Options options;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input UnorderedMap<ComponentRef, ComponentRef> mapIn;
    output UnorderedMap<ComponentRef, ComponentRef> mapOut;
    output Pointer<Variable> newVar;
    output ComponentRef newCref;
    output Boolean created;
  protected
    ComponentRef baseCref;
    ComponentRef parentCref;
    ComponentRef diffParentCref;
    Pointer<Variable> parent;
    Pointer<Variable> diffParent;
    Option<ComponentRef> existing;
  algorithm
    mapOut := mapIn;
    created := false;
    newVar := baseVar;
    newCref := ComponentRef.EMPTY();

    if not BVariable.isContinuous(baseVar, staticAsContinuous) then
      return;
    end if;

    baseCref := BVariable.getVarName(baseVar);
    existing := UnorderedMap.get(baseCref, mapOut);
    if isSome(existing) then
      newCref := Util.getOption(existing);
      newVar := BVariable.getVarPointer(newCref, sourceInfo());
      return;
    end if;

    (newCref, newVar) := makeVariable(baseVar, name, role, options, idx);
    UnorderedMap.add(baseCref, newCref, mapOut);
    created := true;

    () := match BVariable.getParent(baseVar)
      case SOME(parent) algorithm
        parentCref := BVariable.getVarName(parent);
        diffParent := match UnorderedMap.get(parentCref, mapOut)
          case SOME(diffParentCref) then BVariable.getVarPointer(diffParentCref, sourceInfo());
          else algorithm
            (diffParentCref, diffParent) := makeVariable(parent, name, role, options, idx);
            UnorderedMap.add(parentCref, diffParentCref, mapOut);
          then diffParent;
        end match;

        BVariable.addRecordChild(diffParent, newVar);
        newVar := BVariable.setParent(newVar, diffParent);
      then ();

      else ();
    end match;
  end mapVariable;

  function makeVariable
    input Pointer<Variable> baseVar;
    input String name;
    input VariableRole role;
    input Options options;
    input Pointer<Integer> idx;
    output ComponentRef cref;
    output Pointer<Variable> varPtr;
  algorithm
    if options.allocation == Allocation.REUSE then
      (cref, varPtr) := makeReusableVariable(BVariable.getVarName(baseVar), name, role);
    else
      (cref, varPtr) := makeFreshVariable(baseVar, name, role, idx);
    end if;
  end makeVariable;

  function makeReusableVariable
    input output ComponentRef cref;
    input String name;
    input VariableRole role;
    output Pointer<Variable> varPtr;
  algorithm
    (cref, varPtr) := match role
      case VariableRole.SEED then
        BVariable.makeSeedVar(cref, name);

      case VariableRole.RESULT then
        BVariable.makePDerVar(cref, name, isTmp = false);

      case VariableRole.TMP then
        BVariable.makePDerVar(cref, name, isTmp = true);

      case VariableRole.ADJOINT_RESULT then
        BVariable.makePDerVar(cref, name, isTmp = false);

      case VariableRole.ADJOINT_TMP then
        BVariable.makePDerVar(cref, name, isTmp = true);
    end match;
  end makeReusableVariable;

  function makeFreshVariable
    input Pointer<Variable> baseVar;
    input String name;
    input VariableRole role;
    input Pointer<Integer> idx;
    output ComponentRef cref;
    output Pointer<Variable> varPtr;
  protected
    ComponentRef baseCref = BVariable.getVarName(baseVar);
    InstNode qual;
    Variable var;
    VariableKind varKind;
  algorithm
    () := match ComponentRef.node(baseCref)
      case qual as InstNode.VAR_NODE() algorithm
        qual.name := freshPrefix(name, role);
        cref := ComponentRef.append(baseCref, ComponentRef.fromNode(qual, ComponentRef.scalarType(baseCref)));

        var := if role == VariableRole.SEED
          then BVariable.fromCref(cref, NFAttributes.IMPL_DISCRETE_ATTR)
          else BVariable.fromCref(cref, Variable.attributes(Pointer.access(baseVar)));

        varKind := freshVariableKind(baseVar, role);
        var.backendinfo := BackendInfo.setVarKind(var.backendinfo, varKind);
        if role <> VariableRole.SEED and role <> VariableRole.RESULT then
          var.backendinfo := BackendInfo.setHideResult(var.backendinfo, true);
        end if;

        (varPtr, cref) := BVariable.makeVarPtrCyclic(var, cref);
      then ();

      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed for " + ComponentRef.toString(baseCref)});
      then fail();
    end match;
  end makeFreshVariable;

  function freshPrefix
    input String name;
    input VariableRole role;
    output String prefix;
  algorithm
    prefix := match role
      case VariableRole.SEED           then NBVariable.SEED_STR + "_" + name;
      case VariableRole.RESULT         then "$" + name;
      case VariableRole.TMP            then "$" + name;
      case VariableRole.ADJOINT_RESULT then "$ADJ_" + name;
      case VariableRole.ADJOINT_TMP    then "$ADJ_" + name;
    end match;
  end freshPrefix;

  function freshVariableKind
    input Pointer<Variable> baseVar;
    input VariableRole role;
    output VariableKind varKind;
  algorithm
    varKind := match BVariable.getVarKind(baseVar)
      case varKind as VariableKind.RECORD() algorithm
        varKind.children := {};
      then varKind;

      else match role
        case VariableRole.SEED           then VariableKind.SEED_VAR();
        case VariableRole.RESULT         then VariableKind.JAC_VAR();
        case VariableRole.TMP            then VariableKind.JAC_TMP_VAR();
        case VariableRole.ADJOINT_RESULT then VariableKind.JAC_VAR();
        case VariableRole.ADJOINT_TMP    then VariableKind.JAC_TMP_VAR();
      end match;
    end match;
  end freshVariableKind;

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
