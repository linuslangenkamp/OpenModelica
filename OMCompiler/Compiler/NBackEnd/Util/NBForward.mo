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

encapsulated package NBForward
"file:        NBForward.mo
 package:     NBForward
 description: Shared forward-mode program construction for symbolic
              Jacobians and Hessian-vector products.
"

public
  import NBVariable;

protected
  // OF imports
  import Absyn.Path;
  import DAE;

  // NF imports
  import Algorithm = NFAlgorithm;
  import ComponentRef = NFComponentRef;
  import Expression = NFExpression;
  import NFBackendExtension.{BackendInfo, VariableKind};
  import NFInstNode.InstNode;
  import NFFunction.Function;
  import Statement = NFStatement;
  import Type = NFType;
  import Variable = NFVariable;

  // Backend imports
  import BVariable = NBVariable;
  import Differentiate = NBDifferentiate;
  import NBDifferentiate.DifferentiationArguments;
  import NBEquation.Equation;
  import Slice = NBSlice;
  import NBVariable.VariablePointers;
  import StrongComponent = NBStrongComponent;

  // Util imports
  import Error;
  import UnorderedMap;
  import UnorderedSet;
  import Util;

public
  type Allocation = enumeration(
    REUSE "Use NBVariable seed/pDer partner variables",
    FRESH "Always allocate a fresh role-named derivative variable"
  );

  type VariableRole = enumeration(
    SEED,
    RESULT,
    TMP,
    ADJOINT_RESULT,
    ADJOINT_TMP
  );

  uniontype Program
    record PROGRAM
      String name;
      UnorderedMap<ComponentRef, ComponentRef> diffMap;
      list<StrongComponent> primalComps;
      list<StrongComponent> comps;
      Boolean scalarized;
      list<Pointer<Variable>> seedVars;
      list<Pointer<Variable>> resultVars;
      list<Pointer<Variable>> tmpVars;
      list<Pointer<Variable>> seedBaseVars;
      list<Pointer<Variable>> resultBaseVars;
      list<Pointer<Variable>> tmpBaseVars;
    end PROGRAM;
  end Program;

  function create
    "Create a symbolic forward-mode program.

     differentiationVars are the independent variables x.
     functionVars are the requested rows F.
     innerVars are dependent backend variables that need tangents but are not rows.
     If baseProgram is given, its generated components are differentiated. This
     is the chaining API used for forward-over-adjoint Hessian-vector products.
    "
    input String name;
    input VariablePointers differentiationVars;
    input VariablePointers functionVars;
    input VariablePointers innerVars;
    input Option<array<StrongComponent>> strongComponents;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input Allocation allocation = Allocation.FRESH;
    input Option<Program> baseProgram = NONE();
    input Option<UnorderedMap<ComponentRef, ComponentRef>> initialMap = NONE();
    input String seedName = "";
    input String resultName = "";
    input String tmpName = "";
    input Boolean cleanupAlgorithms = false;
    output Program program;
  protected
    Program base;
    list<StrongComponent> primalComps, comps;
    list<Pointer<Variable>> seedBaseVars, resultSourceVars, resultBaseVars, tmpBaseVars;
    list<Pointer<Variable>> resultVars = {}, tmpVars = {}, seedVars = {};
    UnorderedMap<ComponentRef, ComponentRef> diffMap;
    list<StrongComponent> diffedComps;
    Boolean scalarized;
    String seedPrefix = if seedName == "" then name else seedName;
    String resultPrefix = if resultName == "" then name else resultName;
    String tmpPrefix = if tmpName == "" then name else tmpName;
  algorithm
    diffMap := match initialMap
      case SOME(diffMap) then UnorderedMap.copy(diffMap);
      else UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual);
    end match;

    if isSome(baseProgram) then
      base := Util.getOption(baseProgram);
      primalComps := base.primalComps;
      comps := base.comps;
      scalarized := base.scalarized;
    else
      if isSome(strongComponents) then
        comps := list(comp for comp guard(not StrongComponent.isDiscrete(comp)) in Util.getOption(strongComponents));
        primalComps := comps;
        scalarized := differentiationVars.scalarized;
      else
        Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed because neither strong components nor a base program were given."});
        fail();
      end if;
    end if;

    seedBaseVars := VariablePointers.toList(differentiationVars);
    (diffMap, seedVars) := mapVariables(
      seedBaseVars,
      seedPrefix,
      VariableRole.SEED,
      allocation,
      staticAsContinuous,
      idx,
      diffMap,
      seedVars
    );

    resultSourceVars := VariablePointers.toList(functionVars);
    resultBaseVars := getNamingVars(resultSourceVars, baseProgram);
    tmpBaseVars := list(var for var guard(BVariable.isContinuous(var, staticAsContinuous)) in VariablePointers.toList(innerVars));

    (diffMap, resultVars, _) := mapVariablesWithNaming(
      resultSourceVars,
      SOME(resultBaseVars),
      resultPrefix,
      VariableRole.RESULT,
      allocation,
      staticAsContinuous,
      idx,
      diffMap
    );

    (diffMap, tmpVars) := mapVariables(
      tmpBaseVars,
      tmpPrefix,
      VariableRole.TMP,
      allocation,
      staticAsContinuous,
      idx,
      diffMap,
      tmpVars
    );

    diffedComps := differentiateStrongComponentList(
      comps,
      diffMap,
      funcMap,
      scalarized,
      idx,
      name,
      cleanupAlgorithms
    );

    program := Program.PROGRAM(
      name           = name,
      diffMap        = diffMap,
      primalComps    = primalComps,
      comps          = diffedComps,
      scalarized     = scalarized,
      seedVars       = seedVars,
      resultVars     = resultVars,
      tmpVars        = tmpVars,
      seedBaseVars   = seedBaseVars,
      resultBaseVars = resultBaseVars,
      tmpBaseVars    = tmpBaseVars
    );
  end create;

  function mapVariables
    "Map base variables to derivative variables for one forward/adjoint role."
    input list<Pointer<Variable>> baseVars;
    input String name;
    input VariableRole role;
    input Allocation allocation;
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
        allocation,
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

protected
  function differentiateStrongComponentList
    "Forward differentiate strong components with an explicit seed map."
    input list<StrongComponent> comps;
    input UnorderedMap<ComponentRef, ComponentRef> diffMap;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean scalarized;
    input Pointer<Integer> idx;
    input String contextName;
    input Boolean cleanupAlgorithms = false;
    output list<StrongComponent> diffedComps;
  protected
    DifferentiationArguments diffArguments;
  algorithm
    diffArguments := Differentiate.DIFFERENTIATION_ARGUMENTS(
      diffCref        = ComponentRef.EMPTY(),
      new_vars        = {},
      diff_map        = SOME(diffMap),
      diffType        = NBDifferentiate.DifferentiationType.JACOBIAN,
      funcMap         = funcMap,
      scalarized      = scalarized,
      adjoint_map     = NONE(),
      current_grad    = Expression.EMPTY(Type.REAL()),
      collectAdjoints = false
    );

    (diffedComps, _) := Differentiate.differentiateStrongComponentList(
      comps,
      diffArguments,
      idx,
      contextName,
      getInstanceName()
    );

    if cleanupAlgorithms then
      diffedComps := cleanupForwardComponents(diffedComps, diffMap);
    end if;
  end differentiateStrongComponentList;

  function getNamingVars
    input list<Pointer<Variable>> sourceVars;
    input Option<Program> baseProgram;
    output list<Pointer<Variable>> namingVars = {};
  protected
    Program base;
  algorithm
    if isSome(baseProgram) then
      base := Util.getOption(baseProgram);
      for sourceVar in sourceVars loop
        namingVars := lookupBaseVar(sourceVar, base.resultVars, base.resultBaseVars) :: namingVars;
      end for;
      namingVars := listReverse(namingVars);
    else
      namingVars := sourceVars;
    end if;
  end getNamingVars;

  function lookupBaseVar
    input Pointer<Variable> sourceVar;
    input list<Pointer<Variable>> generatedVars;
    input list<Pointer<Variable>> baseVars;
    output Pointer<Variable> baseVar = sourceVar;
  protected
    list<Pointer<Variable>> generatedRest = generatedVars;
    list<Pointer<Variable>> baseRest = baseVars;
    Pointer<Variable> generatedVar;
    Pointer<Variable> candidateBaseVar;
    ComponentRef sourceCref = BVariable.getVarName(sourceVar);
  algorithm
    while not listEmpty(generatedRest) and not listEmpty(baseRest) loop
      generatedVar :: generatedRest := generatedRest;
      candidateBaseVar :: baseRest := baseRest;
      if ComponentRef.isEqual(sourceCref, BVariable.getVarName(generatedVar)) then
        baseVar := candidateBaseVar;
        return;
      end if;
    end while;
  end lookupBaseVar;

  function mapVariablesWithNaming
    input list<Pointer<Variable>> sourceVars;
    input Option<list<Pointer<Variable>>> namingVarsOpt;
    input String name;
    input VariableRole role;
    input Allocation allocation;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input UnorderedMap<ComponentRef, ComponentRef> mapIn;
    output UnorderedMap<ComponentRef, ComponentRef> mapOut;
    output list<Pointer<Variable>> tangentVars;
    output list<Pointer<Variable>> mappedSourceVars;
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
    mappedSourceVars := {};

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
        allocation,
        staticAsContinuous,
        idx,
        mapOut
      );

      if mapped and not ComponentRef.isEmpty(tangentCref) then
        tangentVars := tangentVar :: tangentVars;
        mappedSourceVars := sourceVar :: mappedSourceVars;
      end if;
    end while;

    tangentVars := listReverse(tangentVars);
    mappedSourceVars := listReverse(mappedSourceVars);
  end mapVariablesWithNaming;

  function mapVariableWithNaming
    input Pointer<Variable> sourceVar;
    input Pointer<Variable> namingVar;
    input String name;
    input VariableRole role;
    input Allocation allocation;
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

    (newCref, newVar) := makeVariable(namingVar, name, role, allocation, idx);
    UnorderedMap.add(sourceCref, newCref, mapOut);
    mapped := true;

    () := match (BVariable.getParent(sourceVar), BVariable.getParent(namingVar))
      case (SOME(sourceParent), SOME(namingParent)) algorithm
        sourceParentCref := BVariable.getVarName(sourceParent);
        diffParent := match UnorderedMap.get(sourceParentCref, mapOut)
          case SOME(diffParentCref) then BVariable.getVarPointer(diffParentCref, sourceInfo());
          else algorithm
            (diffParentCref, diffParent) := makeVariable(namingParent, name, role, allocation, idx);
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
    input Allocation allocation;
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

    (newCref, newVar) := makeVariable(baseVar, name, role, allocation, idx);
    UnorderedMap.add(baseCref, newCref, mapOut);
    created := true;

    () := match BVariable.getParent(baseVar)
      case SOME(parent) algorithm
        parentCref := BVariable.getVarName(parent);
        diffParent := match UnorderedMap.get(parentCref, mapOut)
          case SOME(diffParentCref) then BVariable.getVarPointer(diffParentCref, sourceInfo());
          else algorithm
            (diffParentCref, diffParent) := makeVariable(parent, name, role, allocation, idx);
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
    input Allocation allocation;
    input Pointer<Integer> idx;
    output ComponentRef cref;
    output Pointer<Variable> varPtr;
  algorithm
    if allocation == Allocation.REUSE then
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

  function cleanupForwardComponents
    "Drop original algorithm assignments left by generic forward
     differentiation. A forward program should only assign derivative
     variables; primal/reverse programs execute in their own stages."
    input list<StrongComponent> comps;
    input UnorderedMap<ComponentRef, ComponentRef> diffMap;
    output list<StrongComponent> cleaned = {};
  protected
    UnorderedSet<ComponentRef> derivativeCrefs;
    list<StrongComponent> compCleaned;
  algorithm
    derivativeCrefs := UnorderedSet.fromList(
      UnorderedMap.valueList(diffMap),
      ComponentRef.hash,
      ComponentRef.isEqual
    );

    for comp in comps loop
      compCleaned := cleanupForwardComponent(comp, derivativeCrefs);
      cleaned := listAppend(compCleaned, cleaned);
    end for;

    cleaned := listReverse(cleaned);
  end cleanupForwardComponents;

  function cleanupForwardComponent
    input StrongComponent comp;
    input UnorderedSet<ComponentRef> derivativeCrefs;
    output list<StrongComponent> cleaned;
  protected
    Pointer<Equation> eqnPtr;
    Equation eqn;
    Algorithm alg;
    list<Statement> stmts;
  algorithm
    cleaned := match comp
      case StrongComponent.MULTI_COMPONENT(eqn = Slice.SLICE(__)) algorithm
        eqnPtr := Slice.getT(comp.eqn);
        eqn := Pointer.access(eqnPtr);
        () := match eqn
          case Equation.ALGORITHM(alg = alg) algorithm
            stmts := cleanupForwardStatements(alg.statements, derivativeCrefs);
            if listEmpty(stmts) then
              cleaned := {};
            else
              alg.statements := stmts;
              eqn.alg := alg;
              Pointer.update(eqnPtr, eqn);
              cleaned := {comp};
            end if;
          then ();

          else algorithm
            cleaned := {comp};
          then ();
        end match;
      then cleaned;

      else {comp};
    end match;
  end cleanupForwardComponent;

  function cleanupForwardStatements
    input list<Statement> stmtsIn;
    input UnorderedSet<ComponentRef> derivativeCrefs;
    output list<Statement> stmtsOut = {};
  protected
    list<Statement> body;
    list<tuple<Expression, list<Statement>>> branchesIn;
    list<tuple<Expression, list<Statement>>> branches;
    Expression condition;
    InstNode iterator;
    Option<Expression> range;
    Statement.ForType forType;
    DAE.ElementSource source;
  algorithm
    for stmtIn in stmtsIn loop
      () := match stmtIn
        case Statement.ASSIGNMENT() algorithm
          if keepForwardAssignment(stmtIn, derivativeCrefs) then
            stmtsOut := stmtIn :: stmtsOut;
          end if;
        then ();

        case Statement.FOR(iterator = iterator, range = range, body = body, forType = forType, source = source) algorithm
          body := cleanupForwardStatements(body, derivativeCrefs);
          if not listEmpty(body) then
            stmtsOut := Statement.FOR(iterator, range, body, forType, source) :: stmtsOut;
          end if;
        then ();

        case Statement.IF(branches = branchesIn, source = source) algorithm
          branches := {};
          for branch in branchesIn loop
            (condition, body) := branch;
            body := cleanupForwardStatements(body, derivativeCrefs);
            if not listEmpty(body) then
              branches := (condition, body) :: branches;
            end if;
          end for;

          if not listEmpty(branches) then
            stmtsOut := Statement.IF(listReverse(branches), source) :: stmtsOut;
          end if;
        then ();

        else ();
      end match;
    end for;

    stmtsOut := listReverse(stmtsOut);
  end cleanupForwardStatements;

  function keepForwardAssignment
    input Statement stmt;
    input UnorderedSet<ComponentRef> derivativeCrefs;
    output Boolean keep;
  protected
    ComponentRef lhsCref;
  algorithm
    keep := match stmt
      case Statement.ASSIGNMENT(lhs = Expression.CREF(cref = lhsCref)) then
        UnorderedSet.contains(ComponentRef.stripSubscriptsAll(lhsCref), derivativeCrefs)
        and not isSelfAssignment(stmt);

      else false;
    end match;
  end keepForwardAssignment;

  function isSelfAssignment
    input Statement stmt;
    output Boolean self;
  protected
    ComponentRef lhsCref;
    ComponentRef rhsCref;
  algorithm
    self := match stmt
      case Statement.ASSIGNMENT(
        lhs = Expression.CREF(cref = lhsCref),
        rhs = Expression.CREF(cref = rhsCref))
      then ComponentRef.isEqual(lhsCref, rhsCref);

      else false;
    end match;
  end isSelfAssignment;

  annotation(__OpenModelica_Interface="nbackend");
end NBForward;
