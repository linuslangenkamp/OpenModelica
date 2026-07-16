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
  import NBProgram;
  import NBVariable;

protected
  // OF imports
  import Absyn.Path;
  import DAE;

  // NF imports
  import Algorithm = NFAlgorithm;
  import ComponentRef = NFComponentRef;
  import Expression = NFExpression;
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
  import StrongComponent = NBStrongComponent;

  // Util imports
  import Error;
  import UnorderedMap;
  import UnorderedSet;
  import Util;

public
  function create
    "Forward differentiate a staged backend program.
     Dependencies required by nested derivatives are created automatically."
    input NBProgram.Program program;
    input String stageName = "";
    output NBProgram.Program forwardProgram;
  algorithm
    forwardProgram := createForward(program, stageName);
  end create;

protected
  function createForward
    input NBProgram.Program program;
    input String stageName;
    output NBProgram.Program forwardProgram;
  protected
    list<Pointer<Variable>> seedSourceVars, resultSourceVars, resultBaseVars, tmpSourceVars, passiveSeedSourceVars;
    list<Pointer<Variable>> sourceVars;
    list<Pointer<Variable>> resultVars = {}, tmpVars = {}, seedVars = {};
    UnorderedMap<ComponentRef, ComponentRef> diffMap;
    list<StrongComponent> diffedComps;
    list<NBProgram.Program> dependencies;
    NBProgram.Options stageOptions;
    String seedPrefix, resultPrefix, tmpPrefix, contextName, debugOrigin;
    Boolean cleanupAlgorithms;
  algorithm
    stageOptions := NBProgram.stageOptions(program, NBProgram.Kind.FORWARD, stageName);
    (dependencies, diffMap) := createDerivativeDependencies(program, stageOptions);

    NBProgram.Options.OPTIONS(
      seedPrefix = seedPrefix,
      resultPrefix = resultPrefix,
      tmpPrefix = tmpPrefix,
      cleanupAlgorithms = cleanupAlgorithms,
      debugOrigin = debugOrigin) := stageOptions;
    contextName := if tmpPrefix <> "" then tmpPrefix else program.name;

    seedSourceVars := NBProgram.uniqueVariables(program.domainVars);
    (diffMap, seedVars) := NBProgram.mapVariables(
      seedSourceVars,
      seedPrefix,
      NBProgram.VariableRole.SEED,
      stageOptions,
      program.staticAsContinuous,
      program.idx,
      diffMap,
      seedVars
    );

    resultSourceVars := NBProgram.uniqueVariables(program.rangeVars);
    resultBaseVars := NBProgram.getNamingVars(resultSourceVars, program.resultBaseVars);
    tmpSourceVars := NBProgram.uniqueVariables(
      list(var for var guard(BVariable.isContinuous(var, program.staticAsContinuous)) in program.innerVars)
    );

    (diffMap, resultVars) := NBProgram.mapVariablesWithNaming(
      resultSourceVars,
      SOME(resultBaseVars),
      resultPrefix,
      NBProgram.VariableRole.RESULT,
      stageOptions,
      program.staticAsContinuous,
      program.idx,
      diffMap
    );

    (diffMap, tmpVars) := NBProgram.mapVariables(
      tmpSourceVars,
      tmpPrefix,
      NBProgram.VariableRole.TMP,
      stageOptions,
      program.staticAsContinuous,
      program.idx,
      diffMap,
      tmpVars
    );

    passiveSeedSourceVars := solvedSeedVariables(program.comps, program.seedVars);
    (diffMap, tmpVars) := NBProgram.mapVariables(
      passiveSeedSourceVars,
      tmpPrefix,
      NBProgram.VariableRole.TMP,
      stageOptions,
      program.staticAsContinuous,
      program.idx,
      diffMap,
      tmpVars,
      force = true
    );

    diffedComps := differentiateStrongComponentList(
      program.comps,
      diffMap,
      program.funcMap,
      program.scalarized,
      program.idx,
      contextName,
      cleanupAlgorithms,
      debugOrigin
    );

    sourceVars := NBProgram.uniqueVariables(
      listAppend(program.sourceVars, listAppend(seedSourceVars, listAppend(resultSourceVars, tmpSourceVars)))
    );

    forwardProgram := NBProgram.fromTransform(
      sourceProgram = program,
      kind          = NBProgram.Kind.FORWARD,
      dependencies  = dependencies,
      sourceVars    = sourceVars,
      diffMap       = diffMap,
      comps         = diffedComps,
      vars          = NBProgram.variableSets(
        domainVars     = program.domainVars,
        rangeVars      = resultVars,
        innerVars      = tmpVars,
        seedVars       = seedVars,
        resultVars     = resultVars,
        tmpVars        = tmpVars,
        resultBaseVars = resultBaseVars),
      options       = stageOptions
    );
  end createForward;

  function createDerivativeDependencies
    "Create derivative dependencies required before differentiating program.

     Every call represents one independent direction. Existing derivative maps
     are not reused; only dependencies for this direction are merged."
    input NBProgram.Program program;
    input NBProgram.Options stageOptions;
    output list<NBProgram.Program> dependencies = {};
    output UnorderedMap<ComponentRef, ComponentRef> diffMap =
      UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual);
  protected
    NBProgram.Program dependencyInput;
    NBProgram.Program source;
    NBProgram.Program tangentInput;
    NBProgram.Program tangentProgram;
    NBProgram.Program derivativeDependency;
    NBProgram.Allocation allocation;
    String seedPrefix, resultPrefix, tmpPrefix, debugOrigin, tangentName;
    Boolean cleanupAlgorithms;
  algorithm
    NBProgram.Options.OPTIONS(
      allocation = allocation,
      seedPrefix = seedPrefix,
      resultPrefix = resultPrefix,
      tmpPrefix = tmpPrefix,
      cleanupAlgorithms = cleanupAlgorithms,
      debugOrigin = debugOrigin) := stageOptions;

    for dependency in program.dependencies loop
      if not isProgramSource(dependency, program.source) then
        dependencyInput := NBProgram.withOptions(
          dependency,
          NBProgram.options(allocation, seedPrefix, resultPrefix, tmpPrefix, cleanupAlgorithms, debugOrigin)
        );
        derivativeDependency := create(dependencyInput);
        dependencies := derivativeDependency :: dependencies;
        mergeDiffMap(derivativeDependency.diffMap, diffMap);
      end if;
    end for;

    if isSome(program.source) and not listEmpty(program.sourceVars) then
      source := Util.getOption(program.source);
      tangentName := if tmpPrefix <> "" then "TAN_" + tmpPrefix else "TAN_" + program.name;

      tangentInput := NBProgram.fromSourceTangent(
        source,
        tangentName,
        NBProgram.uniqueVariables(program.sourceVars),
        NBProgram.options(
          NBProgram.Allocation.FRESH,
          seedPrefix,
          "",
          tangentName,
          cleanupAlgorithms = true,
          debugOrigin = debugOrigin)
      );

      tangentProgram := create(tangentInput);
      dependencies := tangentProgram :: dependencies;
      mergeDiffMap(tangentProgram.diffMap, diffMap);
    end if;

    if program.kind <> NBProgram.Kind.PRIMAL then
      dependencies := program :: dependencies;
    end if;

    dependencies := listReverse(dependencies);
  end createDerivativeDependencies;

  function solvedSeedVariables
    "Return stage seed variables that occur as solved variables.
     These passive seeds need derivative crefs to keep component structure."
    input list<StrongComponent> comps;
    input list<Pointer<Variable>> seedVars;
    output list<Pointer<Variable>> solvedSeeds = {};
  protected
    UnorderedSet<ComponentRef> solved = UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual);
    ComponentRef cref;
  algorithm
    for comp in comps loop
      for solvedVar in StrongComponent.getVariables(comp) loop
        UnorderedSet.add(BVariable.getVarName(solvedVar), solved);
      end for;
    end for;

    for seedVar in seedVars loop
      cref := BVariable.getVarName(seedVar);
      if UnorderedSet.contains(cref, solved) then
        solvedSeeds := seedVar :: solvedSeeds;
      end if;
    end for;

    solvedSeeds := listReverse(solvedSeeds);
  end solvedSeedVariables;

  function isProgramSource
    input NBProgram.Program dependency;
    input Option<NBProgram.Program> source;
    output Boolean isSource;
  protected
    NBProgram.Program sourceProgram;
  algorithm
    isSource := match source
      case SOME(sourceProgram) then dependency.name == sourceProgram.name
        and dependency.kind == sourceProgram.kind
        and dependency.level == sourceProgram.level;
      else false;
    end match;
  end isProgramSource;

  function mergeDiffMap
    input UnorderedMap<ComponentRef, ComponentRef> from;
    input UnorderedMap<ComponentRef, ComponentRef> into;
  protected
    ComponentRef key;
    ComponentRef value;
    ComponentRef existing;
  algorithm
    for entry in UnorderedMap.toList(from) loop
      (key, value) := entry;
      () := match UnorderedMap.get(key, into)
        case SOME(existing) guard(ComponentRef.isEqual(existing, value)) then ();
        case SOME(existing) algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {
            getInstanceName() + " got conflicting derivative mappings for " + ComponentRef.toString(key)
            + ": " + ComponentRef.toString(existing) + " and " + ComponentRef.toString(value)
          });
        then fail();
        else algorithm
          UnorderedMap.add(key, value, into);
        then ();
      end match;
    end for;
  end mergeDiffMap;

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
    input String debugOrigin = "";
    output list<StrongComponent> diffedComps;
  protected
    DifferentiationArguments diffArguments;
    String origin;
  algorithm
    origin := if debugOrigin <> "" then debugOrigin else getInstanceName();

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
      origin
    );

    if cleanupAlgorithms then
      diffedComps := cleanupForwardComponents(diffedComps, diffMap);
    end if;
  end differentiateStrongComponentList;

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

        case Statement.WHEN(branches = branchesIn, source = source) algorithm
          branches := {};
          for branch in branchesIn loop
            (condition, body) := branch;
            body := cleanupForwardStatements(body, derivativeCrefs);
            if not listEmpty(body) then
              branches := (condition, body) :: branches;
            end if;
          end for;

          if not listEmpty(branches) then
            stmtsOut := Statement.WHEN(listReverse(branches), source) :: stmtsOut;
          end if;
        then ();

        case Statement.WHILE(condition = condition, body = body, source = source) algorithm
          body := cleanupForwardStatements(body, derivativeCrefs);
          if not listEmpty(body) then
            stmtsOut := Statement.WHILE(condition, body, source) :: stmtsOut;
          end if;
        then ();

        case Statement.FAILURE(body = body, source = source) algorithm
          body := cleanupForwardStatements(body, derivativeCrefs);
          if not listEmpty(body) then
            stmtsOut := Statement.FAILURE(body, source) :: stmtsOut;
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
