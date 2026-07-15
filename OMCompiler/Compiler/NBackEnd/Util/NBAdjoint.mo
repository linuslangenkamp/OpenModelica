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

encapsulated package NBAdjoint
"file:        NBAdjoint.mo
 package:     NBAdjoint
 description: Strong-component adjoint program generation for the new backend.
"

public
  import NBEquation;
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
  import NFFunction.Function;
  import NFInstNode.InstNode;
  import Operator = NFOperator;
  import SimplifyExp = NFSimplifyExp;
  import Statement = NFStatement;
  import Type = NFType;
  import Variable = NFVariable;

  // Backend imports
  import BackendDAE = NBackendDAE.BackendDAE;
  import NFBackendExtension.BackendInfo;
  import BEquation = NBEquation;
  import BVariable = NBVariable;
  import Differentiate = NBDifferentiate;
  import NBDifferentiate.DifferentiationType;
  import NBEquation.Equation;
  import Replacements = NBReplacements;
  import Slice = NBSlice;
  import NBSolve;
  import StrongComponent = NBStrongComponent;
  import Tearing = NBTearing;
  import NFOperator.{MathClassification, SizeClassification};
  import NBVariable.{VariablePointer, VariablePointers};

  // Util imports
  import Error;
  import Flags;
  import UnorderedMap;
  import UnorderedSet;
  import Util;

public
  function create
    "Create a symbolic adjoint program for lambda^T * F(x).
     The returned program can be differentiated again by NBForward.create."
    input NBProgram.Program program;
    output NBProgram.Program adjointProgram;
  protected
    list<StrongComponent> comps, diffed_comps = {};
    UnorderedMap<ComponentRef, ComponentRef> diff_map = UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual);

    list<Pointer<Variable>> res_vars, tmp_vars, seed_vars, row_vars, base_tmp_vars, baseTmpVarCandidates;
    list<StrongComponent> compAdjComps;
    list<Pointer<Variable>> compNewVars;
    String seedName;
    NBProgram.Allocation allocation;
    VariablePointers differentiationVars;
  algorithm
    comps := program.comps;
    differentiationVars := VariablePointers.fromList(program.domainVars, program.scalarized);
    NBProgram.Options.OPTIONS(allocation = allocation) := program.options;

    for c in comps loop
      if not supportsStrongComponent(c) then
        Error.addMessage(Error.INTERNAL_ERROR, {
          getInstanceName() + " only supports SINGLE_COMPONENT, MULTI_COMPONENT, SLICED_COMPONENT, RESIZABLE_COMPONENT, GENERIC_COMPONENT, ALIAS and ALGEBRAIC_LOOP in symbolic adjoint generation."
        });
        fail();
      end if;
      if Flags.isSet(Flags.DEBUG_ADJOINT) then
        print("Primal component: " + StrongComponent.toString(c) + "\n");
      end if;
    end for;

    if Flags.isSet(Flags.DEBUG_ADJOINT) then
      print("Differentiation variables before pDer creation:\n" + BVariable.VariablePointers.toString(differentiationVars, "Differentiation Variables") + "\n");
      print("Function variables before seed creation:\n" + BVariable.VariablePointers.toString(VariablePointers.fromList(program.rangeVars, program.scalarized), "Function Variables") + "\n");
      print("Inner variables before pDer creation:\n" + BVariable.VariablePointers.toString(VariablePointers.fromList(program.innerVars, program.scalarized), "Inner Variables") + "\n");
    end if;

    (diff_map, res_vars) := NBProgram.mapVariables(
      program.domainVars,
      program.name,
      NBProgram.VariableRole.ADJOINT_RESULT,
      program.options,
      program.staticAsContinuous,
      program.idx,
      diff_map
    );
    res_vars := listReverse(res_vars);

    row_vars := program.rangeVars;
    (base_tmp_vars, _) := List.splitOnTrue(program.innerVars, function BVariable.isContinuous(staticAsContinuous = program.staticAsContinuous));

    seedName := if allocation == NBProgram.Allocation.FRESH then program.name + "_LAMBDA" else program.name;
    (diff_map, seed_vars) := NBProgram.mapVariables(
      row_vars,
      seedName,
      NBProgram.VariableRole.SEED,
      program.options,
      program.staticAsContinuous,
      program.idx,
      diff_map
    );
    seed_vars := listReverse(seed_vars);

    if Flags.isSet(Flags.DEBUG_ADJOINT) then
      print("seed vars after seed creation:\n" + BVariable.VariablePointers.toString(VariablePointers.fromList(seed_vars), "Seed Vars") + "\n");
      print("res vars after pDer creation:\n" + BVariable.VariablePointers.toString(VariablePointers.fromList(res_vars), "Res Vars") + "\n");
      print("tmp vars before pDer creation:\n" + BVariable.VariablePointers.toString(VariablePointers.fromList(base_tmp_vars), "Tmp Base Vars") + "\n");
    end if;

    (diff_map, tmp_vars) := NBProgram.mapVariables(
      base_tmp_vars,
      program.name,
      NBProgram.VariableRole.ADJOINT_TMP,
      program.options,
      program.staticAsContinuous,
      program.idx,
      diff_map
    );
    tmp_vars := listReverse(tmp_vars);
    baseTmpVarCandidates := getBaseTmpVarCandidates(base_tmp_vars, tmp_vars, diff_map);

    if Flags.isSet(Flags.DEBUG_ADJOINT) then
      print("tmp vars after pDer creation:\n" + BVariable.VariablePointers.toString(VariablePointers.fromList(tmp_vars), "Tmp Vars") + "\n");
      print("Diff map before component generation:\n" + diffMapToString(diff_map) + "\n");
    end if;

    for comp in comps loop
      (compAdjComps, compNewVars) := generateComponent(
        comp, diff_map, program.funcMap, program.scalarized, program.staticAsContinuous, program.idx, program.name, differentiationVars, baseTmpVarCandidates);

      for ac in compAdjComps loop
        diffed_comps := ac :: diffed_comps;
      end for;

      for v in compNewVars loop
        tmp_vars := v :: tmp_vars;
      end for;

      if Flags.isSet(Flags.DEBUG_ADJOINT) then
        for ac in compAdjComps loop
          print("[adjoint] generated component: " + StrongComponent.toString(ac) + "\n");
        end for;
      end if;
    end for;

    if Flags.isSet(Flags.DEBUG_ADJOINT) then
      print("Final list of differentiated components:\n");
      for comp in diffed_comps loop
        print(StrongComponent.toString(comp) + "\n");
      end for;
    end if;

    adjointProgram := NBProgram.fromTransform(
      sourceProgram = program,
      kind          = NBProgram.Kind.ADJOINT,
      dependencies  = {},
      sourceVars    = listAppend(row_vars, listAppend(program.domainVars, baseTmpVarCandidates)),
      diffMap       = diff_map,
      comps         = diffed_comps,
      vars          = NBProgram.variableSets(
        domainVars     = program.domainVars,
        rangeVars      = res_vars,
        innerVars      = tmp_vars,
        seedVars       = seed_vars,
        resultVars     = res_vars,
        tmpVars        = tmp_vars,
        seedBaseVars   = listReverse(row_vars),
        resultBaseVars = listReverse(program.domainVars),
        tmpBaseVars    = baseTmpVarCandidates)
    );
  end create;

  function supportsStrongComponent
    input StrongComponent comp;
    output Boolean ok;
  algorithm
    ok := match comp
      case StrongComponent.SINGLE_COMPONENT()    then true;
      case StrongComponent.MULTI_COMPONENT()     then true;
      case StrongComponent.SLICED_COMPONENT()    then true;
      case StrongComponent.RESIZABLE_COMPONENT() then true;
      case StrongComponent.GENERIC_COMPONENT()   then true;
      case StrongComponent.ALGEBRAIC_LOOP()      then true;
      case StrongComponent.ALIAS()               then supportsStrongComponent(comp.original);
      else false;
    end match;
  end supportsStrongComponent;

protected
  type AdjointTermList = list<Expression>;

  function makeVarTraverse
    input Pointer<Variable> var_ptr;
    input String name;
    input Pointer<list<Pointer<Variable>>> vars_ptr;
    input UnorderedMap<ComponentRef, ComponentRef> map;
    input Func makeVar;
    input Boolean staticAsContinuous;

    partial function Func
      input output ComponentRef cref;
      input String name;
      output Pointer<Variable> diff_ptr;
    end Func;
  protected
    Variable var = Pointer.access(var_ptr);
    ComponentRef diff, parent_name, diff_parent_name;
    Pointer<Variable> diff_ptr, parent, diff_parent;
  algorithm
    if BVariable.isContinuous(var_ptr, staticAsContinuous) then
      (diff, diff_ptr) := makeVar(var.name, name);
      Pointer.update(vars_ptr, diff_ptr :: Pointer.access(vars_ptr));
      UnorderedMap.add(var.name, diff, map);

      () := match BVariable.getParent(var_ptr)
        case SOME(parent) algorithm
          parent_name := BVariable.getVarName(parent);
          diff_parent := match UnorderedMap.get(parent_name, map)
            case SOME(diff_parent_name) then BVariable.getVarPointer(diff_parent_name, sourceInfo());
            else algorithm
              (diff_parent_name, _) := makeVar(parent_name, name);
              UnorderedMap.add(parent_name, diff_parent_name, map);
            then BVariable.getVarPointer(diff_parent_name, sourceInfo());
          end match;

          BVariable.addRecordChild(diff_parent, diff_ptr);
          diff_ptr := BVariable.setParent(diff_ptr, diff_parent);
        then ();

        else ();
      end match;
    end if;
  end makeVarTraverse;

  function sizeClassificationFromType
    input Type ty;
    output SizeClassification sc;
  algorithm
    sc := match Type.dimensionCount(ty)
      case 0 then SizeClassification.SCALAR;
      case 1 then SizeClassification.ELEMENT_WISE;
      case 2 then SizeClassification.MATRIX;
      else SizeClassification.ELEMENT_WISE;
    end match;
  end sizeClassificationFromType;

  function buildAdjointRhs
    input ComponentRef lhsCref;
    input list<Expression> terms;
    output Expression rhs;
  protected
    Type vty;
    SizeClassification sc;
    Operator addOp;
  algorithm
    vty := ComponentRef.getComponentType(lhsCref);

    if listEmpty(terms) then
      rhs := Expression.makeZero(vty);
      return;
    end if;

    if List.hasOneElement(terms) then
      rhs := listHead(terms);
      return;
    end if;

    sc := sizeClassificationFromType(vty);
    addOp := Operator.fromClassification((MathClassification.ADDITION, sc), vty);

    rhs := SimplifyExp.simplify(Expression.MULTARY(terms, {}, addOp));
    rhs := Expression.map(rhs, Expression.repairOperator);
  end buildAdjointRhs;

  function accumulateAdjointForResidual
    input Expression residual;
    input Expression seed;
    input UnorderedMap<ComponentRef, ComponentRef> diff_map;
    input UnorderedMap<Path, Function> funcMapIn;
    input Boolean scalarized;
    input UnorderedMap<ComponentRef, AdjointTermList> adjoint_map_in;
    output Differentiate.DifferentiationArguments diffArguments;
  algorithm
    diffArguments := Differentiate.DIFFERENTIATION_ARGUMENTS(
      diffCref        = ComponentRef.EMPTY(),
      new_vars        = {},
      diff_map        = SOME(diff_map),
      diffType        = DifferentiationType.JACOBIAN,
      funcMap         = funcMapIn,
      scalarized      = scalarized,
      adjoint_map     = SOME(adjoint_map_in),
      current_grad    = seed,
      collectAdjoints = true
    );

    (_, diffArguments) := Differentiate.differentiateExpression(residual, diffArguments);
  end accumulateAdjointForResidual;

  function addEntryToLoopProductMap
    input Pointer<Variable> vptr;
    input UnorderedMap<ComponentRef, ComponentRef> diff_map;
    input UnorderedMap<ComponentRef, AdjointTermList> loop_product_adjoint_map;
  protected
    Option<ComponentRef> mappedSeed;
  algorithm
    mappedSeed := UnorderedMap.get(BVariable.getVarName(vptr), diff_map);
    if isSome(mappedSeed) then
      UnorderedMap.tryAdd(Util.getOption(mappedSeed), {}, loop_product_adjoint_map);
    end if;
  end addEntryToLoopProductMap;

  function getBaseTmpVarCandidates
    input list<NBVariable.VariablePointer> partialVars;
    input list<NBVariable.VariablePointer> tmpPDerVars;
    input UnorderedMap<ComponentRef, ComponentRef> diff_map;
    output list<NBVariable.VariablePointer> baseTmpVars = {};
  protected
    UnorderedSet<ComponentRef> tmpPDerSet;
    ComponentRef baseCref;
    Option<ComponentRef> o_mapped;
  algorithm
    tmpPDerSet := UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(tmpPDerVars)));

    for v in tmpPDerVars loop
      UnorderedSet.add(BVariable.getVarName(v), tmpPDerSet);
    end for;

    for v in partialVars loop
      baseCref := BVariable.getVarName(v);
      o_mapped := UnorderedMap.get(baseCref, diff_map);
      if isSome(o_mapped) and UnorderedSet.contains(Util.getOption(o_mapped), tmpPDerSet) then
        baseTmpVars := v :: baseTmpVars;
      end if;
    end for;

    baseTmpVars := listReverse(baseTmpVars);
  end getBaseTmpVarCandidates;

  function populateDiffMap
    input list<NBVariable.VariablePointer> vars;
    input UnorderedMap<ComponentRef, ComponentRef> globalDiffMap;
    output UnorderedMap<ComponentRef, ComponentRef> outMap;
  protected
    ComponentRef baseCref;
    Option<ComponentRef> o_mappedCref;
  algorithm
    outMap := UnorderedMap.new<ComponentRef>(
      ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(vars))
    );

    for vp in vars loop
      baseCref := BVariable.getVarName(vp);
      o_mappedCref := UnorderedMap.get(baseCref, globalDiffMap);
      if isSome(o_mappedCref) then
        UnorderedMap.add(baseCref, Util.getOption(o_mappedCref), outMap);
      end if;
    end for;
  end populateDiffMap;

  function generateComponent
    input StrongComponent comp;
    input UnorderedMap<ComponentRef, ComponentRef> diff_map;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean scalarized;
    input Boolean staticAsContinuous;
    input Pointer<Integer> idx;
    input String contextName;
    input VariablePointers seedCandidates "for algebraic loop x-inputs";
    input list<Pointer<Variable>> tmpVarCandidates "base tmp variables to also include in diff_map_x for algebraic loops";
    output list<StrongComponent> adjointComps = {};
    output list<Pointer<Variable>> newTmpVars = {};
  protected
    StrongComponent c_noalias;
    UnorderedMap<ComponentRef, AdjointTermList> fresh_adjoint_map;
    Differentiate.DifferentiationArguments diffArgs;
    Equation eq;
    list<Statement> adjStmts;
    Pointer<Equation> eqPtr;
    list<Slice<VariablePointer>> adjVarSlices;
    Pointer<list<Pointer<Variable>>> ssaPDerVarsPtr = Pointer.create({});
  algorithm
    c_noalias := StrongComponent.removeAlias(comp);

    () := match c_noalias
      local
        Tearing tearing;
        list<VariablePointer> itVarPtrs;
        list<Expression> residuals;
        list<Pointer<Variable>> lambdaPtrs;
        list<ComponentRef> lambdaCrefs;
        Integer iRes;
        Pointer<Variable> lhsVarPtr;
        ComponentRef newC;
        UnorderedMap<ComponentRef, ComponentRef> diff_map_y, diff_map_x, diff_map_union;
        UnorderedMap<ComponentRef, AdjointTermList> loop_product_adjoint_map;
        list<Pointer<Variable>> seedPtrListX;
        list<Pointer<Equation>> linResEqnPtrs;
        AdjointTermList terms_j, terms_x;
        Expression lhs_j, rhs_j, rhs_x;
        Pointer<Equation> resid_j;
        Option<ComponentRef> o_ySeedCref, o_pDerX;
        ComponentRef ySeedCref, baseX, pDerX;
        StrongComponent loopComp;

        StrongComponent ssaAlg;
        list<tuple<ComponentRef, tuple<ComponentRef, Integer>>> replacements = {};
        list<Pointer<Variable>> newVars = {};
        UnorderedSet<ComponentRef> seenCrefs;
        ComponentRef origCref, finalSsaCref, pDerOrigCref, pDerSsaCref;
        Type vty;
        list<Statement> xbarStmts;
        SizeClassification sc_x;
        Operator addOp_x;
        Expression accRhs;
        Boolean init = false;

      case StrongComponent.ALGEBRAIC_LOOP(strict = tearing) algorithm
        itVarPtrs := Tearing.getIterationVars(tearing);
        residuals := list(Equation.getResidualExp(Pointer.access(e)) for e in Tearing.getResidualEqns(tearing));

        lambdaPtrs := {};
        lambdaCrefs := {};
        for iIdx in 1:listLength(residuals) loop
          (lhsVarPtr, newC) := BVariable.makeAuxVar(NBVariable.TEMPORARY_STR, Pointer.access(idx) + 1, Type.REAL(), false);
          Pointer.update(idx, Pointer.access(idx) + 1);
          (newC, lhsVarPtr) := BVariable.makePDerVar(newC, contextName, isTmp = true);
          lambdaPtrs := lhsVarPtr :: lambdaPtrs;
          lambdaCrefs := newC :: lambdaCrefs;
        end for;
        lambdaPtrs := listReverse(lambdaPtrs);
        lambdaCrefs := listReverse(lambdaCrefs);
        newTmpVars := lambdaPtrs;

        diff_map_y := populateDiffMap(itVarPtrs, diff_map);
        seedPtrListX := listAppend(BVariable.VariablePointers.toList(seedCandidates), tmpVarCandidates);
        seedPtrListX := list(vp for vp guard(not UnorderedMap.contains(BVariable.getVarName(vp), diff_map_y)) in seedPtrListX);
        diff_map_x := populateDiffMap(seedPtrListX, diff_map);
        diff_map_union := UnorderedMap.merge(diff_map_y, diff_map_x, sourceInfo());

        loop_product_adjoint_map := UnorderedMap.new<AdjointTermList>(ComponentRef.hash, ComponentRef.isEqual, listLength(itVarPtrs) + listLength(seedPtrListX));
        for vp in itVarPtrs loop addEntryToLoopProductMap(vp, diff_map_y, loop_product_adjoint_map); end for;
        for vp in seedPtrListX loop addEntryToLoopProductMap(vp, diff_map_x, loop_product_adjoint_map); end for;

        iRes := 1;
        for residual_i in residuals loop
          if iRes > listLength(lambdaCrefs) then break; end if;
          diffArgs := accumulateAdjointForResidual(
            residual_i,
            Expression.fromCref(listGet(lambdaCrefs, iRes)),
            diff_map_union,
            funcMap,
            scalarized,
            loop_product_adjoint_map
          );
          loop_product_adjoint_map := Util.getOption(diffArgs.adjoint_map);
          iRes := iRes + 1;
        end for;

        linResEqnPtrs := {};
        for vp in itVarPtrs loop
          o_ySeedCref := UnorderedMap.get(BVariable.getVarName(vp), diff_map_y);
          if isSome(o_ySeedCref) then
            ySeedCref := Util.getOption(o_ySeedCref);
            terms_j := UnorderedMap.getOrDefault(ySeedCref, loop_product_adjoint_map, {});
            lhs_j := buildAdjointRhs(ySeedCref, terms_j);
            rhs_j := Expression.fromCref(ySeedCref);
            resid_j := Equation.makeAssignment(lhs_j, rhs_j, idx, contextName,
              NBEquation.Iterator.EMPTY(), NBEquation.EquationAttributes.default(NBEquation.EquationKind.CONTINUOUS, false));
            linResEqnPtrs := Equation.createResidual(resid_j) :: linResEqnPtrs;
          end if;
        end for;
        linResEqnPtrs := listReverse(linResEqnPtrs);

        if not listEmpty(linResEqnPtrs) then
          loopComp := makeLinearAlgebraicLoop(lambdaPtrs, linResEqnPtrs, NONE(), mixed = false, homotopy = false);
          adjointComps := loopComp :: adjointComps;
        end if;

        xbarStmts := {};
        for seedVarPtrX in seedPtrListX loop
          baseX := BVariable.getVarName(seedVarPtrX);
          o_pDerX := UnorderedMap.get(baseX, diff_map_x);
          if isSome(o_pDerX) then
            pDerX := Util.getOption(o_pDerX);
            terms_x := UnorderedMap.getOrDefault(pDerX, loop_product_adjoint_map, {});
            if not listEmpty(terms_x) then
              rhs_x := Expression.negate(buildAdjointRhs(pDerX, terms_x));
              vty := ComponentRef.getComponentType(pDerX);
              if Expression.containsCref(rhs_x, pDerX) then
                accRhs := rhs_x;
              else
                sc_x := sizeClassificationFromType(vty);
                addOp_x := Operator.fromClassification((MathClassification.ADDITION, sc_x), vty);
                accRhs := SimplifyExp.simplify(Expression.MULTARY({Expression.fromCref(pDerX), rhs_x}, {}, addOp_x));
              end if;
              accRhs := Expression.map(accRhs, Expression.repairOperator);
              xbarStmts := Statement.ASSIGNMENT(
                Expression.fromCref(pDerX), accRhs, vty, DAE.emptyElementSource
              ) :: xbarStmts;
            end if;
          end if;
        end for;
        xbarStmts := listReverse(xbarStmts);
        if not listEmpty(xbarStmts) then
          eqPtr := Equation.makeAlgorithm(xbarStmts, init);
          Equation.createName(eqPtr, idx, contextName);
          adjVarSlices := listReverse(collectAdjointVarSlices(xbarStmts, {}));
          adjointComps := StrongComponent.MULTI_COMPONENT(
            vars   = adjVarSlices,
            eqn    = Slice.SLICE(eqPtr, {}),
            status = NBSolve.Status.EXPLICIT
          ) :: adjointComps;
        end if;
      then ();

      case StrongComponent.SINGLE_COMPONENT() algorithm
        eq := Pointer.access(c_noalias.eqn);
        fresh_adjoint_map := UnorderedMap.new<AdjointTermList>(ComponentRef.hash, ComponentRef.isEqual, 16);
        diffArgs := Differentiate.DIFFERENTIATION_ARGUMENTS(
          diffCref        = ComponentRef.EMPTY(),
          new_vars        = {},
          diff_map        = SOME(diff_map),
          diffType        = DifferentiationType.JACOBIAN,
          funcMap         = funcMap,
          scalarized      = scalarized,
          adjoint_map     = SOME(fresh_adjoint_map),
          current_grad    = Expression.EMPTY(Type.REAL()),
          collectAdjoints = true
        );

        (diffArgs, adjStmts) := Differentiate.differentiateEquationAdjoint(eq, diffArgs);

        if not listEmpty(adjStmts) then
          eqPtr := Equation.makeAlgorithm(adjStmts, init);
          Equation.createName(eqPtr, idx, contextName);
          adjVarSlices := listReverse(collectAdjointVarSlices(adjStmts, {}));

          adjointComps := {StrongComponent.MULTI_COMPONENT(
            vars   = adjVarSlices,
            eqn    = Slice.SLICE(eqPtr, {}),
            status = NBSolve.Status.EXPLICIT
          )};
        end if;
      then ();

      case StrongComponent.MULTI_COMPONENT() algorithm
        eq := match Pointer.access(Slice.getT(c_noalias.eqn))
          case Equation.ALGORITHM() algorithm
            (ssaAlg, replacements, newVars) := algorithmToSSA(c_noalias);
            if Flags.isSet(Flags.DEBUG_ADJOINT) then
              print("SSA algorithm for adjoint of component " + StrongComponent.toString(c_noalias) + ":\n" + StrongComponent.toString(ssaAlg) + "\n");
            end if;

            for ssaVarPtr in newVars loop
              makeVarTraverse(ssaVarPtr, contextName, ssaPDerVarsPtr, diff_map,
                function BVariable.makePDerVar(isTmp = true), staticAsContinuous = staticAsContinuous);
            end for;
            for pDerVarPtr in Pointer.access(ssaPDerVarsPtr) loop
              newTmpVars := pDerVarPtr :: newTmpVars;
            end for;

          then match ssaAlg
            case StrongComponent.MULTI_COMPONENT() then Pointer.access(Slice.getT(ssaAlg.eqn));
            else Pointer.access(Slice.getT(c_noalias.eqn));
          end match;
          else algorithm
            then Pointer.access(Slice.getT(c_noalias.eqn));
          end match;

        fresh_adjoint_map := UnorderedMap.new<AdjointTermList>(ComponentRef.hash, ComponentRef.isEqual, 16);
        diffArgs := Differentiate.DIFFERENTIATION_ARGUMENTS(
          diffCref        = ComponentRef.EMPTY(),
          new_vars        = {},
          diff_map        = SOME(diff_map),
          diffType        = DifferentiationType.JACOBIAN,
          funcMap         = funcMap,
          scalarized      = scalarized,
          adjoint_map     = SOME(fresh_adjoint_map),
          current_grad    = Expression.EMPTY(Type.REAL()),
          collectAdjoints = true
        );

        (diffArgs, adjStmts) := Differentiate.differentiateEquationAdjoint(eq, diffArgs);

        if not listEmpty(newVars) then
          seenCrefs := UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual, 4);
          for replacement in listReverse(replacements) loop
            (origCref, (finalSsaCref, _)) := replacement;
            if not UnorderedSet.contains(origCref, seenCrefs) then
              UnorderedSet.add(origCref, seenCrefs);
              if UnorderedMap.contains(origCref, diff_map) and
                 UnorderedMap.contains(finalSsaCref, diff_map) then
                pDerOrigCref := UnorderedMap.getOrFail(origCref, diff_map);
                pDerSsaCref  := UnorderedMap.getOrFail(finalSsaCref, diff_map);
                vty := ComponentRef.getSubscriptedType(pDerSsaCref, true);
                adjStmts := Statement.ASSIGNMENT(
                  Expression.fromCref(pDerSsaCref),
                  Expression.fromCref(pDerOrigCref),
                  vty, DAE.emptyElementSource) :: adjStmts;
              end if;
            end if;
          end for;
        end if;

        if not listEmpty(adjStmts) then
          eqPtr := Equation.makeAlgorithm(adjStmts, init);
          Equation.createName(eqPtr, idx, contextName);
          adjVarSlices := listReverse(collectAdjointVarSlices(adjStmts, {}));

          adjointComps := {StrongComponent.MULTI_COMPONENT(
            vars   = adjVarSlices,
            eqn    = Slice.SLICE(eqPtr, {}),
            status = NBSolve.Status.EXPLICIT
          )};
        end if;
      then ();

      case StrongComponent.SLICED_COMPONENT() algorithm
        eq := Pointer.access(Slice.getT(c_noalias.eqn));
        adjointComps := generateForComponent(eq, c_noalias, diff_map, funcMap, scalarized, init, idx, contextName);
      then ();

      case StrongComponent.RESIZABLE_COMPONENT() algorithm
        eq := Pointer.access(Slice.getT(c_noalias.eqn));
        adjointComps := generateForComponent(eq, c_noalias, diff_map, funcMap, scalarized, init, idx, contextName);
      then ();

      case StrongComponent.GENERIC_COMPONENT() algorithm
        eq := Pointer.access(Slice.getT(c_noalias.eqn));
        adjointComps := generateForComponent(eq, c_noalias, diff_map, funcMap, scalarized, init, idx, contextName);
      then ();

      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " unsupported component type: " + StrongComponent.toString(c_noalias)});
      then ();
    end match;
  end generateComponent;

  function generateForComponent
    input Equation eq;
    input StrongComponent originalComp;
    input UnorderedMap<ComponentRef, ComponentRef> diff_map;
    input UnorderedMap<Path, Function> funcMap;
    input Boolean scalarized;
    input Boolean init;
    input Pointer<Integer> idx;
    input String contextName;
    output list<StrongComponent> adjointComps = {};
  protected
    UnorderedMap<ComponentRef, AdjointTermList> fresh_adjoint_map;
    Differentiate.DifferentiationArguments diffArgs;
    list<Statement> adjStmts;
    Pointer<Equation> eqPtr;
    list<Slice<VariablePointer>> adjVarSlices;
  algorithm
    fresh_adjoint_map := UnorderedMap.new<AdjointTermList>(ComponentRef.hash, ComponentRef.isEqual, 16);
    diffArgs := Differentiate.DIFFERENTIATION_ARGUMENTS(
      diffCref        = ComponentRef.EMPTY(),
      new_vars        = {},
      diff_map        = SOME(diff_map),
      diffType        = DifferentiationType.JACOBIAN,
      funcMap         = funcMap,
      scalarized      = scalarized,
      adjoint_map     = SOME(fresh_adjoint_map),
      current_grad    = Expression.EMPTY(Type.REAL()),
      collectAdjoints = true
    );

    (diffArgs, adjStmts) := Differentiate.differentiateEquationAdjoint(eq, diffArgs);

    if not listEmpty(adjStmts) then
      eqPtr := Equation.makeAlgorithm(adjStmts, init);
      Equation.createName(eqPtr, idx, contextName);
      adjVarSlices := listReverse(collectAdjointVarSlices(adjStmts, {}));

      adjointComps := {StrongComponent.MULTI_COMPONENT(
        vars   = adjVarSlices,
        eqn    = Slice.SLICE(eqPtr, {}),
        status = NBSolve.Status.EXPLICIT
      )};
    end if;
  end generateForComponent;

  function collectAdjointVarSlices
    input list<Statement> stmts;
    input output list<Slice<VariablePointer>> varSlices;
  protected
    Pointer<Variable> vPtr;
    ComponentRef baseCref;
  algorithm
    for s in stmts loop
      () := match s
        case Statement.ASSIGNMENT(lhs = Expression.CREF()) algorithm
          baseCref := ComponentRef.stripSubscriptsAll(Expression.toCref(s.lhs));
          try
            vPtr := BVariable.getVarPointer(baseCref, sourceInfo());
            varSlices := Slice.SLICE(vPtr, {}) :: varSlices;
          else
          end try;
        then ();
        case Statement.FOR() algorithm
          varSlices := collectAdjointVarSlices(s.body, varSlices);
        then ();
        case Statement.IF() algorithm
          for branch in s.branches loop
            varSlices := collectAdjointVarSlices(Util.tuple22(branch), varSlices);
          end for;
        then ();
        else ();
      end match;
    end for;
  end collectAdjointVarSlices;

  function makeLinearAlgebraicLoop
    input list<NBVariable.VariablePointer> itVarPtrs;
    input list<Pointer<NBEquation.Equation>> resEqnPtrs;
    input Option<BackendDAE> jac = NONE();
    input Boolean mixed = false;
    input Boolean homotopy = false;
    output StrongComponent comp;
  protected
    Integer m1 = listLength(itVarPtrs);
    Integer m2 = listLength(resEqnPtrs);
    list<Slice<NBVariable.VariablePointer>> itVars_s;
    list<Slice<Pointer<NBEquation.Equation>>> res_s;
    Tearing.Tearing tearingSet;
  algorithm
    if m1 <> m2 then
      Error.addMessage(Error.INTERNAL_ERROR, {"makeLinearAlgebraicLoop: |vars| != |eqns|"});
      fail();
    end if;

    itVars_s := list(Slice.SLICE(vp, {}) for vp in itVarPtrs);
    res_s    := list(Slice.SLICE(ep, {}) for ep in resEqnPtrs);

    tearingSet := Tearing.TEARING_SET(
      iteration_vars = itVars_s,
      residual_eqns  = res_s,
      innerEquations = listArray({}),
      jac            = jac
    );

    comp := StrongComponent.ALGEBRAIC_LOOP(
      idx      = -1,
      strict   = tearingSet,
      casual   = NONE(),
      linear   = true,
      mixed    = mixed,
      homotopy = homotopy,
      status   = NBSolve.Status.IMPLICIT
    );
  end makeLinearAlgebraicLoop;

  function makeSSAVar
    input ComponentRef baseCref;
    input Integer idx;
    output Pointer<Variable> ssaVarPtr;
    output ComponentRef ssaCref;
  protected
    Pointer<Variable> origVarPtr;
    Variable origVar;
    InstNode newNode;
    Type ty;
  algorithm
    origVarPtr := BVariable.getVarPointer(baseCref, sourceInfo());
    origVar    := Pointer.access(origVarPtr);
    ty         := ComponentRef.getSubscriptedType(baseCref, false);

    newNode := InstNode.VAR_NODE(
      ComponentRef.firstName(baseCref) + "_" + intString(idx),
      Pointer.create(NBVariable.DUMMY_VARIABLE));
    ssaCref := ComponentRef.CREF(newNode, {}, ty,
      NFComponentRef.Origin.CREF, ComponentRef.EMPTY());

    origVar.backendinfo := BackendInfo.BACKEND_INFO(
      origVar.backendinfo.varKind,
      origVar.backendinfo.attributes,
      origVar.backendinfo.annotations,
      origVar.backendinfo.var_pre,
      NONE(),
      NONE(),
      NONE(),
      origVar.backendinfo.var_start,
      origVar.backendinfo.parent
    );

    (ssaVarPtr, ssaCref) := BVariable.makeVarPtrCyclic(origVar, ssaCref);
  end makeSSAVar;

  function algorithmToSSA
    input StrongComponent comp;
    output StrongComponent ssaComp;
    output list<tuple<ComponentRef, tuple<ComponentRef, Integer>>> replacements;
    output list<Pointer<Variable>> newVars;
  protected
    Equation eqn;
    Algorithm alg;
    Statement stmt;
    ComponentRef lhsCref, baseCref, ssaCref;
    Integer cnt, idx, lineIdx;
    Pointer<Variable> ssaVarPtr;
    Expression lhsExp, rhsExp;
    UnorderedMap<ComponentRef, Integer> assignCount =
      UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual);
    UnorderedMap<ComponentRef, Integer> ssaIdx =
      UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual);
    UnorderedMap<ComponentRef, Expression> activeRepl =
      UnorderedMap.new<Expression>(ComponentRef.hash, ComponentRef.isEqual);
    list<Statement> ssaStmts = {};
    list<tuple<ComponentRef, tuple<ComponentRef, Integer>>> replAcc = {};
    list<Pointer<Variable>> newVarsAcc = {};
    Pointer<Equation> ssaEqnPtr;
  algorithm
    (ssaComp, replacements, newVars) := match comp
      case StrongComponent.MULTI_COMPONENT() algorithm
        eqn := Pointer.access(Slice.getT(comp.eqn));
        Equation.ALGORITHM(alg = alg) := eqn;

        for origStmt in alg.statements loop
          () := match origStmt
            case Statement.ASSIGNMENT() algorithm
              lhsCref := match origStmt.lhs
                case Expression.CREF(cref = lhsCref) then lhsCref;
                else ComponentRef.EMPTY();
              end match;
              if not ComponentRef.isEmpty(lhsCref) then
                baseCref := ComponentRef.stripSubscriptsAll(lhsCref);
                cnt := UnorderedMap.getOrDefault(baseCref, assignCount, 0);
                UnorderedMap.add(baseCref, cnt + 1, assignCount);
              end if;
            then ();
            else ();
          end match;
        end for;

        lineIdx := 1;
        for origStmt in alg.statements loop
          stmt := match origStmt
            case Statement.ASSIGNMENT() algorithm
              rhsExp := Expression.map(origStmt.rhs,
                function Replacements.applySimpleExp(replacements = activeRepl));

              lhsExp  := origStmt.lhs;
              lhsCref := match origStmt.lhs
                case Expression.CREF(cref = lhsCref) then lhsCref;
                else ComponentRef.EMPTY();
              end match;

              if not ComponentRef.isEmpty(lhsCref) then
                baseCref := ComponentRef.stripSubscriptsAll(lhsCref);
                if UnorderedMap.getOrDefault(baseCref, assignCount, 1) > 1 then
                  idx := UnorderedMap.getOrDefault(baseCref, ssaIdx, 0) + 1;
                  UnorderedMap.add(baseCref, idx, ssaIdx);
                  (ssaVarPtr, ssaCref) := makeSSAVar(baseCref, idx);
                  newVarsAcc := ssaVarPtr :: newVarsAcc;

                  ssaCref := ComponentRef.copySubscripts(lhsCref, ssaCref);
                  UnorderedMap.add(baseCref,
                    Expression.fromCref(ComponentRef.stripSubscriptsAll(ssaCref)),
                    activeRepl);

                  replAcc := (baseCref,
                    (ComponentRef.stripSubscriptsAll(ssaCref), lineIdx)) :: replAcc;

                  lhsExp := Expression.fromCref(ssaCref);
                end if;
              end if;
            then Statement.ASSIGNMENT(lhsExp, rhsExp, origStmt.ty, origStmt.source);

            else origStmt;
          end match;

          ssaStmts := stmt :: ssaStmts;
          lineIdx := lineIdx + 1;
        end for;

        alg.statements := listReverse(ssaStmts);
        eqn := match eqn
          case Equation.ALGORITHM() algorithm eqn.alg := alg; then eqn;
          else eqn;
        end match;
        ssaEqnPtr := Pointer.create(eqn);
      then (StrongComponent.MULTI_COMPONENT(
              vars   = listAppend(comp.vars, list(Slice.SLICE(v, {}) for v in listReverse(newVarsAcc))),
              eqn    = Slice.SLICE(ssaEqnPtr, {}),
              status = comp.status
            ), listReverse(replAcc), listReverse(newVarsAcc));

      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR,
          {getInstanceName() + " expects a MULTI_COMPONENT with an ALGORITHM equation."});
      then fail();
    end match;
  end algorithmToSSA;

  function diffMapToString
    input UnorderedMap<ComponentRef, ComponentRef> map;
    output String s;
  algorithm
    s := UnorderedMap.toString(map, ComponentRef.toString, ComponentRef.toString, "\n  ", " -> ");
    s := "{\n  " + s + "\n}";
  end diffMapToString;

  annotation(__OpenModelica_Interface="nbackend");
end NBAdjoint;
