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

encapsulated package NBJacobian
"file:        NBJacobian.mo
 package:     NBJacobian
 description: This file contains the functions to create and manipulate jacobians.
              The main type is inherited from NBackendDAE.mo
              NOTE: There is no real jacobian type, it is a BackendDAE.
"

public
  import BackendDAE = NBackendDAE;
  import Module = NBModule;
  import NBEquation;
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
  import NBAdjacency.Mapping;
  import BEquation = NBEquation;
  import BVariable = NBVariable;
  import NBAdjoint;
  import NBEquation.{Equation, EquationPointers, EqData};
  import NBForward;
  import NBProgram;
  import Jacobian = NBackendDAE.BackendDAE;
  import Matching = NBMatching;
  import Partition = NBPartition;
  import Slice = NBSlice;
  import Sorting = NBSorting;
  import StrongComponent = NBStrongComponent;
  import Tearing = NBTearing;
  import NBVariable.{VariablePointer, VariablePointers, VarData};

  // Sparsity-pattern graph coloring, shared with the old backend.
  import Coloring;

  // Util imports
  import StringUtil;
  import UnorderedMap;
  import UnorderedSet;
  import Util;

public
  type JacobianType = enumeration(ODE, DAE, LS, NLS, OPT_LFG, OPT_MRF, OPT_R0);

  function isDynamic
    "is the jacobian used for integration (-> true)
     or solving algebraic systems (-> false)?"
    input JacobianType jacType;
    output Boolean b;
  algorithm
    b := match jacType
      case JacobianType.ODE     then true;
      case JacobianType.DAE     then true;
      case JacobianType.OPT_LFG then true;
      case JacobianType.OPT_MRF then true;
      case JacobianType.OPT_R0  then true;
      else false;
    end match;
  end isDynamic;

  function main
    "Wrapper function for any jacobian function. This will be called during
     simulation and gets the corresponding subfunction from Config."
    extends Module.wrapper;
    input Partition.Kind kind;
  protected
    constant Module.jacobianInterface func = getModule();
  algorithm
    bdae := match bdae
      local
        String name             "Context name for jacobian";
        VariablePointers knowns "Variable array of knowns";

      case BackendDAE.MAIN(varData = BVariable.VAR_DATA_SIM(knowns = knowns))
        algorithm
          if Flags.isSet(Flags.JAC_DUMP) then
            print(StringUtil.headline_1("[symjacdump] Creating symbolic Jacobians:") + "\n");
          end if;

          name := match kind
            case NBPartition.Kind.ODE algorithm
              name := "ODE_JAC";
              bdae.ode := applyToPartitions(bdae.ode, bdae.funcMap, knowns, name, func);
            then name;
            case NBPartition.Kind.DAE algorithm
              name := "DAE_JAC";
              bdae.dae := SOME(applyToPartitions(Util.getOption(bdae.dae), bdae.funcMap, knowns, name, func));
            then name;
            else algorithm
              Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for: " + Partition.Partition.kindToString(kind)});
            then fail();
          end match;

          bdae.ode_event := applyToPartitions(bdae.ode_event, bdae.funcMap, knowns, name, func);
          bdae.algebraic := applyToPartitions(bdae.algebraic, bdae.funcMap, knowns, name, func);
          bdae.alg_event := applyToPartitions(bdae.alg_event, bdae.funcMap, knowns, name, func);
          bdae.init := applyToPartitions(bdae.init, bdae.funcMap, knowns, name, func);
          if isSome(bdae.init_0) then
            bdae.init_0 := SOME(applyToPartitions(Util.getOption(bdae.init_0), bdae.funcMap, knowns, name, func));
          end if;
      then bdae;

      else algorithm
        // maybe add failtrace here and allow failing
        Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for: " + BackendDAE.toString(bdae)});
      then fail();

    end match;
  end main;

  function applyToPartitions
    input output list<Partition.Partition> partitions;
    input output UnorderedMap<Path, Function> funcMap;
    input VariablePointers knowns;
    input String name;
    input Module.jacobianInterface func;
  algorithm
    partitions := list(partJacobian(part, funcMap, knowns, name, func) for part in partitions);
  end applyToPartitions;

  function nonlinear
    input VariablePointers seedCandidates;
    input VariablePointers partialCandidates;
    input EquationPointers equations;
    input array<StrongComponent> comps;
    input Option<Adjacency.Matrix> full;
    input UnorderedMap<Path, Function> funcMap;
    input String name;
    input Boolean staticAsContinuous;
    output Option<Jacobian> jacobian;
  protected
    constant Module.jacobianInterface func = if Flags.isSet(Flags.NLS_ANALYTIC_JACOBIAN)
      then jacobianSymbolic
      else jacobianNumeric;
  algorithm
    jacobian := func(
        name                = name,
        jacType             = JacobianType.NLS,
        seedCandidates      = seedCandidates,
        partialCandidates   = partialCandidates,
        equations           = equations,
        strongComponents    = SOME(comps),
        full                = full,
        funcMap             = funcMap,
        staticAsContinuous  = staticAsContinuous
      );
  end nonlinear;

  function combine
    input list<BackendDAE> jacobians;
    input String name;
    output BackendDAE jacobian;
  protected
    JacobianType jacType = JacobianType.NLS;
    list<Pointer<Variable>> variables = {}, unknowns = {}, auxiliaryVars = {}, aliasVars = {};
    list<Pointer<Variable>> diffVars = {}, dependencies = {}, resultVars = {}, tmpVars = {}, seedVars = {};
    list<StrongComponent> comps = {};
    list<SparsityPatternCol> col_wise_pattern = {};
    list<SparsityPatternRow> row_wise_pattern = {};
    list<ComponentRef> seed_vars = {};
    list<ComponentRef> partial_vars = {};
    Integer nnz = 0;
    VarData varData;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring = SparsityColoring.lazy(EMPTY_SPARSITY_PATTERN);
  algorithm
    if List.hasOneElement(jacobians) then
      jacobian := listHead(jacobians);
      jacobian := match jacobian case BackendDAE.JACOBIAN() algorithm
          jacobian.name := name;
        then jacobian;
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for\n" + BackendDAE.toString(jacobian)});
        then fail();
      end match;
    else
      for jac in jacobians loop
        () := match jac
          local
            VarData tmpVarData;
            SparsityPattern tmpPattern;

          case BackendDAE.JACOBIAN(varData = tmpVarData as VarData.VAR_DATA_JAC(), sparsityPattern = tmpPattern) algorithm
            jacType       := jac.jacType;
            variables     := listAppend(VariablePointers.toList(tmpVarData.variables), variables);
            unknowns      := listAppend(VariablePointers.toList(tmpVarData.unknowns), unknowns);
            auxiliaryVars := listAppend(VariablePointers.toList(tmpVarData.auxiliaries), auxiliaryVars);
            aliasVars     := listAppend(VariablePointers.toList(tmpVarData.aliasVars), aliasVars);
            diffVars      := listAppend(VariablePointers.toList(tmpVarData.diffVars), diffVars);
            dependencies  := listAppend(VariablePointers.toList(tmpVarData.dependencies), dependencies);
            resultVars    := listAppend(VariablePointers.toList(tmpVarData.resultVars), resultVars);
            tmpVars       := listAppend(VariablePointers.toList(tmpVarData.tmpVars), tmpVars);
            seedVars      := listAppend(VariablePointers.toList(tmpVarData.seedVars), seedVars);

            comps         := listAppend(arrayList(jac.comps), comps);

            col_wise_pattern  := listAppend(tmpPattern.col_wise_pattern, col_wise_pattern);
            row_wise_pattern  := listAppend(tmpPattern.row_wise_pattern, row_wise_pattern);
            seed_vars         := listAppend(tmpPattern.seed_vars, seed_vars);
            partial_vars      := listAppend(tmpPattern.partial_vars, partial_vars);
            nnz               := nnz + tmpPattern.nnz;
            sparsityColoring  := SparsityColoring.combine(sparsityColoring, jac.sparsityColoring);
          then ();

          else algorithm
            Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for\n" + BackendDAE.toString(jac)});
          then fail();
        end match;
      end for;

      varData := VarData.VAR_DATA_JAC(
        variables     = VariablePointers.fromList(variables),
        unknowns      = VariablePointers.fromList(unknowns),
        auxiliaries   = VariablePointers.fromList(auxiliaryVars),
        aliasVars     = VariablePointers.fromList(aliasVars),
        diffVars      = VariablePointers.fromList(diffVars),
        dependencies  = VariablePointers.fromList(dependencies),
        resultVars    = VariablePointers.fromList(resultVars),
        tmpVars       = VariablePointers.fromList(tmpVars),
        seedVars      = VariablePointers.fromList(seedVars)
      );

      sparsityPattern := SPARSITY_PATTERN(
        col_wise_pattern  = col_wise_pattern,
        row_wise_pattern  = row_wise_pattern,
        seed_vars         = seed_vars,
        partial_vars      = partial_vars,
        nnz               = nnz
      );

      jacobian := BackendDAE.JACOBIAN(
        name              = name,
        jacType           = jacType,
        varData           = varData,
        comps             = listArray(comps),
        //sparsity          = Adjacency.Matrix.SPARSITY(arrayCreate()),
        sparsityPattern   = sparsityPattern,
        sparsityColoring  = sparsityColoring,
        isAdjoint         = name == "ADJ" // this is maybe bad (e.g. when name changes)
      );
    end if;
  end combine;

  function getModule
    "Returns the module function that was chosen by the user."
    output Module.jacobianInterface func;
  algorithm
    func := match Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN)
      case "symbolic" then jacobianSymbolic;
      case "symbolicadjoint" then jacobianSymbolicAdjoint;
      case "bidirectional" then jacobianSymbolic;
      case "numeric"  then jacobianNumeric;
      case "none"     then jacobianNone;
      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because of unknown jacobian type: " + Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN)});
      then fail();
    end match;
  end getModule;

  function toString
    input BackendDAE jacobian;
    input output String str;
  algorithm
    str := BackendDAE.toString(jacobian, str);
  end toString;

  function jacobianTypeString
    input JacobianType jacType;
    output String str;
  algorithm
    str := match jacType
      case JacobianType.ODE     then "[ODE]";
      case JacobianType.DAE     then "[DAE]";
      case JacobianType.LS      then "[LS-]";
      case JacobianType.NLS     then "[NLS]";
      case JacobianType.OPT_LFG then "[OPT-LFG]";
      case JacobianType.OPT_MRF then "[OPT-MRF]";
      case JacobianType.OPT_R0  then "[OPT-R0]";
                                else "[ERR]";
    end match;
  end jacobianTypeString;

  // necessary as wrapping value type for UnorderedMap
  type CrefLst = list<ComponentRef>;

  type SparsityPatternCol = tuple<ComponentRef, list<ComponentRef>> "seed_var, {partial_vars}";
  type SparsityPatternRow = SparsityPatternCol                      "partial_var, {seed_vars}";

  uniontype SparsityPattern
    record SPARSITY_PATTERN
      list<SparsityPatternCol> col_wise_pattern   "colum-wise sparsity pattern";
      list<SparsityPatternRow> row_wise_pattern   "row-wise sparsity pattern";
      list<ComponentRef> seed_vars                "independent variables solved here ($SEED)";
      list<ComponentRef> partial_vars             "LHS variables of the jacobian ($pDER)";
      Integer nnz                                 "number of nonzero elements";
    end SPARSITY_PATTERN;

    function toString
      input SparsityPattern pattern;
      output String str = StringUtil.headline_2("Sparsity Pattern (nnz: " + intString(pattern.nnz) + ")");
    protected
      ComponentRef cref;
      list<ComponentRef> dependencies;
      Boolean colEmpty = listEmpty(pattern.col_wise_pattern);
      Boolean rowEmpty = listEmpty(pattern.row_wise_pattern);
    algorithm
      str := str + "\n" + StringUtil.headline_3("### Seeds (col vars) ###");
      str := str + List.toString(pattern.seed_vars, ComponentRef.toString) + "\n";
      str := str + "\n" + StringUtil.headline_3("### Partials (row vars) ###");
      str := str + List.toString(pattern.partial_vars, ComponentRef.toString) + "\n";
      if not colEmpty then
        str := str + "\n" + StringUtil.headline_3("### Columns ###");
        for col in pattern.col_wise_pattern loop
          (cref, dependencies) := col;
          str := str + "(" + ComponentRef.toString(cref) + ")\t affects:\t" + ComponentRef.listToString(dependencies) + "\n";
        end for;
      end if;
      if not rowEmpty then
        str := str + "\n" + StringUtil.headline_3("##### Rows #####");
        for row in pattern.row_wise_pattern loop
          (cref, dependencies) := row;
          str := str + "(" + ComponentRef.toString(cref) + ")\t depends on:\t" + ComponentRef.listToString(dependencies) + "\n";
        end for;
      end if;
    end toString;

    function lazy
      input VariablePointers seedCandidates;
      input VariablePointers partialCandidates;
      input Option<array<StrongComponent>> strongComponents "Strong Components";
      input JacobianType jacType;
      output SparsityPattern sparsityPattern;
      output SparsityColoring sparsityColoring;
    protected
      list<ComponentRef> seed_vars, partial_vars;
      list<SparsityPatternCol> cols = {};
      list<SparsityPatternRow> rows = {};
      Integer nnz;
    algorithm
      // get all relevant crefs
      seed_vars     := VariablePointers.getScalarVarNames(seedCandidates, false);
      partial_vars  := VariablePointers.getScalarVarNames(partialCandidates, false);

      // assume full dependency
      cols := list((s, partial_vars) for s in seed_vars);
      rows := list((p, seed_vars) for p in partial_vars);
      nnz := listLength(partial_vars) * listLength(seed_vars);

      sparsityPattern := SPARSITY_PATTERN(cols, rows, seed_vars, partial_vars, nnz);
      sparsityColoring := SparsityColoring.lazy(sparsityPattern);
    end lazy;

    // Pretty-print the bipartite adjacency map used during sparsity detection:
    // map[cref] -> list of neighbor crefs on the opposite side.
    function adjacencyMapToString
      input UnorderedMap<ComponentRef, list<ComponentRef>> map;
      output String s;
    protected
      list<ComponentRef> keys;
      ComponentRef k;
      list<ComponentRef> neighs;
      list<String> lines = {};
    algorithm
      keys := UnorderedMap.keyList(map);
      for k in keys loop
        neighs := UnorderedMap.getOrFail(k, map);
        lines := ("  " + ComponentRef.toString(k) + " -> " + ComponentRef.listToString(neighs)) :: lines;
      end for;
      lines := listReverse(lines);
      s := "Adjacency map (" + intString(listLength(keys)) + " keys):\n" + stringDelimitList(lines, "\n");
    end adjacencyMapToString;

    function resolveDependency
      input ComponentRef cref;
      input UnorderedMap<ComponentRef, list<ComponentRef>> map;
      input UnorderedSet<ComponentRef> seed_set;
      input UnorderedSet<ComponentRef> visited;
      input UnorderedSet<ComponentRef> dep_set "collect seed dependencies here";
    protected
      list<ComponentRef> tmp_lst = {}; // HACK: the compiler needs help with the type
    algorithm
      if UnorderedSet.add(cref, visited) then
        if UnorderedSet.contains(cref, seed_set) then
          UnorderedSet.add(cref, dep_set);
        else
          for dep in UnorderedMap.getOrDefault(cref, map, tmp_lst) loop
            resolveDependency(dep, map, seed_set, visited, dep_set);
          end for;
        end if;
      end if;
    end resolveDependency;

    function resolveRowDependencies
      input ComponentRef row;
      input UnorderedMap<ComponentRef, list<ComponentRef>> map;
      input UnorderedSet<ComponentRef> seed_set;
      output list<ComponentRef> dependencies;
    protected
      UnorderedSet<ComponentRef> dep_set = UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual);
      list<ComponentRef> tmp_lst = {}; // HACK: the compiler needs help with the type
    algorithm
      for dep in UnorderedMap.getOrDefault(row, map, tmp_lst) loop
        resolveDependency(dep, map, seed_set, UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual), dep_set);
      end for;
      dependencies := List.sort(UnorderedSet.toList(dep_set), ComponentRef.isGreater);
    end resolveRowDependencies;

    function create
      input VariablePointers seedCandidates;
      input VariablePointers partialCandidates;
      input Option<array<StrongComponent>> strongComponents "Strong Components";
      input JacobianType jacType;
      input Boolean staticAsContinuous;
      output SparsityPattern sparsityPattern;
      output SparsityColoring sparsityColoring;
    protected
      UnorderedMap<ComponentRef, list<ComponentRef>> map;
    algorithm
      (sparsityPattern, map) := match strongComponents
        local
          Mapping seed_mapping, partial_mapping;
          array<StrongComponent> comps;
          list<ComponentRef> seed_vars, seed_vars_array, partial_vars, partial_vars_array, jac_row_vars, row_deps, tmp, row_vars = {}, col_vars = {};
          UnorderedSet<ComponentRef> set, seed_set;
          list<SparsityPatternCol> cols = {};
          list<SparsityPatternRow> rows = {};
          ComponentRef row_cref;
          Integer nnz = 0;

        case SOME(comps) guard(arrayEmpty(comps)) algorithm
        then (EMPTY_SPARSITY_PATTERN, UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual));

        case SOME(comps) algorithm
          // create index mapping only for variables
          seed_mapping    := Mapping.create(EquationPointers.empty(), seedCandidates);
          partial_mapping := Mapping.create(EquationPointers.empty(), partialCandidates);

          // get all relevant crefs
          partial_vars        := VariablePointers.getScalarVarNames(partialCandidates, false);
          seed_vars           := VariablePointers.getScalarVarNames(seedCandidates, false);
          jac_row_vars        := getSparsityRowCrefs(partialCandidates, jacType, staticAsContinuous);
          // unscalarized seed vars are currently needed for sparsity pattern
          seed_vars_array     := VariablePointers.getVarNames(seedCandidates);
          partial_vars_array  := VariablePointers.getVarNames(partialCandidates);

          // create a sufficient big unordered map
          map := UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(seed_vars) + listLength(partial_vars)));
          set := UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(seed_vars_array)));
          seed_set := UnorderedSet.fromList(seed_vars, ComponentRef.hash, ComponentRef.isEqual);

          // save all seed_vars and partial_vars to know later on if a cref should be added
          for cref in seed_vars loop UnorderedMap.add(cref, {}, map); end for;
          for cref in partial_vars loop UnorderedMap.add(cref, {}, map); end for;
          for cref in seed_vars_array loop UnorderedSet.add(cref, set); end for;
          for cref in partial_vars_array loop UnorderedSet.add(cref, set); end for;

          // traverse all components and save cref dependencies (only column-wise)
          for i in 1:arrayLength(comps) loop
            if not StrongComponent.isDiscrete(comps[i]) then
              StrongComponent.collectCrefs(comps[i], seedCandidates, partialCandidates, seed_mapping, partial_mapping, map, set, jacType);
            end if;
          end for;

          // create row-wise sparsity pattern
          for cref in listReverse(jac_row_vars) loop
            // only create rows for actual Jacobian result variables / rows
            if UnorderedMap.contains(cref, map) then
              rows := (cref, resolveRowDependencies(cref, map, seed_set)) :: rows;
              row_vars := cref :: row_vars;
            end if;
          end for;

          // create column-wise sparsity pattern
          for cref in listReverse(seed_vars) loop
            // transpose the resolved row dependencies
            tmp := {};
            for row in rows loop
              (row_cref, row_deps) := row;
              if List.contains(row_deps, cref, ComponentRef.isEqual) then
                tmp := row_cref :: tmp;
              end if;
            end for;
            tmp := List.sort(UnorderedSet.unique_list(tmp, ComponentRef.hash, ComponentRef.isEqual), ComponentRef.isGreater);
            cols := (cref, tmp) :: cols;
            col_vars := cref :: col_vars;
          end for;

          // find number of nonzero elements
          for col in cols loop
            (_, tmp) := col;
            nnz := nnz + listLength(tmp);
          end for;
        then (SPARSITY_PATTERN(cols, rows, col_vars, row_vars, nnz), map);

        case NONE() algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because of missing strong components."});
        then fail();

        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
        then fail();
      end match;

      // create coloring
      if Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN) == "bidirectional" and isDynamic(jacType) then
        sparsityColoring := SparsityColoring.StarBiColoringAlg(sparsityPattern, jacType);
      else
        sparsityColoring := SparsityColoring.PartialD2ColoringAlgC(sparsityPattern, jacType);
      end if;
      // sparsityColoring := SparsityColoring.PartialD2ColoringAlgColumnAndRow(sparsityPattern, map);

      if Flags.isSet(Flags.DUMP_SPARSE) then
        print(toString(sparsityPattern) + "\n" + SparsityColoring.toString(sparsityColoring) + "\n");
      end if;
    end create;

    function createForRows
      "Create sparsity for an explicit list of row variables. This is used by derivative
       consumers whose rows are generated variables and cannot be selected by JacobianType."
      input VariablePointers seedCandidates;
      input VariablePointers partialCandidates;
      input VariablePointers rowCandidates;
      input Option<array<StrongComponent>> strongComponents "Strong Components";
      input JacobianType jacType;
      input Boolean staticAsContinuous;
      output SparsityPattern sparsityPattern;
    protected
      UnorderedMap<ComponentRef, list<ComponentRef>> map;
    algorithm
      (sparsityPattern, map) := match strongComponents
        local
          Mapping seed_mapping, partial_mapping;
          array<StrongComponent> comps;
          list<ComponentRef> seed_vars, seed_vars_array, partial_vars, partial_vars_array, jac_row_vars, row_deps, tmp, row_vars = {}, col_vars = {};
          UnorderedSet<ComponentRef> set, seed_set;
          list<SparsityPatternCol> cols = {};
          list<SparsityPatternRow> rows = {};
          ComponentRef row_cref;
          Integer nnz = 0;

        case SOME(comps) guard(arrayEmpty(comps)) algorithm
        then (EMPTY_SPARSITY_PATTERN, UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual));

        case SOME(comps) algorithm
          seed_mapping    := Mapping.create(EquationPointers.empty(), seedCandidates);
          partial_mapping := Mapping.create(EquationPointers.empty(), partialCandidates);

          partial_vars        := VariablePointers.getScalarVarNames(partialCandidates, false);
          seed_vars           := VariablePointers.getScalarVarNames(seedCandidates, false);
          jac_row_vars        := VariablePointers.getScalarVarNames(rowCandidates, false);
          seed_vars_array     := VariablePointers.getVarNames(seedCandidates);
          partial_vars_array  := VariablePointers.getVarNames(partialCandidates);

          map := UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(seed_vars) + listLength(partial_vars)));
          set := UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(seed_vars_array)));
          seed_set := UnorderedSet.fromList(seed_vars, ComponentRef.hash, ComponentRef.isEqual);

          for cref in seed_vars loop UnorderedMap.add(cref, {}, map); end for;
          for cref in partial_vars loop UnorderedMap.add(cref, {}, map); end for;
          for cref in seed_vars_array loop UnorderedSet.add(cref, set); end for;
          for cref in partial_vars_array loop UnorderedSet.add(cref, set); end for;

          for i in 1:arrayLength(comps) loop
            if not StrongComponent.isDiscrete(comps[i]) then
              StrongComponent.collectCrefs(comps[i], seedCandidates, partialCandidates, seed_mapping, partial_mapping, map, set, jacType);
            end if;
          end for;

          for cref in listReverse(jac_row_vars) loop
            if UnorderedMap.contains(cref, map) then
              rows := (cref, resolveRowDependencies(cref, map, seed_set)) :: rows;
              row_vars := cref :: row_vars;
            end if;
          end for;

          for cref in listReverse(seed_vars) loop
            tmp := {};
            for row in rows loop
              (row_cref, row_deps) := row;
              if List.contains(row_deps, cref, ComponentRef.isEqual) then
                tmp := row_cref :: tmp;
              end if;
            end for;
            tmp := List.sort(UnorderedSet.unique_list(tmp, ComponentRef.hash, ComponentRef.isEqual), ComponentRef.isGreater);
            cols := (cref, tmp) :: cols;
            col_vars := cref :: col_vars;
          end for;

          for col in cols loop
            (_, tmp) := col;
            nnz := nnz + listLength(tmp);
          end for;
        then (SPARSITY_PATTERN(cols, rows, col_vars, row_vars, nnz), map);

        case NONE() algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because of missing strong components."});
        then fail();

        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
        then fail();
      end match;

      if Flags.isSet(Flags.DUMP_SPARSE) then
        print(toString(sparsityPattern) + "\n");
      end if;
    end createForRows;

    function createEmpty
      output SparsityPattern sparsityPattern = EMPTY_SPARSITY_PATTERN;
      output SparsityColoring sparsityColoring = EMPTY_SPARSITY_COLORING;
    end createEmpty;
  end SparsityPattern;

  constant SparsityPattern EMPTY_SPARSITY_PATTERN = SPARSITY_PATTERN({}, {}, {}, {}, 0);
  constant SparsityColoring EMPTY_SPARSITY_COLORING = SPARSITY_COLORING(listArray({}), listArray({}));

  type SparsityColoringCol = list<ComponentRef>  "seed variable lists belonging to the same color";
  type SparsityColoringRow = SparsityColoringCol "partial variable lists for each color (multiples allowed!)";

  uniontype SparsityColoring
    record SPARSITY_COLORING
      "column wise coloring with extra row sparsity information"
      array<SparsityColoringCol> cols;
      array<SparsityColoringRow> rows;
    end SPARSITY_COLORING;

    record SPARSITY_BICOLORING
      "bidirectional (star bicoloring) with separate column and row color groups.
       cols[1..nColColors] are seed variable groups for forward (column-wise) evaluation.
       rows[1..nRowColors] are partial variable groups for adjoint (row-wise) evaluation."
      array<SparsityColoringCol> cols   "seed vars per column-color (forward direction)";
      array<SparsityColoringRow> rows   "partial vars per row-color (adjoint direction)";
      Integer nColColors                "number of column colors used";
      Integer nRowColors                "number of row colors used";
    end SPARSITY_BICOLORING;

    function toString
      input SparsityColoring sparsityColoring;
      output String str = StringUtil.headline_2("Sparsity Coloring");
    protected
      String body;
    algorithm
      body := match sparsityColoring
        case SPARSITY_COLORING() then toStringUnidirectional(sparsityColoring);
        case SPARSITY_BICOLORING() then toStringBidirectional(sparsityColoring);
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because of unknown sparsity coloring type."});
        then fail();
      end match;
      str := str + body;
    end toString;

    function toStringUnidirectional
      input SparsityColoring sparsityColoring;
      output String str = "";
    protected
      array<SparsityColoringCol> cols = getCols(sparsityColoring);
      array<SparsityColoringRow> rows = getRows(sparsityColoring);
    algorithm
      if arrayLength(cols) == 0 then
        str := str + "\n<empty sparsity pattern>\n";
      end if;
      for i in 1:arrayLength(cols) loop
        str := str + "Column Color (" + intString(i) + ")\n"
          + "  - Column: " + ComponentRef.listToString(cols[i]) + "\n";
      end for;
      for i in 1:arrayLength(rows) loop
        str := str + "Row Color (" + intString(i) + ")\n"
          + "  - Row:    " + ComponentRef.listToString(rows[i]) + "\n";
      end for;
    end toStringUnidirectional;

    function toStringBidirectional
      input SparsityColoring sparsityColoring;
      output String str = "";
    protected
      array<SparsityColoringCol> cols = getCols(sparsityColoring);
      array<SparsityColoringRow> rows = getRows(sparsityColoring);
      Integer nColColors, nRowColors;
    algorithm
      nColColors := arrayLength(cols);
      nRowColors := arrayLength(rows);
      str := str + "\n[Bidirectional] Column colors: " + intString(nColColors)
        + ", Row colors: " + intString(nRowColors) + "\n";
      for i in 1:arrayLength(cols) loop
        str := str + "Forward Column Color (" + intString(i) + ")\n"
          + "  - Seeds: " + ComponentRef.listToString(cols[i]) + "\n";
      end for;
      for i in 1:arrayLength(rows) loop
        str := str + "Adjoint Row Color (" + intString(i) + ")\n"
          + "  - Partials: " + ComponentRef.listToString(rows[i]) + "\n";
      end for;
    end toStringBidirectional;

    function lazy
      "creates a lazy coloring that just groups each independent variable individually
      and implies dependence for each row"
      input SparsityPattern sparsityPattern;
      output SparsityColoring sparsityColoring;
    protected
      array<SparsityColoringCol> cols;
      array<SparsityColoringRow> rows;
    algorithm
      cols := listArray(list({cref} for cref in sparsityPattern.seed_vars));
      rows := arrayCreate(arrayLength(cols), sparsityPattern.partial_vars);
      sparsityColoring := SPARSITY_COLORING(cols, rows);
    end lazy;

    function PartialD2ColoringAlgC
      "author: kabdelhak 2022-03
      taken from: 'What Color Is Your Jacobian? Graph Coloring for Computing Derivatives'
      https://doi.org/10.1137/S0036144504444711
      A greedy partial distance-2 coloring algorithm implemented in C."
      input SparsityPattern sparsityPattern;
      input JacobianType jacType;
      output SparsityColoring sparsityColoring;
    protected
      array<ComponentRef> seeds, partials;
      UnorderedMap<ComponentRef, Integer> seed_indices, partial_indices;
      Integer sizeCols, sizeRows;
      ComponentRef idx_cref;
      list<ComponentRef> deps;
      array<list<Integer>> cols, rows, colored_cols, colored_rows;
      array<SparsityColoringCol> cref_colored_cols, cref_colored_rows;
      function getIndices
        input ComponentRef cref;
        input UnorderedMap<ComponentRef, Integer> seed_indices;
        input UnorderedMap<ComponentRef, Integer> partial_indices;
        input array<list<Integer>> rows;
        output list<Integer> indices;
      algorithm
        if UnorderedMap.contains(cref, seed_indices) then
          indices := {UnorderedMap.getSafe(cref, seed_indices, sourceInfo())};
        elseif UnorderedMap.contains(cref, partial_indices) then
          indices := rows[UnorderedMap.getSafe(cref, partial_indices, sourceInfo())];
        else
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because cref " + ComponentRef.toString(cref)
            + " is neither a seed nor a partial candidate!"});
          fail();
        end if;
      end getIndices;
    algorithm
      // create index -> cref arrays
      seeds := listArray(sparsityPattern.seed_vars);
      partials := listArray(sparsityPattern.partial_vars);

      // create cref -> index maps
      sizeCols := arrayLength(seeds);
      sizeRows := arrayLength(partials);
      seed_indices := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(sizeCols));
      partial_indices := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(sizeRows));
      for i in 1:sizeCols loop
        UnorderedMap.add(seeds[i], i, seed_indices);
      end for;
      for i in 1:sizeRows loop
        UnorderedMap.add(partials[i], i, partial_indices);
      end for;
      cols := arrayCreate(sizeCols, {});
      rows := arrayCreate(sizeRows, {});

      // prepare index based sparsity pattern for C
      for tpl in sparsityPattern.col_wise_pattern loop
        (idx_cref, deps) := tpl;
        cols[UnorderedMap.getSafe(idx_cref, seed_indices, sourceInfo())] := list(UnorderedMap.getSafe(dep, partial_indices, sourceInfo()) for dep in deps);
      end for;
      for tpl in sparsityPattern.row_wise_pattern loop
        (idx_cref, deps) := tpl;
        rows[UnorderedMap.getSafe(idx_cref, partial_indices, sourceInfo())] := listAppend(getIndices(dep, seed_indices, partial_indices, rows) for dep in deps);
      end for;

      // call C function (old backend - ToDo: port to new backend!)
      // colored_cols := Coloring.createColoring(cols, rows, sizeRows, sizeCols);
      colored_cols := Coloring.createColoring(rows, cols, sizeCols, sizeRows);
      // get cref based coloring
      cref_colored_cols := arrayCreate(arrayLength(colored_cols), {});
      for i in 1:arrayLength(colored_cols) loop
        cref_colored_cols[i] := list(seeds[idx] for idx in colored_cols[i]);
      end for;

      // Row coloring (color partials)
      colored_rows := Coloring.createColoring(cols, rows, sizeRows, sizeCols);
      cref_colored_rows := arrayCreate(arrayLength(colored_rows), {});
      for i in 1:arrayLength(colored_rows) loop
        cref_colored_rows[i] := list(partials[idx] for idx in colored_rows[i]);
      end for;

      //sparsityColoring := SPARSITY_COLORING(cref_colored_cols, arrayCreate(sizeRows, {}));
      //sparsityColoring := SPARSITY_COLORING(cref_colored_cols, arrayCreate(arrayLength(cref_colored_cols), {}));
      sparsityColoring := SPARSITY_COLORING(cref_colored_cols, cref_colored_rows);
    end PartialD2ColoringAlgC;

    function StarBiColoringAlg
      "author: fbrandt 2025
      Star bicoloring via ColPack for bidirectional Jacobian evaluation.
      Jointly computes a column and row coloring to minimize total evaluation count.
      Reference: Gebremedhin, Tarafdar, Manne, Pothen.
      'New Acyclic and Star Coloring Algorithms with Application to Computing Hessians'
      https://doi.org/10.1137/050639879"
      input SparsityPattern sparsityPattern;
      input JacobianType jacType;
      output SparsityColoring sparsityColoring;
    protected
      array<ComponentRef> seeds, partials;
      UnorderedMap<ComponentRef, Integer> seed_indices, partial_indices;
      Integer sizeCols, sizeRows, nnz, ptr, c, ri;
      ComponentRef idx_cref;
      list<ComponentRef> deps;
      // per-row adjacency (0-based column indices)
      array<list<Integer>> rowAdj;
      // CSR arrays (values are 0-based)
      array<Integer> rowPtr, colIdxArr;
      // ColPack outputs
      array<Integer> colColors, rowColors;
      Integer nColColors, nRowColors;
      // color groups
      array<list<ComponentRef>> colGroups, rowGroups;
    algorithm
      // create index -> cref arrays
      seeds := listArray(sparsityPattern.seed_vars);
      // this assumes ODE Jacobian
      partials := listArray(list(cref for cref guard(isRowInJacobian(cref, jacType)) in sparsityPattern.partial_vars));
      sizeCols := arrayLength(seeds);
      sizeRows := arrayLength(partials);

      // build cref -> 1-based index maps
      seed_indices := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(sizeCols));
      partial_indices := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(sizeRows));
      for i in 1:sizeCols loop
        UnorderedMap.add(seeds[i], i, seed_indices);
      end for;
      for i in 1:sizeRows loop
        UnorderedMap.add(partials[i], i, partial_indices);
      end for;

      // build per-row adjacency: rowAdj[i] = list of 0-based (for C) column indices
      rowAdj := arrayCreate(sizeRows, {});
      nnz := 0;
      for tpl in sparsityPattern.row_wise_pattern loop
        (idx_cref, deps) := tpl;
        if UnorderedMap.contains(idx_cref, partial_indices) then
          ri := UnorderedMap.getSafe(idx_cref, partial_indices, sourceInfo());
          rowAdj[ri] := list(UnorderedMap.getSafe(dep, seed_indices, sourceInfo()) - 1
            for dep guard(UnorderedMap.contains(dep, seed_indices)) in deps);
          nnz := nnz + listLength(rowAdj[ri]);
        end if;
      end for;

      // convert to CSR format (0-based values stored in 1-based MetaModelica arrays)
      rowPtr := arrayCreate(sizeRows + 1, 0);
      colIdxArr := arrayCreate(max(nnz, 1), 0);
      ptr := 0;
      for i in 1:sizeRows loop
        rowPtr[i] := ptr;
        for cidx in rowAdj[i] loop
          colIdxArr[ptr + 1] := cidx;
          ptr := ptr + 1;
        end for;
      end for;
      rowPtr[sizeRows + 1] := ptr;

      // call ColPack star bicoloring
      (colColors, nColColors, rowColors, nRowColors) :=
        colpackStarBicoloring(sizeRows, sizeCols, rowPtr, colIdxArr);

      // group seeds by column color
      colGroups := arrayCreate(nColColors, {});
      for j in 1:sizeCols loop
        c := colColors[j];
        if c > 0 then
          colGroups[c] := seeds[j] :: colGroups[c];
        end if;
      end for;

      // group partials by row color
      rowGroups := arrayCreate(nRowColors, {});
      for i in 1:sizeRows loop
        c := rowColors[i];
        if c > 0 then
          rowGroups[c] := partials[i] :: rowGroups[c];
        end if;
      end for;

      sparsityColoring := SPARSITY_BICOLORING(colGroups, rowGroups, nColColors, nRowColors);
    end StarBiColoringAlg;

    function PartialD2ColoringAlgColumnAndRow
      "author: fbrandt 2025-10
      taken from: 'What Color Is Your Jacobian? Graph Coloring for Computing Derivatives'
      https://doi.org/10.1137/S0036144504444711 (Algorithm 3.2)
      A greedy partial distance-2 coloring algorithm done twice to compute both column and row coloring."
      input SparsityPattern sparsityPattern;
      input UnorderedMap<ComponentRef, list<ComponentRef>> map;
      output SparsityColoring sparsityColoring;
    protected
      array<ComponentRef> seed_nodes, partial_nodes;
      list<SparsityColoringCol> col_groups = {};
      list<SparsityColoringRow> row_groups = {};
      array<SparsityColoringCol> cols_arr;
      array<SparsityColoringRow> rows_arr;
    algorithm
      // Nodes to color: seeds (columns) and partials (rows)
      seed_nodes := listArray(sparsityPattern.seed_vars);
      partial_nodes  := listArray(sparsityPattern.partial_vars);

      // Column coloring (seeds -> partials -> seeds)
      col_groups := GreedyPartialD2Color(seed_nodes, map);
      // Row coloring (partials -> seeds -> partials)
      row_groups := GreedyPartialD2Color(partial_nodes, map);
      // Build arrays for result
      cols_arr := listArray(col_groups);
      rows_arr := listArray(row_groups);

      sparsityColoring := SPARSITY_COLORING(cols_arr, rows_arr);
    end PartialD2ColoringAlgColumnAndRow;

    // Distance-2 greedy coloring on a bipartite graph represented by 'map':
    // Given a node set 'nodes' (either seeds or partials), assign colors so that
    // no two nodes at distance 2 (node -> opposite side -> node) share a color.
    // Returns the list of color groups in stable order.
    function GreedyPartialD2Color
      input array<ComponentRef> nodes;
      input UnorderedMap<ComponentRef, list<ComponentRef>> map;
      output list<list<ComponentRef>> groups_lst;
    protected
      UnorderedMap<ComponentRef, Integer> index_lookup;
      array<Integer> coloring, forbidden_colors;
      array<Boolean> color_exists;
      array<list<ComponentRef>> groups;
      Integer i, color, n = arrayLength(nodes);
      ComponentRef node, mid, neigh;
    algorithm
      // Build cref -> index lookup for the given nodes.
      index_lookup := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(n));
      for i in 1:n loop
        UnorderedMap.add(nodes[i], i, index_lookup);
      end for;

      // Init data structures
      coloring := arrayCreate(n, 0);
      forbidden_colors := arrayCreate(n, 0);
      color_exists := arrayCreate(n, false);
      groups := arrayCreate(n, {});

      // Greedy partial distance-2 coloring:
      // For node i, forbid colors of any already-colored neighbor at distance 2.
      for i in 1:n loop
        node := nodes[i];

        // Mark forbidden colors for neighbors at distance 2: node -> mid -> neigh
        for mid in UnorderedMap.getSafe(node, map, sourceInfo()) loop
          for neigh in UnorderedMap.getSafe(mid, map, sourceInfo()) loop
            color := coloring[UnorderedMap.getSafe(neigh, index_lookup, sourceInfo())];
            if color > 0 then
              forbidden_colors[color] := i;
            end if;
          end for;
        end for;

        // Pick smallest available color
        color := 1;
        while forbidden_colors[color] == i loop
          color := color + 1;
        end while;

        coloring[i] := color;
        color_exists[color] := true;
        groups[color] := node :: groups[color];
      end for;

      // Collect groups (reverse to keep stable order)
      groups_lst := {};
      for i in arrayLength(color_exists):-1:1 loop
        if color_exists[i] then
          groups_lst := groups[i] :: groups_lst;
        end if;
      end for;
    end GreedyPartialD2Color;

    function PartialD2ColoringAlg
      "author: kabdelhak 2022-03
      taken from: 'What Color Is Your Jacobian? Graph Coloring for Computing Derivatives'
      https://doi.org/10.1137/S0036144504444711
      A greedy partial distance-2 coloring algorithm. Slightly adapted to also track row sparsity."
      input SparsityPattern sparsityPattern;
      input UnorderedMap<ComponentRef, list<ComponentRef>> map;
      output SparsityColoring sparsityColoring;
    protected
      array<ComponentRef> cref_lookup;
      UnorderedMap<ComponentRef, Integer> index_lookup;
      array<Boolean> color_exists;
      array<Integer> coloring, forbidden_colors;
      array<list<ComponentRef>> col_coloring, row_coloring;
      Integer color;
      list<SparsityColoringCol> cols_lst = {};
      list<SparsityColoringRow> rows_lst = {};
    algorithm
      // integer to cref and reverse lookup arrays
      cref_lookup := listArray(sparsityPattern.seed_vars); // x, y, z
      index_lookup := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(sparsityPattern.seed_vars)));
      for i in 1:arrayLength(cref_lookup) loop
        UnorderedMap.add(cref_lookup[i], i, index_lookup); // x->1, y->2, z->3
      end for;

      // create empty colorings
      coloring := arrayCreate(arrayLength(cref_lookup), 0);
      forbidden_colors := arrayCreate(arrayLength(cref_lookup), 0);
      color_exists := arrayCreate(arrayLength(cref_lookup), false);
      col_coloring := arrayCreate(arrayLength(cref_lookup), {});
      row_coloring := arrayCreate(arrayLength(cref_lookup), {});

      for i in 1:arrayLength(cref_lookup) loop
        // all neighbors w of v_i
        for row_var /* w */ in UnorderedMap.getSafe(cref_lookup[i], map, sourceInfo()) loop
          // all colored neighbors x of w
          for col_var /* x */ in UnorderedMap.getSafe(row_var, map, sourceInfo()) loop
            color := coloring[UnorderedMap.getSafe(col_var, index_lookup, sourceInfo())];
            if color > 0 then
              forbidden_colors[color] := i;
            end if;
          end for;
        end for;
        // assign the smallest available color to v_i
        color := 1;
        while forbidden_colors[color] == i loop
          color := color + 1;
        end while;
        coloring[i] := color;
        // also save all row dependencies of this color
        row_coloring[color] := listAppend(row_coloring[color], UnorderedMap.getSafe(cref_lookup[i], map, sourceInfo()));
        color_exists[color] := true;
      end for;

      for i in 1:arrayLength(coloring) loop
        col_coloring[coloring[i]] := cref_lookup[i] :: col_coloring[coloring[i]];
      end for;

      // traverse in reverse to have correct ordering in the end)
      for i in arrayLength(color_exists):-1:1 loop
        if color_exists[i] then
          cols_lst := col_coloring[i] :: cols_lst;
          rows_lst := row_coloring[i] :: rows_lst;
        end if;
      end for;

      sparsityColoring := SPARSITY_COLORING(listArray(cols_lst), listArray(rows_lst));
    end PartialD2ColoringAlg;

    function getCols
      input SparsityColoring coloring;
      output array<SparsityColoringCol> cols;
    algorithm
      cols := match coloring
        case SPARSITY_COLORING() then coloring.cols;
        case SPARSITY_BICOLORING() then coloring.cols;
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because unknown sparsity coloring type was given."});
          then fail();
      end match;
    end getCols;

    function getRows
      input SparsityColoring coloring;
      output array<SparsityColoringRow> rows;
    algorithm
      rows := match coloring
        case SPARSITY_COLORING() then coloring.rows;
        case SPARSITY_BICOLORING() then coloring.rows;
        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because unknown sparsity coloring type was given."});
          then fail();
      end match;
    end getRows;

    function combine
      "combines sparsity patterns by just appending them because they are supposed to
      be entirely independent of each other."
      input SparsityColoring coloring1;
      input SparsityColoring coloring2;
      output SparsityColoring coloring_out;
    protected
      array<SparsityColoringCol> cols1, cols2;
      array<SparsityColoringCol> cols_big, cols_small;
      array<SparsityColoringRow> rows1, rows2;
      array<SparsityColoringRow> rows_big, rows_small;
    algorithm
      cols1 := getCols(coloring1);
      cols2 := getCols(coloring2);
      rows1 := getRows(coloring1);
      rows2 := getRows(coloring2);

      // append the smaller to the bigger
      (cols_big, cols_small) := if arrayLength(cols2) > arrayLength(cols1) then (arrayCopy(cols2), cols1) else (arrayCopy(cols1), cols2);
      (rows_big, rows_small) := if arrayLength(rows2) > arrayLength(rows1) then (arrayCopy(rows2), rows1) else (arrayCopy(rows1), rows2);

      // append the columns
      for i in 1:arrayLength(cols_small) loop
        cols_big[i] := listAppend(cols_big[i], cols_small[i]);
      end for;

      // append the rows
      for i in 1:arrayLength(rows_small) loop
        rows_big[i] := listAppend(rows_big[i], rows_small[i]);
      end for;

      coloring_out := match (coloring1, coloring2)
        case (SPARSITY_BICOLORING(), _) then SPARSITY_BICOLORING(cols_big, rows_big, arrayLength(cols_big), arrayLength(rows_big));
        case (_, SPARSITY_BICOLORING()) then SPARSITY_BICOLORING(cols_big, rows_big, arrayLength(cols_big), arrayLength(rows_big));
        else SPARSITY_COLORING(cols_big, rows_big);
      end match;
    end combine;
  end SparsityColoring;

protected
  // ToDo: all the DAEMode stuff is probably incorrect!

  function colpackStarBicoloring
    "Calls ColPack's star bicoloring algorithm via external C wrapper.
    Input: CSR sparsity pattern (0-based row pointers and column indices).
    Output: 1-based column and row colors (0 = uncolored by that direction)."
    input Integer nRows;
    input Integer nCols;
    input array<Integer> rowPtr   "CSR row pointers, size nRows+1, 0-based";
    input array<Integer> colIdx   "CSR column indices, size nnz, 0-based";
    output array<Integer> colColors "column colors (1-based; 0 = not column-colored)";
    output Integer nColColors       "number of column colors used";
    output array<Integer> rowColors "row colors (1-based; 0 = not row-colored)";
    output Integer nRowColors       "number of row colors used";
    external "C" ColPackBicoloring_starBicolor(nRows, nCols, rowPtr, colIdx, colColors, nColColors, rowColors, nRowColors) annotation(Library = "omcruntime");
  end colpackStarBicoloring;

  function isRowInJacobian
    "Checks if a cref of the partial derivatives, is an actual row in the sparsity pattern (ODE and OPT-Jacobians). If this is false, its an inner variable."
    input ComponentRef cref;
    input JacobianType jacType;
    output Boolean b;
  algorithm
    b := BVariable.checkCref(cref, BVariable.isResidual, sourceInfo())
           or (BVariable.checkCref(cref, BVariable.isStateDerivative, sourceInfo()) and jacType <> JacobianType.OPT_MRF and jacType <> JacobianType.OPT_R0)
           or (jacType == JacobianType.OPT_LFG and BVariable.checkCref(cref, BVariable.isLfgFunction, sourceInfo()))
           or (jacType == JacobianType.OPT_MRF and BVariable.checkCref(cref, BVariable.isMrfFunction, sourceInfo()))
           or (jacType == JacobianType.OPT_R0 and BVariable.checkCref(cref, BVariable.isInitialConstraint, sourceInfo()));
  end isRowInJacobian;

  function partJacobian
    input output Partition.Partition part;
    input UnorderedMap<Path, Function> funcMap;
    input VariablePointers knowns;
    input String name                                     "Context name for jacobian";
    input Module.jacobianInterface func;
  protected
    JacobianType jacType;
    VariablePointers unknowns;
    list<Pointer<Variable>> derivative_vars, state_vars;
    VariablePointers seedCandidates, partialCandidates;
    Option<Jacobian> jacobian "Resulting jacobian";
    Option<Jacobian> adjointJac;
    Partition.Kind kind = Partition.Partition.getKind(part);
    Boolean updated;
  algorithm
    // create algebraic loop jacobians
    part.strongComponents := match part.strongComponents
      local
        array<StrongComponent> comps;
        StrongComponent tmp;
      case SOME(comps) algorithm
        for i in 1:arrayLength(comps) loop
          (tmp, updated) := compJacobian(comps[i], part.adjacencyMatrix, funcMap, kind);
          if updated then arrayUpdate(comps, i, tmp); end if;
        end for;
      then SOME(comps);
      else part.strongComponents;
    end match;

    // create the simulation jacobian
    if Partition.Partition.isODEorDAE(part) then
      partialCandidates := part.unknowns;
      unknowns  := if Partition.Partition.getKind(part) == NBPartition.Kind.DAE then Util.getOption(part.daeUnknowns) else part.unknowns;
      jacType   := if Partition.Partition.getKind(part) == NBPartition.Kind.DAE then JacobianType.DAE else JacobianType.ODE;

      derivative_vars := list(var for var guard(BVariable.isStateDerivative(var)) in VariablePointers.toList(unknowns));
      state_vars := list(Util.getOption(BVariable.getVarState(var)) for var in derivative_vars);
      seedCandidates := VariablePointers.fromList(state_vars, partialCandidates.scalarized);

      jacobian := func(name, jacType, seedCandidates, partialCandidates, part.equations, part.strongComponents, part.adjacencyMatrix, funcMap, Partition.kindIsInitial(kind));

      if Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN) == "bidirectional" and isSome(jacobian) and not BackendDAE.getIsAdjoint(Util.getOption(jacobian)) then
        // Bidirectional: generate adjoint jacobian in addition to forward
        adjointJac := jacobianSymbolicAdjoint(name, jacType, seedCandidates, partialCandidates, part.equations, part.strongComponents, part.adjacencyMatrix, funcMap, kind == NBPartition.Kind.INI);
        part.association := Partition.Association.CONTINUOUS(kind, jacobian, adjointJac, NONE(), NONE(), NONE());
      elseif isSome(jacobian) then
        if BackendDAE.getIsAdjoint(Util.getOption(jacobian)) then
          part.association := Partition.Association.CONTINUOUS(kind, NONE(), jacobian, NONE(), NONE(), NONE());
        else
          part.association := Partition.Association.CONTINUOUS(kind, jacobian, NONE(), NONE(), NONE(), NONE());
        end if;
      else
        part.association := Partition.Association.CONTINUOUS(kind, NONE(), NONE(), NONE(), NONE(), NONE());
      end if;
      if Flags.isSet(Flags.JAC_DUMP) then
        print(Partition.Partition.toString(part, 2));
      end if;
    end if;
  end partJacobian;

  function compJacobian
    input output StrongComponent comp;
    input Option<Adjacency.Matrix> full;
    input UnorderedMap<Path, Function> funcMap;
    input Partition.Kind kind;
    output Boolean updated;
  protected
    Tearing strict;
    list<StrongComponent> residual_comps;
    list<VariablePointer> seed_candidates, residual_vars, inner_vars;
    constant Boolean staticAsContinuous = Partition.kindIsInitial(kind);
  algorithm
    (comp, updated) := match comp
      case StrongComponent.ALGEBRAIC_LOOP(strict = strict) algorithm
        // create residual components
        residual_comps        := list(StrongComponent.fromSolvedEquationSlice(eqn) for eqn in strict.residual_eqns);

        // create seed and partial candidates
        seed_candidates := list(Slice.getT(var) for var in strict.iteration_vars);
        residual_vars   := list(Equation.getResidualVar(Slice.getT(eqn)) for eqn in strict.residual_eqns);
        inner_vars      := listAppend(list(var for var guard(BVariable.isContinuous(var, staticAsContinuous)) in StrongComponent.getVariables(comp)) for comp in strict.innerEquations);

        // update jacobian to take slices (just to have correct inner variables and such)
        strict.jac := nonlinear(
          seedCandidates     = VariablePointers.fromList(seed_candidates),
          partialCandidates  = VariablePointers.fromList(listAppend(residual_vars, inner_vars)),
          equations          = EquationPointers.fromList(list(Slice.getT(eqn) for eqn in strict.residual_eqns)),
          comps              = Array.appendList(strict.innerEquations, residual_comps),
          full               = full,
          funcMap            = funcMap,
          name               = Partition.Partition.kindToString(kind) + (if comp.linear then "_LS_JAC_" else "_NLS_JAC_") + intString(comp.idx),
          staticAsContinuous = staticAsContinuous);
        comp.strict := strict;

        if Flags.isSet(Flags.JAC_DUMP) then
          print("\n" + StrongComponent.toString(comp) + "\n");
        end if;
      then (comp, true);
      else (comp, false);
    end match;
  end compJacobian;

  function jacobianSymbolic extends Module.jacobianInterface;
  protected
    Pointer<Integer> idx = Pointer.create(0);

    BVariable.VarData varDataJac;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring;

    BVariable.checkVar func = getTmpFilterFunction(jacType);
    list<Pointer<Variable>> row_vars, inner_vars;
    NBProgram.Program primalProgram, program;
    NBProgram.Flat flat;
  algorithm
    (row_vars, inner_vars) := List.splitOnTrue(VariablePointers.toList(partialCandidates), func);

    primalProgram := NBProgram.fromStrongComponents(
      name,
      seedCandidates,
      VariablePointers.fromList(row_vars, partialCandidates.scalarized),
      VariablePointers.fromList(inner_vars, partialCandidates.scalarized),
      strongComponents,
      funcMap,
      staticAsContinuous,
      idx,
      NBProgram.options(
        NBProgram.Allocation.REUSE,
        name,
        name,
        name,
        debugOrigin = getInstanceName())
    );
    program := NBForward.create(primalProgram);
    flat := NBProgram.flatten(program);

    varDataJac := varDataFromFlat(flat, partialCandidates, reverseSeeds = true);

    (sparsityPattern, sparsityColoring) := SparsityPattern.create(seedCandidates, partialCandidates, strongComponents, jacType, staticAsContinuous);

    jacobian := SOME(Jacobian.JACOBIAN(
      name              = name,
      jacType           = jacType,
      varData           = varDataJac,
      comps             = listArray(flat.comps),
      // sparsity
      sparsityPattern   = sparsityPattern,
      sparsityColoring  = sparsityColoring,
      isAdjoint         = false
    ));
  end jacobianSymbolic;

protected
  function varDataFromFlat
    input NBProgram.Flat flat;
    input VariablePointers diffVars;
    input Boolean reverseSeeds = false;
    output BVariable.VarData varData;
  protected
    list<Pointer<Variable>> seedVars;
    list<Pointer<Variable>> variables;
  algorithm
    seedVars := if reverseSeeds then listReverse(flat.seedVars) else flat.seedVars;
    variables := listAppend(flat.unknowns, seedVars);

    varData := BVariable.VAR_DATA_JAC(
      variables     = VariablePointers.fromList(variables),
      unknowns      = VariablePointers.fromList(flat.unknowns),
      auxiliaries   = VariablePointers.fromList(seedVars),
      aliasVars     = VariablePointers.fromList({}),
      diffVars      = diffVars,
      dependencies  = VariablePointers.fromList({}),
      resultVars    = VariablePointers.fromList(flat.resultVars),
      tmpVars       = VariablePointers.fromList(flat.tmpVars),
      seedVars      = VariablePointers.fromList(seedVars)
    );
  end varDataFromFlat;

  function jacobianSymbolicAdjoint extends Module.jacobianInterface;
  protected
    Pointer<Integer> idx = Pointer.create(0);

    BVariable.VarData varDataJac;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring;

    String newName;
    BVariable.checkVar func = getTmpFilterFunction(jacType);
    list<Pointer<Variable>> row_vars, inner_vars;
    NBProgram.Program primalProgram, program;
    NBProgram.Flat flat;
  algorithm
    newName := name + "_ADJ";
    (row_vars, inner_vars) := List.splitOnTrue(VariablePointers.toList(partialCandidates), func);

    primalProgram := NBProgram.fromStrongComponents(
      newName,
      seedCandidates,
      VariablePointers.fromList(row_vars, partialCandidates.scalarized),
      VariablePointers.fromList(inner_vars, partialCandidates.scalarized),
      strongComponents,
      funcMap,
      staticAsContinuous,
      idx,
      NBProgram.options(
        NBProgram.Allocation.REUSE,
        newName,
        newName,
        newName,
        debugOrigin = getInstanceName())
    );
    program := NBAdjoint.create(primalProgram);
    flat := NBProgram.flatten(program);

    varDataJac := varDataFromFlat(flat, partialCandidates);

    (sparsityPattern, sparsityColoring) := SparsityPattern.create(seedCandidates, partialCandidates, strongComponents, jacType, staticAsContinuous);

    if Flags.isSet(Flags.DEBUG_ADJOINT) then
      print("Adjoint sparsity pattern and coloring:\n");
      print(SparsityPattern.toString(sparsityPattern) + "\n" + SparsityColoring.toString(sparsityColoring) + "\n");
    end if;

    jacobian := SOME(Jacobian.JACOBIAN(
      name              = newName,
      jacType           = jacType,
      varData           = varDataJac,
      comps             = listArray(flat.comps),
      sparsityPattern   = sparsityPattern,
      sparsityColoring  = sparsityColoring,
      isAdjoint         = true
    ));
  end jacobianSymbolicAdjoint;

  function jacobianNumeric "still creates sparsity pattern"
    extends Module.jacobianInterface;
  protected
    VarData varDataJac;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring;
    list<Pointer<Variable>> res_vars, tmp_vars;
    BVariable.checkVar func = getTmpFilterFunction(jacType);
  algorithm
    (res_vars, tmp_vars) := List.splitOnTrue(VariablePointers.toList(partialCandidates), func);
    (tmp_vars, _) := List.splitOnTrue(tmp_vars, function BVariable.isContinuous(staticAsContinuous = staticAsContinuous));

    varDataJac := BVariable.VAR_DATA_JAC(
      variables     = VariablePointers.fromList({}),
      unknowns      = partialCandidates,
      auxiliaries   = VariablePointers.fromList({}),
      aliasVars     = VariablePointers.fromList({}),
      diffVars      = VariablePointers.fromList({}),
      dependencies  = VariablePointers.fromList({}),
      resultVars    = VariablePointers.fromList(res_vars),
      tmpVars       = VariablePointers.fromList(tmp_vars),
      seedVars      = seedCandidates
    );

    (sparsityPattern, sparsityColoring) := SparsityPattern.create(seedCandidates, partialCandidates, strongComponents, jacType, staticAsContinuous);

    jacobian := SOME(Jacobian.JACOBIAN(
      name              = name,
      jacType           = jacType,
      varData           = varDataJac,
      comps             = listArray({}),
      sparsityPattern   = sparsityPattern,
      sparsityColoring  = sparsityColoring,
      isAdjoint         = false
    ));
  end jacobianNumeric;

  function jacobianNone
    extends Module.jacobianInterface;
  algorithm
    jacobian := NONE();
  end jacobianNone;

public
  function getTmpFilterFunction
    " - ODE filter by state derivative / algebraic
      - LS/NLS/DAE filter by residual / inner"
    input JacobianType jacType;
    output BVariable.checkVar func;
  algorithm
    func := match jacType
      case JacobianType.ODE     then BVariable.isStateDerivative;
      case JacobianType.DAE     then BVariable.isResidual;
      case JacobianType.LS      then BVariable.isResidual;
      case JacobianType.NLS     then BVariable.isResidual;
      case JacobianType.OPT_LFG then BVariable.isLfgFunction;
      case JacobianType.OPT_MRF then BVariable.isMrfFunction;
      case JacobianType.OPT_R0  then BVariable.isInitialConstraint;
      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because jacobian type is not known: " + jacobianTypeString(jacType)});
      then fail();
    end match;
  end getTmpFilterFunction;

protected
  function getSparsityRowCrefs
    "Returns the actual jacobian row crefs from the partial candidates"
    input VariablePointers partialCandidates;
    input JacobianType jacType;
    input Boolean staticAsContinuous;
    output list<ComponentRef> row_crefs;
  protected
    list<Pointer<Variable>> row_vars;
    BVariable.checkVar func = getTmpFilterFunction(jacType);
  algorithm
    (row_vars, _) := List.splitOnTrue(VariablePointers.toList(partialCandidates), func);
    row_vars := list(var for var guard(BVariable.isContinuous(var, staticAsContinuous)) in row_vars);
    row_crefs := VariablePointers.getScalarVarNames(VariablePointers.fromList(row_vars, partialCandidates.scalarized), false);
  end getSparsityRowCrefs;

  annotation(__OpenModelica_Interface="nbackend");
end NBJacobian;
