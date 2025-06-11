/*
* This file is part of OpenModelica.
*
* Copyright (c) 1998-2021, Open Source Modelica Consortium (OSMC),
* c/o Linköpings universitet, Department of Computer and Information Science,
* SE-58183 Linköping, Sweden.
*
* All rights reserved.
*
* THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
* THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
* ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
* RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
* ACCORDING TO RECIPIENTS CHOICE.
*
* The OpenModelica software and the Open Source Modelica
* Consortium (OSMC) Public License (OSMC-PL) are obtained
* from OSMC, either from the above address,
* from the URLs: http://www.ida.liu.se/projects/OpenModelica or
* http://www.openmodelica.org, and in the OpenModelica distribution.
* GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
*
* This program is distributed WITHOUT ANY WARRANTY; without
* even the implied warranty of  MERCHANTABILITY or FITNESS
* FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
* IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
*
* See the full OSMC Public License conditions for more details.
*
*/
encapsulated package NBOptimization
"file:        NBOptimization.mo
 package:     NBOptimization
 description: This file contains the functions for (optional) dynamic optimization
"

// TODO: add doc

public
  import Module = NBModule;
protected
  // OF imports
  import DAE;

  // NF imports
  import BackendExtension = NFBackendExtension;
  import NFBackendExtension.{StateSelect, TearingSelect};
  import NFBackendExtension.VariableKind;
  import Call = NFCall;
  import ComponentRef = NFComponentRef;
  import Expression = NFExpression;
  import ExpressionIterator = NFExpressionIterator;
  import NFFunction.Function;
  import Type = NFType;
  import Operator = NFOperator;
  import Variable = NFVariable;
  import NFFlatten.FunctionTreeImpl;
  import NFPrefixes.Variability;

  // Backend imports
  import BackendDAE = NBackendDAE;
  import BEquation = NBEquation;
  import BVariable = NBVariable;
  import Causalize = NBCausalize;
  import Differentiate = NBDifferentiate;
  import NBDifferentiate.{DifferentiationType, DifferentiationArguments};
  import NBEquation.{Equation, EquationAttributes, EquationKind, EquationPointers, EqData, Iterator};
  import Replacements = NBReplacements;
  import SimplifyExp = NFSimplifyExp;
  import Solve = NBSolve;
  import NBSolve.Status;
  import StrongComponent = NBStrongComponent;
  import Tearing = NBTearing;
  import NBVariable.{VariablePointers, VariablePointer, VarData};

  // Util imports
  import MetaModelica.Dangerous;
  import StringUtil;
  import UnorderedMap;
  import UnorderedSet;
public

  function main
    "Wrapper function for any optimization function."
    extends Module.wrapper;
  protected
    Module.optimizationInterface func;
  algorithm
    (func) := getModule();

    bdae := match bdae
      local
        VarData varData         "Data containing variable pointers";
        EqData eqData           "Data containing equation pointers";

      case BackendDAE.MAIN(varData = varData, eqData = eqData)
        algorithm
          (varData, eqData) := func(varData, eqData);
          bdae.varData := varData;
          bdae.eqData := eqData;
      then bdae;

      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
      then fail();
    end match;
  end main;

  function getModule
    "Returns the module function that was chosen by the user."
    output Module.optimizationInterface func;
  protected
    String flag = "default";
  algorithm
    func := match flag
      case "default" then optimizationDefault;
      /* ... New optimization modules have to be added here */
      else fail();
    end match;
  end getModule;

protected
  function optimizationDefault
    "TODO: add doc for the module here"
    extends Module.optimizationInterface;
  algorithm
    print("Optimization Entry point\n");
    /* (varData, eqData) := match (varData, eqData) */
  end optimizationDefault;

  annotation(__OpenModelica_Interface="backend");
end NBOptimization;
