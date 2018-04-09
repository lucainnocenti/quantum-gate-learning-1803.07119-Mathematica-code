(* ::Package:: *)

BeginPackage["GateLearning`", {"QM`", "QM`QGates`", "QPauliAlgebra`"}];

Unprotect @@ Names["GateLearning`*"];
ClearAll @@ Names["GateLearning`*"];
ClearAll @@ Names["GateLearning`Private`*"];

All2Body;
AllDiagonalXYZ;
AllDiagonalXZ;
AuxiliaryHam;
GateHam;
nBodyInteractionsList;

Commutator::usage = "Commutator[a, b] computes the commutator between a and b."

ParametrizedHamiltonian::usage = "\
ParametrizedHamiltonian[nQubits, factorsGenerator, symbol] returns, as a QPauliExpr, a general Hamiltonian with the class of interactions specified by factorsGenerator, and a symbolic parameter attached to each Pauli component. The input `symbol` determines the symbol to use for the parameters.
ParametrizedHamiltonian[nQubits, symbol] returns a general Hamiltonian with single- and two-qubit interactions over the given number of qubits.
";
HamPhysical;
ImposeVanishingComponents::usage = "\
ImposeVanishingComponents[expr] extracts all the Pauli components from expr and solves for all of them to be vanishing.";
ImposeVanishingCommutator::usage = "\
ImposeVanishingCommutator[expr1, expr2] finds the parameters that make the two expressions commute with each other.";
ImposeVanishingComponent::usage = "\
ImposeVanishingComponent[expr, component] finds the values of the parameters for which the given Pauli component vanishes, and replaces it back in the original expression.";
selectPhysical;

(*
gateLog;
gateCondition;
*)

Begin["`Private`"];


flatten1[x_] := Flatten[x, 1];

iQPauliExpr = QPauliAlgebra`Private`iQPauliExpr;

Commutator[x_iQPauliExpr, y_iQPauliExpr] := Plus[
  QPauliTimes[x, y], -QPauliTimes[y, x]
];
Commutator[x_? MatrixQ, y_? MatrixQ] := x.y - y.x;

(* indicesDiagonalOps

    Return list of indices denoting diagonal interactions.

    Parameters
    ----------
    numQubits: length of each output list.
    numOps: number of nonzero elements in each list.
    directions: for which diretion compute the outputs (if directions == {1}
      then only lists correponsing to XX interactions will be returned).

    Examples
    --------
    In[] := indicesDiagonalOps[3, 2, {1, 2}]
    Out[] = {{1, 1, 0}, {1, 0, 1}, {0, 1, 1}, {2, 2, 0}, {2, 0, 2}, {0, 2, 2}}
*)
indicesDiagonalOps[numQubits_Integer, numOps_Integer, directions_List] := Map[
  Permutations,
  Normal @ SparseArray[
    Thread[Range @ numOps -> #],
    numQubits
  ] & /@ directions
] // flatten1;


(* Returns list of n-body interaction directions. For example for pairwise
   interactions, `nBody = 2` and the output is
   {{1, 1}, {1, 2}, {1, 3}, {2, 1}, {2, 2},
    {2, 3}, {3, 1}, {3, 2}, {3, 3}}
*)
nBodyInteractionsDirections[nBody_Integer] := Tuples @ (
  ConstantArray[#, nBody] & @ Range @ 3
);


qubitTuples[nQubits_Integer, nQubitsInInteractions_Integer] := Subsets[
  Range @ nQubits, {nQubitsInInteractions}
];


(* Return the list of all possible interaction between n bodies, in a qubit
   network with `nQubits` nodes. Each element of the output list is a list of
   `nQubits` integers, describing a specific product of Pauli matrices.
   For example the output {1, 1, 0} corresponds to X[1] X[2]. *)
nBodyInteractionsList[nQubits_Integer, nBodiesPerInteraction_Integer] := With[
  {
    interactionTypes = nBodyInteractionsDirections @ nBodiesPerInteraction,
    couplings = qubitTuples[nQubits, nBodiesPerInteraction]
  },
  Map[
    ReplacePart[
      ConstantArray[0, nQubits],
      Thread[Rule @@ #]
    ] &,
    Tuples @ {couplings, interactionTypes}
  ]
];


(* Returns the list of self- and pair-wise interactions in a qubit network With
   `numQubits` nodes. *)
pairwiseInteractionsList[numQubits_Integer] := Join[
  nBodyInteractionsList[numQubits, 1],
  nBodyInteractionsList[numQubits, 2]
];
All2Body = pairwiseInteractionsList;


(* Return list of all self-interactions and diagonal pairwise interactions.

   Options
   -------
   whichInteractions : List
     List of integers, specifying which diagonal interactions to keep (X, Y,  or Z)
*)
diagonalPairwiseInteractions[
  numQubits_Integer, whichInteractions_List : {1, 2, 3}
] := Join[
  indicesDiagonalOps[numQubits, 1, Range @ 3],
  indicesDiagonalOps[numQubits, 2, whichInteractions]
];


AllDiagonalXYZ[numQubits_Integer] := diagonalPairwiseInteractions[numQubits, {1, 2, 3}];
AllDiagonalXZ[numQubits_Integer] := diagonalPairwiseInteractions[numQubits, {1, 3}];


(* Return parametrized product of the specified list of pauli products.
   This can be used for example to generate the generic 2-qubit interactions
   Hamiltonian.
*)

parametrizedPauliProductsSum[
  factors_List, parameter_Symbol : Global`\[CapitalXi]
] := Total @ Apply[parameter[##] PauliProduct[##] &, factors, {1}];


(*  Return a general Hamiltonian over `numQubits` qubits, with the class of
    interactions specified by `factorsGenerator`, and a symbolic parameter
    attached to each Pauli component.

    Parameters
    ----------
    numQubits : Integer,
      Number of qubits in the generated Hamiltonian.
    factorsGenerator : function, optional
      If given, it must be a function taking a single integer argument, and
      returning a corresponding list of Pauli indices.
      If omitted, the returned generator contains all possible single- and
      two-qubit interactions.
    parameter : Symbol, optional
      The symbol used for the parameters in the output Hamiltonian. If omitted
      it defaults to Global`\[CapitalXi]`.

    Examples
    --------
    In[] := ParametrizedHamiltonian[3, AllDiagonalXYZ]
    Out[] = (... Hamiltonian with all possible diagonal single- and two- qubit
                 interactions ...)
*)

Options[ParametrizedHamiltonian] = {"ParameterSymbol" -> Global`\[CapitalXi]};
ParametrizedHamiltonian[
  numQubits_Integer, factorsGenerator_, OptionsPattern[]
] := PauliBasis @ parametrizedPauliProductsSum[
  Join[factorsGenerator @ numQubits, {ConstantArray[0, numQubits]}],
  OptionValue @ "ParameterSymbol"
];


(* Old version, now using ParametrizedHamiltonian *)
HamPhysical[numQubits_Integer, parameter_Symbol, opsToKeep_] := Total[
  parameter[##] PauliProduct[##] & @@@ Join[
    opsToKeep @ numQubits,
    {ConstantArray[0, numQubits]}
  ]
] // PauliBasis;


pauliIndexPatt = {__Integer};

pauliComponent[matrix_ ? MatrixQ, component : pauliIndexPatt] := Tr @ Dot[
  matrix, PauliProduct @@ component
] / 2 ^ NumberOfQubits @ matrix;

pauliComponent[expr_iQPauliExpr, component : pauliIndexPatt] := pauliComponent[
  Normal @ expr, component
];


pauliComponents[expr_, components : {pauliIndexPatt..}] := Table[
  pauliComponent[expr, component],
  {component, components}
];

pauliComponents[expr_] := With[{
    numQubits = NumberOfQubits @ expr
  },
  With[{
      allInteractions = Tuples @ ConstantArray[#, numQubits] & @ Range[0, 3]
    },
    pauliComponents[expr, allInteractions]
  ]
];


pauliComponentProjection[matrix_ ? MatrixQ, component : pauliIndexPatt] := Times[
  pauliComponent[matrix, component],
  PauliProduct @@ component
];
pauliComponentProjection[matrix_ ? MatrixQ, components : {pauliIndexPatt..}] := Sum[
  pauliComponentProjection[matrix, component],
  {component, components}
];
pauliComponentProjection[expr_iQPauliExpr, components_] := pauliComponentProjection[
  Normal @ expr, components
] // PauliBasis;


(*
    Select a subset of the interactions in the input expression.

    Inputs
    ------
    `expr`: Expression containing parametrised interactions.
        Can be in the form of a matrix, or an `iQPauliExpr`.
    `factorsGenerator`: A function returning a list of interaction indices.
        A few examples of such function are `All2Body` or `AllDiagonalXZ`.
*)
selectPhysical[expr_, factorsGenerator_] := pauliComponentProjection[
  expr, factorsGenerator @ NumberOfQubits @ expr
];


(*  Assuming that expr is a parametrized expression, compute the parameters
    making the expression vanish. More specifically, impose that every Pauli
    component is zero and solve for the parameters.
*)
ImposeVanishingComponents[
  expr : (_iQPauliExpr | _?MatrixQ), parameters_List
] := With[{
    components = DeleteCases[0] @ Simplify @ pauliComponents @ expr
  },
  NSolve[Thread[components == 0], parameters]
];

ImposeVanishingComponents[expr_iQPauliExpr] := ImposeVanishingComponents[
  expr, Variables @ Normal @ expr
];

ImposeVanishingComponents[expr_? MatrixQ] := ImposeVanishingComponents[
  expr, Variables @ expr
];


ImposeVanishingCommutator[expr_iQPauliExpr, otherExpr_iQPauliExpr] := (
  ImposeVanishingComponents @ Commutator[expr, otherExpr]
);


ImposeVanishingComponent[expr_iQPauliExpr, component : pauliIndexPatt] := Module[
  {componentCoeff, solution},
  componentCoeff = pauliComponent[expr, component];
  If[Not @ TrueQ[Chop @ componentCoeff == 0],
    solution = First @ NSolve[componentCoeff, Variables @ componentCoeff];
    expr /. solution,
    (* otherwise just return the expression unchanged *)
    expr
  ]
];

ImposeVanishingComponent[expr_iQPauliExpr, components : {pauliIndexPatt..}] := Fold[
  ImposeVanishingComponent[#1, #2] &,
  expr, components
];


(* indexToLetter
    Small utility function to convert from integer to letter notation for the
    different interaction types (converts 1 into "X" and so on).
*)
indexToLetter[int_Integer] := int /. {1 -> "X", 2 -> "Y", 3 -> "Z"};
indexToLetter[{ints__Integer}] := indexToLetter /@ {ints};

(* toHJNotation
    Converts from Xi[0, 1, 2] notation to J_{23}^{XY}.
*)
toHJNotation[
  _[args__],
  twoQubitSymbol_ : Global`\[ScriptCapitalJ],
  oneQubitSymbol_ : Global`\[ScriptH]
] := Which[
  (* If a constant term.. *)
  Length @ Flatten @ DeleteCases[{args}, 0] == 0,
  Subscript[oneQubitSymbol, 0],
  (* If a one-qubit interaction.. *)
  Length @ Flatten @ DeleteCases[{args}, 0] == 1,
  Subsuperscript[
    oneQubitSymbol,
    Position[{args}, _?(# != 0 &)][[1, 1]],
    DeleteCases[{args}, 0][[1]] // indexToLetter
  ],
  (* If two-qubit interaction.. *)
  Length @ Flatten @ DeleteCases[{args}, 0] == 2,
  Subsuperscript[
    twoQubitSymbol,
    Row @ Flatten @ Position[{args}, _?(# != 0 &)],
    DeleteCases[{args}, 0] // indexToLetter // Row
  ]
];
toHJNotation[args__Integer, otherargs___] := toHJNotation[{args}, otherargs];


(* gateLog
    Mostly here for backward compatibility reasons. It expects an `iQPauliExpr`
    as input. It's probably better to just use `PauliBasisLog` instead of this.
*)
gateLog[gateMatrix_] := PauliBasisLog @ Normal @ gateMatrix;
gateLog[G_, Null]:= PauliBasisLog @ Normal @ G;
gateLog[G_, P_] := PauliBasis @ KroneckerProduct[
  -I MatrixLog @ Normal @ G // Chop,
  Normal @ P
];


gateCondition[gate_, H2p_, factorsGenerator_, P_] := Module[
  {H, Hphys, Hunphys, HH, Hg, HG, n},
  (* Compute the principal logarithm *)
  H = gateLog[gate, P];
  (* Extract from that only the physical components and store them in `Hphys` *)
  Hphys = selectPhysical[H, factorsGenerator] // Chop;
  (* Extract all the other interactions and store them in `Hunphys` *)
  n = Length @ Normal @ H;
  Hunphys = H - Hphys - Tr[Normal @ H] / n;
  Hg = H2p - Hunphys;
  HG = Normal[Hg];
  HH = Normal[H + Hg] - HG // Simplify;

  {
    Variables @ Normal @ H2p,
    Hg,
    Select[Flatten[HH.HG - HG.HH] // Chop, # =!= 0&]
  }
];


simplifyNames[s_, op_] := MapIndexed[
  #1 -> ToExpression[ToString @ s <> ToString @ First[#2 - 1]]&,
  op
];


AuxiliaryHam[
  gate_, numQubits_Integer, symb_Symbol,
  idx_ : All2Body, P_ : Null
] := Module[{Ham, cond, Hsol, var},
  {var, Ham, cond} = gateCondition[
    gate,
    HamPhysical[numQubits, symb, idx],
    idx,
    P
  ];
  Hsol = Ham /. First @ Solve[Thread[cond == 0], var] // Quiet // Chop;
  Hsol /. simplifyNames[symb, var]
];


GateHam[G_, n_, s_, idx_ : All2Body, P_ : Null] := QPauliAlgebra`QPauliExprCollect[
  AuxiliaryHam[G, n, s, idx, P] + gateLog[G, P] // Chop
];


(* Protect all package symbols *)
With[{syms = Names["GateLearning`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[];
EndPackage[];
