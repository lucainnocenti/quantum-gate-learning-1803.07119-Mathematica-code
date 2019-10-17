(* ::Package:: *)

BeginPackage["QPauliAlgebra`", {"QM`", "QM`QGates`"}];

Unprotect @@ Names["QPauliAlgebra`*"];
ClearAll @@ Names["QPauliAlgebra`*"];
ClearAll @@ Names["QPauliAlgebra`Private`*"];

QPauliExpr;
QPauliExprToRegularExpr;
QPauliTimes;
QPauliExprCollect;
QPauliExprGetCoefficient;
QPauliOpsList;
PauliBasis;
PauliBasisLog;
$QPauliExprPrettyPrint;

NumberOfQubits::usage = "Returns the number of qubits in an expression.";

Begin["`Private`"];


(* Bunch of aliases to ease writing ScriptCapital expressions *)
sc1 = \[ScriptOne];
scX = \[ScriptCapitalX];
scY = \[ScriptCapitalY];
scZ = \[ScriptCapitalZ];
gsc1 = Global`\[ScriptOne];
gscX = Global`\[ScriptCapitalX];
gscY = Global`\[ScriptCapitalY];
gscZ = Global`\[ScriptCapitalZ];


(* Look for pauliOps[stuff] expressions in a QPauliExpr object, return the max
   index found in such expressions (if found) *)
extractMaxQubitIndex[expr_] := If[# > 0, #, 1] &[
  Cases[expr, pauliOps[s__] :> s, All] // DeleteCases @ sc1 //
    Map @ First // Max
];


NumberOfQubits[expr_iQPauliExpr] := extractMaxQubitIndex @ expr;
NumberOfQubits[matrix_ ? MatrixQ] := Log[2, Length @ matrix];


iQPauliExpr::wrongNumQubits = "\
The value given to numQubits is not valid.";

iQPauliExpr[_?PossibleZeroQ] := 0;

(* ------------------------
   Upvalues for iQPauliExpr
   ------------------------ *)

iQPauliExpr /:
Normal[iQPauliExpr[expr_]] := With[{
    numQubits = extractMaxQubitIndex @ expr
  },
  Normal[iQPauliExpr @ expr, numQubits]
];


iQPauliExpr /:
Normal[iQPauliExpr[expr_], numQubits_Integer] := If[
  numQubits < extractMaxQubitIndex @ expr,
  Message[iQPauliExpr::wrongNumQubits]; Abort[],
  expr /. pauliOps[s__] :> Dot @@ pauliOps /@ {s} /.
  {
    (* Replace pauliOps[\[ScriptCapitalX][1]] and similar expressions with the
       corresponding matrices *)
    pauliOps[s_[n_]] :> QOneQubitGate[numQubits, n,
      PauliMatrix[s /. Thread[{scX, scY, scZ} -> Range @ 3]]
    ],
    pauliOps[sc1] :> IdentityMatrix[2 ^ numQubits]
  } /. Row@{s__} :> Dot@s
];


iQPauliExpr /:
QPauliExpr[
  iQPauliExpr[expr___]
] := iQPauliExpr[expr];


(* The product of iQPauliExpr expressions is handled by QPauliTimes *)
iQPauliExpr /:
Times[left___, middle_iQPauliExpr, right___] := QPauliTimes[
  left, middle, right
];


iQPauliExpr /:
Plus[
  iQPauliExpr[left_], iQPauliExpr[right_]
] := iQPauliExpr[left + right];


iQPauliExpr /:
Plus[
  iQPauliExpr[left_], right__
] := iQPauliExpr @ left + QPauliExpr @ right;


(* $QPauliExprPrettyPrint is a switch that determines whether to
   pretty print iQPauliExpr expressions. If True, the pauliOps
   expressions are highlighted for better visibility *)
$QPauliExprPrettyPrint = True;


basicStyle[color_] := Function[op,
  Style[op /. symb_Symbol :> SymbolName @ symb, color, Bold, Larger]
];

stylePauliOpsExprs[expr_] := expr /. {
  pauliOps[s__] /; Length @ {s} == 1 :> Row[basicStyle[Blue] /@ {s}],
  pauliOps[s__] /; Length @ {s} == 2 :> Row[basicStyle[Green] /@ {s}],
  pauliOps[s__] /; Length @ {s} == 3 :> Row[basicStyle[Red] /@ {s}],
  pauliOps[s__] /; Length @ {s} > 3 :> Row[basicStyle[Purple] /@ {s}]
};


(* Define how `iQPauliExpr` expressions should be converted to boxes *)
iQPauliExpr /:
MakeBoxes[
  iQPauliExpr[
    (* We only want the MakeBoxes to trigger if there actually is some pauliOps
       in the input expression *)
    expr_ /; FirstCase[expr, _pauliOps, None, All] =!= None
  ],
  StandardForm | TraditionalForm
] := If[
  TrueQ @ $QPauliExprPrettyPrint,
  ToBoxes @ Interpretation[
    stylePauliOpsExprs @ expr,
    iQPauliExpr @ expr
  ],
  ToBoxes @ iQPauliExpr[expr]
];


(*pauliOps /: MakeBoxes[pauliOps[s__], _] := ToBoxes @ Interpretation[
  Times @@ (
    {s} /. symb_Symbol /; (Context @ symb != "System`") :> SymbolName @ symb
  ),
  pauliOps[s]
];*)


(* -------------------------------------------------------------
   Conversion from natural form expression to iQPauliExpr object
   ------------------------------------------------------------- *)


pauliSymbolPattern = Alternatives[
  x, scX, Global`x,
  y, scY, Global`y,
  z, scZ, Global`z
][_Integer];

pauliSymbolQ = MatchQ[#, pauliSymbolPattern] &;

easyToNiceSymbolsRules = {
  x -> scX, Global`x -> scX,
  y -> scY, Global`y -> scY,
  z -> scZ, Global`z -> scZ
};


(* Sort the content of every pauliOps expression. For example,
   pauliOps[x[2], y[1]] is converted into pauliOps[y[1], x[2]] *)
sortPauliOps[expr_] := If[Length @ expr > 1,
  expr /. pauliOps[args__] :> pauliOps[Sequence @@ SortBy[{args}, First]],
  expr
];


replaceXYZWithPauliOps[expr_] := expr /. {
  s : pauliSymbolPattern :> pauliOps[
    s /. easyToNiceSymbolsRules
  ]
};

mergePauliOpsFactors[expr_, wrapper_ : times] := expr //. {
  wrapper[ops : (pauliOps[__]..)] :> pauliOps[
    Sequence @@ (First /@ {ops})
  ]
};


(* Replace expressions of the form pauliOps[x[1]] + 3 with
   pauliOps[x[1]] + 3 * pauliOps[\[ScriptOne]] *)
putIdentityOpOnScalars[expr_] := Which[
  Head @ expr === Plus,
  putIdentityOpOnScalars /@ expr,
  Cases[expr, _pauliOps, {0, 2}] == {},
  expr * pauliOps[sc1],
  True,
  expr
];


(*Attributes @ QPauliExpr = HoldAll;*)

QPauliExpr[expr_ ? (NumericQ @ # &)] := iQPauliExpr[expr * pauliOps[sc1]];

(* If `expr` is already an `iQPauliExpr` expression, nothing happens *)
QPauliExpr[expr_] /; MatchQ[expr, _iQPauliExpr] := expr;

(* Otherwise, if not `pauliOps` objects are detected, proceed with expansion of
   the expression, replacing of x[i] with \[ScriptCapitalX][i] etc., and
   put \[ScriptOne] on scalar expression. The result is then wrapped with
   iQPauliExpr. *)
QPauliExpr[expr_] := With[{
    correctedExpr = If[# === Missing, expr,
      expr /. {gscX -> Global`x, gscY -> Global`y, gscZ -> Global`z}
    ] & @ FirstCase[expr, (gscX | gscY | gscZ)[__], Missing, {0, Infinity}]
  },
  iQPauliExpr[
    putIdentityOpOnScalars @ sortPauliOps @
    (# /. s_pauliOps :> pauliOpsProduct[s] &) @
    mergePauliOpsFactors @ replaceXYZWithPauliOps @
    symbolicNonCommutativeProduct[correctedExpr,
      "ScalarsPattern" -> Except[pauliSymbolPattern],
      "NonCommutativeProductWrapper" -> times
    ]
  ]
];


QPauliExprToRegularExpr[expr_iQPauliExpr] := First @ expr /. {
  pauliOps[s__] :> Times @ s
} /. {
  sc1 -> 1,
  s_Symbol /; Context @ s == "QPauliAlgebra`Private`" :> (
    ToExpression["Global`" <> SymbolName @ s]
  )
};


(* ----------------------------------------------------------------
   Implementation of noncommutative product and Pauli algebra rules
   ---------------------------------------------------------------- *)


Attributes[makeAdditionalOperatorRules] = HoldAll;
makeAdditionalOperatorRules[args_List] := Block[{eqs, lhs, rhs, symbNCP},
  eqs = Sequence @@ Map[Hold, Hold @ args, {2}] // Evaluate;
  symbNCP = Function[Null,
    symbolicNonCommutativeProduct[#, "NonCommutativeProductWrapper" -> times],
    HoldAll
  ];
  Table[
    lhs = eq[[{1}, 1]] /. Hold[s__] :> symbNCP @ s;
    lhs = With[{lhsToInject = Sequence @@ lhs},
      eq[[{1}, 1]] /.
        Hold[__] :> Hold[times[left___, lhsToInject, right___]]
    ];

    rhs = eq[[{1}, 2]] /. Hold[s__] :> symbNCP @ s;
    rhs = With[{rhsToInject = rhs},
      eq[[{1}, 1]] /.
        Hold[__] :> Hold[times[left, rhsToInject, right]]
    ];
    (* output *)
    {lhs, rhs} /. {Hold[left__], Hold[right__]} :> (left :> right),
    (* iterators *)
    {eq, eqs}
  ]
];

makeAdditionalOperatorRules[Hold[args__]] :=
  makeAdditionalOperatorRules @ {args};


Attributes @ replaceTimesTotimes = HoldAll;
replaceTimesTotimes[expr_] := ReleaseHold[
  Hold[expr] /. {
    Times -> times,
    Power[s_, n_Integer /; n > 0] :> times @@ ConstantArray[s, n]
  }
];


Attributes @ distributeTimes = HoldAll;
distributetimes[expr_] := ReplaceAll[expr,
  times[s__] :> Distribute[times[s]]
];


symbolicNonCommutativeProduct::usage = "symbolicNonCommutativeProduct[expr] \
evaluates the input expression without assuming that the symbols commute. By \
default all (and only) the numerical values are treated as scalars, and all \
the symbols as non-commuting operators. The options \"Scalars\" and \"Additio\
nalOperatorRules\" can be used to override this assumption.";

Attributes[symbolicNonCommutativeProduct] = HoldAll;
Options[symbolicNonCommutativeProduct] = {
  "Scalars" -> {},
  "ScalarsPattern" -> None,
  "AdditionalOperatorRules" -> {},
  "NonCommutativeProductWrapper" -> NonCommutativeMultiply
};
symbolicNonCommutativeProduct[expr_, OptionsPattern[]] := With[{
    (* For starters, all `Times` expressions are replaced with a temporary
       wrapper `times`. This is necessary because `Times` assumes
       commutativity of the expressions, hence automatically reordering symbols
       around. Expressions of the form `x^n` are also converted to
       `times[x, x, ..., x]` for consistency. *)
    exprNC = replaceTimesTotimes[expr],
    (* If the option "ScalarsPattern" is provided, its content (and nothing
       else) is used to determine what should be considered a scalar (that is,
       not a noncommuting operator).
       Otherwise, it is assumed that all numeric symbols, plus any element
       given with the option "Scalars", are to be considered scalars.*)
    scalar = If[OptionValue @ "ScalarsPattern" =!= None,
      OptionValue @ "ScalarsPattern",
      _ ? (NumericQ @ # || MemberQ[OptionValue @ "Scalars", #] &)
    ],
    customRules = If[
      MatchQ[OptionValue @ "AdditionalOperatorRules", _Hold],
      makeAdditionalOperatorRules @
        Evaluate @ OptionValue @ "AdditionalOperatorRules",
      (* else.. *)
      {}
    ]
  },
  exprNC //. {
    (* Distribute times over Plus *)
    times[left___, HoldPattern @ Plus[middle__], right___] :> (
      Plus @@ (times[left, #, right] & /@ {middle})
    ),

    (* Take scalars out of sum *)
    times[left___, (a : scalar) * middle___, right___] :>
      a times[left, middle, right],
    times[left___, a : scalar /; Head @ a =!= times, right___] :> Times[
      a,
      times[left, right]
    ],

    (* Simulate Flat and OneIdentity properties (kind of) *)
    times[s : (_Symbol | _?NumericQ | _times)] :> s,
    times[left___, times[middle___], right___] :> times[left, middle, right],
    times[] :> 1,

    (* Apply additional rules if specified *)
    Sequence @@ customRules
  } /. times -> OptionValue @ "NonCommutativeProductWrapper"
];


(* `pauliOpsProduct` is where the rules of the Pauli algebra are actually
   implemented.
   It can take as input  either a number of `pauliOps` inputs, or directly
   a sequence of sc1, scX, scY, scZ objects. If gives as output (in symbolic
   form) the product of the corresponding pauli operators.*)

pauliOpsProduct[ops : (pauliOps[__])..] := pauliOpsProduct[
  Sequence @@ Sequence @@@ {ops}
];

pauliOpsProduct[pauliOps[ops__]] := pauliOpsProduct[ops];

pauliOpsProduct[ops__] := Module[
  {terms, coeff = 1},
  terms = {ops};
  terms = terms //. {
    {left___, sc1, right___} :> {left, right},
    {left___, s_[n_], s_[n_], right___} :> {left, right},

    {left___, scX[n_], scY[n_], right___} :> (
      coeff *= I;
      {left, scZ[n], right}
    ),
    {left___, scY[n_], scZ[n_], right___} :> (
      coeff *= I;
      {left, scX[n], right}
    ),
    {left___, scX[n_], scZ[n_], right___} :> (
      coeff *= -I;
      {left, scY[n], right}
    ),
    (* Sort by qubit numbers *)
    {left___, s_[n_], ss_[m_], right___} /; n > m :> {
      left, ss[m], s[n], right
    },
    (* Sort by lexicographical order (taking commutation properties into account) *)
    {left___, s_[n_], ss_[n_], right___} /;
      Not @ OrderedQ @ {s, ss} :> (
        coeff *= -1;
        {left, ss[n], s[n], right}
      )
  };

  If[Length @ terms > 0,
    coeff * pauliOps @@ terms,
    coeff * pauliOps @ sc1
  ]
];


QPauliTimes[left_, middle_, right__] := QPauliTimes[left, QPauliTimes[middle, right]];

QPauliTimes[leftExpr_iQPauliExpr, rightExpr_iQPauliExpr] := iQPauliExpr[
  symbolicNonCommutativeProduct[
    Times[First @ leftExpr, First @ rightExpr],
    "ScalarsPattern" -> Except[pauliOps[__]],
    "NonCommutativeProductWrapper" -> pauliOpsProduct
  ]
];

QPauliTimes[left_, right_iQPauliExpr] := QPauliTimes[QPauliExpr @ left, right];

QPauliTimes[left_iQPauliExpr, right_] := QPauliTimes[left, QPauliExpr @ right];

QPauliTimes[left_, right_] := Times[left, right];



(* ------------------------------------------------
   Conversion from matrices to Pauli representation
   ------------------------------------------------ *)


pauliLabels = {sc1, scX, scY, scZ};


(* Take a sequence of indices and give the corresponding product of Pauli
   operators, in symbolic form.
   Example:
   In[1] := pauliNames[1, 3]
   Out[1] = x[1] z[2] *)
pauliNames[indices__] := Times @@ MapIndexed[
  pauliLabels[[#1 + 1]][First @ #2] &,
  {indices}
];


(* `indices` is here used to denote what (product of) pauli matrices is requested,
   use  for example {1, 1} to ask for the X1X2 component.
*)
matrixPauliComponent[matrix_, {indices__}] := Tr[
  Dot[matrix, PauliProduct @ indices]
];

numberOfQubits[gateMatrix_?MatrixQ] := Log[2, Length @ gateMatrix];


(* Convert a matrix into its representation in terms of Pauli operators. *)
PauliBasis[matrix_] /; And[
  SameQ @@ Dimensions @ matrix,
  IntegerQ @ numberOfQubits @ matrix
] := QPauliExpr @ Evaluate @ With[
  {dim = numberOfQubits @ matrix},
  Chop @ Expand @ Times[
    1 / 2 ^ dim,
    Total @ Flatten @ Outer[
      pauliNames @ ## * matrixPauliComponent[matrix, {##}] &,
      Sequence @@ ConstantArray[Range[0, 3], dim]
    ]
  ] /. sc1[_] -> 1
];


(* Decompose with Pauli operatrs the logarithm of the input matrix *)
PauliBasisLog[matrix_] := PauliBasis[-I * MatrixLog @ matrix];


(* -----------------------------------------------
   Collect `pauliOps` in `iQPauliExpr` expressions
   ----------------------------------------------- *)


QPauliOpsList[numQubits_Integer] := Flatten @ Outer[pauliNames,
  Sequence @@ ConstantArray[Range[0, 3], numQubits]
] // # /. sc1[_] -> 1 & // Map[QPauliExpr] // Sort;

QPauliOpsList[expr_iQPauliExpr] := QPauliOpsList[
  expr, extractMaxQubitIndex @ expr
];


allPauliOps[expr_iQPauliExpr] := Join @@ (
  (# /@ Range @ extractMaxQubitIndex @ expr &) /@ {scX, scY, scZ}
);


iQPauliExprCoefficientRules[expr_iQPauliExpr] := With[{
    inner = First @ expr
  },
  CoefficientRules[
    inner /. {pauliOps[sc1] -> 1, pauliOps[s__] :> Times[s]},
    allPauliOps @ expr
  ]
];
(*iQPauliExprCoefficientRules[expr_iQPauliExpr] := Cases[expr,
  coeff_. * pauliOps[s__] :> Sow[{coeff, {s}}],
  {0, 3}
] // Reap // Last // First //
     GroupBy[#, Last] & //
     Map[First, #, {2}] & //
     Apply[Plus, #, {1}] &;*)


QPauliExprCollect[expr_iQPauliExpr, func_ : Simplify] := (
  (* Extract coefficients in a CoefficientRules-like fashion *)
  iQPauliExprCoefficientRules[expr] // Association //
  (* Apply function to each cofficient (usually to simplify them), then wrap
     each of them with Hold to prevent them from being automatically processed
     by other stuff *)
  Map @ func // Map @ wrap // Normal //
  (* Convert back to sum structure *)
  FromCoefficientRules[#, allPauliOps @ expr] & //
  (* We need Evaluate here because QPauliExpr is HoldAll *)
  Evaluate // QPauliExpr //
  (* Finally, remove the Hold wrapper from the coefficients *)
  # /. wrap[s_] :> s &
);


(*QPauliExprGetCoefficient[expr_iQPauliExpr, term_] := With[{
    niceTerm = term /. {Global`x -> scX, Global`y -> scY, Global`z -> scZ},
    cleanedExpr = First @ expr /. pauliOps[s__] -> Times @@ s
  },
  D[cleanedExpr, niceTerm /. Times -> Sequence]
];*)
QPauliExprGetCoefficient[expr_iQPauliExpr, term_] := With[{
    dim = extractMaxQubitIndex @ expr
  },
  Tr @ Dot[
    Normal @ expr,
    Normal[QPauliExpr @ term, dim]
  ] / 2^dim // Simplify
];


(* Protect all package symbols *)
With[{syms = Names["QPauliAlgebra`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[];
EndPackage[];
