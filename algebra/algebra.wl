(* ::Package:: *)

(* ::Section:: *)
(*Begin*)


BeginPackage["lily`algebra`",{"lily`class`"}];
(*delete the class before clearing all symbols.*)
classUnset["algebra"]//Quiet;
Unprotect@@Names[$Context<>"*"];
ClearAll@@Names[$Context<>"*"];


(* ::Subsection:: *)
(*lily`list`*)


{
    classData,classDefine,classProtect,classUnset,
    instancePreIntercept,instancePostIntercept,
    instanceDefaultData,instanceDefault,
    instanceDefine,instanceReset,instanceUnset,
    instanceAdd,instanceDelete
};


(* ::Subsection:: *)
(*Class algebra*)


algebraDefine::usage = 
    "define and initiate algebras.";
algebraDefineQ::usage = 
    "check whether an algebra is defined.";
algebraDefineInternal::usage = 
    "define the internal algebras.";

algebraDefault::usage = 
    "set default algebras to build the compounded algebra.";

algebraReset::usage = 
    "reset the algebras.";
algebraUnset::usage = 
    "unset the algebras.";

algebraAdd::usage = 
    "add to the algebras.";
algebraDelete::usage = 
    "delete from the algebras.";

algebraShow::usage = 
    "show the algebra.";

operator::usage = 
    "return the operators/generators.";
relation::usage = 
    "return the rules of multiplication table.";
printing::usage = 
    "return the formatting rules.";


(* ::Subsection:: *)
(*Kernel functions*)


algebraSimplify::usage = 
    "simplify the expression by the default algebra.";
algebraPrint::usage = 
    "format the expression by the default algebra.";
algebraEquation::usage = 
    "return a formatted equation with the input at RHS and the simplified one at LHS.";
    
scalarQ::usage =
    "check whether the expression is C-number by the default algebra.";
operatorQ::usage =
    "check whether the expression is Q-number by the default algebra.";
generatorQ::usage =
    "check whether the symbol is a generator the default algebra.";    


(* ::Subsection:: *)
(*Shortcuts*)


algS::usage = 
    "algebraSimplify.";
algP::usage = 
    "algebraPrint.";
algSP::usage =
    "algebraSimplify + algebraPrint.";
algSS::usage =
    "algebraSimplify + FullSimplify.";
algSSP::usage =
    "algebraSimplify + FullSimplify + algebraPrint.";
algE::usage =
    "algebraEquation.";
algES::usage =
    "algebraEquation + FullSimplify.";
algEqualQ::usage =
    "x==y for Q-numbers.";
algSameQ::usage =
    "x==y for Q-numbers.";


(* ::Subsection:: *)
(*Commutator, adjoint and power*)


comm::usage = 
    "commutator.";
anticomm::usage = 
    "anti-commutator.";    
jacobiIdentity::usage =
    "the Jacobi identity.";
commSim::usage = 
    "simplify the commutator.";
anticommSim::usage = 
    "simplify the anti-commutator.";

commDefine::usage = 
    "define commutation relations.";

adjoint::usage = 
    "the adjoint action of Lie algebra, ad^order_op expr."
adjointExp::usage = 
    "the adjoint action of Lie group upto the max order, Exp[para op] expr Exp[-para op].";

operatorPower::usage = 
    "power of operators, op^order.";
operatorExp::usage = 
    "exponential of operators upto the max order, Exp[para op].";


(* ::Subsection:: *)
(*Inner product*)


innerProduct::usage =
    "inner product of two vectors, A \[CircleTimes] A -> k.";


(* ::Subsection:: *)
(*Tensor product*)


id::usage = 
    "identity of tensor product.";
tensorRankSet::usage =
    "set the tensor rank of generators with respect to tensor product.";
tensorRank::usage =
    "calculate the tensor rank of operators.";
tensorThread::usage = 
    "composite tensors over multiplication according to tensorRank.";    


(* ::Subsection:: *)
(*Scalar extraction*)


scalarSeparate::usage =
    "separate scalars and operators.";
scalarExtract::usage =
    "extract scalars.";


(* ::Subsection:: *)
(*Begin private*)


Begin["`Private`"];


(* ::Section:: *)
(*Private*)


(* ::Subsection:: *)
(*lily`base`*)


lengthEqualQ[lists___] :=
    Equal@@Map[Length,{lists}];

pink[expr_] :=
    Style[expr,RGBColor[1,0.5,0.5]];
violet[expr_] :=
    Style[expr,RGBColor[0.5,0.5,1]];
orange[expr_] :=
    Style[expr,RGBColor[1,0.5,0]];

stripPattern[pattern_] :=
    pattern//.{
        (
            Verbatim[Pattern]|Verbatim[Optional]|
                Verbatim[PatternTest]|Verbatim[Condition]
        )[$$pattern_,_]:>$$pattern
    };

reserveSymbol//Attributes = {Listable};
reserveSymbol[symbol_Symbol] :=
    Module[ {},
        Unprotect@symbol;
        ClearAll@symbol;
        symbol::usage =
            "This symbol has been cleared and reserved.";
        Protect@symbol;
    ];
reserveSymbol[input_] :=
    input;

hideContext/:MakeBoxes[hideContext[expr_],form_] := 
    Block[ {Internal`$ContextMarks = False},
        MakeBoxes[expr,form]
    ];

optionTableForm[] :=
    Sequence[
        TableSpacing->{2,2},
        TableAlignments->{Left,Top}
    ];
    
defaultStringTemplate[msg_String] :=
    StringTemplate[
        msg,
        InsertionFunction->(Style[#,Pink]&),
        CombinerFunction->(Style[#,RGBColor[0.5,0.5,1]]&)@*Row
    ];
    
setArgumentCompletion[function_String,{args___}] :=
    setArgumentCompletion`kernel[{function},{args}];
setArgumentCompletion[functionList:{__String},{args___}] :=
    setArgumentCompletion`kernel[functionList,{args}];
setArgumentCompletion`kernel[functionList:{___},{args___}] :=
    Module[ {processed},
        processed = {args}/.{
            None->0,
            "AbsoluteFileName"->2,
            "RelativeFileName"->3,
            "Color"->4,
            "PackageName"->7,
            "DirectoryName"->8,
            "InterpreterType"->9
        };
        Function[
            function,
            FE`Evaluate@FEPrivate`AddSpecialArgCompletion[#]&[function->processed]
        ]/@functionList;
    ];


(* ::Subsection:: *)
(*algebraInternal*)


algebraInternal::usage = 
    "internal algebra relations.";
algebraInternal[] = 
    {"conjugate","tensorProduct","comultiplication"};


(* ::Subsubsection:: *)
(*multiplication*)


NonCommutativeMultiply//Unprotect;
NonCommutativeMultiply//ClearAll;
NonCommutativeMultiply//Attributes = {Flat,OneIdentity};

algebraInternal["multiplication"] = <|
    "operator"->{},
    "relation"->{
        x_**y_/;scalarQ[x]||scalarQ[y]:>x*y,
        (k_?scalarQ*x_)**y_:>k*x**y,
        x_**(k_?scalarQ*y_):>k*x**y,
        (x_+y_)**z_:>x**z+y**z,
        z_**(x_+y_):>z**x+z**y
    },
    "printing"->{}
|>;    


(* ::Subsubsection:: *)
(*tensor product*)


CircleTimes//Unprotect;
CircleTimes//ClearAll;
CircleTimes//Attributes = {Flat,OneIdentity};

algebraInternal["tensorProduct"] = <|
    "operator"->{id},
    "relation"->{
        CircleTimes[x_,k_?scalarQ*y_.]:>
            k CircleTimes[x,y],
        CircleTimes[k_?scalarQ*x_.,y_]:>
            k CircleTimes[x,y],
        CircleTimes[x_+y_,z_]:>
            CircleTimes[x,z]+CircleTimes[y,z], 
        CircleTimes[z_,x_+y_]:>
            CircleTimes[z,x]+CircleTimes[z,y],
        x_CircleTimes**y_CircleTimes:>
            tensorThread[x**y]/;tensorThread`rankEqualQ[x,y],
        id**x_:>x,
        x_**id:>x            
    },
    "printing"->{}
|>;


(* ::Subsubsection:: *)
(*conjugate*)


SuperDagger//Unprotect;
SuperDagger//ClearAll;

algebraInternal["conjugate"] = <|
    "operator"->{},
    "relation"->{
        SuperDagger[1]:>1,
        SuperDagger[k_?scalarQ*x_.]:>
            Conjugate[k] SuperDagger[x],
        SuperDagger[x_+y_]:>
            SuperDagger[x]+SuperDagger[y],
        SuperDagger[x_**y_]:>
            SuperDagger[y]**SuperDagger[x]
    },
    "printing"->{}
|>;


(* ::Subsubsection:: *)
(*comultiplication*)


algebraInternal["comultiplication"] = <|
    "operator"->{},
    "relation"->{},
    "printing"->{}
|>;


(* ::Subsection:: *)
(*Class algebra*)


(* ::Subsubsection:: *)
(*Argument patterns*)


patternAlg = _String|_Symbol;
patternAlgs = (_String|_Symbol)..;
patternAlgList = {(_String|_Symbol)..};


(* ::Subsubsection:: *)
(*algebraDefine*)


algebraDefine[algList:patternAlgList] :=
    Module[ {},
        instanceDefine["algebra",algList];
        (*set the auto-completion of algebra names*)
        setArgumentCompletion[
            {"algebraDefault","algebraReset","algebraUnset"},
            {Keys@classData["algebra","instanceData"]}
        ];
        setArgumentCompletion[
            {"algebraAdd","algebraDelete"},
            {Keys@classData["algebra","instanceData"],classData["algebra","memberList"]}
        ];
    ];
algebraDefine[alg:patternAlg] :=
    algebraDefine[{alg}];

algebraDefineQ[alg:patternAlg] :=
    KeyExistsQ[
        classData["algebra","instanceData"],
        alg
    ];
algebraDefineQ[_] = False;

algebraDefineInternal[] :=
    Module[ {alg},
        algebraDefine@algebraInternal[];
        Table[
            algebraAdd[{alg},algebraInternal@alg],
            {alg,algebraInternal[]}
        ];
    ];


(* ::Subsubsection:: *)
(*algebraDefault*)


algebraDefault[algList:patternAlgList] :=
    Module[ {},
        instanceDefault["algebra",algList];
        Print@defaultStringTemplate["The default algebras: \n``"]@algList;
    ];
algebraDefault[alg:patternAlg] :=
    algebraDefault[{alg}];


(* ::Subsubsection:: *)
(*algebraReset, algebraUnset, algebraAdd, algebraDelete*)


algebraReset[algList:patternAlgList] :=
    instanceReset["algebra",algList];
algebraReset[alg:patternAlg] :=
    instanceReset["algebra",{alg}];


algebraUnset[algList:patternAlgList] :=
    instanceUnset["algebra",algList];
algebraUnset[alg:patternAlg] :=
    instanceUnset["algebra",{alg}];


algebraAdd[algList:patternAlgList,assoc_] :=
    instanceAdd["algebra",algList,assoc];
algebraAdd[alg:patternAlg,assoc_] :=
    instanceAdd["algebra",{alg},assoc];

algebraAdd[algList:patternAlgList][assoc_] :=
    instanceAdd["algebra",algList,assoc];
algebraAdd[alg:patternAlg][assoc_] :=
    instanceAdd["algebra",{alg},assoc];


algebraDelete[algList:patternAlgList,assoc_] :=
    instanceDelete["algebra",algList,assoc];
algebraDelete[alg:patternAlg,assoc_] :=
    instanceDelete["algebra",{alg},assoc];

algebraDelete[algList:patternAlgList][assoc_] :=
    instanceDelete["algebra",algList,assoc];
algebraDelete[alg:patternAlg][assoc_] :=
    instanceDelete["algebra",{alg},assoc];


(* ::Subsubsection:: *)
(*algebraShow*)


algebraShow[alg:patternAlg]/;algebraDefineQ[alg] :=
    algebraShow`kernel[
        defaultStringTemplate["Algebra: \n``"]@alg,
        classData["algebra","instanceData",alg,"operator"],
        classData["algebra","instanceData",alg,"relation"],
        classData["algebra","instanceData",alg,"printing"]
    ];
algebraShow[] :=
    algebraShow`kernel[
        defaultStringTemplate["Default algebras: \n``"]@classData["algebra","instanceDefaultList"],
        instanceDefaultData["algebra","operator"],
        instanceDefaultData["algebra","relation"],
        instanceDefaultData["algebra","printing"]
    ];
algebraShow`kernel[title_,operatorList_,relationList_,printingList_] :=
    TableForm[{
        title,
        violet@"Operators:",
        operatorList//Row[#,Spacer[4]]&,
        violet@"Relations:",
        relationList//Map[hideContext,#,{1}]&//TableForm,
        violet@"Printings:",
        printingList//Map[hideContext,#,{1}]&//TableForm
    },TableDepth->1,optionTableForm[]];


(* ::Subsection:: *)
(*Default arguments*)


algebraDefine[] :=
    Keys@classData["algebra","instanceData"];
algebraDefault[] :=
    classData["algebra","instanceDefaultList"];


(*reset/unset the default except internal algebras*)
algebraReset[] :=
    algebraReset@Complement[
        algebraDefault[],
        algebraInternal[]
    ];
algebraUnset[] :=
    algebraUnset@Complement[
        algebraDefault[],
        algebraInternal[]
    ];
    
(*reset/unset all the defined except internal algebras*)
algebraReset[All] :=
    algebraReset@Complement[
        algebraDefine[],
        algebraInternal[]
    ];
algebraUnset[All] :=
    algebraUnset@Complement[
        algebraDefine[],
        algebraInternal[]
    ];


operator[] :=
    instanceDefaultData["algebra","operator"];
relation[] :=
    instanceDefaultData["algebra","relation"];
printing[] :=
    instanceDefaultData["algebra","printing"];

operator[alg:patternAlg] :=
    classData["algebra","instanceData",alg,"operator"];
relation[alg:patternAlg] :=
    classData["algebra","instanceData",alg,"relation"];
printing[alg:patternAlg] :=
    classData["algebra","instanceData",alg,"printing"];


(* ::Subsection:: *)
(*Kernel functions*)


algebraSimplify//Attributes = {Listable};
algebraSimplify//Options = {"caching"->True};
algebraSimplify[expr_,OptionsPattern[]] :=
    Switch[ OptionValue@"caching",
        False,
            algebraSimplify`default[expr],
        True,
            algebraSimplify`caching[expr]
    ];

algebraSimplify`default::usage =
    "use a top-down search strategy, similar to breadth-first search.";
algebraSimplify`default[expr_] :=
    ReplaceRepeated[expr,instanceDefaultData["algebra","relation"]]//Simplify;

algebraSimplify`caching::usage =
    "cache the default algebra.";
algebraSimplify`caching[expr_] :=
    Block[ {scalarQ,generatorQ,generatorList,relationList},
        generatorList =
            instanceDefaultData["algebra","operator"];
        relationList =
            instanceDefaultData["algebra","relation"];
        scalarQ[$$expr_] :=
            FreeQ[$$expr,Alternatives@@generatorList];
        generatorQ[op:_Symbol|__Symbol[___]] :=
            MemberQ[generatorList,op];
        ReplaceRepeated[expr,relationList]//Simplify
    ];


algebraPrint//Attributes = {Listable};
algebraPrint[expr_] :=
    ReplaceRepeated[expr,instanceDefaultData["algebra","printing"]];


algebraEquation//Attributes = {HoldFirst};
algebraEquation[expr_] :=
    algebraPrint[HoldForm@expr]==algebraPrint@algebraSimplify[expr];


scalarQ[expr_] :=
    FreeQ[expr,Alternatives@@instanceDefaultData["algebra","operator"]];
operatorQ[expr__] :=
    Not@FreeQ[expr,Alternatives@@instanceDefaultData["algebra","operator"]];


generatorQ[op_Symbol|op_Symbol[___]] :=
    MemberQ[instanceDefaultData["algebra","operator"],op];


(* ::Subsection:: *)
(*Shortcuts*)


SetAttributes[{algS,algP,algSP,algSSP},Listable];
SetAttributes[{algE,algES},HoldFirst];

algS[expr_] :=
    algebraSimplify[expr];
algP[expr_] :=
    algebraPrint[expr];
algSP[expr_] :=
    algebraSimplify[expr]//algebraPrint;
algSS[expr_] :=
    algebraSimplify[expr]//FullSimplify;
algSSP[expr_] :=
    algebraSimplify[expr]//FullSimplify//algebraPrint;
    
algE[expr_] :=
    algebraEquation[expr];
algES[expr_] :=
    algebraPrint[HoldForm@expr]==algebraPrint@FullSimplify@algebraSimplify[expr];
    
algEqualQ[x_,y_] :=
    algebraSimplify[x-y]==0;    
algSameQ[x_,y_] :=
    algebraSimplify[x-y]===0;


(* ::Subsection:: *)
(*Commutator, adjoint and power*)


(*n-commutator: [x,y,z,...]=[x,[y,[z,...]]]*)
comm[x_,y_] :=
    x**y-y**x;
comm[x_,y__] :=
    x**comm[y]-comm[y]**x;
       
anticomm[x_,y_] :=
    x**y+y**x;
anticomm[x_,y__] :=
    x**anticomm[y]+anticomm[y]**x;

(*Jacobi identity: [x,y,z]+[y,z,x]+[z,x,y]*)
jacobiIdentity[x_,y_,z_] :=
    algebraSimplify[
        comm[x,y,z]+comm[y,z,x]+comm[z,x,y]
    ];   


commSim[x___] :=
    comm[x]//algebraSimplify;
anticommSim[x___] :=
    anticomm[x]//algebraSimplify;


commDefine/:(
    commDefine[x_,y_,
        OrderlessPatternSequence[
            sign:1|-1|"boson"|"fermion"|"even"|"odd":"boson",
            order:"normal"|"reverse":"normal"
        ]
    ]:>result_
) :=
    If[ order==="normal",
        Inactive[RuleDelayed][
            x**y,
            comm`sign@sign stripPattern@y**stripPattern@x+result
        ]//Activate,
        Inactive[RuleDelayed][
            y**x,
            comm`sign@sign stripPattern@x**stripPattern@y-result
        ]//Activate
    ];
commDefine/:(
    commDefine[x_,y_,
        OrderlessPatternSequence[
            sign:1|-1|"boson"|"fermion"|"even"|"odd":"boson",
            order:"normal"|"reverse":"normal"
        ]
    ]:>Verbatim[Condition][result_,condition_]
) :=
    If[ order==="normal",
        Inactive[RuleDelayed][
            x**y,
            Condition[comm`sign@sign stripPattern@y**stripPattern@x+result,condition]
        ]//Activate,
        Inactive[RuleDelayed][
            y**x,
            Condition[comm`sign@sign stripPattern@x**stripPattern@y-result,condition]
        ]//Activate
    ];
comm`sign::usage = 
    "comm`sign specifies the sign of generators: \n"<>
    "sign[1]=1, sign[-1]=-1, \n"<>
    "sign[\"boson\"]=1, sign[\"fermion\"]=-1, \n"<>
    "sign[\"even\"]=1, sign[\"odd\"]=-1.";
comm`sign[1] = comm`sign["boson"] = comm`sign["even"] = 1;
comm`sign[-1] = comm`sign["fermion"] = comm`sign["odd"] = -1;


(*adjoint[x,y,n]=[x,[x,[...,y]]]*)
adjoint[op_,0][expr_] :=
    expr;
adjoint[op_,order_:1][expr_] :=
    comm@@Join[ConstantArray[op,order],{expr}];

adjointExp[op_,orderMax_,parameter_:1][expr_] :=
    Module[ {order},
        Sum[adjoint[op,order][expr] parameter^order/order!,{order,0,orderMax}]
    ];


operatorPower[_,0] = 
    1;
operatorPower[op_,1] :=
    op;
operatorPower[op_,order_:1] :=
    NonCommutativeMultiply@@ConstantArray[op,order];

operatorExp[op_,orderMax_,parameter_:1] :=
    Module[ {order},
        Sum[operatorPower[op,order] parameter^order/order!,{order,0,orderMax}]
    ];


(* ::Subsection:: *)
(*Inner product*)


innerProduct[x_,y_] :=
    algebraSimplify[SuperDagger[x]**y];
innerProduct[x_] :=
    innerProduct[x,x];


(* ::Subsection:: *)
(*Tensor product*)


tensorRank`generatorRank[_] = 1;

tensorRankSet//Attributes = {Listable};
tensorRankSet[op_?generatorQ,rank_] :=
    tensorRank`generatorRank[op] ^= rank;    
    
tensorRank[op_] :=
    tensorRank`kernel[op];    
tensorRank`kernel[_?scalarQ] =
    0;
tensorRank`kernel[op_?generatorQ] :=
    tensorRank`generatorRank[op];
tensorRank`kernel[op:_CircleTimes|_Times] :=
    tensorRank`kernel/@List@@op//Total;
tensorRank`kernel[op:_NonCommutativeMultiply|_Plus] :=
    tensorRank`kernel/@List@@op//Max;


(*migrated from lily`base`threadByLength*)
tensorThread[op1_**op2_] :=
    Module[ {slot,head},
        Map[Thread[#,head]&]@Split[
            Thread@head[
                tensorThread`padRight[List@@op1,slot],
                tensorThread`padRight[List@@op2,slot]
            ],
            MemberQ[#2,slot]&
        ]/.{slot->Sequence[]}/.{List[op_]:>op}/.{head->NonCommutativeMultiply,List->CircleTimes}
    ];
tensorThread`padRight[opList_,slot_] :=
    Flatten@Riffle[opList,ConstantArray[slot,#]&/@(tensorRank`generatorRank/@opList-1)];
tensorThread`rankEqualQ[op1_,op2_] :=
    Equal@@Map[Total]@Map[tensorRank`generatorRank,{List@@op1,List@@op2},{2}];    


(* ::Subsection:: *)
(*Scalar extraction*)


scalarSeparate[exprs__] :=
    scalarSeparate`kernel[exprs];
scalarExtract[exprs__] :=
    scalarSeparate`kernel[exprs]/.HoldPattern[x_->y_]:>x;
    
scalarSeparate`kernel[0] :=
    0->0;
scalarSeparate`kernel[c_?scalarQ*q_?generatorQ] :=
    c->q;
scalarSeparate`kernel[c_?scalarQ*q_NonCommutativeMultiply] :=
    c->q;
scalarSeparate`kernel[term1_+term2_] :=
    {scalarSeparate`kernel@term1,scalarSeparate`kernel@term2}//Flatten;
scalarSeparate`kernel[{exprs__}] :=
    scalarSeparate`kernel/@{exprs}//Flatten;


(* ::Section:: *)
(*Defining class*)


classDefine[
    "algebra",
    {"operator","relation","printing"},
    {"setUnsorted","setUnsorted","setUnsorted"},
    {{},algebraInternal["multiplication"]["relation"],{}}
];
algebraDefineInternal[];


(* ::Section:: *)
(*End*)


End[];

Protect@@Names[$Context<>"*"];

EndPackage[];
