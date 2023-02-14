(* ::Package:: *)

(* ::Section:: *)
(*Begin*)


BeginPackage["lily`class`"];

classUnset/@Keys[classData]//Quiet;
Unprotect@@Names[$Context<>"*"];
ClearAll@@DeleteCases[Names[$Context<>"*"],"classData"|"instanceDefaultData"];


(*class + instance + member + structure*) 

classData::usage = 
    "store the data of classes.";
classDefine::usage = 
    "define and initiate the class.";
classDefineQ::usage = 
    "check whether the class is defined.";
classProtect::usage = 
    "protect the defined class against classUnset. The protected class will not be unset when reloading the package.";
classUnset::usage = 
    "unset the class if defined and unprotected. When loading the package, unprotected class will be unset.";


(*instance methods*)

instanceDefaultData::usage = 
    "store the data of default instance of class.";
instanceDefault::usage = 
    "set the instances into default.";

instanceDefine::usage = 
    "define the instances.";
instanceReset::usage = 
    "reset the instances.";
instanceUnset::usage = 
    "unset the instances, and update the default instance list.";

instanceAdd::usage = 
    "add elementlist to the instances.";
instanceDelete::usage = 
    "delete elementlist from the instances.";
    
instancePreIntercept::usage = 
    "reserved function to modify the pre-process of instance methods.";
instancePostIntercept::usage = 
    "reserved function to modify the post-process of instance methods.";


Begin["`Private`"];


(* ::Section:: *)
(*Private*)


(* ::Subsection:: *)
(*lily`base`*)


pink[expr_] :=
    Style[expr,RGBColor[1,0.5,0.5]];
violet[expr_] :=
    Style[expr,RGBColor[0.5,0.5,1]];
orange[expr_] :=
    Style[expr,RGBColor[1,0.5,0]];

complement[list1_List,ruleList:{(_Rule|_RuleDelayed)..}] :=
    DeleteCases[list1,Alternatives@@Verbatim/@ruleList];
complement[list1_List,list2_List] :=
    DeleteCases[list1,Alternatives@@list2];

complementFromLast[list1_,list2_] :=
    Module[ {fun},
        fun[$$list_,{pattern_,part_}] :=
            DeleteCases[$$list,pattern,{1},part];
        Fold[fun,Reverse@list1,Tally@list2]//Reverse
    ];

symbolAdd[symbols__Symbol] :=
    Last@{symbols};
    
symbolDelete[symbols__Symbol] :=
    Null;

echo//Attributes = {HoldAll};
echo[code_] :=
    Module[ {codeResult},
        codeResult = code;
        Print[
            pink@ToString@Unevaluated@code,
            " = ",
            violet@codeResult
        ];
        codeResult
    ];

initiate/:(set:Set|SetDelayed|UpSet|UpSetDelayed)[initiate[expr_],value_]:=
    If[ ValueQ[expr,Method->"TrialEvaluation"],
        expr,
        set[expr,value]
    ];
initiate/:(set:TagSet|TagSetDelayed)[tag_,initiate[expr_],value_] :=
    If[ ValueQ[expr,Method->"TrialEvaluation"],
        expr,
        set[tag,expr,value]
    ];

hideContext/:MakeBoxes[hideContext[expr_],form_] := 
    Block[ {Internal`$ContextMarks = False},
        MakeBoxes[expr,form]
    ];

messageHideContext//Attributes = {HoldFirst};
messageHideContext[args__] :=
    Block[ {Internal`$ContextMarks = False},
        Message[args]
    ];

mergeByKey[rules:{___Rule},default:_:Identity][data:{___?AssociationQ}] :=
    mergeByKey[data,rules,default];
mergeByKey[{<||>...},{___Rule},Repeated[_,{0,1}]] :=
    <||>;
mergeByKey[data:{__?AssociationQ},rules:{___Rule},default:_:Identity] :=
    Module[ {
            (* unique symbol that is used for identifying where the undefined keys were after transposing the association *)
            missingToken,
            assoc,
            keys,
            queryRules,
            mergeRules = 
                Replace[
                    Flatten@Replace[
                        rules,
                        Verbatim[Rule][lst_List,fun_]:>Thread[lst->fun],
                        {1}
                    ],
                    Verbatim[Rule][Key[k_],fun_]:>k->fun,
                    {1}
                ],
            keysSameQ = SameQ@@Keys[data]
        },
        (* avoid KeyUnion if it's not necessary *)
        If[ keysSameQ,
            assoc = data,
            assoc = KeyUnion[DeleteCases[data,<||>],missingToken&]
        ];
        keys = Keys[First@assoc];
        (* this is essentially how GeneralUtilities`AssociationTranspose works *)
        assoc = 
            AssociationThread[
                keys,
                If[ keysSameQ,
                    Transpose@Values[assoc],
                    DeleteCases[Transpose@Values[assoc],missingToken,{2}]
                ]
            ];
        keys = Key/@keys;
        queryRules = 
            DeleteCases[
                Thread[
                    keys->Lookup[mergeRules,keys,default]
                ],
                _->Identity
            ];
        If[ MatchQ[queryRules,{__Rule}],
            Query[queryRules]@assoc,
            assoc
        ]
    ];


(* ::Subsection:: *)
(*Data structures of members*)


memberStructureInternal::usage = 
    "pre-defined data structures of members, including listUnsorted, listSorted, setUnsorted, setSorted and boolean.";
memberStructureInternal = <|
    "boolean"-><|
        "instanceDefine"->True,
        "instanceReset"->True,
        "instanceAdd"->Or,
        "instanceDelete"->And,
        "memberStructureUsage"->"Boolean value: add is Or and delete is And."
    |>,
    "string"-><|
        "instanceDefine"->"",
        "instanceReset"->"",
        "instanceAdd"->StringJoin,
        "instanceDelete"->StringDelete,
        "memberStructureUsage"->"string: add is StringJoin and delete is StringDelete."
    |>,
    "symbol"-><|
        "instanceDefine"->Null,
        "instanceReset"->Null,
        "instanceAdd"->symbolAdd,
        "instanceDelete"->symbolDelete,
        "memberStructureUsage"->"symbol: add is replacing and delete is replacing with Null."
    |>,
    "listUnsorted"-><|
        "instanceDefine"->{},
        "instanceReset"->{},
        "instanceAdd"->Join,
        "instanceDelete"->complementFromLast,
        "memberStructureUsage"->"unsorted list allowing duplicates."
    |>,
    "listSorted"-><|
        "instanceDefine"->{},
        "instanceReset"->{},
        "instanceAdd"->Sort@*Join,
        "instanceDelete"->Sort@*complementFromLast,
        "memberStructureUsage"->"sorted list allowing duplicates."
    |>,
    "setUnsorted"-><|
        "instanceDefine"->{},
        "instanceReset"->{},
        "instanceAdd"->DeleteDuplicates@*Join,
        "instanceDelete"->complement,
        "memberStructureUsage"->"unsorted set without duplicates."
    |>,
    "setSorted"-><|
        "instanceDefine"->{},
        "instanceReset"->{},
        "instanceAdd"->Union,
        "instanceDelete"->Complement,
        "memberStructureUsage"->"sorted set without duplicates."
    |>
|>;
memberStructure::usage = 
    "store the member structures.";
memberStructure = 
    memberStructureInternal;


memberStructureQ::usage = 
    "check whether the structure is pre-defined.";
memberStructureQ[structure_String] :=
    KeyExistsQ[memberStructure,structure];
memberStructureQ[_] = False;


memberStructureDefine::usage =
    "define a new data structure of member.";
memberStructureDefine::strcthasdef =
    "the member structure `` has already been defined.";
memberStructureDefine::strctlackkeys =
    "the member structure `` lacks necessary keys."
memberStructureDefine[structure_,assoc_] :=
    Which[    
        memberStructureQ[structure],
            messageHideContext[memberStructureDefine::strcthasdef,structure];
            Abort[],
        Apply[And,KeyExistsQ[assoc,#]&/@Keys@memberStructure["boolean"]]==False,
            messageHideContext[memberStructureDefine::strctlackkeys,structure];
            Abort[],
        True,
            AssociateTo[memberStructure,structure->assoc];
            Keys@memberStructure
    ];


memberStructureUnset::strctnotdef =
    "the member structure `` has not been defined.";    
memberStructureUnset::strctinternal =
    "the member structure `` is internal and cannot be unset.";    
memberStructureUnset[structure_] :=
    Which[    
        Not@memberStructureQ[structure],
            messageHideContext[memberStructureUnset::strctnotdef,structure];
            Abort[],
        KeyExistsQ[memberStructureInternal,structure]==True,
            messageHideContext[memberStructureUnset::strctinternal,structure];
            Abort[],
        True,
            KeyDropFrom[memberStructure,structure];
            Keys@memberStructure
    ];


(* ::Subsection:: *)
(*Class constructors*)


(* ::Subsubsection:: *)
(*classData/classDefine*)


classData//initiate = <||>;
instanceDefaultData//initiate = <||>;

classDefineQ[class_] :=
    KeyExistsQ[classData,class]===True;


(*define data class*)

classDefine[class_,memberList_List,structureList_List,commonValueList_List] :=
    Module[ {},
        classDefine`checkInput[class,memberList,structureList,commonValueList];
        classDefine`initiateClass[class,memberList,structureList,commonValueList];
    ];
classDefine[class_,memberList_List,structure_:"setUnsorted",commomValue_:{}] :=
    Module[ {structureList,commonValueList},
        structureList = ConstantArray[structure,Length@memberList];
        commonValueList = ConstantArray[commomValue,Length@memberList];
        classDefine`checkInput[class,memberList,structureList,commonValueList];
        classDefine`initiateClass[class,memberList,structureList,commonValueList];
    ];

(*input check*)
classDefine::membernull =
    "there is empty member name.";
classDefine::memberdup =
    "there are duplicated member names.";
classDefine::classdef =
    "the class has been defined.";
classDefine::structureundef =
    "there is undefined data structure.";
classDefine::lengthneq =
    "the numbers of members, structures and default values are not equal.";
classDefine`checkInput[class_,memberList_,structureList_,commonValueList_] :=
    Which[
        classDefineQ@class===True,
            Message[classDefine::classdef];
            Abort[],
        MemberQ[""]@memberList===True,
            Message[classDefine::membernull];
            Abort[],
        DuplicateFreeQ@memberList===False,
            Message[classDefine::memberdup];
            Abort[],
        And@@memberStructureQ/@structureList===False,
            Message[classDefine::structureundef];
            Abort[],
        Equal@@Length/@{memberList,structureList,commonValueList}===False,
            Message[classDefine::lengthneq];
            Abort[]
    ];

(*initiate the class*)
classDefine`initiateClass[class_,memberList_,structureList_,commonValueList_] :=
    Module[ {structureAssoc,commonValueAssoc,instanceFunctionAssoc},
        (*pre-store the associations*)
        commonValueAssoc = AssociationThread[memberList->commonValueList];
        structureAssoc = AssociationThread[memberList->structureList];
        instanceFunctionAssoc = Map[memberStructure,structureAssoc]//Transpose;
        (*initiate and store the class data to classData*)
        AssociateTo[
            classData,
            class-><|
                "instanceData"-><||>,
                "instanceCommonData"->commonValueAssoc,
                "instanceDefaultList"->{},
                instanceFunctionAssoc,
                "memberList"->memberList,
                "memberStructureData"->structureAssoc,
                "isClassProtected"->False
            |>
        ];
        (*initiate and store the default instance of class in instanceDefaultData*)
        AssociateTo[
            instanceDefaultData,
            class->commonValueAssoc
        ];
    ];


(* ::Subsubsection:: *)
(*classUnset/classProtect*)


classUnset::classundef =
    "the class has not been defined.";
classUnset::classprotected =
    "the class has been protected.";
classUnset[class_] :=
    Module[ {},
        Which[
            classDefineQ@class===False,
                Message[classUnset::classundef],
            classData[class,"isClassProtected"]===True,
                Message[classUnset::classprotected],
            True,
                (*remove the class data from classData*)
                KeyDropFrom[
                    classData,
                    class
                ];
                (*remove the default instance of class from instanceDefaultData*)
                KeyDropFrom[
                    instanceDefaultData,
                    class
                ];
        ];
    ];
classUnset[input_Keys] :=
    Identity[input];


classProtect::classundef =
    "the class has not been defined.";
classProtect[class_,state_?BooleanQ] :=
    Module[ {},
        Which[
            classDefineQ@class===False,
                Message[classProtect::classundef],
            True,
                AssociateTo[classData[class],"isClassProtected"->state]
        ];
    ];


(* ::Subsection:: *)
(*Instance methods*)


(* ::Subsubsection:: *)
(*instanceDefineCheck*)


instanceDefineCheck::usage = 
    "the inputs will be checked by this private method before calling public methods.";
instanceDefineCheck::classundef =
    "the class `` has not been defined.";
instanceDefineCheck::insundef =
    "the instance `` has not been defined.";
instanceDefineCheck::insdef =
    "the instance `` has been defined.";
instanceDefineCheck::memundef =
    "the member `` has not been defined.";

instanceDefineCheck["ifClassNotDefined"][class_] :=
    If[ classDefineQ[class]===False,
        messageHideContext[instanceDefineCheck::classundef,class];
    ];

instanceDefineCheck["ifInstanceNotDefined"][class_,instanceList_] :=
    Module[ {instanceNotDefList},
        instanceNotDefList = Complement[
            instanceList,
            Keys@classData[class,"instanceData"]
        ];
        If[ instanceNotDefList=!={},
            messageHideContext[instanceDefineCheck::insundef,instanceNotDefList];
        ];
    ];

instanceDefineCheck["ifInstanceHasDefined"][class_,instanceList_] :=
    Module[ {instanceHasDefList},
        instanceHasDefList = Intersection[
            instanceList,
            Keys@classData[class,"instanceData"]
        ];
        If[ instanceHasDefList=!={},
            messageHideContext[instanceDefineCheck::insdef,instanceHasDefList];
        ];
    ];
    
instanceDefineCheck["ifMemberNotDefined"][class_,memberList_] :=
    Module[ {memberNotDefList},
        memberNotDefList = Complement[
            memberList,
            classData[class,"memberList"]
        ];
        If[ memberNotDefList=!={},
            messageHideContext[instanceDefineCheck::memundef,memberNotDefList];
        ];
    ];


(* ::Subsubsection:: *)
(*instanceDefaultUpdate*)


instanceDefaultUpdate::usage = 
    "the default instance will be updated by this private method "<>
    "after calling public methods of default, reset, unset, add and delete.";
instanceDefaultUpdate[class_] :=
    Module[ {defaultInstance,functionListByStructure},
        (*prepare the add functions according to structure*)
        functionListByStructure =
            classData[class,"instanceAdd"]//Map[Apply]//Normal;
        (*construct the default values from common and input*)
        defaultInstance = Join[
            {classData[class,"instanceCommonData"]},
            Map[
                classData[class,"instanceData",#]&,
                classData[class,"instanceDefaultList"]
            ]
        ]//mergeByKey[functionListByStructure];
        (*update the default values to dataType[class,member]*)
        AssociateTo[
            instanceDefaultData,
            class->defaultInstance
        ];
    ];


(* ::Subsubsection:: *)
(*instanceDefine*)


instanceDefine[class_,instanceList_] :=
    Module[ {},
        (*check existence of class and instance*)
        instanceDefineCheck["ifClassNotDefined"][class];
        instanceDefineCheck["ifInstanceHasDefined"][class,instanceList];
        (*kernel*)
        instanceDefine`kernel[class,#]&/@instanceList;
    ];
instanceDefine`kernel[class_,instance_] :=
    Module[ {newInstance},
        (*initiate the new instance*)
        newInstance = AssociationMap[
            classData[class,"instanceDefine",#]&,
            classData[class,"memberList"]
        ];
        (*intercept before defining the new instance*)
        instancePreIntercept["instanceDefine"][class,instance];
        (*define the new instance*)
        AssociateTo[
            classData[class,"instanceData"],
            instance->newInstance
        ];
        (*intercept if necessary*)
        instancePostIntercept["instanceDefine"][class,instance];
    ];


(* ::Subsubsection:: *)
(*instanceDefault*)


instanceDefault[class_,instanceList_] :=
    Module[ {},
        (*check existence of class and instance*)
        instanceDefineCheck["ifTypeNotDefined"][class];
        instanceDefineCheck["ifInstanceNotDefined"][class,instanceList];
        (*kernel*)
        instanceDefault`kernel[class,instanceList];
        (*update the default instance*)
        instanceDefaultUpdate[class];
    ];
instanceDefault`kernel[class_,instanceList_] :=
    Module[ {},
        (*intercept before setting the default instance*)
        instancePreIntercept["instanceDefault"][class,instanceList];
        (*set the default instance*)
        AssociateTo[
            classData[class],
            "instanceDefaultList"->instanceList
        ];
        (*intercept if necessary*)
        instancePostIntercept["instanceDefault"][class,instanceList];
    ];


(* ::Subsubsection:: *)
(*instanceReset*)


instanceReset[class_,instanceList_] :=
    Module[ {},
        (*check existence of class and instance*)
        instanceDefineCheck["ifTypeNotDefined"][class];
        instanceDefineCheck["ifInstanceNotDefined"][class,instanceList];
        (*kernel*)
        instanceReset`kernel[class,#]&/@instanceList;
        (*update the default instance*)
        instanceDefaultUpdate[class];
    ];
instanceReset`kernel[class_,instance_] :=
    Module[ {resetInstance},
        (*pre-store the reset instance*)
        resetInstance = AssociationMap[
            classData[class,"instanceReset",#]&,
            classData[class,"memberList"]
        ];
        (*intercept before reset the instance*)
        instancePreIntercept["instanceReset"][class,instance];
        (*reset the instance*)
        AssociateTo[
            classData[class,"instanceData"],
            instance->resetInstance
        ];
        (*intercept if necessary*)
        instancePostIntercept["instanceReset"][class,instance];
    ];


(* ::Subsubsection:: *)
(*instanceUnset*)


instanceUnset[class_,instanceList_] :=
    Module[ {},
        (*check existence of class and instance*)
        instanceDefineCheck["ifTypeNotDefined"][class];
        instanceDefineCheck["ifInstanceNotDefined"][class,instanceList];
        instanceUnset`kernel[class,#]&/@instanceList;
        (*remove the instances in both the input and default instance list*)
        instanceUnset`updateInstanceDefaultList[class,instanceList];
        (*update the default instance*)
        instanceDefaultUpdate[class];
    ];
instanceUnset`kernel[class_,instance_] :=
    Module[ {},
        (*intercept before unset the instance*)
        instancePreIntercept["instanceUnset"][class,instance];
        (*unset the instance*)
        KeyDropFrom[classData[class,"instanceData"],instance];
        (*intercept if necessary*)
        instancePostIntercept["instanceUnset"][class,instance];
    ];
instanceUnset::rmdefault =
    "the following instances `` have been removed from default.";
instanceUnset`updateInstanceDefaultList::usage =
    "remove the instances both in the input and the default instance list.";
instanceUnset`updateInstanceDefaultList[class_,instanceList_] :=
    Module[ {removedDefaultList,leftDefaultList},
        removedDefaultList = Intersection[
            classData[class,"instanceDefaultList"],
            instanceList
        ];
        leftDefaultList = Complement[
            classData[class,"instanceDefaultList"],
            instanceList
        ];
        If[ removedDefaultList=!={},
            Message[instanceUnset::rmdefault,removedDefaultList]
        ];
        AssociateTo[
            classData[class],
            "instanceDefaultList"->leftDefaultList
        ];
    ];


(* ::Subsubsection:: *)
(*instanceAdd*)


instanceAdd[class_,instanceList_,memberRuleOrAssoc_] :=
    Module[ {memberAssoc,memberList},
        memberAssoc = Association[memberRuleOrAssoc];
        memberList = Keys@memberAssoc;
        (*check existence of class, instance and member*)
        instanceDefineCheck["ifTypeNotDefined"][class];
        instanceDefineCheck["ifInstanceNotDefined"][class,instanceList];
        instanceDefineCheck["ifMemberNotDefined"][class,memberList];
        (*kernel*)
        Function[
            instance,
            KeyValueMap[
                instanceAdd`kernel[class,instance,#1,#2]&,
                memberAssoc
            ]
        ]/@instanceList;
        (*update the default instance*)
        instanceDefaultUpdate[class];
    ];
instanceAdd`kernel[class_,instance_,member_,elementList_] :=
    Module[ {list},
        (*pre-store the desired result*)
        list = classData[class,"instanceAdd",member][
            classData[class,"instanceData",instance,member],
            elementList
        ];
        (*intercept before adding to the instance*)
        instancePreIntercept["instanceAdd"][class,instance,member,list];
        (*add to the instance*)
        AssociateTo[
            classData[class,"instanceData",instance],
            member->list
        ];
        (*intercept if necessary*)
        instancePostIntercept["instanceAdd"][class,instance,member,list];
    ];


(* ::Subsubsection:: *)
(*instanceDelete*)


instanceDelete[class_,instanceList_,memberRuleOrAssoc_] :=
    Module[ {memberAssoc,memberList},
        memberAssoc = Association[memberRuleOrAssoc];
        memberList = Keys@memberAssoc;
        (*check existence of class, instance and member*)
        instanceDefineCheck["ifTypeNotDefined"][class];
        instanceDefineCheck["ifInstanceNotDefined"][class,instanceList];
        instanceDefineCheck["ifMemberNotDefined"][class,memberList];
        (*kernel*)
        Function[
            instance,
            KeyValueMap[
                instanceDelete`kernel[class,instance,#1,#2]&,
                memberAssoc
            ]
        ]/@instanceList;
        (*update the default instance*)
        instanceDefaultUpdate[class];
    ];
instanceDelete`kernel[class_,instance_,member_,elementList_] :=
    Module[ {list},
        (*pre-store the desired result*)
        list = classData[class,"instanceDelete",member][
            classData[class,"instanceData",instance,member],
            elementList
        ];
        (*intercept before deleting from the instance*)
        instancePreIntercept["instanceDelete"][class,instance,member,list];
        (*delete from the instance*)
        AssociateTo[
            classData[class,"instanceData",instance],
            member->list
        ];
        (*intercept if necessary*)
        instancePostIntercept["instanceDelete"][class,instance,member,list];
    ];


(* ::Section:: *)
(*End*)


End[];

Protect@@Names[$Context<>"*"];
Unprotect["classData","instanceDefaultData"];

EndPackage[];
