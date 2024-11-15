(* ::Package:: *)

(* ::Subsection::Closed:: *)
(*Setup*)


(* ::Input::Initialization:: *)
(*Get["https://people.brandeis.edu/~headrick/Mathematica/grassmann.m"]*)
SetDirectory[NotebookDirectory[]];
<<grassmann.m
(*Grading[Unevaluated[f[\[Phi]_]]]:=Grading[\[Phi]]
Grading[f[b[1]]]
Grading[b[1]]
Grading[GD[f[b[1]],b[1]]]*)
(*Grading[D[d[1,0][b[1]],b[1]]]*)(*this little piece explain that GD should only be used for derivative wrt fermionic variables and D for bosonic variables*)


(* ::Input::Initialization:: *)
fieldsQ[a_] :=MemberQ[bosonFields,a]||MemberQ[fermionFields,a] 
NumFields = Length[fermionFields]+Length[bosonFields];
Fermion@@fermionFields;
Boson@@bosonFields;


(* ::Subsection::Closed:: *)
(*derivative*)


(* ::Input::Initialization:: *)
ClearAll[d]
d[n__][Plus[x_,y___]]:=d[n][x]+d[n][Plus[y]]
d[n__][x_]:=x/;Length[DeleteCases[{n},0]]==0
d[n1__][d[n2__][x_]]:=d[({n1}+{n2})/.List->Sequence][x]
d[n__][Times[a_,x___]]:=a d[n][Times[x]]/;NumericQ[a](*NumericQ[\[Pi]] = True but NumberQ[\[Pi]] = False*)
d[n__][Times[\[Lambda][v_][i_],x___]]:=\[Lambda][v][i] d[n][Times[x]]
d[n__][Times[\[Lambda][v_][i_]^power_,x___]]:=\[Lambda][v][i]^power d[n][Times[x]]
d[n__][\[Lambda][v_][i_]^_.]:=0


(* ::Input::Initialization:: *)
Grading[Unevaluated[d[n__][\[Phi]_]]]:=Grading[\[Phi]]
d[n__][0]:=0
d[n__][a_]:=0/;NumberQ[a]
d[n1_][HoldPattern[NonCommutativeMultiply[x_,y__]]]:=Sum[Binomial[n1,k1]d[k1][x]**d[n1-k1][NonCommutativeMultiply[y]],{k1,0,n1}]
d[n1_,n2_][HoldPattern[NonCommutativeMultiply[x_,y__]]]:=Sum[Binomial[n1,k1]Binomial[n2,k2]d[k1,k2][x]**d[n1-k1,n2-k2][NonCommutativeMultiply[y]],{k1,0,n1},{k2,0,n2}]
d[n1_,n2_,n3_][HoldPattern[NonCommutativeMultiply[x_,y__]]]:=Sum[Binomial[n1,k1]Binomial[n2,k2]Binomial[n3,k3]d[k1,k2,k3][x]**d[n1-k1,n2-k2,n3-k3][NonCommutativeMultiply[y]],{k1,0,n1},{k2,0,n2},{k3,0,n3}]


(* ::Input::Initialization:: *)
d[n__][Times[c1,x___]]:=c1 d[n][Times[x]];
d[n__][Times[c2,x___]]:=c2 d[n][Times[x]];
d[n__][Times[c3,x___]]:=c3 d[n][Times[x]];
d[n__][Times[c4,x___]]:=c4 d[n][Times[x]];
d[n__][Times[c5,x___]]:=c5 d[n][Times[x]];
d[n__][Times[c6,x___]]:=c6 d[n][Times[x]];
d[n__][Times[c7,x___]]:=c7 d[n][Times[x]];
d[n__][Times[c8,x___]]:=c8 d[n][Times[x]];
d[n__][Times[c9,x___]]:=c9 d[n][Times[x]];
d[n__][Times[c10,x___]]:=c10 d[n][Times[x]];
d[n__][Times[c11,x___]]:=c11 d[n][Times[x]];
d[n__][Times[c12,x___]]:=c12 d[n][Times[x]];
d[n__][Times[c13,x___]]:=c13 d[n][Times[x]];
d[n__][Times[\[Zeta],x___]]:=\[Zeta] d[n][Times[x]];
d[n__][Times[\[Epsilon],x___]]:=\[Epsilon] d[n][Times[x]]

d[n__][c1]:=0;
d[n__][c2]:=0;
d[n__][c3]:=0;
d[n__][c4]:=0;
d[n__][c5]:=0;
d[n__][c6]:=0;
d[n__][c7]:=0;
d[n__][c8]:=0;
d[n__][c9]:=0;
d[n__][c10]:=0;
d[n__][c11]:=0;
d[n__][c12]:=0;
d[n__][c13]:=0;
d[n__][\[Zeta]]:=0;
NumericQ[\[Zeta]]:=True


d[n__][\[Mu][i_]^_.]:=0


d[n__][Times[\[Mu][v_],x___]]:=\[Mu][v] d[n][Times[x]]
d[n__][Times[\[Mu][v_]^m_,x___]]:=\[Mu][v]^m d[n][Times[x]]


(*here I define some other symbols for \[Lambda]*)
(*d[n__][\[Mu][i_]^_.]:=0
d[n__][\[Eta][i_]^_.]:=0

d[n__][Times[\[Mu][v_][i_],x___]]:=\[Mu][v][i] d[n][Times[x]]
d[n__][Times[\[Mu][i_]^m_,x___]]:=\[Mu][i]^m d[n][Times[x]]
d[n__][\[Mu][v_][i_]^_.]:=0

d[n__][Times[\[Mu]1[i_],x___]]:=\[Mu]1[i] d[n][Times[x]]
d[n__][Times[\[Mu]1[i_]^m_,x___]]:=\[Mu]1[i]^m d[n][Times[x]]
d[n__][\[Mu]1[i_]^_.]:=0

d[n__][Times[\[Mu]2[i_],x___]]:=\[Mu]2[i] d[n][Times[x]]
d[n__][Times[\[Mu]2[i_]^m_,x___]]:=\[Mu]2[i]^m d[n][Times[x]]
d[n__][\[Mu]2[i_]^_.]:=0

d[n__][Times[\[Mu]3[i_],x___]]:=\[Mu]3[i] d[n][Times[x]]
d[n__][Times[\[Mu]3[i_]^m_,x___]]:=\[Mu]3[i]^m d[n][Times[x]]
d[n__][\[Mu]3[i_]^_.]:=0*)


(* ::Subsection:: *)
(*bracket*)


(* ::Input::Initialization:: *)
ClearAll[bracket]
bracket[front___,Times[a_,x___],end___]:=a bracket[front,Times[x],end]/;NumericQ[a]
bracket[front___,0,end___]:=0
bracket[front___,Plus[a_,b__],end___]:=bracket[front,a,end]+bracket[front,Plus[b],end]

Grading[Unevaluated[bracket[Ops__]]]:=Total[Grading/@(List[Ops])]+1  (*!!!  need to change for different theories*)


(* ::Input::Initialization:: *)
ClearAll[derivative]
derivative[front_,end_]:=Block[{frontDer,endDer,front0,end0},

front0= Cases[If[Head[front]===Times,Variables[front],Flatten[{front}]],_?(Grading[#]>0&)];
end0= Cases[
If[Head[end]===Times,Variables[end],Flatten[{end}]]
,_?(Grading[#]>0&)];(*this line is not very safe. Think again*)
(*If anything goes wrong, it probably is due to this line*)
(*this function only gives the correct result if there is no plus in front and end *)


frontDer = Cases[Flatten[{front0/.{NonCommutativeMultiply->List}}],
z:(HoldPattern[GD[d[m__][_],_]]|HoldPattern[\!\(\*
TagBox[
StyleBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", "1", "]"}], "[", 
RowBox[{"d", "[", "m__", "]"}], "]"}], "[", "_", "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]):>{m}
(*HoldPattern[GD[d[m__][_],_]]->{m}*)
];
endDer     = Cases[Flatten[{end0     /.{NonCommutativeMultiply->List}}],
z:(HoldPattern[GD[d[m__][_],_]]|HoldPattern[\!\(\*
TagBox[
StyleBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", "1", "]"}], "[", 
RowBox[{"d", "[", "m__", "]"}], "]"}], "[", "_", "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]):>{m}];
frontDer=If[Length[frontDer]==0,{{0,0}},frontDer];
endDer     =If[Length[endDer]==0,{{0,0}},endDer];

Return[
{Total[frontDer,2],Total[endDer,2],Flatten[frontDer+endDer]}
]
] 

updateList[list_,new_,pos_]:=Block[{newlist=list},newlist[[pos]]=new;newlist]


(* ::Input::Initialization:: *)
ClearAll[bracket1]
bracket1[ops__,{v1_,v2_}]:=Block[{arg = List[ops]},Apply[bracket,GExpand/@(List[ops])]/.{bracket[exp__]:>bracket[exp, {v1,v2,derivative[List[exp][[v1]],List[exp][[v2]]]}]}/.{GD[__]:>1,\!\(\*
TagBox[
StyleBox[
RowBox[{
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", "1", "]"}], "[", 
RowBox[{"d", "[", "__", "]"}], "]"}], "[", "_", "]"}], ":>", "1"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)}
];


(* ::Input::Initialization:: *)
wick2[exp_]:=wick[exp,{1,2}];
wick3[exp_]:=wick[wick[wick[exp,{1,2}],{1,3}],{2,3}];


(* ::Subsection:: *)
(*plug in Bootstrap result Subscript[I, \[CapitalGamma]]*)


(* ::Subsubsection:: *)
(*I\[CapitalDelta]*)


(* ::Input:: *)
(*(**)
(*wedge[A_,B_]:=A[1]B[2]-A[2]B[1]*)
(*dot[A_,B_]:=A[1]B[1]+A[2]B[2]*)
(*Isegment = Exp[-dot[\[Lambda][1],z[1->2]]];*)
(*pregenerate2[dz12_]:=pregenerate2[dz12]=SeriesCoefficient[*)
(*D[Isegment,{z[1->2][1],dz12[[1]]},{z[1->2][2],dz12[[2]]}]*)
(*,{z[1->2][1],0,0},{z[1->2][2],0,0}];*)
(*dzList = Tuples[{0,1,2,3,4,5,6,7,8},2];*)
(*Do[Print[dz12];DI\[CapitalDelta][dz12]=pregenerate2[dz12],{dz12,dzList}];*)
(*Save[FileNameJoin[{NotebookDirectory[],"DI\[CapitalDelta]datahh.nb"}],DI\[CapitalDelta]]*)
(**)*)
(**)
(*(*A1 = (z[1->2][1]+z[2->3][1]+z[3->1][1]) \[Lambda][1][1]+(z[1->2][2]+z[2->3][2]+z[3->1][2]) \[Lambda][1][2];*)
(*A2 = (z[1->2][1]+z[2->3][1]+z[3->1][1]) \[Lambda][2][1]+(z[1->2][2]+z[2->3][2]+z[3->1][2]) \[Lambda][2][2];*)
(*A3 = (z[1->2][1]+z[2->3][1]+z[3->1][1]) \[Lambda][3][1]+(z[1->2][2]+z[2->3][2]+z[3->1][2]) \[Lambda][3][2];*)
(*Itriangle = (-\[Pi]^-2)(wedge[\[Lambda][2],\[Lambda][3]]/(A2 A3)Exp[dot[z[1->2], \[Lambda][2]]+dot[z[1->3], \[Lambda][3]]]+wedge[\[Lambda][3],\[Lambda][1]]/(A3 A1)Exp[-dot[z[1->2], \[Lambda][1]]+dot[z[2->3], \[Lambda][3]]]+wedge[\[Lambda][1],\[Lambda][2]]/(A1 A2)Exp[-dot[z[1->3], \[Lambda][1]]-dot[z[2->3], \[Lambda][2]]])/.{z[3->1][i_]:>-z[1->3][i]}/.{\[Lambda][3][i_]:>-(\[Lambda][1][i]+\[Lambda][2][i])};*)*)
(*(*ClearAll[A1,A2,A3]*)*)


(* ::Input:: *)
(*(*SeriesCoefficient[Itriangle*)
(*,{z[1->2][1],0,0},{z[1->2][2],0,0},{z[2->3][1],0,0},{z[2->3][2],0,0},{z[1->3][1],0,0},{z[1->3][2],0,0}]*)*)


(* ::Input:: *)
(*(*ClearAll[J]*)
(*SetDirectory[NotebookDirectory[]]*)
(*J=<<"./bitriangleAns4.m";*)
(*Ibitriangle=Exp[*)
(*-dot[z[1->4], \[Lambda][1]]*)
(*+ dot[z[1->3], \[Lambda][2]]-dot[z[1->4], \[Lambda][2]]-dot[z[2->3], \[Lambda][2]]*)
(*+dot[z[1->3], \[Lambda][3]]-dot[z[1->4], \[Lambda][3]]]J/.{tritriCo->1}/.{\[Lambda][v_,i_]:>\[Lambda][v][i]} /.{ZHold[1,i_]:>z[1->3][i]-z[1->4][i]+z[3->4][i],ZHold[2,i_]:>z[1->3][i]-z[1->4][i]-z[2->3][i]+z[2->4][i]} ;*)
(*ClearAll[J]*)*)


(* ::Input:: *)
(**)


(* ::Subsubsection:: *)
(*pregenerate*)


(* ::Input:: *)
(*(*it turns out the most time consuming process is to calculate derivative of I\[CapitalDelta], so we calculate here first*)*)
(*(*ClearAll[pregenerate3,pregenerate4]*)
(*pregenerate3[dz12_,dz13_,dz23_]:=pregenerate3[dz12,dz13,dz23]=SeriesCoefficient[*)
(*D[Itriangle,{z[1->2][1],dz12[[1]]},{z[1->2][2],dz12[[2]]},{z[1->3][1],dz13[[1]]},{z[1->3][2],dz13[[2]]},{z[2->3][1],dz23[[1]]},{z[2->3][2],dz23[[2]]}]*)
(*,{z[1->2][1],0,0},{z[1->2][2],0,0},{z[2->3][1],0,0},{z[2->3][2],0,0},{z[1->3][1],0,0},{z[1->3][2],0,0}];*)
(*pregenerate4[dz14_,dz13_,dz23_,dz24_,dz34_]:=pregenerate4[dz14,dz13,dz23,dz24,dz34]=*)
(*(D[Ibitriangle,*)
(*{z[1->4][1],dz14[[1]]},{z[1->4][2],dz14[[2]]},*)
(*{z[1->3][1],dz13[[1]]},{z[1->3][2],dz13[[2]]},*)
(*{z[2->3][1],dz23[[1]]},{z[2->3][2],dz23[[2]]},*)
(*{z[2->4][1],dz24[[1]]},{z[2->4][2],dz24[[2]]},*)
(*{z[3->4][1],dz34[[1]]},{z[3->4][2],dz34[[2]]}*)
(*]/.{z[1->4][i_]->0,z[1->3][i_]:>0,z[2->3][i_]:>0,z[2->4][i_]:>0,z[3->4][i_]:>0});*)
(*DI\[CapitalDelta][dz14_,dz13_,dz23_,dz24_,dz34_]:=pregenerate4[dz14,dz13,dz23,dz24,dz34];*)*)
(*(*//SeriesCoefficient[#*)
(*,{z[1->4][1],0,0},{z[1->4][2],0,0},{z[2->3][1],0,0},{z[2->3][2],0,0},{z[1->3][1],0,0},{z[1->3][2],0,0},{z[2->4][1],0,0},{z[2->4][2],0,0},{z[3->4][1],0,0},{z[3->4][2],0,0}]&*)*)
(**)
(*(**)
(*ClearAll[DI\[CapitalDelta]];*)
(*dzList = Tuples[{0,1},2];*)
(*Do[Print[dz12,dz13,dz23];DI\[CapitalDelta][dz12,dz13,dz23]=pregenerate[dz12,dz13,dz23],{dz12,dzList},{dz13,dzList},{dz23,dzList}];*)
(*Save[FileNameJoin[{NotebookDirectory[],"DI\[CapitalDelta]data.nb"}],DI\[CapitalDelta]]*)
(**)*)


(* ::Input:: *)
(*(*ClearAll[DI\[CapitalDelta]]*)
(*dzList = Tuples[{0,1,2},2];*)
(*Do[Print[dz14,dz13,dz23,dz24,dz34];DI\[CapitalDelta][dz14,dz13,dz23,dz24,dz34]=pregenerate4[dz14,dz13,dz23,dz24,dz34],{dz14,dzList},{dz13,dzList},{dz23,dzList},{dz24,dzList},{dz34,dzList}]*)
(*Save[FileNameJoin[{NotebookDirectory[],"DI\[CapitalDelta]data_temp.nb"}],DI\[CapitalDelta]]*)*)


(* ::Input:: *)
(*(*ClearAll[DI\[CapitalDelta]]*)
(*SetDirectory[NotebookDirectory[]];*)
(*DI\[CapitalDelta]dataList=NotebookOpen[FileNameJoin[{Directory[],"DI\[CapitalDelta]data.nb"}]];*)
(*SelectionMove[DI\[CapitalDelta]dataList,All,Notebook];*)
(*SelectionEvaluate[DI\[CapitalDelta]dataList];*)
(*NotebookClose[DI\[CapitalDelta]dataList]*)*)


(* ::Subsubsection:: *)
(*plugin I\[CapitalGamma]*)


(* ::Input::Initialization:: *)
ClearAll[d\[Lambda]1,d\[Lambda]2,d\[Lambda]]
d\[Lambda][v_][1] := ( d[1,0][#]+Times[\[Lambda][v][1],#])&
d\[Lambda][v_][2] := ( d[0,1][#]+Times[\[Lambda][v][2],#])&

(*
dzij is 
{i ,j ,{\!\(number\ of\ \(
\*SubscriptBox[\(\[PartialD]\), \(zij[1]\)]\(+number\)\)\ of\ 
\*SubscriptBox[\(\[PartialD]\), \(zij[2]\)]\),   \!\(number\ of\ \(
\*SubscriptBox[\(\[PartialD]\), \(zji[1]\)]\(+number\)\)\ of\ 
\*SubscriptBox[\(\[PartialD]\), \(zji[2]\)]\),{\!\(number\ of\ \(
\*SubscriptBox[\(\[PartialD]\), \(zij[1]\)]\(+number\)\)\ of\ 
\*SubscriptBox[\(\[PartialD]\), \(zji[1]\)]\), \!\(number\ of\ \(
\*SubscriptBox[\(\[PartialD]\), \(zij[2]\)]\(+number\)\)\ of\ 
\*SubscriptBox[\(\[PartialD]\), \(zji[2]\)]\)}}} 
*)

(*
we have (-1) coming from integration by part of the derivative of the second slot. However, we also have the convention 
DI\[CapitalDelta][{m, n}] = (-1)^(m+n)\[Lambda][1][1]^m\[Lambda][1][2]^n
To compensate, we include a factor (-1)^dz12[[3]][[2]] below.
*)
ClearAll[I\[CapitalGamma]tobracket2,I\[CapitalGamma]tobracket3,I\[CapitalGamma]tobracket4]
I\[CapitalGamma]tobracket2[front_,end_,dz12_]:=Block[{coefRules,coef,nMax,niList},
coefRules =CoefficientRules[(-1)^dz12[[3]][[2]] DI\[CapitalDelta][dz12[[3]][[3]]],
{\[Lambda][1][1],\[Lambda][1][2]}];
coef = Association@@coefRules;
niList = Keys[coef];
Sum[coef[ni]NonCommutativeMultiply[
Nest[d\[Lambda][1][1],Nest[d\[Lambda][1][2],front,ni[[2]]],ni[[1]]]//GExpand,
end]//GExpand,
{ni,niList}]
]


I\[CapitalGamma]tobracket3[front_,mid_,end_,dz12_,dz13_,dz23_]:=Block[{coefRules,coef,nMax,niList},
coefRules =CoefficientRules[(-1)^(dz12[[3]][[2]]+dz13[[3]][[2]]+dz23[[3]][[2]]) DI\[CapitalDelta][dz12[[3]][[3]],dz13[[3]][[3]],dz23[[3]][[3]]]
,
{\[Lambda][1][1],\[Lambda][1][2],\[Lambda][2][1],\[Lambda][2][2]}];

coef = Association@@coefRules;
niList = Keys[coef];
Sum[coef[ni]NonCommutativeMultiply[
Nest[d\[Lambda][1][1],Nest[d\[Lambda][1][2],front,ni[[2]]],ni[[1]]]//GExpand,
Nest[d\[Lambda][2][1],Nest[d\[Lambda][2][2],mid,ni[[4]]],ni[[3]]]//GExpand,
end]//GExpand,
{ni,niList}]
]

I\[CapitalGamma]tobracket4[front_,second_,third_,fourth_,dz14_,dz13_,dz23_,dz24_,dz34_]:=Block[{coefRules,coef,nMax,niList},
coefRules =CoefficientRules[(-1)^(dz14[[3]][[2]]+dz13[[3]][[2]]+dz23[[3]][[2]]+dz24[[3]][[2]]+dz34[[3]][[2]]) DI\[CapitalDelta][dz14[[3]][[3]],dz13[[3]][[3]],dz23[[3]][[3]],dz24[[3]][[3]],dz34[[3]][[3]]]
,
{\[Lambda][1][1],\[Lambda][1][2],\[Lambda][2][1],\[Lambda][2][2],\[Lambda][3][1],\[Lambda][3][2]}];

coef = Association@@coefRules;
niList = Keys[coef];
Sum[coef[ni]NonCommutativeMultiply[
Nest[d\[Lambda][1][1],Nest[d\[Lambda][1][2],front,ni[[2]]],ni[[1]]]//GExpand,
Nest[d\[Lambda][2][1],Nest[d\[Lambda][2][2],second,ni[[4]]],ni[[3]]]//GExpand,
Nest[d\[Lambda][3][1],Nest[d\[Lambda][3][2],third,ni[[6]]],ni[[5]]]//GExpand,
fourth]//GExpand,
{ni,niList}]
]
(*it is very easy to write down a general I\[CapitalGamma]tobracket for any number of entries, but I won't do it for now*)
ClearAll[pluginI\[CapitalGamma]2,pluginI\[CapitalGamma]3,pluginI\[CapitalGamma]4,product2,product3,product4]
pluginI\[CapitalGamma]2[exp_] :=exp/.{bracket->I\[CapitalGamma]tobracket2} 
pluginI\[CapitalGamma]3[exp_] :=exp/.{bracket->I\[CapitalGamma]tobracket3} 
pluginI\[CapitalGamma]4[exp_] :=exp/.{bracket->I\[CapitalGamma]tobracket4} 

product2[exp_] :=exp/.{bracket[old__]:>I\[CapitalGamma]tobracket2[old,{1,2,{0,0,{0,0}}}]} 
product3[exp_] :=(exp//wick[#,{1,2}]&//wick[#,{1,3}]&)/.{bracket[old__]:>I\[CapitalGamma]tobracket3[old,{2,3,{0,0,{0,0}}}]} 
product4[exp_] :=(exp//wick[#,{1,4}]&//wick[#,{1,3}]&//wick[#,{2,3}]&//wick[#,{2,4}]&)/.{bracket[old__]:>I\[CapitalGamma]tobracket4[old,{3,4,{0,0,{0,0}}}]} 

product2[i_,j_][exp_] :=exp/.{bracket[old__]:>(-1)^i/Factorial[i] (-1)^j/Factorial[j] I\[CapitalGamma]tobracket2[old,{1,2,{i+j,0,{i,j}}}]} 
product3[i_,j_][exp_] :=(exp//wick[#,{1,2}]&//wick[#,{1,3}]&)/.{bracket[old__]:>(-1)^i/Factorial[i] (-1)^j/Factorial[j] I\[CapitalGamma]tobracket3[old,{2,3,{i+j,0,{i,j}}}]} 


(* ::Input::Initialization:: *)
<<DI\[CapitalDelta]data_function.m;
