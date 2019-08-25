(* ::Package:: *)

(* ::Title:: *)
(*AmpCalc*)


(*:History:*)


(* ::Subsubtitle:: *)
(*Updated on 07.01.2014: the third translated argument list obtained by canceling in xTensorReduce is changed back,  the correct order of m12 and m22 is m22, m12.*)


(* ::Section:: *)
(*Output Setting*)


(* ::Subsubsection::Closed:: *)
(*Auxiliary functions*)


(* The codes FCTBox and FCtotr are copied from FeynCalc.m by Rolf Mertig. The functions are called TBox and totr there. *)
(*---------Beginning of FeynCalc codes---------*)
FCTBox::usage="";
FCTBox[]="\[Null]";
FCTBox[a_]:=FCtotr[a];
FCTBox[a_,b__] := RowBox @ Map[(ToBoxes @@ {#, TraditionalForm})&, {a, b}];

FCtotr::usage="";
FCtotr[Subscript[y_,in__Integer]]:=SubscriptBox[FCtotr[y],RowBox[{in}]];
FCtotr[y_Symbol]:=If[FormatValues[Evaluate[y]]==={},ToString[y],ToBoxes[y,TraditionalForm],y];
FCtotr[y_String]:=y;
FCtotr[y_]:=ToBoxes[y,TraditionalForm]/;Head[y]=!=Symbol;

(* From FeynCalc *)
Unprotect[SuperscriptBox];
SuperscriptBox[FormBox[SubscriptBox[x_,y_],f_],z_] :=
SubsuperscriptBox[x, y, z]
Protect[SuperscriptBox];

Unprotect[SubscriptBox];
SubscriptBox[FormBox[SuperscriptBox[x_,y_],f_],z_] :=
SubsuperscriptBox[x, z, y]
Protect[SubscriptBox];
(*---------End of FeynCalc codes---------*)


(* codes from R.Maeder's book, p .183 *)
xConstantQ[c_Symbol]:=MemberQ[Attributes[c],Constant]
xConstantQ[c_?NumericQ]:=True


(* ::Subsubsection::Closed:: *)
(*momentum*)


momentum/:MakeBoxes[momentum[mom_,lor___],TraditionalForm]/;FreeQ[{Plus,Times},Head[mom]]:=SuperscriptBox[FCTBox[mom],FCTBox[lor]];
momentum/:MakeBoxes[momentum[mom_,lor___],TraditionalForm]/;!FreeQ[{Plus,Times},Head[mom]]:=SuperscriptBox[RowBox[{"(",FCTBox[mom],")"}],FCTBox[lor]];


(* ::Subsubsection::Closed:: *)
(*scalarproduct*)


SetAttributes[scalarproduct,Orderless];
scalarproduct/:MakeBoxes[scalarproduct[x_,y_],TraditionalForm]/;FreeQ[{Plus,Times},Head[x]]&&FreeQ[{Plus,Times},Head[y]]:=RowBox[{FCTBox[x],"\[CenterDot]", FCTBox[y]}];
scalarproduct/:MakeBoxes[scalarproduct[x_,y_],TraditionalForm]/;!FreeQ[{Plus,Times},Head[x]]&&FreeQ[{Plus,Times},Head[y]]:=RowBox[{"(",FCTBox[x],")",".",FCTBox[y]}];
scalarproduct/:MakeBoxes[scalarproduct[x_,y_],TraditionalForm]/;FreeQ[{Plus,Times},Head[x]]&&!FreeQ[{Plus,Times},Head[y]]:=RowBox[{FCTBox[x],".","(",FCTBox[y],")"}];
scalarproduct/:MakeBoxes[scalarproduct[x_,y_],TraditionalForm]/;!FreeQ[{Plus,Times},Head[x]]&&!FreeQ[{Plus,Times},Head[y]]:=RowBox[{"(",FCTBox[x],")",".","(",FCTBox[y],")"}];
scalarproduct/:MakeBoxes[scalarproduct[x_],TraditionalForm]/;FreeQ[{Plus,Times},Head[x]] :=SuperscriptBox[FCTBox[x],"2"];
scalarproduct/:MakeBoxes[scalarproduct[x_],TraditionalForm]/;!FreeQ[{Plus,Times},Head[x]] :=SuperscriptBox[RowBox[{"(",FCTBox[x],")"}],"2"];
scalarproduct[x_,x_]:=scalarproduct[x];
(*scalarproduct[x_]:=scalarproduct[x,x];*)


(* ::Subsubsection::Closed:: *)
(*metrictensor, Levicivita*)


SetAttributes[metrictensor,Orderless];
metrictensor/:MakeBoxes[metrictensor[lor1_,lor2_] ,TraditionalForm] :=SuperscriptBox["g",FCTBox[lor1,lor2]];
metrictensor[lor_,lor_]:=D;

Levicivita\[Epsilon]/:MakeBoxes[Levicivita\[Epsilon][lor___] ,TraditionalForm] := SubscriptBox["\[Epsilon]", FCTBox[Sequence@@({lor}/.momentum[p_]:>p)]]


(* ::Subsubsection::Closed:: *)
(*Diracgamma, Diracgamma5, Diracsigma, Diracslash, Diracspinor*)


Diracgamma/:MakeBoxes[Diracgamma[lor_],TraditionalForm]:=SuperscriptBox["\[Gamma]",FCTBox[lor]];
Diracgamma5/:MakeBoxes[Diracgamma5[___],TraditionalForm]:=SuperscriptBox["\[Gamma]",FCTBox[5]];
Diracsigma/: MakeBoxes[Diracsigma[lor1_,lor2_],TraditionalForm]:=SuperscriptBox["\[Sigma]",FCTBox[lor1,lor2]];

Diracslash/:MakeBoxes[Diracslash[mom_],TraditionalForm]/;FreeQ[{Plus,Times},Head[mom]]:=RowBox[{"(",FCTBox[mom],".","\[Gamma]",")"}];
Diracslash/:MakeBoxes[Diracslash[mom_],TraditionalForm]/;!FreeQ[{Plus,Times},Head[mom]]:=RowBox[{"(","(",FCTBox[mom],")",".","\[Gamma]",")"}];

Diracspinor/:MakeBoxes[Diracspinor[s_:1,p_,m_],TraditionalForm]:=RowBox[{If[s===-1,"v","u"],"(",FCTBox[p],",",FCTBox[m],")"}];
MakeBoxes[Dot[Diracspinor[s1_:1,p1_,m1_],y__,Diracspinor[s2_:1,p2_,m2_]],TraditionalForm]:=RowBox[{OverscriptBox[RowBox[{If[s1===-1,"v","u"],"(",FCTBox[p1],",",FCTBox[m1],")"}],"_"],".",FCTBox[Dot[y]],".",RowBox[{If[s2===-1,"v","u"],"(",FCTBox[p2],",",FCTBox[m2],")"}]}];
MakeBoxes[Dot[Diracspinor[s1_:1,p1_,m1_],Diracspinor[s2_:1,p2_,m2_]],TraditionalForm]:=RowBox[{OverscriptBox[RowBox[{If[s1===-1,"v","u"],"(",FCTBox[p1],",",FCTBox[m1],")"}],"_"],".",RowBox[{If[s2===-1,"v","u"],"(",FCTBox[p2],",",FCTBox[m2],")"}]}];
DiracspinorU[p_,m_]:=Diracspinor[1,p,m];
DiracspinorV[p_,m_]:=Diracspinor[-1,p,m];


(* ::Subsubsection::Closed:: *)
(*FeynAmplDenominator, propagator*)


FeynAmplDenominator/:MakeBoxes[FeynAmplDenominator[x__List],TraditionalForm]:=FractionBox[1,RowBox[If[#[[2]]=!=0,RowBox[{"(",FCTBox[#[[1]]//scalarproduct],"-",FCTBox[#[[2]]^2],")"}],FCTBox[#[[1]]//scalarproduct]]&/@{x}]];

propagator/:MakeBoxes[propagator[p_,m_],TraditionalForm]:=FractionBox[1,If[m=!=0,RowBox[{FCTBox[p//scalarproduct],"-",FCTBox[m^2]}],FCTBox[p^2]]];


(* ::Subsubsection::Closed:: *)
(*Paulitau, KroneckerDelta2, Levicivita2*)


Paulitau/:MakeBoxes[Paulitau[index_],TraditionalForm]:=SubscriptBox["\[Tau]",FCTBox[index]];
paulitau/:MakeBoxes[paulitau,TraditionalForm]:="\[Tau]";

SetAttributes[KroneckerDelta2,Orderless];
KroneckerDelta2/:MakeBoxes[KroneckerDelta2[i_,j_],TraditionalForm]:=SubscriptBox["\[Delta]",RowBox[{FCTBox[i],FCTBox[j]}]]

Levicivita2/:MakeBoxes[Levicivita2[i_,j_,k_],TraditionalForm]:=SubscriptBox["\[Epsilon]",RowBox[{FCTBox[i],FCTBox[j],FCTBox[k]}]]


(* ::Subsubsection::Closed:: *)
(*Dotgamma, Dotisospin*)


Dotgamma/:MakeBoxes[Dotgamma[x__],TraditionalForm]:=FCTBox[Dot[x]];
Dotisospin/:MakeBoxes[Dotisospin[x__],TraditionalForm]:=FCTBox[Dot[x]];


(* ::Subsubsection::Closed:: *)
(*Loop functions*)


LFA0/:MakeBoxes[LFA0,TraditionalForm]:=SubscriptBox["A","0"]
LFA0i/:MakeBoxes[LFA0i,TraditionalForm]:=SubscriptBox["A","0i"]
LFB0/:MakeBoxes[LFB0,TraditionalForm]:=SubscriptBox["B","0"]
LFB0i/:MakeBoxes[LFB0i,TraditionalForm]:=SubscriptBox["B","0i"]
DLFB0/:MakeBoxes[DLFB0,TraditionalForm]:=SubsuperscriptBox["B","0","\[Prime]"]

LFC0/:MakeBoxes[LFC0,TraditionalForm]:=SubscriptBox["C","0"]
LFC0i/:MakeBoxes[LFC0i,TraditionalForm]:=SubscriptBox["C","0i"]
LFD0/:MakeBoxes[LFD0,TraditionalForm]:=SubscriptBox["D","0"]
LFD0i/:MakeBoxes[LFD0i,TraditionalForm]:=SubscriptBox["D","0i"]

LFE0/:MakeBoxes[LFE0,TraditionalForm]:=SubscriptBox["E","0"]
LFE0i/:MakeBoxes[LFE0i,TraditionalForm]:=SubscriptBox["E","0i"]

UVepsR/:MakeBoxes[UVepsR,TraditionalForm]:="R";
$mu/:MakeBoxes[$mu,TraditionalForm]:=SubscriptBox["\[Mu]","d"];
$HIGHORDER/:MakeBoxes[$HIGHORDER,TraditionalForm]:="H";



(* ::Section:: *)
(*Functions*)


(* ::Subsubsection::Closed:: *)
(*xWrite, xRead, xSave, xLoad*)


xWrite[exp_,filename_String,fileaddress_String:NotebookDirectory[]]:=Module[{xL},
xL=OpenWrite[fileaddress<>filename];
Write[xL,exp];
Close[xL];
]

xRead[filename_String,fileaddress_String:NotebookDirectory[]]:=Module[{xL,xxL},
xL=OpenRead[fileaddress<>filename];
xxL=Read[xL];
Close[xL];xxL]


xSave::usage="xSave[\"filename1\",\"filename2\",...,\"directory\"] saves values and definitions for all symbols whose names match the string patterns filename1, filename2,..., to \"directory\".";


xSave[filename1_String,filenames___,directory_String]:=Module[
{save},
save[name_String,dir_String]:=Put[Symbol[name],dir<>name<>".dat"];
save[name1_String,name2___,dir_String]:=Module[{},save[name1,dir];save[name2,dir];];
save[filename1,filenames,directory];
];


xLoad::usage="xLoad[name1,name2,...,\"directory\"] gets values for all the symbols name1,name2,...from the files whose names correspond to name1, name2,..., respectively, from \"directory\".";


xLoad[name_Symbol,dir_String]:=Module[{},name=Get[dir<>ToString[name]<>".dat"];];
xLoad[name1_,name2__,dir_String]:=xLoad[#,dir]&/@{name1,name2}


(* ::Subsubsection::Closed:: *)
(*xPrintTime*)


$xPrintTimeMessageOn=False;
SetAttributes[xPrintTime,HoldAll]
Options[print]={messageOn->True};
print[exp___,OptionsPattern[]]:=If[OptionValue[messageOn],Print[exp],Return[]]
xPrintTime[exp_]:=With[{timing=Timing[exp]},print["Time used: ", timing[[1]], " seconds" ];timing[[2]]];
xPrintTime[exp_,message_]:=If[$xPrintTimeMessageOn,(print[message<>"..."];xPrintTime[exp]),exp]


(* ::Subsubsection::Closed:: *)
(*xDrop*)


(* ::Input:: *)
(**)


xDrop[a_,x_Integer]:=Drop[a,{x}];
xDrop[a_,n_List]:=Module[{nsorted,max,list},
If[n==={},Return[a]];
nsorted=n//Sort;max=Length[nsorted];list=a;
Do[list=Drop[list,{nsorted[[max-i+1]]}],{i,1,max}];
Return[list];
];


(* ::Subsubsection::Closed:: *)
(*xDotSimplify*)


(* ::Input:: *)
(**)


Options[xDotSimplify]={SeparateDiracIsospin->True};
xDotSimplify[exp0_,OptionsPattern[]]:=Module[
{dot,dot0,exp,dotgamma,dotisospin},
dot[x___,y_Plus,z___]:=dot[x,#,z]&/@y;
dot[x___,y_,z___]/;FreeQ[y,Diracslash|Diracgamma|Diracgamma5|Diracspinor|Paulitau]:=y*dot[x,z];
dot[x___,y0_*y_,z___]/;FreeQ[y0,Diracslash|Diracgamma|Diracgamma5|Diracspinor|Paulitau]:=y0*dot[x,y,z];
dot[x___,0,z___]:=0;
dot0[x___,dot0[y___],z___]:=dot0[x,y,z];
(*dot0[x___,y0_*dot0[y___],z___]:=dot0[x,y0,y,z];(*in the case that y0 and y are in different spaces*)*)
exp=exp0//xExpandPair;(*26.11.13*)
If[OptionValue[SeparateDiracIsospin],
dotgamma[x___,y_,z___]/;FreeQ[y,Diracslash|Diracgamma|Diracgamma5|Diracspinor]:=dotgamma[x,z];
dotgamma[x___,y_*Paulitau[y0_],z___]:=dotgamma[x,y,z];
(*dotgamma[x___,y_*Levicivita2[a___,Paulitau[y0_],b___],z___]:=dotgamma[x,y,z];(*11,12,13*)*)
dotisospin[x___,y_,z___]/;FreeQ[y,Paulitau]:=dotisospin[x,z];
dotisospin[x___,y_*y0_,z___]/;FreeQ[y0,Paulitau]:=dotisospin[x,y,z];
exp/.{Dot->dot,Dotgamma->dot,Dotisospin->dot}/.dot->dot0/.dot0[x___]:>dotgamma[x]*dotisospin[x]/.{dotgamma->Dotgamma,dotisospin->Dotisospin}/.{Dotgamma[]->1,Dotgamma[x_]:>x,Dotisospin[]->1,Dotisospin[x_]:>x}//Expand
,
exp/.Dot->dot/.dot->dot0/.dot0->Dot//Expand
]
];


(* ::Subsubsection::Closed:: *)
(*xDiracSimplify*)


(* ::Input:: *)
(**)


Options[xDiracSimplify]={ShiftGamma5->True,SimplifyGamma->True,SimplifyMomentum->True,SimplifySpinor->True};
xDiracSimplify[exp0_,OptionsPattern[]]:=Module[
{Gamma5Simpliy,SameLorentz,SameMomentum,diracEquation,exp,exp1,exp2,exp3,exp4,uu},
exp=exp0//xDotSimplify;(*16.11.13*)
If[FreeQ[exp,Diracgamma|Diracgamma5]|Diracslash,Return[exp//xExpandPair]];
(*1.shift all of the \[Gamma]^5 s to the right side, and simlify with (\[Gamma]^5)^2=1.*)
If[OptionValue[ShiftGamma5],
Gamma5Simpliy[x___,a_,a_,y___]/;Head[a]===Diracgamma5:=Gamma5Simpliy[x,y];
Gamma5Simpliy[x___,a_,y1_,y2___]/;Head[a]===Diracgamma5&&Head[y1]===Diracgamma:=-Gamma5Simpliy[x,y1,a,y2];
Gamma5Simpliy[x___,a_,y1_,y2___]/;Head[a]===Diracgamma5&&Head[y1]===Diracslash:=-Gamma5Simpliy[x,y1,a,y2];
exp1=exp/.Dotgamma->Gamma5Simpliy/.Gamma5Simpliy->Dotgamma/.{Dotgamma[]->1,Dotgamma[x_]:>x};,
exp1=exp;];
(*2.simplify the \[Gamma]s with same lorentz indices*)
If[OptionValue[SimplifyGamma],
SameLorentz[x___,a_,a_,y___]/;Head[a]===Diracgamma:=metrictensor[a[[1]],a[[1]]]*SameLorentz[x,y];
SameLorentz[x___,a_,y1_,y2___,a_,z___]/;Head[a]===Diracgamma&&Head[y1]===Diracgamma&&Length[(uu=Cases[{y1,y2},_Diracgamma])]===Length[Union[uu]]:=2SameLorentz[x,y2,y1,z]-SameLorentz[x,y1,a,y2,a,z];
SameLorentz[x___,a_,y1_,y2___,a_,z___]/;Head[a]===Diracgamma&&Head[y1]===Diracslash&&Length[(uu=Cases[{y1,y2},_Diracgamma])]===Length[Union[uu]]:=2SameLorentz[x,y2,y1,z]-SameLorentz[x,y1,a,y2,a,z];
exp2=exp1/.Dotgamma->SameLorentz/.SameLorentz->Dotgamma/.{Dotgamma[]->1,Dotgamma[x_]:>x};,
exp2=exp1;];
(*3.simpliy the momenta in Dotgamma 15.11.2013*)
If[OptionValue[SimplifyMomentum],
SameMomentum[x___,a_,a_,y___]/;Head[a]===Diracslash:=scalarproduct[a[[1]],a[[1]]]*SameMomentum[x,y];
(*Important!!! the follwing Codes are promoted to deal with two and more pairs of momentum of the same. 16.11.13*)
SameMomentum[x___,a_,y1_,y2___,a_,z___]/;Head[a]===Diracslash&&Head[y1]===Diracgamma&&Length[(uu=Cases[{y1,y2},_Diracslash])]===Length[Union[uu]]:=2momentum[a[[1]],y1[[1]]]*SameMomentum[x,y2,a,z]-SameMomentum[x,y1,a,y2,a,z];
SameMomentum[x___,a_,y1_,y2___,a_,z___]/;Head[a]===Diracslash&&Head[y1]===Diracslash&&Length[(uu=Cases[{y1,y2},_Diracslash])]===Length[Union[uu]]:=2scalarproduct[a[[1]],y1[[1]]]*SameMomentum[x,y2,a,z]-SameMomentum[x,y1,a,y2,a,z];
exp3=exp2/.Dotgamma->SameMomentum/.SameMomentum->Dotgamma/.{Dotgamma[]->1,Dotgamma[x_]:>x};,
exp3=exp2;];
(*4.simplify by using Dirac Equation. 17.11.13*)
If[OptionValue[SimplifySpinor],
diracEquation[Diracspinor[a_,xp_,xm_],Diracslash[xp_],x___]:=a*xm*diracEquation[Diracspinor[a,xp,xm],x];
diracEquation[x___,Diracslash[xp_],Diracspinor[a_,xp_,xm_]]:=a*xm*diracEquation[x,Diracspinor[a,xp,xm]];

diracEquation[Diracspinor[a_,xp_,xm_],x___,y_,Diracslash[xp_],z___]/;Head[y]===Diracgamma:=2 momentum[xp,y[[1]]]*diracEquation[Diracspinor[a,xp,xm],x,z]-diracEquation[Diracspinor[a,xp,xm],x,Diracslash[xp],y,z];
diracEquation[Diracspinor[a_,xp_,xm_],x___,y_,Diracslash[xp_],z___]/;Head[y]===Diracslash:=2 scalarproduct[xp,y[[1]]]*diracEquation[Diracspinor[a,xp,xm],x,z]-diracEquation[Diracspinor[a,xp,xm],x,Diracslash[xp],y,z];

diracEquation[x___,Diracslash[xp_],y_,z___,Diracspinor[a_,xp_,xm_]]/;Head[y]===Diracgamma:=2 momentum[xp,y[[1]]]*diracEquation[x,z,Diracspinor[a,xp,xm]]-diracEquation[x,y,Diracslash[xp],z,Diracspinor[a,xp,xm]];
diracEquation[x___,Diracslash[xp_],y_,z___,Diracspinor[a_,xp_,xm_]]/;Head[y]===Diracslash:=2 scalarproduct[xp,y[[1]]]*diracEquation[x,z,Diracspinor[a,xp,xm]]-diracEquation[x,y,Diracslash[xp],z,Diracspinor[a,xp,xm]];

diracEquation[x___,Diracslash[xp_],y_,z___,Diracspinor[a_,xp_,xm_]]/;Head[y]===Diracgamma5:=-diracEquation[x,y,Diracslash[xp],z,Diracspinor[a,xp,xm]];
exp4=exp3/.Dotgamma->diracEquation/.diracEquation->Dotgamma/.{Dotgamma[]->1,Dotgamma[x_]:>x},
exp4=exp3;];
Return[exp4];
];


(* ::Subsubsection::Closed:: *)
(*xDiracContract*)


xDiracContract0[exp_]:=Module[{mom,met,gamma,eps,dotgamma,rule,rulereversed,coe1,coe2,coe3},
(*1.Rules for contractions of Metric Tensor g^(\[Mu]\[Vee]) with quantities involving Lorentz indice*)
SetAttributes[met,Orderless];
met/:met[x_,y_]met[x_,z_]:=met[y,z];
met/:met[x_,y_]^2:=met[x,x];
met/:met[x_,y_]eps[a_]/;!FreeQ[{a},x]&&!FreeQ[{a},y]:=0;
met/:met[x_,y_]eps[a_]/;!FreeQ[{a},x]&&FreeQ[{a},y]:=(eps[a]/.x:>y);
met/:met[x_,y_]gamma[y_]:=gamma[x];
met/:met[x_,y_]dotgamma[a___,gamma[y_],b___]:=dotgamma[a,gamma[x],b];
met/:met[x_,y_]mom[a_,y_]:=mom[a,x];
(*2.Rules for momentum contractions*)
mom/:mom[x_,z_]mom[y_,z_]:=scalarproduct[x,y];
mom/:mom[x_,y_]^2:=scalarproduct[x];
mom/:mom[x_,y_]gamma[y_]:=Diracslash[x];
mom/:mom[x_,y_] dotgamma[a___,gamma[y_],b___]:=dotgamma[a,Diracslash[x],b];
(*3.*)
rule={momentum->mom,metrictensor->met,Diracgamma->gamma,Levicivita\[Epsilon]->eps,Dotgamma->dotgamma};
rulereversed=Reverse/@rule;
{coe1,coe2}=xSeparate[exp,momentum,metrictensor,Levicivita\[Epsilon],Diracgamma,Dotgamma];(*This sentence of codes wastes a lot of time*)
coe3=(coe2/.rule)/.rulereversed;
Return[coe1.coe3]];


xDiracContract[exp_]:=Module[{mom,met,gamma,eps,dotgamma,rule,rulereversed},
(*1.Rules for contractions of Metric Tensor g^(\[Mu]\[Vee]) with quantities involving Lorentz indice*)
SetAttributes[met,Orderless];
met/:met[x_,y_]met[x_,z_]:=met[y,z];
met/:met[x_,y_]^2:=met[x,x];
met/:met[x_,y_]eps[a_]/;!FreeQ[{a},x]&&!FreeQ[{a},y]:=0;
met/:met[x_,y_]eps[a_]/;!FreeQ[{a},x]&&FreeQ[{a},y]:=(eps[a]/.x:>y);
met/:met[x_,y_]gamma[y_]:=gamma[x];
met/:met[x_,y_]dotgamma[a___,gamma[y_],b___]:=dotgamma[a,gamma[x],b];
met/:met[x_,y_]mom[a_,y_]:=mom[a,x];
(*2.Rules for momentum contractions*)
mom/:mom[x_,z_]mom[y_,z_]:=scalarproduct[x,y];
mom/:mom[x_,y_]^2:=scalarproduct[x];
mom/:mom[x_,y_]gamma[y_]:=Diracslash[x];
mom/:mom[x_,y_] dotgamma[a___,gamma[y_],b___]:=dotgamma[a,Diracslash[x],b];
(*3.*)
rule={momentum->mom,metrictensor->met,Diracgamma->gamma,Levicivita\[Epsilon]->eps,Dotgamma->dotgamma};
rulereversed=Reverse/@rule;
(exp/.rule//Expand)/.rulereversed//Expand
];


(* ::Subsubsection::Closed:: *)
(*xSeparate*)


xSeparate[exp_,head__]:=Module[
{var,coe,multi,res},
If[Head[exp]===List,Return[Table[xSeparate[exp[[i]],head],{i,1,Length[exp]}]]];
(*notice that Variables looks for variables only inside sums,products,and rational powers*)
var=Select[Variables[exp],!FreeQ[#,Alternatives[head]]&]//Sort;
If[Length[var]===0,Return[{{exp},{1}}]];
(*The first element of coe is irrelevant of var*)
coe=CoefficientArrays[exp,var];
multi[{v_}]:=var[[v]];
multi[{v1_,vn__}]:=var[[v1]]multi[{vn}];
res=Table[Drop[coe[[i]]//ArrayRules,-1],{i,2,Length[coe]}]/.(x_->y_):>{multi[x],y};
If[Length[coe]>0&&coe[[1]]=!=0,res=Prepend[res,{{1,coe[[1]]}}]];
res=Flatten[res,1];
res=SortBy[res,First];
res={res[[All,2]],res[[All,1]]};
Return[res];
];


(* ::Subsubsection::Closed:: *)
(*xSU2Simplify*)


xSU2Simplify[expp_]:=Module[{dot,dot0,tau,xKroneckerDelta,xLevicivita,ik,exp,exp0,rule,rulereversed},
exp=expp//xDotSimplify//Expand;
If[Head[exp]===Plus,Return[xSU2Simplify/@exp]];(*Add on 10.01.2014*)
(*1.dot definitions*)
dot[a___,b_Plus,c___]:=dot[a,#,c]&/@b;
dot[a___,b0_*b_,c___]/;FreeQ[b0,tau]:=b0*dot[a,b,c];
dot[a___,0,c___]:=0;
dot[a___,b0_,c___]/;FreeQ[b0,tau]:=b0*dot[a,c];
dot[a___,b_,c_,d___]:=dot[a,dot[b,c]//Expand,d]//Expand;
(*2.KroneckerDelta*)
Attributes[xKroneckerDelta]={Orderless};
(*xKroneckerDelta/:xKroneckerDelta[i_, j_]exp0_:=(exp0/.i-> j)/;!FreeQ[exp0,i];*)(*waste plenty of time*)
xKroneckerDelta/:xKroneckerDelta[i_, j_]xLevicivita[var__]/;!FreeQ[{var},i]:=xLevicivita[var]/.i->j;
xKroneckerDelta/:xKroneckerDelta[i_, j_]tau[i_]:=tau[j];
(*xKroneckerDelta/:xKroneckerDelta[i_, j_]dot[a___,tau[i_],b___]:=dot[a,tau[j],b];*)
xKroneckerDelta/:xKroneckerDelta[i_, j_]xKroneckerDelta[j_,k_]:=xKroneckerDelta[i,k];(*the above added on 11.12.13*)
xKroneckerDelta/:xKroneckerDelta[i_, j_]^2:=xKroneckerDelta[i,i];
xKroneckerDelta/:xKroneckerDelta[i_, i_]/;!NumberQ[i]:=3;
(*3.Levicivita*)
xLevicivita/:xLevicivita[var1__] xLevicivita[var2__]:=Module[{commonIndices,rest1,rest2,s1,s2,ex,from},
commonIndices=Intersection@@(Select[#1,Function[y,!NumberQ[y]]]&)/@{{var1},{var2}};
rest1=Complement[{var1},commonIndices];
rest2=Complement[{var2},commonIndices];
s1=Signature[{var1}]/Signature[Join[commonIndices,rest1]];
s2=Signature[{var2}]/Signature[Join[commonIndices,rest2]];
ex=(({rest1,#1,Signature[#1]}&)/@Permutations[rest2])/Signature[rest2];from=Plus@@Apply[Times,({#1[[3]],Thread[xKroneckerDelta[#1[[1]],#1[[2]]]]}&)/@ex,2];
Length[commonIndices]! s1 s2 from];
xLevicivita/:xLevicivita[var1__] ^2:=3!;
xLevicivita[j_,i_,i_]:=0;
xLevicivita[i_,j_,i_]:=0;
xLevicivita[i_,i_,j_]:=0;
(*4.Rules for simplification: pauli algebra*)
tau/:dot[tau[0],tau[0]]:=tau[0];
tau/:dot[tau[0],tau[ii_]]:=tau[ii];
tau/:dot[tau[ii_],tau[0]]:=tau[ii];
tau/:dot[tau[ii_],tau[ij_]]:=xKroneckerDelta[ii,ij]tau[0]+I*xLevicivita[ii,ij,ik=Unique[ik]]tau[ik];
(*5.Simplify exp*)
rule={Dotisospin->dot,Paulitau->tau,KroneckerDelta2->xKroneckerDelta,Levicivita2->xLevicivita};
rulereversed=Reverse/@rule;
Expand[exp/.rule]/.{tau[0]->1,HoldPattern[xLevicivita[a___,b_,c___]tau[b_]]:>xLevicivita[a,paulitau,c]}/.rulereversed//xUniqueLevicivita2
]



(* ::Subsubsection::Closed:: *)
(*xUniqueLevicivita2*)


(* ::Input:: *)
(**)


xUniqueLevicivita2[exp_]:=Module[
{LC2},
If[FreeQ[exp,Levicivita2],Return[exp]];
LC2[index__]:=Signature[{index}]*Levicivita2[Sequence@@Sort[{index}]];
exp/.Levicivita2->LC2
];


(* ::Subsubsection::Closed:: *)
(*xExpandPair*)


(* ::Input:: *)
(**)


xExpandPair[exp_]:=Module[{momExpand,spExpand,slExpand},
(*Codes from Feng-Kun Guo's AmplCalc*)
(*1.Set Expand rules for momExpand*)
a:momExpand[_Plus,___]:=Thread[Unevaluated[a],Plus,1];
momExpand[a_?xConstantQ b_,x___]:=a momExpand[b,x];
momExpand[0,x___]:=0;
(*End of Guo's AmplCalc*)
(*2.Set Expand rules for spExpand*)
spExpand[a_?xConstantQ p1_, p2_]:=a spExpand[p1,p2];
spExpand[ p1_, a_?xConstantQ p2_]:=a spExpand[p1,p2];
spExpand[0,p_]:=0;
spExpand[p_,0_]:=0;
(*3.Ser Expand rules for slExpand 25.11.2013*)
a:slExpand[_Plus,___]:=Thread[Unevaluated[a],Plus,1];
slExpand[a_?xConstantQ b_]:=a slExpand[b];
slExpand[0]:=0;
(*4.Apply Expand rules to exp*)
exp/.{momentum[x__]:>momExpand[Sequence@@Expand[{x}]],scalarproduct[x_]:>Distribute@spExpand[Sequence@@Expand[{x,x}]],scalarproduct[x_,y_]:>Distribute@spExpand[Sequence@@Expand[{x,y}]],Diracslash[x__]:>slExpand[Sequence@@Expand[{x}]]}/.{momExpand->momentum,spExpand->scalarproduct,slExpand->Diracslash}
];


(* ::Subsubsection::Closed:: *)
(*xClassifyFAD*)


xClassifyFAD[exp_]:=Module[{fad,pro,fadd,fad3,fad3sort},
fad[x___,y_?(FreeQ[#,k]&),z___]:=fad[x,z]pro[Sequence@@y];
fadd=exp/.FeynAmplDenominator->fad/.{fad->FeynAmplDenominator,pro->propagator}//.FeynAmplDenominator[x___]FeynAmplDenominator[y___]:>FeynAmplDenominator[x,y]/.FeynAmplDenominator[]->1;
(*fad[x___,y_?(FreeQ[#,k]&),z___]:=fad[x,z]*1/(scalarproduct[y[[1]]]-y[[2]]^2)//xExpandPair;
fadd=exp/.FeynAmplDenominator->fad/.{fad->FeynAmplDenominator}//.FeynAmplDenominator[x___]FeynAmplDenominator[y___]:>FeynAmplDenominator[x,y]/.FeynAmplDenominator[]->1;*)

fad3=Cases[{fadd},_FeynAmplDenominator,Infinity]//Union;
fad3sort=Table[SortBy[fad3[[i]],First]//Simplify,{i,Length[fad3]}];
fadd/.Thread[fad3->fad3sort]
];


(* ::Subsubsection::Closed:: *)
(*xFADReduce*)


(* ::Input:: *)
(**)


xFADReduce[exp_]:=Module[
{fadlist,fadlistReduced},
If[FreeQ[exp,FeynAmplDenominator],Return[exp]];
fadlist=Cases[{exp},_FeynAmplDenominator,Infinity]//Union;
fadlistReduced=Expand[xReduceFAD/@fadlist]/.FeynAmplDenominator[]:>1//.FeynAmplDenominator[x___] FeynAmplDenominator[y___]:>FeynAmplDenominator[x,y]/.FeynAmplDenominator[z___]:>Map[Simplify,SortBy[FeynAmplDenominator[z],First],Infinity];
exp/.Thread[fadlist->fadlistReduced]
];


xReduceFAD[exp_FeynAmplDenominator]:=Module[
{denlist,d,denshort,position,qsp,const,reducedmatrix,\[Alpha],\[Alpha]0,c,densimp,Fadlist,posi,i,densimp2,Fadlist2,non0co,temp},
(*1.Case selection rules*)
If[Length[exp]===1,Return[exp]];
If[FreeQ[exp,k],Return[exp]];
(*2.Elements to be dealt with*)
exp=Map[Simplify,exp,Infinity];
denlist=Table[scalarproduct[exp[[i,1]]]-exp[[i,2]]^2,{i,Length[exp]}]//xExpandPair//Simplify;
denshort=denlist//Union;
position=Table[Position[d/@denlist,d[denshort[[i]]]]//Flatten,{i,Length[denshort]}];
qsp=Select[denshort//Variables,!FreeQ[#,k]&]//Sort;
(*3.Using k related sp[k], sp[k,_] as basis, then find whether the first k related element in FAD can be expressed by the following k related elments. If can, then simplification will take place.*)
{const,reducedmatrix}={#[[1]],#[[2]]//Transpose}&@Normal[CoefficientArrays[denshort,qsp]];
\[Alpha][own_,co_,const_]:=own-co.const;
If[MatrixRank[reducedmatrix]===MatrixRank[temp=Drop[#,{1}]&/@reducedmatrix],
\[Alpha]0=LinearSolve[temp,reducedmatrix[[All,1]]];
c=\[Alpha][const[[1]],\[Alpha]0,Drop[const,{1}]]//Factor;
If[c=!=0,
(*4. (N1-\[Alpha]0.N)/c=1, where Ni is the propagator denominator, such as k^2-m^2. In the numerator of this equation, the k related elements are cancelled to zero, so it is divided by c to nomalize it to 1.*)
densimp=(1/c)Prepend[-\[Alpha]0,1].Table[Drop[exp,{position[[i,1]]}],{i,Length[denshort]}];
Fadlist=Cases[{densimp},_FeynAmplDenominator,Infinity]//Union;
Return[densimp/.Thread[Fadlist->xReduceFAD/@Fadlist]]
,
For[i=1,!i>Length[\[Alpha]0],i++,
If[\[Alpha]0[[i]]=!=0,non0co=\[Alpha]0[[i]];
posi=i;
Break[]
];
];
(*5. However, it exists the case that the k non-related parts are cancelled too. In this case, take (N1-\[Alpha]0.(N-Ni))/(Ni*\[Alpha]0i)=1*)
densimp2=1/non0co Prepend[Drop[-\[Alpha]0,{posi}],1].Drop[Table[Append[Drop[exp,{position[[i,1]]}],exp[[position[[posi+1,1]]]]],{i,Length[denshort]}],{posi+1}];
Fadlist2=Cases[{densimp2},_FeynAmplDenominator,Infinity]//Union;
Return[densimp2/.Thread[Fadlist2->xReduceFAD/@Fadlist2]]
];
,
Return[xReduceFAD[xDrop[exp,position[[1]]]]*exp[[position[[1]]]]]
]
];


(* ::Subsubsection::Closed:: *)
(*xUniqueFAD*)


(* ::Input:: *)
(**)


Options[xUniqueFAD]={sort->True};
xUniqueFAD[amp_,OptionsPattern[]]:=Module[
{fadd,fadsimp,head,head0},
If[FreeQ[amp,FeynAmplDenominator],Return[amp]];
If[Head[amp]===List,Return[xUniqueFAD/@amp]];
If[Head[amp//Expand]===Plus,Return[xUniqueFAD/@(amp//Expand)]];

fadd=Union[Cases[{amp},_FeynAmplDenominator,Infinity]]/.FeynAmplDenominator->head;
fadsimp[fad_head]:=Module[
{coe,factor,fad0},
coe=CoefficientList[List@@fad[[All,1]],k];
factor=Product[coe[[i,2]]^2,{i,Length[fad]}];
fad0=Simplify[factor^(-1)*(FeynAmplDenominator@@Table[{k+coe[[i,1]]/coe[[i,2]],fad[[i,2]]/Abs[coe[[i,2]]]},{i,Length[fad]}]/.Abs[x_]:>x)];
fad0/.FeynAmplDenominator[x__]:>FeynAmplDenominator[Sequence@@If[OptionValue[sort],SortBy[{x},Last],{x}]]
];
Thread[fadd->fadsimp/@fadd]/.Rule->Set;
amp/.FeynAmplDenominator->head
];


(* ::Subsubsection::Closed:: *)
(*xShiftK*)


(* ::Input:: *)
(**)


xShiftK[exp_]:=Module[
{expp,num,fadden,faddensort,first,a,b,rule,m},
(*1.*)
If[FreeQ[exp,FeynAmplDenominator],Return[exp]];
If[Head[exp]===List,Return[xShiftK/@exp]];
expp=exp//Expand;
If[Head[expp]===Plus,Return[xShiftK/@(expp)]];
(*2.*)
(*expp=exp//xClassifyFAD;*)

num=expp/.FeynAmplDenominator[___]:>1;
fadden=Cases[{expp},_FeynAmplDenominator,Infinity];
If[Length[fadden]>1,Print["error in xShiftK! Please use xClassify in advance. Absorted"];Abort[];];
(*faddensort=SortBy[fadden[[1]],First]//Simplify*);
faddensort=fadden[[1]];
(*3.*)
If[(first=faddensort[[1,1]])===k,
num*faddensort,
{a,b}=CoefficientList[first,k];
rule=k->k-a/b;
num=num/b^2/.rule//xExpandPair//xDotSimplify;(*add DotSimplify on 18.12.13*)
m=faddensort[[1,2]];
faddensort[[1]]={k+a/b,m/Abs[b]};
Simplify[num*(faddensort/.rule)]//Expand
]
];


(* ::Subsubsection::Closed:: *)
(*xReduceK*)


(* ::Input:: *)
(**)


xReduceK[exp_]:=Module[
{expp,coe,faddenPre,fadden,sps,spslist,spup,spdown,spcommon,power,denshort,d,denlist,position,const,reducedmatrix,column,augmented,\[Alpha]},
(*1.Cases selection rules*)
If[FreeQ[exp,FeynAmplDenominator]||FreeQ[exp,scalarproduct[k,_]],Return[exp]];
If[Head[exp]===List,Return[xReduceK/@exp]];
expp=exp//xClassifyFAD//Expand;
If[Head[expp]===Plus,Return[xReduceK/@(expp)]];
(*2.If exp is form of FeynAmplDenominator*scalarproduct[k,_]*coe, then the following codes proceed.*)
coe=expp/.{scalarproduct[__]:>1,FeynAmplDenominator[__]:>1};
faddenPre=Cases[{expp},_FeynAmplDenominator,Infinity];
If[Length[faddenPre]>1,Print["error in xReduceK, please use xClassfyFAD to combine the FeynAmplDenominators in advance."];Abort[];];
fadden=faddenPre[[1]];
sps=(expp/.FeynAmplDenominator[__]:>1)/coe//Factor;
spslist={sps}/.Times:>List/.s_^n_:>Table[s,{i,n}]//Flatten;
(*3.Extract the scalarproducts in numerator and denorminator*)
spup=Complement[spslist,{scalarproduct[k]}];(*after union,exclude scalarproduct[k]*)
If[spup==={},Return[expp]];
denlist=Table[scalarproduct[fadden[[i,1]]]-fadden[[i,2]]^2,{i,Length[fadden]}]//xExpandPair//Simplify;
spdown=Select[denlist//Variables,!FreeQ[#,k]&];
If[(spcommon=spdown\[Intersection]spup)==={},Return[exp]];
power=Table[Count[spslist,spcommon[[i]]],{i,Length[spcommon]}];
coe=coe*(sps/.Thread[spcommon->1]);
denshort=denlist//Union;
(*4.Preparation for the linear equations*)
position=Table[Position[d/@denlist,d[denshort[[i]]]]//Flatten,{i,Length[denshort]}];
{const,reducedmatrix}={#[[1]],#[[2]]//Transpose}&@Normal[CoefficientArrays[denshort,spdown]];
column=CoefficientArrays[spcommon[[1]],spdown][[2]]//Normal;
augmented=Table[Append[reducedmatrix[[i]],column[[i]]],{i,Length[column]}];
(*5.Solve Augmented*\[Alpha]=column and determine whether it can express spcommon with denshort*)        
If[MatrixRank[augmented]===MatrixRank[reducedmatrix],
\[Alpha]=LinearSolve[reducedmatrix,column];
Return[coe*xReduceK[(spcommon[[1]]^(power[[1]]-1)*Product[spcommon[[i]]^power[[i]],{i,2,Length[spcommon]}])(\[Alpha].Table[Drop[fadden,{position[[i,1]]}],{i,Length[denshort]}]-\[Alpha].const*fadden)]],
Return[coe*spcommon[[1]]^power[[1]]*xReduceK[fadden*Product[spcommon[[i]]^power[[i]],{i,2,Length[spcommon]}]]]
 ];
];


(* ::Subsubsection::Closed:: *)
(*xReduceK2*)


(* ::Input:: *)
(**)


xReduceK2[exp_]:=Module[
{expp,coe,faddenPre,fadden,core,power},
(*1.Case selection rules*)
If[FreeQ[exp,FeynAmplDenominator]||FreeQ[exp,scalarproduct[k]],Return[exp]];
If[Head[exp]===List,Return[xReduceK2/@exp]];
	expp=exp//xClassifyFAD//Expand;
If[Head[expp]===Plus,Return[xReduceK2/@expp]];
(*2.term without head of Plus and contains k square continues*)
coe=expp/.{FeynAmplDenominator[___]:>1,scalarproduct[k]->1};
faddenPre=Cases[{expp},_FeynAmplDenominator,Infinity];
If[Length[faddenPre]>1,Print["error in xReduceK2, please use xClassifyFAD to combine the FeynAmplDenominators in advance."];Abort[];];
fadden=faddenPre[[1]];
core=(expp/coe)//Factor;
power=({core/.FeynAmplDenominator[___]:>1}/.s_^ss_:>Table[s,{i,ss}])//Flatten//Length;
coe*xReduceK2[scalarproduct[k]^(power-1)*(Drop[fadden,{1}]+(fadden[[1,2]]^2-(xExpandPair[scalarproduct[fadden[[1,1]]]-scalarproduct[k]]//Simplify))*fadden)/.FeynAmplDenominator[]:>1]//Expand
];


(* ::Subsubsection::Closed:: *)
(*xExtractK*)


xExtractK[amp_]:=Module[{index,rule,y},
rule={scalarproduct[k]:>momentum[k,Unique[index]]^2,
scalarproduct[k]^n_:>Product[momentum[k,Unique[index]]^2,{i,1,n}],
scalarproduct[k,x_]:>momentum[k,y=Unique[index]]momentum[x,y],
scalarproduct[k,x_]^n_:>Product[momentum[k,y=Unique[index]]momentum[x,y],{i,n}],
Dotgamma[a___,Diracslash[k],b___]:>momentum[k,y=Unique[index]]Dotgamma[a,Diracgamma[y],b],(*26.11.13*)
Diracslash[k]->momentum[k,y=Unique[index]]Diracgamma[y](*add on 05.12.13*)
};
amp//.rule

]


(* ::Subsubsection::Closed:: *)
(*xTensorDecompositionPaVe*)


Options[xTensorDecompositonPaVe]={$ABCDE->False};(*06.12.13*)
xTensorDecompositonPaVe[a___]/;FreeQ[{a},_FeynAmplDenominator]:=0;
xTensorDecompositonPaVe[index_List,fad_FeynAmplDenominator]:=Module[
{met,permutations,sum,gsps,factor,fad1,fad2,fad3,$\[Mu],$$\[Mu],$\[Nu],$p,$m,rank,len,mom,norm=1(*4\[Pi] \[Mu]r^2*),a1,a2,a3,a4,a5,result},
(*-----Local--functions---14.11.2013*)
(*1.met gives a Lorentz-index symmetric block constructed with Metric Tensor, eg. met{\[Mu],\[Nu],\[Rho],\[Sigma]} will give {gg}^\[Mu]\[Nu]\[Rho]\[Sigma]=g^\[Mu]\[Nu] g^\[Rho]\[Sigma]+g^\[Nu]\[Rho] g^\[Mu]\[Sigma]+g^\[Rho]\[Mu] g^\[Nu]\[Sigma], the last equation of Eq.(2.3)in A.Denner's NPB734(2006)62*)
met[]=1;
met[x__]/;Length[{x}]>2:=Sum[met[{x}[[1]],{x}[[i]]]*met[Sequence@@Delete[{x},{{1},{i}}]],{i,2,Length[{x}]}];
(*2.Local function 2, permutations generates the first three Eqs in Eq.(2.3). if two gs exist,     the met function will also be used. num is a list of numbers which specifies the powers of the gs and ps in metmom. ind is Lorentz indice list. Important: (number of Lorentz indice)=2*(number of gs)+(number of momenta), see sum function defined below and refer to Eq.(11) in PLB263p1*)
permutations[{},{},{}]=1;
permutations[num_List,metmom_List,ind_List]/;num=!={}:=   Plus@@(Switch[metmom[[1]],met,metmom[[1]]@@#,_,Times@@(mom[metmom[[1]],#]&/@#)]*permutations[Drop[num,{1}],Drop[metmom,{1}],Complement[ind,#]]&/@Union[Sort/@Permutations[ind,{num[[1]]}]])//Expand;
(*3.sum function produces all the {g...p...} term, see Eq.(2.3)*)
sum[tensorrank_,npoint_]:=Module[{gmax},
gmax=If[EvenQ[tensorrank],tensorrank/2,If[OddQ[tensorrank],(tensorrank-1)/2,Print["error in TensorDecomposition--sum"];Abort[]]];
(*distribute the number of Lorentz index for gs and ps.*)
gsps[ik_,i___,{ip_}]/;Length[{i}]<npoint-1&&ip=!=0:=Sum[gsps[ik,i,j,{ip-j}],{j,0,ip}];
gsps[ik_,i___,{0}]/;Length[{i}]<npoint:=gsps[ik,i,Sequence@@Table[0,{j,1,npoint-Length[{i}]}]];
gsps[ik_,i___,{ip_}]/;Length[{i}]===npoint-1&&ip=!=0:=gsps[ik,i,ip];
Sum[gsps[2ig,{tensorrank-2ig}],{ig,0,gmax}]];
(*--------------------*)
(*fad1=xUniqueFAD[fad]*)(*//xShiftK*);(*bugggggggggggg*)
(*fad1=SortBy[fad,First]//Simplify;*)
(*fad1=SortBy[fad,massOrder[Last[#]]&];*)
fad1=fad;
Switch[Head[fad1],FeynAmplDenominator,fad2=fad1/.k->0;factor=1,Times,factor=fad1/.FeynAmplDenominator[__]:>1;fad2=fad1/factor/.k->0//Simplify,_,Print["error in xTensorDecomposition"]];
(*fad3=fad2*)(*Union[fad2]*);
(*If[Length[fad3]=!=Length[fad2],Print["error"];Abort[]];*)
$\[Mu]=Table[Unique[$$\[Mu]],{i,Length@index}];(*temporary Lorentz indices*)
$p=List@@fad2[[All,1]];If[$p[[1]]=!=0,Print["eRRorrrrrrrrrr"]];
$m=List@@fad2[[All,2]];
rank=index//Length;
len=fad2//Length;
(*If[rank===0,
Return[factor*xPaVe[{{},$p,$m}]],
Return[(factor*((sum[rank,len]//Expand)
/.gsps[ik_,j___]:>permutations[Flatten@{ik,j},Flatten@{met,$p},$\[Mu]]*(norm)^(rank-ik/2) xPaVe[Sequence@@Flatten@{Table[0,{ii,1,ik}],Flatten[Table[Table[jj-1,{ii,1,{j}[[jj]]}],{jj,1,Length[{j}]}]]},{$p,$m}]))/.Thread[$\[Mu]->index]/.mom[0,_]:>0/.{met->metrictensor,mom->momentum}]]*)
result=If[#1===0,
Return[factor*#4[Sequence@@#5]],
Return[(factor*((sum[#1,#2]//Expand)
/.gsps[ik_,j___]:>permutations[Flatten@{ik,j},Flatten@{met,$p},$\[Mu]]*(norm)^(rank-ik/2) #3[Sequence@@Flatten@{Table[0,{ii,1,ik}],Flatten[Table[Table[jj-1,{ii,1,{j}[[jj]]}],{jj,1,Length[{j}]}]]},Sequence@@#5]))/.Thread[$\[Mu]->index]/.mom[0,_]:>0/.{met->metrictensor,mom->momentum}];]&;
(*result[rank,point,ABCDEtensorname,variable,ABCDEscalarname].18.11.13*)
If[True,
Switch[len,
1,
a1={$m[[1]]^2};result[rank,1,LFA0i,LFA0,a1],
2,
a2={scalarproduct[$p[[2]]-$p[[1]]],$m[[1]]^2,$m[[2]]^2};result[rank,2,LFB0i,LFB0,a2],
3,
a3={scalarproduct[$p[[2]]-$p[[1]]],scalarproduct[$p[[3]]-$p[[2]]],scalarproduct[$p[[3]]-$p[[1]]],$m[[1]]^2,$m[[2]]^2,$m[[3]]^2};result[rank,3,LFC0i,LFC0,a3],
4,
a4={scalarproduct[$p[[2]]-$p[[1]]],scalarproduct[$p[[3]]-$p[[2]]],scalarproduct[$p[[4]]-$p[[3]]],scalarproduct[$p[[4]]-$p[[1]]],scalarproduct[$p[[3]]-$p[[1]]],scalarproduct[$p[[4]]-$p[[2]]],$m[[1]]^2,$m[[2]]^2,$m[[3]]^2,$m[[4]]^2};result[rank,4,LFD0i,LFD0,a4],
5,
a5={scalarproduct[$p[[2]]-$p[[1]]],scalarproduct[$p[[3]]-$p[[2]]],scalarproduct[$p[[4]]-$p[[3]]],scalarproduct[$p[[5]]-$p[[4]]],scalarproduct[$p[[3]]-$p[[1]]],scalarproduct[$p[[4]]-$p[[2]]],scalarproduct[$p[[5]]-$p[[3]]],scalarproduct[$p[[4]]-$p[[1]]],scalarproduct[$p[[5]]-$p[[2]]],$m[[1]]^2,$m[[2]]^2,$m[[3]]^2,$m[[4]]^2,$m[[5]]^2};result[rank,5,LFE0i,LFE0,a5],
_,
result[rank,len,xPaVe,xPaVe,{{$p,$m}//Transpose}]
	];,
result[rank,len,xPaVe,xPaVe,{{$p,$m}//Transpose}]
  ]

];


(* ::Subsubsection::Closed:: *)
(*xTensorDecompositionDavy*)


(* ::Input:: *)
(**)


xTensorDecompositonDavy[a___]/;FreeQ[{a},_FeynAmplDenominator]:=0;
xTensorDecompositonDavy[index_List,fad_FeynAmplDenominator]:=Module[
{met,STC,sum,distribute,factor,fad1,fad2,fad3,$\[Mu],$\[Nu],$r,$m,n,rank,mom,norm=1(*4\[Pi] \[Mu]r^2*)},
(*1.Define tensor index distribution function. 24.11.2013*)
(*met: met distributes indices for Metric Tensor, so length of it's variables should be even..*)
met[]=1;
met[x__]/;Length[{x}]>2:=Sum[met[{x}[[1]],{x}[[i]]]*met[Sequence@@Delete[{x},{{1},{i}}]],{i,2,Length[{x}]}];
(*STC=symmetric tensor combination: it is a structure constructed by Metric Tensor and External momenta (TaE) and symmetric with respect to the given Lorentz Indice (LI). The corresponding numbers fo Metric Tensor and External momenta (nTaE) should also be specified.*)
STC[{},{},{}]=1;
STC[nTaE_List,TaE_List,LI_List]/;nTaE=!={}:=Plus@@(Switch[TaE[[1]],met,TaE[[1]]@@#,_,Times@@(mom[TaE[[1]],#]&/@#)]*STC[Drop[nTaE,{1}],Drop[TaE,{1}],Complement[LI,#]]&/@Union[Sort/@Permutations[LI,{nTaE[[1]]}]]);
(*sum function according to PLB263p1, Eq.(11), M is tensor rank, N is number of propagator of the different. All the cases with the summation condition are considered*)
sum[M_,N_]:=Module[{lamdamax},
lamdamax=If[EvenQ[M],M/2,If[OddQ[M],(M-1)/2,Print["error in xTensorDecomposition"];Abort[]]];
(*distribute the number of Lorentz index for the symmetric tensor combination. ik is the number of Metric Tensor, p+i=M-2lamba.*)
distribute[ik_,i___,{ip_}]/;Length[{i}]<N-1&&ip=!=0:=Sum[distribute[ik,i,j,{ip-j}],{j,0,ip}];
distribute[ik_,i___,{0}]/;Length[{i}]<N:=distribute[ik,i,Sequence@@Table[0,{j,1,N-Length[{i}]}]];
distribute[ik_,i___,{ip_}]/;Length[{i}]===N-1&&ip=!=0:=distribute[ik,i,ip];
Sum[distribute[2lamda,{M-2lamda}],{lamda,0,lamdamax}]
];
(*2.To get unique FeynAmplDenominator*)
fad1=xUniqueFAD[fad];
Switch[Head[fad1],FeynAmplDenominator,fad2=fad1/.k->0;factor=1,Times,factor=fad1/.FeynAmplDenominator[__]:>1;fad2=fad1/factor/.k->0//Simplify,_,Print["error in xTensorDecomposition"]];
fad3=Union[fad2];
(*3.Elements of the tensor integral*)
$\[Mu]=Table[Unique[$$\[Mu]],{i,Length@index}];
$\[Nu]=Table[Count[fad2,fad3[[i]]],{i,Length[fad3]}];
$r=List@@fad3[[All,1]];
$m=List@@fad3[[All,2]];
(*4.core:see PLB263p1, Eq.(11)*)
n=fad3//Length;
If[index==={},Return[factor*I0[D,Table[Append[fad3[[i]],$\[Nu][[i]]],{i,n}]]]];

rank=index//Length;

(factor*((sum[rank,n]//Expand)
/.distribute[ik_,j___]:>STC[Flatten@{ik,j},Flatten@{met,$r},$\[Mu]]*(norm)^(rank-ik/2)/(-2)^(ik/2)*Product[Gamma[$\[Nu][[i]]+{j}[[i]]]/Gamma[$\[Nu][[i]]],{i,n}]*I0[D+2rank-ik,Table[{$r[[i]],$m[[i]],$\[Nu][[i]]+{j}[[i]]},{i,n}]]))/.Thread[$\[Mu]->index]/.mom[0,_]:>0/.{met->metrictensor,mom->momentum}

];


(* ::Subsubsection::Closed:: *)
(*xLoopAmplitude*)


(*Options[xLoopAmplitude]={IntegrateMethod->$PaVe};*)
(*xLoopAmplitude[amp_,OptionsPattern[]]:=Module[
{listQ,simplifyAmpl,reduceAmpl,separateAmpl,$I,in$I,index,$Is,Tensorintegrate,Tensorinte,separate2,fad,head,const},
(*1.Case selection rules*)
If[FreeQ[amp,FeynAmplDenominator],Print["free of FeynAmplDenominator, Absorted"];Return[amp];Abort[]];
listQ=Head[amp]===List;
simplifyAmpl=xPrintTime[amp//xDotSimplify//xDiracContract//xDiracSimplify//xSU2Simplify//xClassifyFAD,"DotSimplify->DiracContract->DiracSimplify->SU2Simlify->DiracContract->Separate"];
reduceAmpl=xPrintTime[If[listQ,
Table[simplifyAmpl//xReduceK//xReduceK2//xFADReduce//xClassifyFAD//xUniqueFAD//xShiftK,{i,Length[simplifyAmpl]}],
simplifyAmpl//xReduceK//xReduceK2//xFADReduce//xClassifyFAD//xUniqueFAD//xShiftK,
Print["error in LoopAmplitude"];Abort[];],"ReduceK->ReduceK2->FADReduce->ClassifyFAD->UniqueFAD"];
head=Cases[{reduceAmpl},_FeynAmplDenominator,Infinity]//Union;
const=reduceAmpl/.Thread[head->0];(*bug fixed on 11.12.13, the terms without integrateing propagator divided*)
separateAmpl=xSeparate[reduceAmpl-const,k];
Clear[$I];
in$I=(If[listQ,separateAmpl[[All,2]],separateAmpl[[2]]]//xExtractK)/.{momentum[k,a_]^n_:>$I[Sequence@@Table[a,{i,n}]],momentum[k,b_]:>$I[b]}
//.$I[x__]*$I[y__]:>$I[x,y]
/.FeynAmplDenominator[x__]$I[y__]:>$I[{y},fad[x]]
/.FeynAmplDenominator[x__]:>$I[{},fad[x]]
/.fad->FeynAmplDenominator;
index[y___]:=Table["\[Mu]"<>ToString[i],{i,Length[{y}]}];
$Is=Union[Flatten[Union@Cases[{in$I},_$I,Infinity]/.$I[{y___},FeynAmplDenominator[x__]]:>$I[index[y],FeynAmplDenominator[x]]]];
Tensorintegrate=$Is/.{Switch[OptionValue[IntegrateMethod],$PaVe,$I->xTensorDecompositonPaVe,$Davy,$I->xTensorDecompositonDavy,_,Abort[]]}//xExpandPair;
Thread[$Is->Tensorintegrate]/.Rule->Set;
Tensorinte=(in$I/.$I[{y___},FeynAmplDenominator[x__]]:>($I[index[y],FeynAmplDenominator[x]]/.Thread[index[y]:>{y}]));
If[listQ,
Table[separateAmpl[[i,1]].Tensorinte[[i]]//xDiracContract,{i,1,Length[simplifyAmpl]}],
separateAmpl[[1]].Tensorinte//xDiracContract]
];*)


Options[xLoopAmplitude]={IntegrateMethod->$PaVe};
xLoopAmplitude[amp_,OptionsPattern[]]:=Module[
{listQ,simplifyAmpl,reduceAmpl,separateAmpl,$I,in$I,index,$Is,Tensorintegrate,Tensorinte,separate2,fad,head,const},
(*1.Case selection rules*)
If[FreeQ[amp,FeynAmplDenominator],Print["free of FeynAmplDenominator, Absorted"];Return[amp];Abort[]];
simplifyAmpl=xPrintTime[amp//xDotSimplify//xDiracContract//xDiracSimplify//xSU2Simplify//xDiracContract,"DotSimplify->DiracContract->DiracSimplify->SU2Simlify->DiracContract"];
reduceAmpl=xPrintTime[simplifyAmpl//xReduceK//xReduceK2//xFADReduce//xClassifyFAD//xUniqueFAD//xShiftK,"ReduceK->ReduceK2->FADReduce->UniqueFAD->ShiftK"];
head=Cases[{reduceAmpl},_FeynAmplDenominator,Infinity]//Union;
const=reduceAmpl/.Thread[head->0];(*bug fixed on 11.12.13, the terms without integrateing propagator divided*)
separateAmpl=xSeparate[reduceAmpl-const//Expand,k];
Clear[$I];
in$I=(separateAmpl[[2]]//xExtractK)/.{momentum[k,a_]^n_:>$I[Sequence@@Table[a,{i,n}]],momentum[k,b_]:>$I[b]}
//.$I[x__]*$I[y__]:>$I[x,y]
/.FeynAmplDenominator[x__]$I[y__]:>$I[{y},fad[x]]
/.FeynAmplDenominator[x__]:>$I[{},fad[x]]/.fad->FeynAmplDenominator;
index[y___]:=Table["\[Mu]"<>ToString[i],{i,Length[{y}]}];
$Is=Union[Flatten[Union@Cases[{in$I},_$I,Infinity]/.$I[{y___},FeynAmplDenominator[x__]]:>$I[index[y],FeynAmplDenominator[x]]]];
Tensorintegrate=$Is/.{Switch[OptionValue[IntegrateMethod],$PaVe,$I->xTensorDecompositonPaVe,$Davy,$I->xTensorDecompositonDavy,_,Abort[]]}//xExpandPair;
Thread[$Is->Tensorintegrate]/.Rule->Set;
Tensorinte=(in$I/.$I[{y___},FeynAmplDenominator[x__]]:>($I[index[y],FeynAmplDenominator[x]]/.Thread[index[y]:>{y}]));
separateAmpl[[1]].Tensorinte//xDiracContract
];




Options[xLoopAmplitude0]={IntegrateMethod->$PaVe};
xLoopAmplitude0[amp_,OptionsPattern[]]:=Module[
{listQ,simplifyAmpl,reduceAmpl,separateAmpl,$I,in$I,index,$Is,Tensorintegrate,Tensorinte,separate2,fad,head,const},
(*1.Case selection rules*)
If[FreeQ[amp,FeynAmplDenominator],Print["free of FeynAmplDenominator, Absorted"];Return[amp];Abort[]];
simplifyAmpl=xPrintTime[amp//xDotSimplify//xDiracContract//xDiracSimplify//xSU2Simplify//xDiracContract,"DotSimplify->DiracContract->DiracSimplify->SU2Simlify->DiracContract"];
reduceAmpl=xPrintTime[simplifyAmpl(*//xReduceK//xReduceK2//xFADReduce//*)//xClassifyFAD//xUniqueFAD//xShiftK,"ReduceK->ReduceK2->FADReduce->UniqueFAD->ShiftK"];
head=Cases[{reduceAmpl},_FeynAmplDenominator,Infinity]//Union;
const=reduceAmpl/.Thread[head->0];(*bug fixed on 11.12.13, the terms without integrateing propagator divided*)
separateAmpl=xSeparate[reduceAmpl-const//Expand,k];
Clear[$I];
in$I=(separateAmpl[[2]]//xExtractK)/.{momentum[k,a_]^n_:>$I[Sequence@@Table[a,{i,n}]],momentum[k,b_]:>$I[b]}
//.$I[x__]*$I[y__]:>$I[x,y]
/.FeynAmplDenominator[x__]$I[y__]:>$I[{y},fad[x]]
/.FeynAmplDenominator[x__]:>$I[{},fad[x]]/.fad->FeynAmplDenominator;
index[y___]:=Table["\[Mu]"<>ToString[i],{i,Length[{y}]}];
$Is=Union[Flatten[Union@Cases[{in$I},_$I,Infinity]/.$I[{y___},FeynAmplDenominator[x__]]:>$I[index[y],FeynAmplDenominator[x]]]];
Tensorintegrate=$Is/.{Switch[OptionValue[IntegrateMethod],$PaVe,$I->xTensorDecompositonPaVe,$Davy,$I->xTensorDecompositonDavy,_,Abort[]]}//xExpandPair;
Thread[$Is->Tensorintegrate]/.Rule->Set;
Tensorinte=(in$I/.$I[{y___},FeynAmplDenominator[x__]]:>($I[index[y],FeynAmplDenominator[x]]/.Thread[index[y]:>{y}]));
separateAmpl[[1]].Tensorinte//xDiracContract
];


(*Options[xLoopAmplitude2]={IntegrateMethod->$PaVe};
xLoopAmplitude2[amp_,OptionsPattern[]]:=Module[
{listQ,simplifyAmpl,reduceAmpl,separateAmpl,$I,in$I,index,$Is,Tensorintegrate,Tensorinte,separate2,fad,head,const},
(*1.Case selection rules*)
If[FreeQ[amp,FeynAmplDenominator],Print["free of FeynAmplDenominator, Absorted"];Return[amp];Abort[]];
listQ=Head[amp]===List;
simplifyAmpl=xPrintTime[amp//xDotSimplify//xDiracContract//xDiracSimplify//xSU2Simplify//xClassifyFAD,"DotSimplify->DiracContract->DiracSimplify->SU2Simlify->DiracContract->Separate"];

head=Cases[{simplifyAmpl},_FeynAmplDenominator,Infinity]//Union;
const=simplifyAmpl/.Thread[head->0];(*bug fixed on 11.12.13, the terms without integrateing propagator divided*)
separateAmpl=xSeparate[simplifyAmpl-const,k];
Clear[$I];
in$I=(If[listQ,separateAmpl[[All,2]],separateAmpl[[2]]]//xExtractK)/.{momentum[k,a_]^n_:>$I[Sequence@@Table[a,{i,n}]],momentum[k,b_]:>$I[b]}
//.$I[x__]*$I[y__]:>$I[x,y]
/.FeynAmplDenominator[x__]$I[y__]:>$I[{y},fad[x]]
/.FeynAmplDenominator[x__]:>$I[{},fad[x]]
/.fad->FeynAmplDenominator;
index[y___]:=Table["\[Mu]"<>ToString[i],{i,Length[{y}]}];
$Is=Union[Flatten[Union@Cases[{in$I},_$I,Infinity]/.$I[{y___},FeynAmplDenominator[x__]]:>$I[index[y],FeynAmplDenominator[x]]]];
Tensorintegrate=$Is/.{Switch[OptionValue[IntegrateMethod],$PaVe,$I->xTensorDecompositonPaVe,$Davy,$I->xTensorDecompositonDavy,_,Abort[]]}//xExpandPair;
Thread[$Is->Tensorintegrate]/.Rule->Set;
Tensorinte=(in$I/.$I[{y___},FeynAmplDenominator[x__]]:>($I[index[y],FeynAmplDenominator[x]]/.Thread[index[y]:>{y}]));
If[listQ,
Table[separateAmpl[[i,1]].Tensorinte[[i]]//xDiracContract,{i,1,Length[simplifyAmpl]}],
separateAmpl[[1]].Tensorinte//xDiracContract]
];*)


(* ::Subsubsection::Closed:: *)
(*xSetDto4*)


xSetDto40[amp_]:=Module[{LFs,sep,sep1,sep2,sepp,epsUV},
LFs=Cases[{amp},_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i,Infinity]//Union;
sep=xSeparate[amp,Sequence@@LFs];
(*epsUV=D-4, NPB734(2006)62-115,pp106, UV-divergent parts of tensor integrals, here upto rank 5*)
(*1-point function: A---------------*)
epsUV/:epsUV*LFA0[m02_]:=-2m02;
epsUV/:epsUV*LFA0i[ii:(_Integer)..,m02_]/;(EvenQ[Length[{ii}]])&&(SameQ[Sequence@@({ii}//Union),0]):=Module[{n=Length[{ii}]/2},-(m02^(n+1)/(2^(n-1)*(n+1)!))];
(*2-point function: B--------------*)
epsUV/:epsUV*LFB0[p10_,m02_,m12_]:=-2;
epsUV/:epsUV*LFB0i[1,p10_,m02_,m12_]:=1;
epsUV/:epsUV*LFB0i[0,0,p10_,m02_,m12_]:=1/6 (p10-3m02-3m12);
epsUV/:epsUV*LFB0i[1,1,p10_,m02_,m12_]:=-(2/3);
epsUV/:epsUV*LFB0i[0,0,1,p10_,m02_,m12_]:=-(1/12)(p10-2m02-4m12);
epsUV/:epsUV*LFB0i[1,1,1,p10_,m02_,m12_]:=1/2;
epsUV/:epsUV*LFB0i[0,0,0,0,p10_,m02_,m12_]:=-(1/120)(p10^2-5p10(m02+m12)+10(m02^2+m02 m12+m12^2));
epsUV/:epsUV*LFB0i[0,0,1,1,p10_,m02_,m12_]:=1/60 (3p10-5m02-15m12);
epsUV/:epsUV*LFB0i[1,1,1,1,p10_,m02_,m12_]:=-(2/5);
epsUV/:epsUV*LFB0i[0,0,0,0,1,p10_,m02_,m12_]:= 1/240 (p10^2-4p10 m02-6p10 m12+5m02^2+10m02 m12+15m12^2);
epsUV/:epsUV*LFB0i[0,0,1,1,1,p10_,m02_,m12_]:=-(1/60)(2p10-3m02-12m12);
epsUV/:epsUV*LFB0i[1,1,1,1,1,p10_,m02_,m12_]:=1/3;

(*3-point function: C--------------*)
epsUV/:epsUV*LFC0i[0,0,p10_,p12_,p20_,m02_,m12_,m22_]:=-(1/2);
epsUV/:epsUV*LFC0i[0,0,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;i>0:=1/6;
epsUV/:epsUV*LFC0i[0,0,0,0,p10_,p12_,p20_,m02_,m12_,m22_]:=1/48 (p12+p10+p20)-1/12 (m02+m12+m22);
epsUV/:epsUV*LFC0i[0,0,i_,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;i>0:=-(1/12);
epsUV/:epsUV*LFC0i[0,0,i_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=-(1/24);
epsUV/:epsUV*LFC0i[0,0,0,0,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;i>0:=Module[{delt},delt = If[ #1 === #2, 1, 0]&;-(1/240)(2p12-5m02+(p10-5m12)(1+delt[i,1])+(p20-5m22)(1+delt[i,2]))(*+4(m12-m22)(delt[i,1]-delt[i,2]))*)];(*corrected on 07.01.14, now same with Denner's result*)
epsUV/:epsUV*LFC0i[0,0,i_,i_,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i>0):=1/20;
epsUV/:epsUV*LFC0i[0,0,i_,i_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=1/60;
(*4-point function: D--------------*)
epsUV/:epsUV*LFD0i[0,0,0,0,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]:=-(1/12);
epsUV/:epsUV*LFD0i[0,0,0,0,i_,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]/;i>0:=1/48;
 (*5 others*)
epsUV/:epsUV*LF_/;!FreeQ[{Head[LF]},LFA0|LFB0|LFC0|LFD0|LFA0i|LFB0i|LFC0i|LFD0i]:=0;
sep1=sep[[1]]/.D->epsUV+4;
sep2=sep[[2]];
Sum[sepp=xSeparate[Normal@Series[sep1[[i]],{epsUV,0,1}],epsUV];sepp[[1]].(sepp[[2]]sep2[[i]]),{i,1,Length[sep1]}]/.epsUV->0
]



(*Updated on 07.01.2014*)(*11,03.2014*)
SetAttributes[xSetDto4,Listable]
xSetDto4[amp_]:=Module[{LFs,sep,sep1,sep2,sepp,epsUV},
(*epsUV=D-4, NPB734(2006)62-115,pp106, UV-divergent parts of tensor integrals, here upto rank 5*)
(*1-point function: A---------------*)
epsUV/:epsUV*LFA0[m02_]:=-2m02;
epsUV/:epsUV*LFA0i[ii:(_Integer)..,m02_]/;(EvenQ[Length[{ii}]])&&(SameQ[Sequence@@({ii}//Union),0]):=Module[{n=Length[{ii}]/2},-(m02^(n+1)/(2^(n-1)*(n+1)!))];
(*2-point function: B------up to rank 5--------*)
epsUV/:epsUV*LFB0[p10_,m02_,m12_]:=-2;
epsUV/:epsUV*LFB0i[1,p10_,m02_,m12_]:=1;
epsUV/:epsUV*LFB0i[0,0,p10_,m02_,m12_]:=1/6 (p10-3m02-3m12);
epsUV/:epsUV*LFB0i[1,1,p10_,m02_,m12_]:=-(2/3);
epsUV/:epsUV*LFB0i[0,0,1,p10_,m02_,m12_]:=-(1/12)(p10-2m02-4m12);
epsUV/:epsUV*LFB0i[1,1,1,p10_,m02_,m12_]:=1/2;
epsUV/:epsUV*LFB0i[0,0,0,0,p10_,m02_,m12_]:=-(1/120)(p10^2-5p10(m02+m12)+10(m02^2+m02 m12+m12^2));
epsUV/:epsUV*LFB0i[0,0,1,1,p10_,m02_,m12_]:=1/60 (3p10-5m02-15m12);
epsUV/:epsUV*LFB0i[1,1,1,1,p10_,m02_,m12_]:=-(2/5);
epsUV/:epsUV*LFB0i[0,0,0,0,1,p10_,m02_,m12_]:= 1/240 (p10^2-4p10 m02-6p10 m12+5m02^2+10m02 m12+15m12^2);
epsUV/:epsUV*LFB0i[0,0,1,1,1,p10_,m02_,m12_]:=-(1/60)(2p10-3m02-12m12);
epsUV/:epsUV*LFB0i[1,1,1,1,1,p10_,m02_,m12_]:=1/3;

(*3-point function: C------up to rank 7--------*)
epsUV/:epsUV*LFC0i[0,0,p10_,p12_,p20_,m02_,m12_,m22_]:=-(1/2);
epsUV/:epsUV*LFC0i[0,0,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;i>0:=1/6;
epsUV/:epsUV*LFC0i[0,0,0,0,p10_,p12_,p20_,m02_,m12_,m22_]:=1/48 (p12+p10+p20)-1/12 (m02+m12+m22);
epsUV/:epsUV*LFC0i[0,0,i_,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;i>0:=-(1/12);
epsUV/:epsUV*LFC0i[0,0,i_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=-(1/24);
epsUV/:epsUV*LFC0i[0,0,0,0,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;i>0:=Module[{delt},delt = If[ #1 === #2, 1, 0]&;-(1/240)(2p12-5m02+(p10-5m12)(1+delt[i,1])+(p20-5m22)(1+delt[i,2])(*+4(m12-m22)(delt[i,1]-delt[i,2])*))];(*corrected on 07.01.14, now same with Denner's result*)
epsUV/:epsUV*LFC0i[0,0,i_,i_,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i>0):=1/20;
epsUV/:epsUV*LFC0i[0,0,i_,i_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=1/60;
epsUV/:epsUV*LFC0i[0,0,0,0,0,0,p10_,p12_,p20_,m02_,m12_,m22_]:=Module[{delt,p={Sqrt[p10],Sqrt[p20]},s12=p12,m={Sqrt[m12],Sqrt[m22]},m0=Sqrt[m02]},delt = If[ #1 === #2, 1, 0]&;-(1/2880)(2*s12^2-6*s12*m0^2+30*m0^4+2*s12*Sum[p[[ii]]^2-6m[[ii]]^2,{ii,1,2}]-6m0^2 Sum[2p[[ii]]^2-5m[[ii]]^2,{ii,1,2}]+Sum[Sum[(p[[ii]]^2 p[[jj]]^2-6p[[ii]]^2 m[[jj]]^2+15m[[ii]]^2 m[[jj]]^2)(1+delt[ii,jj]),{ii,1,2}],{jj,1,2}])];
epsUV/:epsUV*LFC0i[0,0,0,0,i_,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i>0):=Module[{delt,p={Sqrt[p10],Sqrt[p20]},s12=p12,m={Sqrt[m12],Sqrt[m22]},m0=Sqrt[m02]},delt = If[ #1 === #2, 1, 0]&;1/720 (3s12-6m0^2+Sum[(p[[ni]]^2-6m[[ni]]^2)(1+2delt[i,ni]),{ni,1,2}])];
epsUV/:epsUV*LFC0i[0,0,0,0,i_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=Module[{delt,p={Sqrt[p10],Sqrt[p20]},s12=p12,m={Sqrt[m12],Sqrt[m22]},m0=Sqrt[m02]},delt = If[ #1 === #2, 1, 0]&;1/720 (2s12-3m0^2+Sum[(p[[ni]]^2-6m[[ni]]^2),{ni,1,2}])];
epsUV/:epsUV*LFC0i[0,0,i_,i_,i_,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i>0):=-(1/30);
epsUV/:epsUV*LFC0i[0,0,i_,i_,i_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=-(1/120);
epsUV/:epsUV*LFC0i[0,0,i_,i_,j_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=-(1/180);
epsUV/:epsUV*LFC0i[0,0,0,0,0,0,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i>0):=Module[{delt,p={Sqrt[p10],Sqrt[p20]},s12=p12,m={Sqrt[m12],Sqrt[m22]},m0=Sqrt[m02]},delt = If[ #1 === #2, 1, 0]&;1/10080 (3s12^2-7s12 m0^2+21m0^4+s12 Sum[(p[[ni]]^2-7m[[ni]]^2)(2+delt[i,ni]),{ni,1,2}]-7m0^2 Sum[(p[[ni]]^2-3m[[ni]]^2)(1+delt[i,ni]),{ni,1,2}]+Sum[Sum[(p[[mi]]^2 p[[ni]]^2-7p[[mi]]^2 m[[ni]]^2+21m[[mi]]^2 m[[ni]]^2)(1+2delt[i,mi]delt[i,ni]),{mi,1,2}],{ni,1,2}])];
epsUV/:epsUV*LFC0i[0,0,0,0,i_,i_,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i>0):=Module[{delt,p={Sqrt[p10],Sqrt[p20]},s12=p12,m={Sqrt[m12],Sqrt[m22]},m0=Sqrt[m02]},delt = If[ #1 === #2, 1, 0]&;-(1/1680)(4s12-7m0^2+Sum[(p[[ni]]^2-7m[[ni]]^2)(1+3delt[i,ni]),{ni,1,2}])];
epsUV/:epsUV*LFC0i[0,0,0,0,i_,i_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=Module[{delt,p={Sqrt[p10],Sqrt[p20]},s12=p12,m={Sqrt[m12],Sqrt[m22]},m0=Sqrt[m02]},delt = If[ #1 === #2, 1, 0]&;-(1/5040)(6s12-7m0^2+Sum[(p[[ni]]^2-7m[[ni]]^2)(2+delt[i,ni]),{ni,1,2}])];
epsUV/:epsUV*LFC0i[0,0,i_,i_,i_,i_,i_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i>0):=1/42;
epsUV/:epsUV*LFC0i[0,0,i_,i_,i_,i_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=1/210;
epsUV/:epsUV*LFC0i[0,0,i_,i_,i_,j_,j_,p10_,p12_,p20_,m02_,m12_,m22_]/;(i=!=j)&&(i>0)&&(j>0):=1/420;
(*4-point function: D-------up to rank 7-------*)
epsUV/:epsUV*LFD0i[0,0,0,0,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]:=-(1/12);
epsUV/:epsUV*LFD0i[0,0,0,0,i_,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]/;i>0:=1/48;
epsUV/:epsUV*LFD0i[0,0,0,0,0,0,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]:=1/480 (p12+p13+p23+p10+p20+p03)-1/96 (m02+m12+m22+m32);
epsUV/:epsUV*LFD0i[0,0,0,0,i_,i_,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]/;(i>0):=-(1/120);
epsUV/:epsUV*LFD0i[0,0,0,0,i_,j_,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]/;(i=!=j)&&(i>0)&&(j>0):=-(1/240);
epsUV/:epsUV*LFD0i[0,0,0,0,0,0,i_,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]/;(i>0):=Module[{delt},delt = If[ #1 === #2, 1, 0]&;-(1/2880)(p10(1+delt[1,i])+p20(1+delt[2,i])+p03(1+delt[3,i])+p12(1+delt[1,i]+delt[2,i])+p13(1+delt[1,i]+delt[3,i])+p23(1+delt[2,i]+delt[3,i]))+1/480 (m02+m12+m22+m32)];
epsUV/:epsUV*LFD0i[0,0,0,0,i_,i_,i_,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]/;(i>0):=1/240;
epsUV/:epsUV*LFD0i[0,0,0,0,i_,i_,j_,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]/;(i=!=j)&&(i>0)&&(j>0):=1/720;
epsUV/:epsUV*LFD0i[0,0,0,0,i_,j_,k_,p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_]/;(i=!=j)&&(i=!=k)&&(j=!=k)&&(i>0)&&(j>0)&&(k>0):=1/1440;
 (*5 others*)
epsUV/:epsUV*LF_/;!FreeQ[{Head[LF]},LFA0|LFB0|LFC0|LFD0|LFA0i|LFB0i|LFC0i|LFD0i]:=0;

LFs=Cases[{amp},LFA0[_]|LFA0i[__]|LFB0[_,_,_]|LFB0i[__]|LFC0i[0,0,___,_,_,_,_,_,_]|LFD0i[0,0,0,0,___,_,_,_,_,_,_,_,_,_,_],Infinity]//Union;
If[LFs==={},
amp/.D->4,
sep=xSeparate[amp,Sequence@@(LFs)];
sep1=sep[[1]]/.D->epsUV+4;
sep2=sep[[2]];
If[sep2[[1]]===1,
sep1[[1]]*sep2[[1]]+Sum[sepp=xSeparate[Normal@Series[sep1[[i]],{epsUV,0,1}],epsUV];sepp[[1]].(sepp[[2]]sep2[[i]]),{i,2,Length[sep1]}]/.epsUV->0,
Sum[sepp=xSeparate[Normal@Series[sep1[[i]],{epsUV,0,1}],epsUV];sepp[[1]].(sepp[[2]]sep2[[i]]),{i,1,Length[sep1]}]/.epsUV->0
]]

]



(* ::Subsubsection::Closed:: *)
(*xTensorReduce*)


(*09.12.13*)
$Dim=D;
Options[xTensorReduce]={$SetDto4->False};
xTensorReduce[amp_,OptionsPattern[]]:=Module[{LFs,RedLFs},
LFs=Cases[{amp},_LFA0i|_LFB0i|_LFC0i|_LFD0i,Infinity]//Union;
RedLFs=xReduceTensor/@LFs;
If[OptionValue[$SetDto4],amp/.Thread[LFs->xSetDto4/@RedLFs],amp/.Thread[LFs->RedLFs]]
];


(*28.07.2015*)
$Dim=D;
Options[xTensorReduce2]={$SetDto4->True};
xTensorReduce2[amp_,OptionsPattern[]]:=Module[{LFs,RedLFs,amp1},
LFs=Cases[{amp},_LFA0i|_LFB0i|_LFC0i|_LFD0i,Infinity]//Union;
If[LFs==={},Return[amp]];
RedLFs=xReduceTensorOnce/@LFs;
amp1=If[OptionValue[$SetDto4],amp/.Thread[LFs->xSetDto4/@RedLFs],amp/.Thread[LFs->RedLFs]];
xTensorReduce2[amp1]
];


xReduceTensor[LFs_]/;MemberQ[{LFA0i,LFB0i,LFC0i,LFD0i},Head[LFs]]:=Module[
{reduce,kinmainv,Xinv,f,c,T,R,delt,getm,theta,til,tm,tT},(*tT=T;*)
reduce[a_]/;Head[a]===LFA0i:=tT[1][Sequence@@a[[1;;-2]]][List@@a[[-1;;-1]]];
reduce[a_]/;Head[a]===LFB0i:=tT[2][Sequence@@a[[1;;-4]]][List@@a[[-3;;-1]]];
reduce[a_]/;Head[a]===LFC0i:=tT[3][Sequence@@a[[1;;-7]]][List@@a[[-6;;-1]]];
reduce[a_]/;Head[a]===LFD0i:=tT[4][Sequence@@a[[1;;-11]]][List@@a[[-10;;-1]]];

(*===========================ReduceTensor .01================================*)
kinmainv[2, {p10_, p12_, p20_, m02_,m12_,m22_}] := Module[{detX,inversenum},
detX=p10 p20-((p10+p20-p12)/2)^2;
inversenum={{p20,-((p10+p20-p12)/2)},{-((p10+p20-p12)/2),p10}};
If[detX===0,Print["Error, Determinate zero"],inversenum/detX]];

(*kinmainv[2, {p10_, p12_, p20_, m02_,m12_,m22_}] := Module[{xp,xp1,xp2,X,detX,inversenum},
xp={xp1,xp2};
X=Table[scalarproduct[xp[[i]],xp[[j]]],{i,Length[xp]},{j,Length[xp]}]/.{scalarproduct[xp1]->p10,scalarproduct[xp2]->p20,scalarproduct[xp1,xp2]->(p10+p20-p12)/2};
detX=X//Det;
If[detX===0,Print["Error, Determinate zero"],X//Inverse]];*)

(*more quickly, though lengthy*)
kinmainv[3, {p10_, p12_, p23_, p30_, p20_, p13_,m02_, m12_, m22_, m32_}] := Module[{detX,inversenum},
detX=(p10 p20-1/4 (p10-p12+p20)^2) p30-1/2 (p20-p23+p30) (-(1/4) (p10-p12+p20) (p10-p13+p30)+1/2 p10 (p20-p23+p30))+1/2 (p10-p13+p30) (-(1/2) p20 (p10-p13+p30)+1/4 (p10-p12+p20) (p20-p23+p30));
inversenum={{p20 p30-1/4 (p20-p23+p30)^2,-(1/2) (p10-p12+p20) p30+1/4 (p10-p13+p30) (p20-p23+p30),-(1/2) p20 (p10-p13+p30)+1/4 (p10-p12+p20) (p20-p23+p30)},{-(1/2) (p10-p12+p20) p30+1/4 (p10-p13+p30) (p20-p23+p30),p10 p30-1/4 (p10-p13+p30)^2,1/4 (p10-p12+p20) (p10-p13+p30)-1/2 p10 (p20-p23+p30)},{-(1/2) p20 (p10-p13+p30)+1/4 (p10-p12+p20) (p20-p23+p30),1/4 (p10-p12+p20) (p10-p13+p30)-1/2 p10 (p20-p23+p30),p10 p20-1/4 (p10-p12+p20)^2}};
If[detX===0,Print["Error, Determinate zero"],inversenum/detX]];

(*kinmainv[3, {p10_, p12_, p23_, p30_, p20_, p13_,m02_, m12_, m22_, m32_}] := Module[{xp,xp1,xp2,xp3,X,detX,inversenum},
xp={xp1,xp2,xp3};
X=Table[scalarproduct[xp[[i]],xp[[j]]],{i,Length[xp]},{j,Length[xp]}]/.{scalarproduct[xp1]->p10,scalarproduct[xp2]->p20,scalarproduct[xp3]->p30,scalarproduct[xp1,xp2]->(p10+p20-p12)/2,scalarproduct[xp2,xp3]->(p20+p30-p23)/2,scalarproduct[xp1,xp3]->(p10+p30-p13)/2};
detX=X//Det;
If[detX===0,Print["Error, Determinate zero"],X//Inverse]];
*)
(*===========================ReduceTensor .02================================*)

(* Only for B1 and B11 the Xinv[1][1,1] will not be used. 09.12.13 why?*)
Xinv[1][1,1][{pp_,_,_}] :=1/pp;(*2-points*)
Xinv[2][i_, j_][a_List]:= Xinv[2][i,j][a] = kinmainv[2, a][[i,j]];(*3-points*)
Xinv[3][i_, j_][a_List]:= Xinv[3][i,j][a] = kinmainv[3, a][[i,j]];(*4-points*)

(*4.12 definition of fk=pk^2-mk^2+m0^2*) 
f[1][{pp_, m02_,m12_}] :=pp-m12+m02; 
f[1][{p10_,p12_,p20_, m02_,m12_,m22_}] :=p10-m12+m02; 
f[2][{p10_,p12_,p20_, m02_,m12_,m22_}] :=p20-m22+m02;
f[1][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=p10-m12+m02;
f[2][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=p20-m22+m02;
f[3][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=p03-m32+m02;

(* The translated argument lists obtained by canceling  *)
c[0][{pp_, m12_, m22_}] := {m22};
c[1][{pp_, m12_, m22_}] := {m12};
c[0][{p10_,p12_,p20_, m02_,m12_,m22_}] := {p12, m22, m12};(*09.12.13, changing the order of m12 and m22 by Yao*)(*07.01.2014The previous change by Yao is false, wasting me plenty of time!!!!*)
c[1][{p10_,p12_,p20_, m02_,m12_,m22_}] := {p20, m02, m22};
c[2][{p10_,p12_,p20_, m02_,m12_,m22_}] := {p10, m02, m12};
c[0][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
     {p13, p12, p23, m32, m12, m22};
c[1][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
     {p20, p23, p03, m02, m22, m32};
c[2][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
     {p10, p13, p03, m02, m12, m32};
c[3][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
     {p10, p12, p20, m02, m12, m22};

(*scalar functions*)
T[0][][___] := 0; (* in dimensional regularization *)
T[1][][{mm_}] := LFA0[mm];
T[2][][{pp_, m12_, m22_}] := LFB0[pp, m12, m22];
T[3][][{p10_,p12_,p20_, m02_,m12_,m22_}] := LFC0[p10,p12,p20,m02,m12,m22];
T[4][][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
                   LFD0[p10,p12,p23,p03,p20,p13, m02,m12,m22,m32];

(*===========================ReduceTensor .03================================*)
(* A Kronecker delta *)
delt = If[ #1 === #2, 1, 0]&;
(* getmdef *)
getm[{_}] := 0; getm[{_,_,_}] := 1; getm[{_,_,_,_,_,_}] := 2;
getm[{_,_,_,_,_,_,_,_,_,_}] := 3;

(*4.18*)
tT[N_Integer][0,0,i___Integer][a_List]:=Block[{P,M,k,epsi},
P=2+Length[{i}];M=getm[a];
1/($Dim+P-2-M) (R[N,0,0][i][a]-Sum[R[N,k][k,i][a],{k,M}])];

(* two special cases *)
R[n0__][j__][a_] := ( R[n0][Sequence @@ Sort[{j}]][a] ) /; !OrderedQ[{j}];
R[n0__][{}][a_] :=  R[n0][][a];

T[n0__][j__][a_] := ( T[n0][Sequence @@ Sort[{j}]][a] ) /; !OrderedQ[{j}];

(* special B-stuff*)
(*tT[2][1][{p10_,m02_,m12_}]   := LFB1[p10,  m02, m12];*)
(* XXX *)
(*tT[2][1,1][{p10_,m02_,m12_}] :=LFB11[p10, m02, m12] /;(p10 === 0);
tT[2][0,0,1][{p10_,0,0}]   := -(p10*LFB0[p10, 0, 0])/(8*(1 - $Dim));
tT[2][1,1,1][{p10_,0,0}]   := ((2 + $Dim)*LFB0[p10, 0, 0])/(8*(1 - $Dim));
*)

(*4.18*)
tT[N_Integer][k_Integer,i___Integer][a_List] := 
 Block[ {P, M ,r, kp },     
  P = 1 + Length[{i}]; M = getm[a];
   Sum[ Xinv[M][k, kp][a]  ( R[N,kp][i][a] - 
       Sum[ delt[ kp,{i}[[r]] ] * (T[N]@@Join[{0,0}, Delete[{i},r]])[a],
             {r, P-1} ]     ), {kp, M} ]];

(*===========================ReduceTensor .04================================*)
(*4.19, no M's in i *)
R[N_Integer, 0, 0][i___Integer][a_List] := Block[{q,P,M},
      q = Length[{i}]; P = 2 + q; M = getm[a];
      a[[-N]] T[N][i][a]  + T[N-1][i][ c[0][a] ]
                                                 ] /; FreeQ[{i}, getm[a]];

R[N_Integer,0,0][i___Integer, mm:(_Integer)..][a_List] := Block[
     {q,M,P,j,k},
      q = Length[{i}]; M = getm[a]; P = Length[{mm}] + 2 + q;
      a[[-N]]  T[N][i, mm][a] + 
(* here was the tough bug found by Ralph Schuster ... *)
      (-1)^(P - q) ( T[N - 1][i][c[0][a]] + Sum[
      Binomial[P - 2 - q, j] * Sum @@ Prepend[ Array[List[k[#], M - 1]&, j],
       (T[N-1]@@Join[{i}, Array[k,j]])[c[0][a]]], {j,P - 2 - q}] ) ] /; ({mm}[[1]] === getm[a]);

(* 4.19 , no M's*)
R[N_Integer, k_Integer][i___Integer][a_List] := Block[{q,P,M},
     q = Length[{i}]; P = 1 + q; M = getm[a];
     1/2( (T[N - 1] @@ til[i][k])[ c[k][a] ] theta[k, i] -
     f[k][a] T[N][i][a]  -  T[N - 1][i][c[0][a]] 
        )                                             ] /;
       FreeQ[{i}, getm[a]];

R[N_Integer,k_Integer][i___Integer, mm:(_Integer)..][a_List]:=Block[
      {q, P, M, kk, j},
      q = Length[{i}]; P = Length[{mm}] + 1 + q; M = getm[a];
       1/2( (T[N-1] @@ til[i,mm][k])[c[k][a]] theta[k, i, mm] -
       f[k][a] T[N][i,mm][a] -(-1)^(P - 1 - q) (
          T[N - 1][i][c[0][a]] + 
          Sum[ 
          Binomial[P - 1 - q, j]  Sum @@ Prepend[Array[List[kk[#], 
                                                       M -1 ]&,j
                                                      ],
                                 (T[N - 1]@@Join[{i}, 
                                                 Array[kk, j]])[c[0][a]]
                                                ], {j, P - 1 - q}
          ]))                                                        ] /;
                                          ({mm}[[1]] === getm[a]);


(* 4.20 *)
(* thetadef *)
theta[k_Integer, i___Integer] := 1 /; FreeQ[{i}, k];
theta[k_Integer, i___Integer] := 0 /;!FreeQ[{i}, k];
 
tm[a_Integer, b_Integer]:= a /; a<=b;
tm[a_Integer, b_Integer]:= (a-1) /; a > b;
til[][_]={};
til[x__][k_]:= (tm[#,k]&)/@{x}; 

reduce[LFs]//.T->tT(*Bug fixed on 12.12.13, here add //.T->tT, important*)
];


xReduceTensorOnce[LFs_]/;MemberQ[{LFA0i,LFB0i,LFC0i,LFD0i},Head[LFs]]:=Module[
{reduce,kinmainv,Xinv,f,c,T,R,delt,getm,theta,til,tm,tT},(*tT=T;*)
reduce[a_]/;Head[a]===LFA0i:=tT[1][Sequence@@a[[1;;-2]]][List@@a[[-1;;-1]]];
reduce[a_]/;Head[a]===LFB0i:=tT[2][Sequence@@a[[1;;-4]]][List@@a[[-3;;-1]]];
reduce[a_]/;Head[a]===LFC0i:=tT[3][Sequence@@a[[1;;-7]]][List@@a[[-6;;-1]]];
reduce[a_]/;Head[a]===LFD0i:=tT[4][Sequence@@a[[1;;-11]]][List@@a[[-10;;-1]]];


(*===========================ReduceTensor .01================================*)
kinmainv[2, {p10_, p12_, p20_, m02_,m12_,m22_}] := Module[{detX,inversenum},
detX=p10 p20-((p10+p20-p12)/2)^2;
inversenum={{p20,-((p10+p20-p12)/2)},{-((p10+p20-p12)/2),p10}};
If[detX===0,Print["Error, Determinate zero"],inversenum/detX]];

(*kinmainv[2, {p10_, p12_, p20_, m02_,m12_,m22_}] := Module[{xp,xp1,xp2,X,detX,inversenum},
xp={xp1,xp2};
X=Table[scalarproduct[xp[[i]],xp[[j]]],{i,Length[xp]},{j,Length[xp]}]/.{scalarproduct[xp1]->p10,scalarproduct[xp2]->p20,scalarproduct[xp1,xp2]->(p10+p20-p12)/2};
detX=X//Det;
If[detX===0,Print["Error, Determinate zero"],X//Inverse]];*)

(*more quickly, though lengthy*)
kinmainv[3, {p10_, p12_, p23_, p30_, p20_, p13_,m02_, m12_, m22_, m32_}] := Module[{detX,inversenum},
detX=(p10 p20-1/4 (p10-p12+p20)^2) p30-1/2 (p20-p23+p30) (-(1/4) (p10-p12+p20) (p10-p13+p30)+1/2 p10 (p20-p23+p30))+1/2 (p10-p13+p30) (-(1/2) p20 (p10-p13+p30)+1/4 (p10-p12+p20) (p20-p23+p30));
inversenum={{p20 p30-1/4 (p20-p23+p30)^2,-(1/2) (p10-p12+p20) p30+1/4 (p10-p13+p30) (p20-p23+p30),-(1/2) p20 (p10-p13+p30)+1/4 (p10-p12+p20) (p20-p23+p30)},{-(1/2) (p10-p12+p20) p30+1/4 (p10-p13+p30) (p20-p23+p30),p10 p30-1/4 (p10-p13+p30)^2,1/4 (p10-p12+p20) (p10-p13+p30)-1/2 p10 (p20-p23+p30)},{-(1/2) p20 (p10-p13+p30)+1/4 (p10-p12+p20) (p20-p23+p30),1/4 (p10-p12+p20) (p10-p13+p30)-1/2 p10 (p20-p23+p30),p10 p20-1/4 (p10-p12+p20)^2}};
If[detX===0,Print["Error, Determinate zero"],inversenum/detX]];

(*kinmainv[3, {p10_, p12_, p23_, p30_, p20_, p13_,m02_, m12_, m22_, m32_}] := Module[{xp,xp1,xp2,xp3,X,detX,inversenum},
xp={xp1,xp2,xp3};
X=Table[scalarproduct[xp[[i]],xp[[j]]],{i,Length[xp]},{j,Length[xp]}]/.{scalarproduct[xp1]->p10,scalarproduct[xp2]->p20,scalarproduct[xp3]->p30,scalarproduct[xp1,xp2]->(p10+p20-p12)/2,scalarproduct[xp2,xp3]->(p20+p30-p23)/2,scalarproduct[xp1,xp3]->(p10+p30-p13)/2};
detX=X//Det;
If[detX===0,Print["Error, Determinate zero"],X//Inverse]];
*)
(*===========================ReduceTensor .02================================*)

(* Only for B1 and B11 the Xinv[1][1,1] will not be used. 09.12.13 why?*)
Xinv[1][1,1][{pp_,_,_}] :=1/pp;(*2-points*)
Xinv[2][i_, j_][a_List]:= Xinv[2][i,j][a] = kinmainv[2, a][[i,j]];(*3-points*)
Xinv[3][i_, j_][a_List]:= Xinv[3][i,j][a] = kinmainv[3, a][[i,j]];(*4-points*)

(*4.12 definition of fk=pk^2-mk^2+m0^2*) 
f[1][{pp_, m02_,m12_}] :=pp-m12+m02; 
f[1][{p10_,p12_,p20_, m02_,m12_,m22_}] :=p10-m12+m02; 
f[2][{p10_,p12_,p20_, m02_,m12_,m22_}] :=p20-m22+m02;
f[1][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=p10-m12+m02;
f[2][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=p20-m22+m02;
f[3][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=p03-m32+m02;

(* The translated argument lists obtained by canceling  *)
c[0][{pp_, m12_, m22_}] := {m22};
c[1][{pp_, m12_, m22_}] := {m12};
c[0][{p10_,p12_,p20_, m02_,m12_,m22_}] := {p12, m22, m12};(*09.12.13, changing the order of m12 and m22 by Yao*)(*07.01.2014The previous change by Yao is false, wasting me plenty of time!!!!*)
c[1][{p10_,p12_,p20_, m02_,m12_,m22_}] := {p20, m02, m22};
c[2][{p10_,p12_,p20_, m02_,m12_,m22_}] := {p10, m02, m12};
c[0][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
     {p13, p12, p23, m32, m12, m22};
c[1][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
     {p20, p23, p03, m02, m22, m32};
c[2][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
     {p10, p13, p03, m02, m12, m32};
c[3][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
     {p10, p12, p20, m02, m12, m22};

(*scalar functions*)
T[0][][___] := 0; (* in dimensional regularization *)
T[1][][{mm_}] := LFA0[mm];
T[2][][{pp_, m12_, m22_}] := LFB0[pp, m12, m22];
T[3][][{p10_,p12_,p20_, m02_,m12_,m22_}] := LFC0[p10,p12,p20,m02,m12,m22];
T[4][][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
                   LFD0[p10,p12,p23,p03,p20,p13, m02,m12,m22,m32];
(*tensor functions*)(*added on 13.01.2014*)
T[1][ij__][{mm_}] := LFA0i[ij,mm];
T[2][ij__][{pp_, m12_, m22_}] := LFB0i[ij,pp, m12, m22];
T[3][ij__][{p10_,p12_,p20_, m02_,m12_,m22_}] := LFC0i[ij,p10,p12,p20,m02,m12,m22];
T[4][ij__][{p10_, p12_, p23_, p03_, p20_, p13_, m02_, m12_, m22_, m32_}] :=
                   LFD0i[ij,p10,p12,p23,p03,p20,p13, m02,m12,m22,m32];

(*===========================ReduceTensor .03================================*)
(* A Kronecker delta *)
delt = If[ #1 === #2, 1, 0]&;
(* getmdef *)
getm[{_}] := 0; getm[{_,_,_}] := 1; getm[{_,_,_,_,_,_}] := 2;
getm[{_,_,_,_,_,_,_,_,_,_}] := 3;

(*4.18*)
tT[N_Integer][0,0,i___Integer][a_List]:=Block[{P,M,k,epsi},
P=2+Length[{i}];M=getm[a];
1/($Dim+P-2-M) (R[N,0,0][i][a]-Sum[R[N,k][k,i][a],{k,M}])];

(* two special cases *)
R[n0__][j__][a_] := ( R[n0][Sequence @@ Sort[{j}]][a] ) /; !OrderedQ[{j}];
R[n0__][{}][a_] :=  R[n0][][a];

T[n0__][j__][a_] := ( T[n0][Sequence @@ Sort[{j}]][a] ) /; !OrderedQ[{j}];

(* special B-stuff*)
(*tT[2][1][{p10_,m02_,m12_}]   := LFB1[p10,  m02, m12];*)
(* XXX *)
(*tT[2][1,1][{p10_,m02_,m12_}] :=LFB11[p10, m02, m12] /;(p10 === 0);
tT[2][0,0,1][{p10_,0,0}]   := -(p10*LFB0[p10, 0, 0])/(8*(1 - $Dim));
tT[2][1,1,1][{p10_,0,0}]   := ((2 + $Dim)*LFB0[p10, 0, 0])/(8*(1 - $Dim));
*)

(*4.18*)
tT[N_Integer][k_Integer,i___Integer][a_List] := 
 Block[ {P, M ,r, kp },     
  P = 1 + Length[{i}]; M = getm[a];
   Sum[ Xinv[M][k, kp][a]  ( R[N,kp][i][a] - 
       Sum[ delt[ kp,{i}[[r]] ] * (T[N]@@Join[{0,0}, Delete[{i},r]])[a],
             {r, P-1} ]     ), {kp, M} ]];

(*===========================ReduceTensor .04================================*)
(*4.19, no M's in i *)
R[N_Integer, 0, 0][i___Integer][a_List] := Block[{q,P,M},
      q = Length[{i}]; P = 2 + q; M = getm[a];
      a[[-N]] T[N][i][a]  + T[N-1][i][ c[0][a] ]
                                                 ] /; FreeQ[{i}, getm[a]];

R[N_Integer,0,0][i___Integer, mm:(_Integer)..][a_List] := Block[
     {q,M,P,j,k},
      q = Length[{i}]; M = getm[a]; P = Length[{mm}] + 2 + q;
      a[[-N]]  T[N][i, mm][a] + 
(* here was the tough bug found by Ralph Schuster ... *)
      (-1)^(P - q) ( T[N - 1][i][c[0][a]] + Sum[
      Binomial[P - 2 - q, j] * Sum @@ Prepend[ Array[List[k[#], M - 1]&, j],
       (T[N-1]@@Join[{i}, Array[k,j]])[c[0][a]]], {j,P - 2 - q}] ) ] /; ({mm}[[1]] === getm[a]);

(* 4.19 , no M's*)
R[N_Integer, k_Integer][i___Integer][a_List] := Block[{q,P,M},
     q = Length[{i}]; P = 1 + q; M = getm[a];
     1/2( (T[N - 1] @@ til[i][k])[ c[k][a] ] theta[k, i] -
     f[k][a] T[N][i][a]  -  T[N - 1][i][c[0][a]] 
        )                                             ] /;
       FreeQ[{i}, getm[a]];

R[N_Integer,k_Integer][i___Integer, mm:(_Integer)..][a_List]:=Block[
      {q, P, M, kk, j},
      q = Length[{i}]; P = Length[{mm}] + 1 + q; M = getm[a];
       1/2( (T[N-1] @@ til[i,mm][k])[c[k][a]] theta[k, i, mm] -
       f[k][a] T[N][i,mm][a] -(-1)^(P - 1 - q) (
          T[N - 1][i][c[0][a]] + 
          Sum[ 
          Binomial[P - 1 - q, j]  Sum @@ Prepend[Array[List[kk[#], 
                                                       M -1 ]&,j
                                                      ],
                                 (T[N - 1]@@Join[{i}, 
                                                 Array[kk, j]])[c[0][a]]
                                                ], {j, P - 1 - q}
          ]))                                                        ] /;
                                          ({mm}[[1]] === getm[a]);


(* 4.20 *)
(* thetadef *)
theta[k_Integer, i___Integer] := 1 /; FreeQ[{i}, k];
theta[k_Integer, i___Integer] := 0 /;!FreeQ[{i}, k];
 
tm[a_Integer, b_Integer]:= a /; a<=b;
tm[a_Integer, b_Integer]:= (a-1) /; a > b;
til[][_]={};
til[x__][k_]:= (tm[#,k]&)/@{x}; 

reduce[LFs]
];


(* ::Subsubsection::Closed:: *)
(*xLTForm, xLTadapted, xLoopTools,xLFForm*)


xLTForm[amp_]:=Module[{LFs,sep,LT,Nfactor=1},
LFs=Cases[{amp},_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i|_DLFB0,Infinity]//Union;
LT[a_]/;Head[a]===LFA0:=Nfactor LoopTools`A0@@a;
LT[a_]/;Head[a]===LFB0:=Nfactor LoopTools`B0@@a;
LT[a_]/;Head[a]===LFC0:=Nfactor LoopTools`C0@@a;
LT[a_]/;Head[a]===LFD0:=Nfactor LoopTools`D0@@a;
LT[a_]/;Head[a]===LFA0i:=Module[{id1},
(a//xTensorReduce)/.LFA0->Nfactor LoopTools`A0];(*29.01.2014*)
(*id1="aa"<>StringJoin@@ToString/@a[[1;;-2]]//ToExpression;LoopTools`A0i@@Prepend[a[[-1;;-1]],id1]];(*Bug corrected on 09.12.13*)*)
LT[a_]/;Head[a]===LFB0i:=Module[{id2},
id2="bb"<>StringJoin@@ToString/@a[[1;;-4]]//ToExpression;Nfactor LoopTools`B0i@@Prepend[a[[-3;;-1]],id2]];
LT[a_]/;Head[a]===LFC0i:=Module[{id3},
id3="cc"<>StringJoin@@ToString/@a[[1;;-7]]//ToExpression;Nfactor LoopTools`C0i@@Prepend[a[[-6;;-1]],id3]];
LT[a_]/;Head[a]===LFD0i:=Module[{id4},
id4="dd"<>StringJoin@@ToString/@a[[1;;-11]]//ToExpression;Nfactor LoopTools`D0i@@Prepend[a[[-10;;-1]],id4]];

LT[a_]/;Head[a]===DLFB0:=Nfactor LoopTools`DB0@@a;

amp/.Thread[LFs->LT/@LFs]
]


xLTadapted[amp_]:=Module[{UncalculableQ,xLTuncalculableQ,xLTcalculable},
UncalculableQ[a_]/;Head[a]===LFB0i:=If[Length[a[[1;;-4]]]>=4,True,False];
UncalculableQ[a_]/;Head[a]===LFC0i:=If[Length[a[[1;;-7]]]>=5,True,False];
UncalculableQ[a_]/;Head[a]===LFD0i:=If[Length[a[[1;;-11]]]>=6,True,False];
xLTuncalculableQ[amp1_]:=Module[{LFs,LFsreduceonce,caseReduce},
LFs=Cases[{amp1},_LFB0i|_LFC0i|_LFD0i,Infinity]//Union;
MemberQ[UncalculableQ/@LFs//Union,True]];
xLTcalculable[amp2_]:=Module[{LFs,LFsreduceonce,caseReduce},
LFs=Cases[{amp2},_LFB0i|_LFC0i|_LFD0i,Infinity]//Union;
caseReduce=If[UncalculableQ[#],xSetDto4@xReduceTensorOnce[#],#]&;
amp2/.Thread[LFs->caseReduce/@LFs]];
NestWhile[xLTcalculable,amp,xLTuncalculableQ]
]


Options[xLoopTools]={$subtractFactor->-1,$renormalizationScale->0.939};
xLoopTools[amp_,OptionsPattern[]]:=Module[{link,LT,Nfactor=1/(16Pi^2),musquare=OptionValue[$renormalizationScale]^2},
link=Install["LoopTools"];
LoopTools`SetDelta[OptionValue[$subtractFactor]];(*The initial value for delta is 0, conresponding to MS bar regularization.*)
LoopTools`SetMudim[musquare];
    LT=Nfactor xLTForm[amp];
Uninstall[link];
Return[LT];]


xLFForm[exp0_](*20160317*):=Module[{rank=7,tuples,allsequence,sequence,getabcd,getabcdrule,exp2},
tuples=Join@@Table[Sort/@Tuples[{0,1,2,3},ii]//Union,{ii,1,rank}];
allsequence=Apply[sequence,tuples,{1}];
getabcd[exp_String]:=ToExpression@StringJoin[exp,StringJoin@@(ToString/@#)]&;
getabcdrule[exp_String]:=Drop[Thread[(getabcd[exp]/@allsequence)->allsequence]/.sequence->Sequence,{1}];
exp2=(exp0/.{A0i[aa0,x___]:>A0[x],B0i[bb0,x___]:>B0[x],C0i[cc0,x___]:>C0[x],D0i[dd0,x___]:>D0[x]}/.Join[getabcdrule["aa"],getabcdrule["bb"],getabcdrule["cc"],getabcdrule["dd"]]);
exp2/.{A0i[x___]:>LFA0i[x],B0i[x___]:>LFB0i[x],C0i[x___]:>LFC0i[x],D0i[x___]:>LFD0i[x]}/.{A0[x___]:>LFA0[x],B0[x___]:>LFB0i[x],C0[x___]:>LFC0[x],D0[x___]:>LFD0[x]}
]


(* ::Subsubsection::Closed:: *)
(*xUniquePaVe*)


xUniquePaVe[amp_]:=Module[{xb0,xc0,xd0},
xb0[a_, m1_,m2_] :=LFB0@@(SortBy[
{ {a,m1,m2},
{a,m2,m1} } ,
{#[[2;;3]],#[[1;;1]]}&
])[[1]];

xc0[a_,b_,c_, m1_,m2_,m3_] :=LFC0@@SortBy[
{ {a,b,c, m1,m2,m3},
{c,b,a, m1,m3,m2},
{a,c,b, m2,m1,m3},
{b,c,a, m2,m3,m1},
{c,a,b, m3,m1,m2},
{b,a,c, m3,m2,m1} },
{#[[4;;6]],#[[1;;3]]}&
][[1]];

xd0[p10_, p12_, p23_, p30_, p20_, p13_, m0_, m1_, m2_, m3_]:=LFD0@@(SortBy[{
   {p10, p12, p23, p30, p20, p13, m0, m1, m2, m3},
   {p10, p13, p23, p20, p30, p12, m0, m1, m3, m2},
   {p20, p12, p13, p30, p10, p23, m0, m2, m1, m3},
   {p20, p23, p13, p10, p30, p12, m0, m2, m3, m1},
   {p30, p13, p12, p20, p10, p23, m0, m3, m1, m2},
   {p30, p23, p12, p10, p20, p13, m0, m3, m2, m1},
   {p10, p20, p23, p13, p12, p30, m1, m0, m2, m3},
   {p10, p30, p23, p12, p13, p20, m1, m0, m3, m2},
   {p12, p20, p30, p13, p10, p23, m1, m2, m0, m3},
   {p12, p23, p30, p10, p13, p20, m1, m2, m3, m0},
   {p13, p30, p20, p12, p10, p23, m1, m3, m0, m2},
   {p13, p23, p20, p10, p12, p30, m1, m3, m2, m0},
   {p20, p10, p13, p23, p12, p30, m2, m0, m1, m3},
   {p20, p30, p13, p12, p23, p10, m2, m0, m3, m1},
   {p12, p10, p30, p23, p20, p13, m2, m1, m0, m3},
   {p12, p13, p30, p20, p23, p10, m2, m1, m3, m0},
   {p23, p30, p10, p12, p20, p13, m2, m3, m0, m1},
   {p23, p13, p10, p20, p12, p30, m2, m3, m1, m0},
   {p30, p10, p12, p23, p13, p20, m3, m0, m1, m2},
   {p30, p20, p12, p13, p23, p10, m3, m0, m2, m1},
   {p13, p10, p20, p23, p30, p12, m3, m1, m0, m2},
   {p13, p12, p20, p30, p23, p10, m3, m1, m2, m0},
   {p23, p20, p10, p13, p30, p12, m3, m2, m0, m1},
   {p23, p12, p10, p30, p13, p20, m3, m2, m1, m0}       }
,
{#[[7;;10]],#[[1;;6]]}&
])[[1]];


amp/.{LFB0->xb0,LFC0->xc0,LFD0->xd0}
]


(* ::Subsubsection::Closed:: *)
(*xOrderPaVe*)


xOrderPaVe[amp_]:=Module[{xb0,xc0,xd0},
xb0[a_, m1_,m2_] :=LFB0@@(Sort[
{ {a,m1,m2},
{a,m2,m1} } 
])[[1]];

xc0[a_,b_,c_, m1_,m2_,m3_] :=LFC0@@Sort[
{ {a,b,c, m1,m2,m3},
{c,b,a, m1,m3,m2},
{a,c,b, m2,m1,m3},
{b,c,a, m2,m3,m1},
{c,a,b, m3,m1,m2},
{b,a,c, m3,m2,m1} }
][[1]];

xd0[p10_, p12_, p23_, p30_, p20_, p13_, m0_, m1_, m2_, m3_]:=LFD0@@(Sort[{
   {p10, p12, p23, p30, p20, p13, m0, m1, m2, m3},
   {p10, p13, p23, p20, p30, p12, m0, m1, m3, m2},
   {p20, p12, p13, p30, p10, p23, m0, m2, m1, m3},
   {p20, p23, p13, p10, p30, p12, m0, m2, m3, m1},
   {p30, p13, p12, p20, p10, p23, m0, m3, m1, m2},
   {p30, p23, p12, p10, p20, p13, m0, m3, m2, m1},
   {p10, p20, p23, p13, p12, p30, m1, m0, m2, m3},
   {p10, p30, p23, p12, p13, p20, m1, m0, m3, m2},
   {p12, p20, p30, p13, p10, p23, m1, m2, m0, m3},
   {p12, p23, p30, p10, p13, p20, m1, m2, m3, m0},
   {p13, p30, p20, p12, p10, p23, m1, m3, m0, m2},
   {p13, p23, p20, p10, p12, p30, m1, m3, m2, m0},
   {p20, p10, p13, p23, p12, p30, m2, m0, m1, m3},
   {p20, p30, p13, p12, p23, p10, m2, m0, m3, m1},
   {p12, p10, p30, p23, p20, p13, m2, m1, m0, m3},
   {p12, p13, p30, p20, p23, p10, m2, m1, m3, m0},
   {p23, p30, p10, p12, p20, p13, m2, m3, m0, m1},
   {p23, p13, p10, p20, p12, p30, m2, m3, m1, m0},
   {p30, p10, p12, p23, p13, p20, m3, m0, m1, m2},
   {p30, p20, p12, p13, p23, p10, m3, m0, m2, m1},
   {p13, p10, p20, p23, p30, p12, m3, m1, m0, m2},
   {p13, p12, p20, p30, p23, p10, m3, m1, m2, m0},
   {p23, p20, p10, p13, p30, p12, m3, m2, m0, m1},
   {p23, p12, p10, p30, p13, p20, m3, m2, m1, m0}       }

])[[1]];


amp/.{LFB0->xb0,LFC0->xc0,LFD0->xd0}
]


(* ::Subsubsection::Closed:: *)
(*xMomentumIntegration*)


xMomentumIntegration0[FeynPara_List,fad_FeynAmplDenominator]:=Module[{nn=Length[fad],para,XX,coe,$p,$m,px,M2,FPintegrad},
If[Length[FeynPara]<nn-1,Print["number of Feynman parameters is not sufficient!!"];Abort[];,para=Table[FeynPara[[int]],{int,1,nn-1}];];
SetAttributes[#,Constant]&/@para;
XX=Product[para[[int]]^(int-1),{int,1,Length[para]}];
coe[int_]:=(1-UnitStep[int-2]para[[int-1]])Product[para[[ii]],{ii,int,Length[para]}]/;int<=nn;
$p=List@@fad[[All,1]]/.k->0;
$m=List@@fad[[All,2]];
px=Sum[coe[int]$p[[int]],{int,1,nn}];
M2=scalarproduct[px]+Plus@@(coe[#]($m[[#]]^2-scalarproduct[$p[[#]]])&/@Table[int,{int,nn}])//xExpandPair;
FPintegrad=I*(-1)^-nn*(Pi)^(D/2)*M2^(D/2-nn)*Gamma[nn-D/2]/Gamma[nn]*((nn-1)! XX)]


xMomentumIntegration[FeynPara_List,fad_FeynAmplDenominator]:=Module[{nn=Length[fad],para,XX,coe,$p,$m,px,M2,FPintegrad},
If[Length[FeynPara]<nn-1,Print["number of Feynman parameters is not sufficient!!"];Abort[];,para=Table[FeynPara[[int]],{int,1,nn-1}];];
SetAttributes[#,Constant]&/@para;
XX=Product[para[[int]]^(int-1),{int,1,Length[para]}];
coe[int_]:=(1-UnitStep[int-2]para[[int-1]])Product[para[[ii]],{ii,int,Length[para]}]/;int<=nn;
coe[0]=coe[nn];
$p=List@@fad[[All,1]]/.k->0;
$m=List@@fad[[All,2]];
px=Sum[coe[int-1]$p[[int]],{int,1,nn}];
M2=scalarproduct[px]+Plus@@(coe[#-1]($m[[#]]^2-scalarproduct[$p[[#]]])&/@Table[int,{int,nn}])//xExpandPair;
FPintegrad=I*(-1)^-nn*(Pi)^(D/2)*M2^(D/2-nn)*Gamma[nn-D/2]/Gamma[nn]*((nn-1)! XX)]


(* ::Subsubsection::Closed:: *)
(*xLFUVdivergent*)


xLFUVdivergent[amp_]:=Module[{amp1,LFs,sep,LT},
amp1=amp//xTensorReduce;
LFs=Cases[{amp1},_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i|_DLFB0,Infinity]//Union;
LT[a_]/;Head[a]===LFA0:=-a[[1]]UVepsR;
LT[a_]/;Head[a]===LFB0:=-UVepsR;
LT[a_]/;Head[a]===LFC0:=0;
LT[a_]/;Head[a]===LFD0:=0;
Coefficient[amp1/.Thread[LFs->LT/@LFs],UVepsR]UVepsR
]


(* ::Subsubsection::Closed:: *)
(*xMandelstamRules*)


(* define: p1,p2 are incoming, and p3,p4 are outgoing *)(*29.10.14*)
xMandelstamRules2OffShell[{p1_,p2_,p3_,p4_}]:={scalarproduct[p1,p2]->1/2 (s-scalarproduct[p1,p1]-scalarproduct[p2,p2]),
scalarproduct[p3,p4]->1/2 (s-scalarproduct[p3,p3]-scalarproduct[p4,p4]),
scalarproduct[p1,p3]->-(1/2) (t-scalarproduct[p1,p1]-scalarproduct[p3,p3]),
scalarproduct[p2,p4]->-(1/2) (t-scalarproduct[p2,p2]-scalarproduct[p4,p4]),
scalarproduct[p1,p4]->-(1/2) (u-scalarproduct[p1,p1]-scalarproduct[p4,p4]),
scalarproduct[p2,p3]->-(1/2) (u-scalarproduct[p2,p2]-scalarproduct[p3,p3]),
scalarproduct[p1+p2,p1+p2]->s,scalarproduct[p3+p4,p3+p4]->s,
scalarproduct[p1-p3,p1-p3]->t,scalarproduct[p2-p4,p2-p4]->t,
scalarproduct[p1-p4,p1-p4]->u,scalarproduct[p2-p3,p2-p3]->u};

xMandelstamRules2OnShell[{m1_,m2_,m3_,m4_}]:=Module[{Onshellrules},Onshellrules={scalarproduct[p1,p2]->1/2 (s-m1^2-m2^2),
scalarproduct[p3,p4]->1/2 (s-m3^2-m4^2),
scalarproduct[p1,p3]->-(1/2) (t-m1^2-m3^2),
scalarproduct[p2,p4]->-(1/2) (t-m2^2-m4^2),
scalarproduct[p1,p4]->-(1/2) (u-m1^2-m4^2),
scalarproduct[p2,p3]->-(1/2) (u-m2^2-m3^2),
scalarproduct[p1+p2,p1+p2]->s,scalarproduct[p3+p4,p3+p4]->s,
scalarproduct[p1-p3,p1-p3]->t,scalarproduct[p2-p4,p2-p4]->t,
scalarproduct[p1-p4,p1-p4]->u,scalarproduct[p2-p3,p2-p3]->u,
scalarproduct[p1]->m1^2,
scalarproduct[p2]->m2^2,
scalarproduct[p3]->m3^2,
scalarproduct[p4]->m4^2,
scalarproduct[p1,p1]->m1^2,
scalarproduct[p2,p2]->m2^2,
scalarproduct[p3,p3]->m3^2,
scalarproduct[p4,p4]->m4^2}];


(* ::Subsubsection::Closed:: *)
(*xCollect, xCollect2*)


(*Collect the expression in terms of the loop integrals*)
SetAttributes[xCollect,Listable]
xCollect[amp_]:=Module[{head,LFs},
head=_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i|_DLFB0;
LFs=Cases[{amp},head,Infinity]//Union;
Collect[amp,LFs,Simplify]];

SetAttributes[xCollect2,Listable]
xCollect2[amp_]:=Module[{head,LFs},
head=_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i|_DLFB0;
LFs=Cases[{amp},head,Infinity]//Union;
Collect[amp,LFs,Together]];

xLFsimplify[exp_]:=Module[{lfs},
lfs=Cases[exp,_LFA0|_LFB0|_LFC0,Infinity];
exp/.Thread[lfs->Simplify[lfs]]
]

SetAttributes[xCollect4,Listable]
xCollect4[amp_]:=Module[{head,LFs},
head=_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i|_DLFB0|Derivative[x___][y_][z___];
LFs=Cases[{amp},head,Infinity]//Union;
Collect[amp,LFs,Simplify]];


(* ::Subsubsection::Closed:: *)
(*xIRRegularPart*)


(*2015-06-10 taken from pins.m*)
xIRRegularPart[FP_List,fad_FeynAmplDenominator,power_Integer][mn_,MandelstamRules_List,ExpandPara_List,xalpha_]:=Module[{momint,momintSeries,FPint0,FPint,kappa,UVR,eps,FPintsep},
kappa[1]=mn^2 (UVR+Log[mn^2/$mu^2]);
kappa[2]=-(1+UVR+Log[mn^2/$mu^2]);
kappa[3]=-(1/(2mn^2))(1+UVR+Log[mn^2/$mu^2])eps;
kappa[4]=-(1/(6mn^4))(1+UVR+Log[mn^2/$mu^2])(1+eps)eps;
momint=xMomentumIntegration[FP,fad]/.MandelstamRules/.ExpandPara/.{Gamma[alpha_-D/2]:>(kappa[alpha]*Gamma[alpha]*(mn^2)^(alpha-D/2))/(I Pi^(D/2))};
momintSeries=If[Head[power]===List,SeriesCoefficient[momint,{xalpha,0,power[[1]]}]xalpha^power[[1]],Series[momint,{xalpha,0,power}]//Normal];
(*FPint=If[Length[fad]>=2,Integrate[momintSeries,Sequence@@(Reverse[{FP[[#]],0,1}&/@Table[ik,{ik,1,Length[fad]-1}],1]),Assumptions->D>50],momintSeries];*)
FPint0[arg_]:=Integrate[arg,Sequence@@(Reverse[{FP[[#]],0,1}&/@Table[ik,{ik,1,Length[fad]-1}],1]),Assumptions->D>50];
FPint=If[Length[fad]>=2,If[Head[momintSeries]===Plus,FPint0/@momintSeries,FPint0[momintSeries]],momintSeries];
FPintsep=xSeparate[Series[FPint/.D->4-2eps,{eps,0,1}]//Normal,UVR,eps];
Collect[FPintsep[[1]].(FPintsep[[2]]/.UVR*eps->-1)/.{eps->0,UVR->UVepsR},xalpha,Simplify]+$HIGHORDER xalpha^(Sequence@@Flatten[{power}]+1) UnitStep[-Length[power]]
]


(* ::Subsubsection::Closed:: *)
(*xPVReductionRules*)


xPVReductionRules[LoopAmp_List]:=Module[{LFis},
LFis=Cases[LoopAmp,_LFA0i|_LFB0i|_LFC0i|_LFD0i,Infinity]//Union;
Thread[LFis->((xTensorReduce/@LFis)//xCollect)]
]
xPVReductionRules0[LoopAmp_List]:=Module[{LFis},
LFis=Cases[LoopAmp,_LFA0i|_LFB0i|_LFC0i|_LFD0i,Infinity]//Union;
Thread[LFis->((xTensorReduce/@LFis))]
]


(* ::Subsubsection::Closed:: *)
(*Derivative of B0 (only valid in dimension 4)*)


xDLFB0[p_,m12_,m22_]:=Module[{m1=Sqrt[m12],m2=Sqrt[m22]},((-p+m1^2+m2^2)p-LFA0[m2^2](p+m1^2-m2^2)-LFA0[m1^2](p-m1^2+m2^2)+LFB0[p,m1^2,m2^2](p(m1^2+m2^2)-(m1^2-m2^2)^2))/(p(m1^4-2(p+m2^2)m1^2+(p-m2^2)^2))]


(* ::Subsubsection::Closed:: *)
(*Davy Reduction*)


(*up to four-point reduction*)
(*ScalarReduce[exp_]:=Module[
{Ilist,ilist,II0},
Ilist=Cases[{exp},_I0,Infinity]//Union;
ilist=Table[ReduceScalar[$I0@@Ilist[[i]]],{i,Ilist//Length}];
Thread[(Ilist/.I0->II0)->ilist]/.Rule->Set;
exp/.I0->II0
];*)
(*$MandelstamRules=MandelstamRules/.{u->2m1^2+2m2^2-s-t};*)
ScalarReduce[exp_,manrules_List]:=Module[
{Ilist,$Ilist},
Ilist=Cases[{exp},_I0,Infinity]//Union;
$Ilist=Ilist/.{I0[x___]:>$I0[x]};
exp/.Thread[Ilist->((ReduceScalar[#,manrules]&)/@$Ilist)]
];
ScalarReduce[exp_]:=ScalarReduce[exp,{}];


RNSN[scalar0_$I0]:=Module[
{RN,SN,n,cancel,scalar,detRN,detSN},
cancel[exp_]:=exp/.$I0->I0/.I0->$I0;
scalar=scalar0//cancel;
n=scalar[[2]]//Length;
RN=Array[scalarproduct[scalar[[2,#1,1]]-scalar[[2,#2,1]]]-scalar[[2,#1,2]]^2-scalar[[2,#2,2]]^2&,{n,n}]//xExpandPair//Simplify;
SN=Prepend[Prepend[#,1]&/@RN,Prepend[Table[1,{i,Length[scalar[[2]]]}],0]];
detRN=RN//Det//Simplify;
detSN=SN//Det//Simplify;
{RN,SN,detRN,detSN}
];


ReduceScalar[scalar0_$I0,manrules_List]:=Module[
{temp,RN,SN,detRN,detSN,norm=1(*4\[Pi] \[Mu]r^2*),n,cancel,cancel0,scalar,nuA,ss,z0,c,cc,z,sum,nu,s3,s4,rightcolumn,zz,i,j,k},
If[MatchQ[Simplify[scalar0[[2]]],{{_,0,0}}],
If[Simplify[scalar0[[1]]-(D-4)===0],
Return[(-norm)^2*(D-4)*(D-3)(*Deliang 150911*(I*\[Pi]^2)/(2\[Pi])^4*)*LFB0[0,0,0]],Return[0]];     ];(*When detSN=!=0&&detRN===0---according to Eq .22*)
If[MatchQ[Simplify[scalar0[[2]]],{{_,0,1}}],
If[Simplify[scalar0[[1]]-(D-2)===0],
Return[-norm*(D-3)(*Deliang 150911*(I*\[Pi]^2)/(2\[Pi])^4*)*LFB0[0,0,0]],Return[0]];    ];
cancel[exp_]:=ScalarReduce[exp/.$I0->I0//Simplify,manrules](*/.I0->$I0;*);
cancel0[exp_]:=exp/.$I0->I0/.I0->$I0;
scalar=scalar0//cancel0;
n=scalar[[2]]//Length;
If[scalar[[1]]===D&&Union[scalar[[2,All,3]]]==={1},Return[ScalarBase[I0@@scalar[[2]]]]]/.manrules;
RN=(Array[scalarproduct[scalar[[2,#1,1]]-scalar[[2,#2,1]]]-scalar[[2,#1,2]]^2-scalar[[2,#2,2]]^2&,{n,n}]//xExpandPair//Simplify)/.manrules;
SN=(Prepend[Prepend[#,1]&/@RN,Prepend[Table[1,{i,Length[scalar[[2]]]}],0]])/.manrules;
detRN=Det[RN]//Simplify;
detSN=Det[SN]//Simplify;
(*Print[{detSN,detRN,SN,RN}];Abort[];*)
ss=scalar;
(*--------------------------------------1----------------------------------------------*)
If[detSN=!=0&&detRN=!=0,
z0=1;
c=-z0*detRN/detSN;
z=LinearSolve[RN,Table[c,{i,n}]];
(*1-1*)
(*Eq .21,Eq,18*)
If[Simplify[scalar[[1]]-D>0],

If[Union[scalar[[2,All,3]]]==={1},
(*Eq .18*)
ss[[1]]=ss[[1]]-2;
sum=c*ss;
Do[ss[[2,i,3]]=ss[[2,i,3]]-1;sum=sum-z[[i]]*ss;ss[[2,i,3]]=ss[[2,i,3]]+1;,{i,n}];

Return[1/(norm*(scalar[[1]]-1-Plus@@scalar[[2,All,3]]))*sum//cancel]
,
(*Eq .21*)
For[k=1,k<=n,k++,If[scalar[[2,k,3]]>1,Break[];]];
ss[[2,k,3]]-=1;
nu=ss[[2,All,3]];
ss[[1]]-=2;

rightcolumn=1/norm*Table[s3=ss;Sum[s3=ss;s3[[2,j,3]]-=1;(z[[j]]-KroneckerDelta[j,i])*s3,{j,n}],{i,n}];
rightcolumn-=1/norm*c*ss;
(*Print[rightcolumn];Abort[];*)

Return[cancel[1/nu[[k]]*LinearSolve[RN,rightcolumn][[k]]]]
];

];
(*1-2*)
(*Eq .15*)
If[Simplify[scalar[[1]]-D<0],
sum=0;
Do[s3=ss;s3[[2,i,3]]-=1;sum+=z[[i]]*s3,{i,n}];
ss[[1]]+=2;
Return[cancel[(sum+norm*(ss[[1]]-1-Plus@@scalar[[2,All,3]])*z0*ss)/c]];
];
(*1-3*)
(*Eq .19*)
If[Simplify[scalar[[1]]-D===0],
(*If[i>1,Abort[]];*)
(*in this case Union[nu]=!={1},and the following For expression make sense*)
For[k=1,k<=n,k++,If[scalar[[2,k,3]]>1,Break[];]];
ss[[2,k,3]]-=1;
nu=ss[[2,All,3]];
rightcolumn=Table[s3=ss;s3[[2,k,3]]-=1;Sum[s4=s3;s4[[2,j,3]]+=1;nu[[j]]*s4,{j,n}],{k,n}];
rightcolumn=rightcolumn-(scalar[[1]]-Plus@@nu)*ss;
(*If[Length@rightcolumn=!=n||Length@RN[[1]]=!=n,Return[Hold/@{RN,rightcolumn,"Simplify[scalar[[1]]===D]"}];Abort[]]*)
(*Print[rightcolumn,ss];*)
Return[cancel[1/nu[[k]]*LinearSolve[RN,rightcolumn][[k]]]]
];
];

(*--------------------------------------2----------------------------------------------*)
If[detSN=!=0&&detRN===0,(*For d=D D-->D-2,reduce nu and realize D-2->D other channels*)

If[Simplify[scalar[[1]]-1-Plus@@scalar[[2,All,3]]-(D-4)=!=0],
z0=1;
z=LinearSolve[SN,Prepend[Table[0,{i,n}],z0]];
If[z[[1]]=!=0,Print["detRN===0&&detSN=!=0 No.1"]];
z=Drop[z,1];
ss[[1]]=ss[[1]]-2;
sum=0;
Do[ss[[2,i,3]]=ss[[2,i,3]]-1;sum=sum-z[[i]]*ss;ss[[2,i,3]]=ss[[2,i,3]]+1,{i,n}];
Return[1/(norm*(scalar[[1]]-1-Plus@@scalar[[2,All,3]]))*sum//cancel]
];

If[Simplify[scalar[[1]]-1-Plus@@scalar[[2,All,3]]-(D-4)===0]&&(Union[scalar[[2,All,3]]]=!={1}),
For[k=1,k<=n,k++,If[scalar[[2,k,3]]>1,Break[];]];
ss[[2,k,3]]-=1;
nu=ss[[2,All,3]];
rightcolumn=Table[s3=ss;s3[[2,k,3]]-=1;Sum[s4=s3;s4[[2,j,3]]+=1;nu[[j]]*s4,{j,n}],{k,n}];
rightcolumn-=(scalar[[1]]-Plus@@nu)*ss;
ss[[1]]-=2;
PrependTo[rightcolumn,-(1/norm)*ss];
ss[[1]]+=2;
Return[cancel[LinearSolve[SN,rightcolumn][[k+1]]/nu[[k]]]];

];

If[Simplify[scalar[[1]]-1-Plus@@scalar[[2,All,3]]-(D-4)===0]&&(Union[scalar[[2,All,3]]]==={1}),
Print[{"detSN=!=0&&detRN===0--1",scalar}];Abort[];
];

Print["detSN=!=0&&detRN===0---End"];Abort[];
];

(*--------------------------------------3----------------------------------------------*)
If[detSN===0&&detRN=!=0,
c=1;
cc=Table[c,{i,1,n}];
z=LinearSolve[RN,cc];
sum=0;
Do[ss[[2,i,3]]=ss[[2,i,3]]-1;
sum=sum+z[[i]]*ss;
ss[[2,i,3]]=ss[[2,i,3]]+1;,{i,n}];
(*Print[sum];Abort[];*)
Return[cancel[sum]]
];

(*--------------------------------------4----------------------------------------------*)
If[detSN===0&&detRN===0,
zz=NullSpace[SN];
If[zz==={},Print["detRN===0&&detSN===0--no solution"];Abort[]];
z=Sort[zz,
Length[Complement[#1,{0}]]<Length[Complement[#2,{0}]]&
][[1]];(*z=Select[zz,Simplify[#[[1]]===0&]]*)
c=-z[[1]];
z=Drop[z,1];
If[c=!=0,
(*Eq .26*)
z=z/c;
sum=0;
Do[s3=ss;s3[[2,i,3]]-=1;sum+=z[[i]]*s3;,{i,n}];
Return[cancel[sum]]
,
(*Eq .28*)
For[i=2;j=1,i<=n,i++,If[z[[j]]===0||z[[i]]=!=0&&scalar[[2,i,3]]>scalar[[2,j,3]],j=i]];
ss[[2,j,3]]+=1;
sum=0;
Do[If[i=!=j,s3=ss;s3[[2,i,3]]-=1;sum+=z[[i]]*s3],{i,n}];

Return[cancel[-sum/z[[j]]]];
];

];
Print[{"Error: ReduceScalar--The End",detRN,detSN,RN,SN,ss}];
];


(* 
I0[D,__]=
  \[Mu]^(4-D) \[Integral]\[DifferentialD]^Dq/((2\[Pi])^D) .../(q^2-m^2)... ;
   I0[D,__]===(I*\[Pi]^2)/(2\[Pi])^4*A0;
LoopTools===A0:
(2\[Pi])^4 \[Mu]^(4-D)/(I \[Pi]^2) \[Integral]\[DifferentialD]^Dq/((2\[Pi])^D) .../(q^2-m^2)... ;
A0===r\[CapitalGamma]*Ellis;
*)
(*Delete[{1,2,3,4},{{1},{4}}]*)

I0[d_,fad_List]/;Head[d]=!=List&&!FreeQ[fad[[All,3]],0]:=I0[d,Delete[fad,{#}&/@Position[fad[[All,3]],0][[All,1]]]];

I0[d_,{}]/;d=!=D:=0;

I0[d_,{}]/;d===D:=0;(*Deliang Yao 2015.08.14*)

I0[d_,{xx___,{x_,y_,m_},{x_,y_,n_},zz___}]:=I0[d,{xx,{x,y,m+n},zz}];(*Deliang Yao 2015.08.14*)
I0[d_,{xx___,{x_,y_,m_},yy__,{x_,y_,n_},zz___}]:=I0[d,{xx,{x,y,m},{x,y,n},yy,zz}];(*Deliang Yao 2015.08.14*)

LFA0[0]=0;(*Deliang 0919*)

(*LFC0[0,0,0,0,0,0]=0;*)

InScalarBase[exp_]:=Module[
{ifad,FAD=FeynAmplDenominator},
If[FreeQ[exp,I0]&&FreeQ[exp,FAD],Return[exp]];
ifad=Union@Cases[{exp},_I0|_FAD,Infinity];
exp/.Thread[ifad->ScalarBase/@ifad]
];

(*I0[{p,m(*,1*)},{}..]--no q--D-Dimension*)
$ABCD=_LFA0|_LFB0|_LFC0|_LFD0;

SF[exp_]:=Union@Cases[exp,$ABCD,Infinity];

Options[ScalarBase]={OutPutForm->ABCD};
ScalarBase[fad0_,OptionsPattern[]]/;!FreeQ[{FeynAmplDenominator,I0},Head[fad0]]:=Module[
{len,temp,fad,factor,FAD=FeynAmplDenominator,UniqueFAD=xUniqueFAD,SP=scalarproduct,ExpandPair=xExpandPair,UniqueScalar=xUniquePaVe},
If[Head[fad0]===FAD,temp=UniqueFAD[fad0];fad=Cases[{temp},_FAD,Infinity][[1]]/.k->0;factor=temp/.FAD[__]:>1,fad=fad0;factor=1;];
If[OptionValue[OutPutForm]===ABCD,
len=fad//Length;
factor*(*((I*\[Pi]^2)/((2\[Pi])^4))**)Switch[len,
1,
    LFA0[fad[[1,2]]^2],
2,
    LFB0[SP[fad[[2,1]]-fad[[1,1]]],fad[[1,2]]^2,fad[[2,2]]^2],
3,
    LFC0[SP[fad[[2,1]]-fad[[1,1]]],SP[fad[[3,1]]-fad[[2,1]]],SP[fad[[3,1]]-fad[[1,1]]],    fad[[1,2]]^2,fad[[2,2]]^2,fad[[3,2]]^2],
4,
    LFD0[SP[fad[[2,1]]-fad[[1,1]]],SP[fad[[3,1]]-fad[[2,1]]],SP[fad[[4,1]]-fad[[3,1]]],   SP[fad[[4,1]]-fad[[1,1]]],SP[fad[[3,1]]-fad[[1,1]]],SP[fad[[4,1]]-fad[[2,1]]], fad[[1,2]]^2,fad[[2,2]]^2,fad[[3,2]]^2,fad[[4,2]]^2],
_,"error in ScalarBase"
]//ExpandPair//Simplify//UniqueScalar
,
factor*fad
]
];
(*Some finite Scalar Functions*)
LFC0[-m_,0,m_,0,m_,m_]/;m=!=0:=-(\[Pi]^2/(8m));
LFC0[0,0,4m_,m_,m_,m_]/;m=!=0:=-(1/(4m))(-(1/2)\[Pi](3\[Pi]+4I Log[2]));


(* ::Subsubsection::Closed:: *)
(*Schwinger Patametrization*)


xSchwingerPara[III0_I0]:=xSchwingerPara[III0,{{$$Z1,$$Z2,$$Z3,$$Z4},{$$\[Zeta]1,$$\[Zeta]2,$$\[Zeta]3,$$\[Zeta]4}}]


xSchwingerPara[III0_I0,{{Z1_,Z2_,Z3_,Z4_},{\[Zeta]1_,\[Zeta]2_,\[Zeta]3_,\[Zeta]4_}}](*up to 4 points*):=Module[
{d=III0[[1]],nlen,xSchPar,xIntMom,xIntLam,$Momlist,$SchPars,x1,x2,x3,x4,x5,x6,
sp=scalarproduct,mom=momentum,SchExp,SchExpPowerPart,SchExpPrefactor,xA,xB2,xC,
IntkExp,\[Lambda],Z\[Zeta]s,(*Z1,Z2,Z3,Z4,\[Zeta]1,\[Zeta]2,\[Zeta]3,\[Zeta]4,*)DetXZ,IntkExp2,IntkPre,IntkPre2,IntkPow,
x\[Alpha],x\[Beta],IntLam},
(*-----------1. Auxiliary function------------------------*)
(**)
(*Schwinger Parametrization Eq .3*)
xSchPar[{q_,m_,\[Alpha]_},x_]:=I^-\[Alpha]/Gamma[\[Alpha]] x^(\[Alpha]-1) Exp[I x (scalarproduct[q]-m^2)];
(*Integrate Momentum Eq .4*)
xIntMom[{A_,B2_},n_]:=I^((*1*)-n/2) (*Pi^(n/2)*) A^-(n/2) Exp[-I *B2/A];(*B2=B^2*)
(*Integrate Schwinger Parameters (
Eq .10*)
xIntLam[\[Alpha]_,\[Beta]_]:=I^(-\[Alpha]-1) Gamma[\[Alpha]+1]\[Beta]^(-\[Alpha]-1);
(**)
(*--------------2. Collect the propagator-----------------------*)
$Momlist=III0[[2]];
nlen=Length[$Momlist];
$Momlist[[All,1]]=$Momlist[[All,1]]+k;
$SchPars=Take[{x1,x2,x3,x4,x5,x6},Length[$Momlist]];
SchExp=Times@@Table[xSchPar[$Momlist[[inti]],$SchPars[[inti]]],{inti,1,Length[$Momlist]}];
(*3. Integrate the interl momentum k*)
SchExpPrefactor=SchExp/.Power[E,x___]:>1;
SchExpPowerPart=CoefficientList[xExpandPair[(SchExp/SchExpPrefactor)[[2]]]/.{sp[k]->k^2,sp[k,x___]:>k mom[x]},k];
xA=(SchExpPowerPart[[3]]/I)/.x1->(\[Lambda]+x1-Plus@@$SchPars);
xB2=xExpandPair[sp[SchExpPowerPart[[2]]/(-2I)]]/.{sp[x_ mom[y_]]:>x^2 sp[y],sp[x_ mom[y_],a_ mom[b_]]:>x a sp[y,b]};
xC=SchExpPowerPart[[1]]/I;
IntkExp=SchExpPrefactor*xIntMom[{xA,xB2},d]*Exp[I xC];
(*------------------3. Integrate lambda----------------------*)
Z\[Zeta]s={{\[Lambda]},{\[Lambda]*\[Zeta]1,\[Lambda]*Z1},{\[Lambda]*\[Zeta]1,\[Lambda]*Z1*\[Zeta]2,\[Lambda]*Z1*Z2},{\[Lambda]*\[Zeta]1,\[Lambda]*Z1*\[Zeta]2,\[Lambda]*Z1*Z2*\[Zeta]3,\[Lambda]*Z1*Z2*Z3}};
DetXZ={1,\[Lambda],\[Lambda]^2*Z1,\[Lambda]^3*Z1^2*Z2};
IntkExp2=(IntkExp*DetXZ[[nlen]]/.Thread[$SchPars->(Z\[Zeta]s[[nlen]])])//Simplify//PowerExpand;
IntkPre=IntkExp2/.Power[E,x___]:>1//PowerExpand;
IntkPre2=IntkPre/.{\[Lambda]->1}//Simplify;
IntkPow=IntkExp2/IntkPre//PowerExpand;
x\[Alpha]=(IntkPre/IntkPre2//Simplify)/.Power[\[Lambda],x___]:>x;
x\[Beta]=IntkPow[[2]]/(-I \[Lambda]);
IntLam={IntkPre2*xIntLam[x\[Alpha],my\[Beta]],my\[Beta]->x\[Beta]}
]


(* ::Subsubsection::Closed:: *)
(*xToDavy*)


xToDavy[LF_,{p1_,p2_,p3_}]/;(Head[LF]===LFA0)||(Head[LF]===LFB0)||(Head[LF]===LFC0)||(Head[LF]===LFD0):=Module[{m1,m2,m3,m4,p21,p32,p43,p41,p31,p42,m12,m22,m32,m42,nlen,rules,int,sp=scalarproduct},
nlen=Length[LF];
Switch[nlen,
1,
{m1}=Sqrt[List@@(Take[LF,{1}])]//PowerExpand;
rules={};
int=I0[D,{{0,m1,1}}];,
3,
{m1,m2}=Sqrt[List@@(Take[LF,{2,3}])]//PowerExpand;
{p21}=List@@Take[LF,{1}];
rules={sp[p1]->p21};
int=I0[D,{{0,m1,1},{p1,m2,1}}];,
6,
{m1,m2,m3}=Sqrt[List@@(Take[LF,{4,6}])]//PowerExpand;
{p21,p32,p31}=List@@Take[LF,{1,3}];
rules={sp[p1]->p21,sp[p2]->p31,sp[p2,p1]->(p21+p31-p32)/2};
int=I0[D,{{0,m1,1},{p1,m2,1},{p2,m3,1}}];,
10,
{m1,m2,m3,m4}=Sqrt[List@@(Take[LF,{7,10}])]//PowerExpand;
{p21,p32,p43,p41,p31,p42}=List@@Take[LF,{1,6}];
rules={sp[p1]->p21,sp[p2]->p31,sp[p3]->p41,sp[p2,p1]->(p21+p31-p32)/2,sp[p3,p2]->(p41+p31-p43)/2,sp[p3,p1]->(p41+p21-p42)/2};
int=I0[D,{{0,m1,1},{p1,m2,1},{p2,m3,1},{p3,m4,1}}];,
_,
Print["xToDavy::only for LFA0,LFB0,LFC0,LFD0"]
];
Return[{int,rules}]
]


(* ::Subsubsection::Closed:: *)
(*Derivatives on scalar integrals*)


ruleint={LFB0[0,0,0]->0,
LFB0[0,m12_,m22_]/;m12=!=m22:>(LFA0[m12]-LFA0[m22])/(m12-m22),
LFB0[0,m12_,m22_]/;m12===m22:>-1+LFA0[m12]/m12,
LFB0[m22_,0,m22_]:>1+LFA0[m22]/m22};

ruleintD={LFB0[0,0,0]->LFB0[0,0,0],(*might contribute finite pieces*)
LFB0[0,m12_,m22_]/;m12=!=m22:>(LFA0[m12]-LFA0[m22])/(m12-m22)(*derived by apart*),
LFB0[0,m12_,m22_]/;m12===m22:>((-2+D) LFA0[m12])/(2 m12),
LFB0[m22_,0,m22_]:>((-2+D) LFA0[m22])/(2 (-3+D) m22 )};


(*1-point one-loop scalar integrals*)


der[{n1_},intA0_LFA0]:=Module[{m1},
m1=intA0[[1]]//Sqrt//PowerExpand;
n1! (*n! added on 25.09.2015*)ScalarReduce[I0[D,{{0,m1,n1+1}}],{}]/.ruleintD(*/.ruleint//xSetDto4*)//xCollect
]
der[{n1_},LFA0[0]]=0;


(*2-point one-loop scalar integrals*)


der[{n1_,n2_,n3_},intB0_LFB0]:=
Module[
{derlist,int2,int2power,you\[Beta],my\[Beta],
p21,m12,m22,m1,m2,
Z1,\[Zeta]1,
coelist,Eqs,Sols,prefacors,results,
d,\[Alpha],\[Beta],\[Gamma],d1,\[Alpha]1,\[Beta]1,\[Gamma]1,
p1,p2,$p1,$p2,$p3,$m1,$m2,$m3,$d,$\[Alpha],$\[Beta],
infoB0,rulemass,ruleindex,rulemom},
(*1. Schwinger Parametrization for template: I0[{D,{0,m1,\[Alpha]},{p1,m2,\[Beta]},{p2,m3,\[Gamma]}}],
which can be obtained by xSchwingerPara.*)
int2[D_,\[Alpha]_,\[Beta]_,my\[Beta]_]:=((-1)^(-D/4) I^(D/2-2 \[Alpha]-2 \[Beta]) my\[Beta]^(D/2-\[Alpha]-\[Beta]) Z1^(-1+\[Beta]) \[Zeta]1^(-1+\[Alpha]) Gamma[-(D/2)+\[Alpha]+\[Beta]])/(Gamma[\[Alpha]] Gamma[\[Beta]]);
int2power[D_,\[Alpha]_,\[Beta]_,my\[Beta]_]:=my\[Beta]^(D/2-\[Alpha]-\[Beta]) Z1^(-1+\[Beta]) \[Zeta]1^(-1+\[Alpha]);
you\[Beta]= m22 Z1+m12 \[Zeta]1-p21 Z1 \[Zeta]1;
(*2 derivatives*)
coelist=Coefficient[you\[Beta],#]&/@{p21,m12,m22};
Eqs[{arg1_,arg2_,arg3_}]:=Module[{args,temp,temp1,temp2,temp3},
	args={arg1,arg2,arg3};
	temp=(D[int2power[d,\[Alpha],\[Beta],my\[Beta]],{my\[Beta],Total[args]}]Times@@(Thread[Power[coelist,args]]))/int2power[d1,\[Alpha]1,\[Beta]1,my\[Beta]];
	temp1=temp/.{my\[Beta]->1,Z1->1,\[Zeta]1->1};
	temp2=List@@(temp/temp1//Simplify);
	temp3=temp2/.Power[x_,y_]:>y;
	Thread[temp3==0]];
Sols[{arg1_,arg2_,arg3_}]:=
	Solve[Eqs[{arg1,arg2,arg3}],{d1,\[Alpha]1,\[Beta]1}]//Flatten;
prefacors[{arg1_,arg2_,arg3_}]:=Module[{args},
	args={arg1,arg2,arg3};
	(D[int2[d,\[Alpha],\[Beta],my\[Beta]],{my\[Beta],Total[args]}]Times@@(Thread[Power[coelist,args]]))/(int2[d1,\[Alpha]1,\[Beta]1,my\[Beta]]/.Sols[args])//FullSimplify];
results[arglist_]:=
	prefacors[arglist]I0[d1,{{0,m1,\[Alpha]1},{p1,m2,\[Beta]1}}]/.Sols[arglist];
(*3. related to LFB0*)
infoB0=xToDavy[intB0,{$p1,$p2,$p3}];
rulemass=Thread[{m1,m2}->(infoB0[[1,2]]//Transpose)[[2]]];
ruleindex=Thread[{\[Alpha],\[Beta]}->(infoB0[[1,2]]//Transpose)[[3]]];
rulemom={p1->$p1};
derlist={n1,n2,n3};
(*Print[infoB0[[2]]];Abort[];*)
ScalarReduce[(results[derlist]/.d->D/.rulemass/.rulemom/.ruleindex),infoB0[[2]]]/.ruleintD(*/.ruleint//xSetDto4*)//xCollect
];


(*3-point one-loop scalar integrals*)


der[{n1_,n2_,n3_,n4_,n5_,n6_},intC0_LFC0]:=
Module[
{derlist,int3,int3power,you\[Beta],my\[Beta],
p21,p32,p31,m12,m22,m32,m1,m2,m3,
Z1,Z2,\[Zeta]1,\[Zeta]2,
coelist,Eqs,Sols,prefacors,results,
d,\[Alpha],\[Beta],\[Gamma],d1,\[Alpha]1,\[Beta]1,\[Gamma]1,
p1,p2,$p1,$p2,$p3,$m1,$m2,$m3,$d,$\[Alpha],$\[Beta],$\[Gamma],
infoC0,rulemass,ruleindex,rulemom},
(*1. Schwinger Parametrization for template: I0[{D,{0,m1,\[Alpha]},{p1,m2,\[Beta]},{p2,m3,\[Gamma]}}],
which can be obtained by xSchwingerPara.*)
int3[D_,\[Alpha]_,\[Beta]_,\[Gamma]_,my\[Beta]_]:=((-1)^(-D/4) I^(D/2-2 \[Alpha]-2 \[Beta]-2 \[Gamma]) my\[Beta]^(D/2-\[Alpha]-\[Beta]-\[Gamma]) Z1^(-1+\[Beta]+\[Gamma]) Z2^(-1+\[Gamma]) \[Zeta]1^(-1+\[Alpha]) \[Zeta]2^(-1+\[Beta]) Gamma[-(D/2)+\[Alpha]+\[Beta]+\[Gamma]])/(Gamma[\[Alpha]] Gamma[\[Beta]] Gamma[\[Gamma]]);
int3power[D_,\[Alpha]_,\[Beta]_,\[Gamma]_,my\[Beta]_]:=my\[Beta]^(D/2-\[Alpha]-\[Beta]-\[Gamma]) Z1^(-1+\[Beta]+\[Gamma]) Z2^(-1+\[Gamma]) \[Zeta]1^(-1+\[Alpha]) \[Zeta]2^(-1+\[Beta]) ;
you\[Beta]= m32 Z1 Z2+m12 \[Zeta]1-p31 Z1 Z2 \[Zeta]1+m22 Z1 \[Zeta]2-p32 Z1^2 Z2 \[Zeta]2-p21 Z1 \[Zeta]1 \[Zeta]2;
(*2 derivatives*)
coelist=Coefficient[you\[Beta],#]&/@{p21,p32,p31,m12,m22,m32};
Eqs[{arg1_,arg2_,arg3_,arg4_,arg5_,arg6_}]:=Module[{args,temp,temp1,temp2,temp3},
	args={arg1,arg2,arg3,arg4,arg5,arg6};
	temp=(D[int3power[d,\[Alpha],\[Beta],\[Gamma],my\[Beta]],{my\[Beta],Total[args]}]Times@@(Thread[Power[coelist,args]]))/int3power[d1,\[Alpha]1,\[Beta]1,\[Gamma]1,my\[Beta]];
	temp1=temp/.{my\[Beta]->1,Z1->1,Z2->1,\[Zeta]1->1,\[Zeta]2->1};
	temp2=List@@(temp/temp1//Simplify);
	temp3=temp2/.Power[x_,y_]:>y;
	Thread[temp3==0]];
Sols[{arg1_,arg2_,arg3_,arg4_,arg5_,arg6_}]:=
	Solve[Eqs[{arg1,arg2,arg3,arg4,arg5,arg6}],{d1,\[Alpha]1,\[Beta]1,\[Gamma]1}]//Flatten;
prefacors[{arg1_,arg2_,arg3_,arg4_,arg5_,arg6_}]:=Module[{args},
	args={arg1,arg2,arg3,arg4,arg5,arg6};
	(D[int3[d,\[Alpha],\[Beta],\[Gamma],my\[Beta]],{my\[Beta],Total[args]}]Times@@(Thread[Power[coelist,args]]))/(int3[d1,\[Alpha]1,\[Beta]1,\[Gamma]1,my\[Beta]]/.Sols[args])//FullSimplify];
results[arglist_]:=
	prefacors[arglist]I0[d1,{{0,m1,\[Alpha]1},{p1,m2,\[Beta]1},{p2,m3,\[Gamma]1}}]/.Sols[arglist];
(*3. related to LFC0*)
infoC0=xToDavy[intC0,{$p1,$p2,$p3}];
rulemass=Thread[{m1,m2,m3}->(infoC0[[1,2]]//Transpose)[[2]]];
ruleindex=Thread[{\[Alpha],\[Beta],\[Gamma]}->(infoC0[[1,2]]//Transpose)[[3]]];
rulemom={p1->$p1,p2->$p2};
derlist={n1,n2,n3,n4,n5,n6};
(*Print[infoC0[[2]]];Abort[];*)
ScalarReduce[(results[derlist]/.d->D/.rulemass/.rulemom/.ruleindex),infoC0[[2]]]/.ruleintD(*/.ruleint//xSetDto4*)//xCollect
];


(*4-point one-loop scalar integrals*)


der[{n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_,n10_},intD0_LFD0]:=
Module[
{derlist,int4,int4power,you\[Beta],my\[Beta],
p21,p32,p43,p41,p31,p42,m12,m22,m32,m42,m1,m2,m3,m4,
Z1,Z2,Z3,\[Zeta]1,\[Zeta]2,\[Zeta]3,
coelist,Eqs,Sols,prefacors,results,
d,\[Alpha],\[Beta],\[Gamma],\[Delta],d1,\[Alpha]1,\[Beta]1,\[Gamma]1,\[Delta]1,
p1,p2,p3,$p1,$p2,$p3,$m1,$m2,$m3,$m4,$d,$\[Alpha],$\[Beta],$\[Gamma],$\[Delta],
infoD0,rulemass,ruleindex,rulemom},
(*1. Schwinger Parametrization for template: I0[{D,{0,m1,\[Alpha]},{p1,m2,\[Beta]},{p2,m3,\[Gamma]}}],
which can be obtained by xSchwingerPara.*)
int4[D_,\[Alpha]_,\[Beta]_,\[Gamma]_,\[Delta]_,my\[Beta]_]:=((-1)^(-D/4) I^(D/2-2 \[Alpha]-2 \[Beta]-2 \[Gamma]-2 \[Delta]) my\[Beta]^(D/2-\[Alpha]-\[Beta]-\[Gamma]-\[Delta]) Z1^(-1+\[Beta]+\[Gamma]+\[Delta]) Z2^(-1+\[Gamma]+\[Delta]) Z3^(-1+\[Delta]) \[Zeta]1^(-1+\[Alpha]) \[Zeta]2^(-1+\[Beta]) \[Zeta]3^(-1+\[Gamma]) Gamma[-(D/2)+\[Alpha]+\[Beta]+\[Gamma]+\[Delta]])/(Gamma[\[Alpha]] Gamma[\[Beta]] Gamma[\[Gamma]] Gamma[\[Delta]]);
int4power[D_,\[Alpha]_,\[Beta]_,\[Gamma]_,\[Delta]_,my\[Beta]_]:=my\[Beta]^(D/2-\[Alpha]-\[Beta]-\[Gamma]-\[Delta]) Z1^(-1+\[Beta]+\[Gamma]+\[Delta]) Z2^(-1+\[Gamma]+\[Delta]) Z3^(-1+\[Delta]) \[Zeta]1^(-1+\[Alpha]) \[Zeta]2^(-1+\[Beta]) \[Zeta]3^(-1+\[Gamma]);
you\[Beta]= m42 Z1 Z2 Z3+m12 \[Zeta]1-p41 Z1 Z2 Z3 \[Zeta]1+m22 Z1 \[Zeta]2-p42 Z1^2 Z2 Z3 \[Zeta]2-p21 Z1 \[Zeta]1 \[Zeta]2+
m32 Z1 Z2 \[Zeta]3-p43 Z1^2 Z2^2 Z3 \[Zeta]3-p31 Z1 Z2 \[Zeta]1 \[Zeta]3-p32 Z1^2 Z2 \[Zeta]2 \[Zeta]3;
(*2 derivatives*)
coelist=Coefficient[you\[Beta],#]&/@{p21,p32,p43,p41,p31,p42,m12,m22,m32,m42};
Eqs[{arg1_,arg2_,arg3_,arg4_,arg5_,arg6_,arg7_,arg8_,arg9_,arg10_}]:=Module[{args,temp,temp1,temp2,temp3},
	args={arg1,arg2,arg3,arg4,arg5,arg6,arg7,arg8,arg9,arg10};
	temp=(D[int4power[d,\[Alpha],\[Beta],\[Gamma],\[Delta],my\[Beta]],{my\[Beta],Total[args]}]Times@@(Thread[Power[coelist,args]]))/int4power[d1,\[Alpha]1,\[Beta]1,\[Gamma]1,\[Delta]1,my\[Beta]];
	temp1=temp/.{my\[Beta]->1,Z1->1,Z2->1,Z3->1,\[Zeta]1->1,\[Zeta]2->1,\[Zeta]3->1};
	temp2=List@@(temp/temp1//Simplify);
	temp3=temp2/.Power[x_,y_]:>y;
	Thread[temp3==0]];
Sols[{arg1_,arg2_,arg3_,arg4_,arg5_,arg6_,arg7_,arg8_,arg9_,arg10_}]:=
	Solve[Eqs[{arg1,arg2,arg3,arg4,arg5,arg6,arg7,arg8,arg9,arg10}],{d1,\[Alpha]1,\[Beta]1,\[Gamma]1,\[Delta]1}]//Flatten;
prefacors[{arg1_,arg2_,arg3_,arg4_,arg5_,arg6_,arg7_,arg8_,arg9_,arg10_}]:=Module[{args},
	args={arg1,arg2,arg3,arg4,arg5,arg6,arg7,arg8,arg9,arg10};
	(D[int4[d,\[Alpha],\[Beta],\[Gamma],\[Delta],my\[Beta]],{my\[Beta],Total[args]}]Times@@(Thread[Power[coelist,args]]))/(int4[d1,\[Alpha]1,\[Beta]1,\[Gamma]1,\[Delta]1,my\[Beta]]/.Sols[args])//FullSimplify];
results[arglist_]:=
	prefacors[arglist]I0[d1,{{0,m1,\[Alpha]1},{p1,m2,\[Beta]1},{p2,m3,\[Gamma]1},{p3,m4,\[Delta]1}}]/.Sols[arglist];
(*3. related to LFC0*)
infoD0=xToDavy[intD0,{$p1,$p2,$p3}];
rulemass=Thread[{m1,m2,m3,m4}->(infoD0[[1,2]]//Transpose)[[2]]];
ruleindex=Thread[{\[Alpha],\[Beta],\[Gamma],\[Delta]}->(infoD0[[1,2]]//Transpose)[[3]]];
rulemom={p1->$p1,p2->$p2,p3->$p3};
derlist={n1,n2,n3,n4,n5,n6,n7,n8,n9,n10};
(*Print[infoD0[[2]]];Abort[];*)
ScalarReduce[(results[derlist]/.d->D/.rulemass/.rulemom/.ruleindex),infoD0[[2]]]/.ruleintD(*/.ruleint//xSetDto4*)//xCollect
];



(* ::Subsubsection::Closed:: *)
(*Functions Preparing*)


xOrderDotGamma[exp_]:=Module[{dot},
dot[x___,Diracgamma[a_Symbol],Diracgamma[b_Symbol],y___]/;OrderedQ[{b,a}]:=2metrictensor[b,a]dot[x,y]-dot[x,Diracgamma[b],Diracgamma[a],y];

dot[x___,Diracslash[a_Symbol],Diracgamma[b_Symbol],y___]:=2momentum[a,b]dot[x,y]-dot[x,Diracgamma[b],Diracslash[a],y];

dot[x___,Diracslash[a_Symbol],Diracslash[b_Symbol],y___]/;OrderedQ[{b,a}]:=2scalarproduct[b,a]dot[x,y]-dot[x,Diracslash[b],Diracslash[a],y];

exp/.Dotgamma->dot/.dot->Dotgamma/.{Dotgamma[]->1,Dotgamma[x_]:>x}
]


xExtract[amp_]:=Module[{index,rule,y},
rule={scalarproduct[k_]:>momentum[k,Unique[index]]^2,
scalarproduct[k_]^n_:>Product[momentum[k,Unique[index]]^2,{i,1,n}],
scalarproduct[k_,x_]:>momentum[k,y=Unique[index]]momentum[x,y],
scalarproduct[k_,x_]^n_:>Product[momentum[k,y=Unique[index]]momentum[x,y],{i,n}],
Dotgamma[a___,Diracslash[k_],b___]:>momentum[k,y=Unique[index]]Dotgamma[a,Diracgamma[y],b],(*26.11.13*)
Diracslash[k_]:>momentum[k,y=Unique[index]]Diracgamma[y](*add on 05.12.13*),
 Levicivita\[Epsilon][a___,momentum[b_],c___]:>Levicivita\[Epsilon][a,y=Unique[index],c]momentum[b,y]
};
amp//.rule

]



xreduceTrOnce[exp_Dotgamma]/;exp[[-1]]=!=Diracgamma5[]:=Module[{tr0,tr,exp1,exp2,exp3},
tr0[inx_,iny_]:=4metrictensor[inx,iny];
tr0[inx_]:=0;
tr0[inx1_,inx2_,inx3_,inx4___]:=Diracgamma/@Dotgamma[inx1,inx2,inx3,inx4];
exp1=(tr@@exp)/.Diracgamma->Sequence;
If[Length[exp1]>=3,
exp2=Drop[exp1,{1}];
exp3=Sum[(-1)^(i+1) metrictensor[exp1[[1]],exp1[[i+1]]]Drop[exp2,{i}],{i,1,Length[exp2]}];
Return[exp3/.tr->tr0],
Return[exp1/.tr->tr0]]
]



xreduceTrOnce[exp_Dotgamma]/;exp[[-1]]===Diracgamma5[]:=Module[{tr0,tr,index,indexy,exp1,exp2},
tr0[inx1_,inx2_,inx3_,inx4_,Diracgamma5[]]:=-4I Levicivita\[Epsilon][inx1,inx2,inx3,inx4];
tr0[inx1_,inx2_,inx3_,Diracgamma5[]]:=0;
tr0[inx1_,inx2_,Diracgamma5[]]:=0;
tr0[inx1_,Diracgamma5[]]:=0;
tr0[Diracgamma5[]]:=0;
tr0[inx1_,inx2_,inx3_,inx4_,inx5_,inx6___,Diracgamma5[]]:=Join[Diracgamma/@Dotgamma[inx1,inx2,inx3,inx4,inx5,inx6],Dotgamma[Diracgamma5[]]];
tr0[inx1_,inx2_,inx3_,inx4_,inx5_,inx6___,Diracgamma5[]];

tr0[inx_,iny_]:=4metrictensor[inx,iny];
tr0[inx_]:=0;
tr0[inx1_,inx2_,inx3_,inx4___]:=Diracgamma/@Dotgamma[inx1,inx2,inx3,inx4];

exp1=(tr@@exp)/.Diracgamma->Sequence;
If[Length[exp1]-1>=5,
exp2=metrictensor[exp1[[-4]],exp1[[-3]]]Drop[Drop[exp1,{-4}],{-3}]-metrictensor[exp1[[-4]],exp1[[-2]]]Drop[Drop[exp1,{-4}],{-2}]+metrictensor[exp1[[-3]],exp1[[-2]]]Drop[Drop[exp1,{-3}],{-2}]+I Levicivita\[Epsilon][exp1[[-4]],exp1[[-3]],exp1[[-2]],indexy=Unique[index]]Join[Drop[exp1,{-4,-1}],tr[indexy]];
Return[exp2/.tr->tr0],
Return[exp1/.tr->tr0]]
]



xDiracTraceDotPart[amp_]:=Module[{dots,dots1,amp2},
dots=Cases[{amp},_Dotgamma,Infinity]//Union;
If[Length[dots]===0,Return[( amp//Expand)]];
dots1=(xreduceTrOnce/@dots);
amp2=amp/.Thread[dots->dots1];
Return[xDiracTraceDotPart[amp2]]
]



xDiracTrace[amp_]:=Module[{dots,dots1,partnoDot,partnoDirac,partDot,amp1,amp2},
amp1=amp//xDiracSimplify//xExtract;
partnoDot=amp1/.Dotgamma[___]->0;
partnoDirac=partnoDot/.{Diracgamma[_]->0,Diracgamma5[]->0};
partDot=amp1-partnoDot;
Return[(4partnoDirac)+xDiracTraceDotPart[partDot]//xDiracContract//xContractEps]
]



Eps=Levicivita\[Epsilon];
xUniqueEps[exp_]:=Module[
{expandEps,orderEps,var,rep,res},

expandEps[exp1_,exp2_,exp3_,exp4_]:=Distribute[Eps[exp1,exp2,exp3,exp4]/.x_momentum:>Distribute@x]/.x0_Eps:>(x0//.Eps[x___,y0_*y1_momentum,z___]:>y0*Eps[x,y1,z]);

orderEps[exp1_,exp2_,exp3_,exp4_]:=If[Times@@#===0,0,Signature@#*Eps@@Sort@#]&@{exp1,exp2,exp3,exp4};

var=Cases[{exp},_Eps,Infinity]//Union;

rep=var/.Eps->expandEps/.Eps->orderEps;

Block[
{Eps},
Thread[var->rep]/.Rule->Set;
res=exp
];
Return[res];
];



xContractEps[exp_]:=Module[{xLevicivita\[Epsilon]2,xLevicivita\[Epsilon],LCsign=-1,result},
xLevicivita\[Epsilon]2/:xLevicivita\[Epsilon]2[x1___,x2_,x3___]momentum[x_,x2_]:=xLevicivita\[Epsilon]2[x1,momentum[x],x3];
xLevicivita\[Epsilon]/:xLevicivita\[Epsilon][i___, i1_, j___] metrictensor[i1_, i2_] :=xLevicivita\[Epsilon][i, i2, j];
xLevicivita\[Epsilon]/:metrictensor[j_,k_] xLevicivita\[Epsilon][i1___,j_,j2___,k_,k3___]:=0;
xLevicivita\[Epsilon][i__]/;Signature[List[i]]===0 =0;
(* Product of two Levi-Civita tensors *)
(*--- Ref: The Mathematica Guidebook -- Programming by M. Trott ---*)
(* Now in 3+1 Minkowski space, multiplying -1 for the product. E.g., one should have Subscript[\[Epsilon], \[Mu]\[Nu]\[Alpha]\[Beta]] \[Epsilon]^\[Mu]\[Nu]\[Alpha]\[Beta]=-24.  *)
xLevicivita\[Epsilon]/:xLevicivita\[Epsilon][var__]*xLevicivita\[Epsilon][var__]/;!Or@@(NumericQ[#]&/@Flatten[{var}]):= LCsign Length[{var}]!;
xLevicivita\[Epsilon]/:Power[xLevicivita\[Epsilon][var2__?(FreeQ[#,_Number]&)],2]:=LCsign Length[{var2}]!;
(*the typical case*)
xLevicivita\[Epsilon]/:xLevicivita\[Epsilon][var1__] xLevicivita\[Epsilon][var2__]:=Module[{commonIndices,rest1,rest2,s1,s2,ex,from},
(*the indices both have*)
commonIndices=Intersection@@(Select[#,Function[y,!NumberQ[y]]]&/@{{var1},{var2}});
(*the indices that exist only once*)
rest1=Complement[{var1},commonIndices];
rest2=Complement[{var2},commonIndices];
(*reordering indices and keep track of sign changes*)s1=Signature[{var1}]/Signature[Join[commonIndices,rest1]];
s2=Signature[{var2}]/Signature[Join[commonIndices,rest2]];
(*the new indices pairs*)ex=({rest1,#,Signature[#]}&/@Permutations[rest2])/Signature[rest2];
(*make Kronecker symbols*)from=Plus@@Apply[Times,{#[[3]],Thread[metrictensor[#[[1]],#[[2]]]]}&/@ex,2];
LCsign Length[commonIndices]! s1 s2 from];
result=(xUniqueEps[exp/.Levicivita\[Epsilon]->xLevicivita\[Epsilon]/.xLevicivita\[Epsilon]->xLevicivita\[Epsilon]2]);
Return[result/.xLevicivita\[Epsilon]2->Levicivita\[Epsilon]//xUniqueEps//Expand]
]


(* ::Subsubsection::Closed:: *)
(*commutators, Levicivita\[Epsilon] by Gammas*)


anticommutator[aa_,bb_]:=aa.bb+bb.aa;
commutator[aa_,bb_]:=aa.bb-bb.aa;


Levicivita\[Epsilon]explicit[\[Mu]_,\[Nu]_,\[Rho]_,\[Sigma]_]:=-(I/8)commutator[anticommutator[commutator[Diracgamma[\[Mu]],Diracgamma[\[Nu]]],Diracgamma[\[Rho]]],Diracgamma[\[Sigma]]].Diracgamma5[];
