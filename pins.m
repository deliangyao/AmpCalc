(* ::Package:: *)

(* ::Title:: *)
(*Pion-Nucleon Scattering*)


(* ::Subtitle:: *)
(*This is a package for calculating pion-nucleon scattering amplitude*)


(* ::Text:: *)
(*De - Liang Yao (yaodeliang@hnu.edu.cn)*)


<<"Ro3int.dat";
<<"Rodint.dat";
FileIndicator=(StringJoin@Insert[ToString/@Take[Date[],{1,3,1}],"_",{{1},{2},{3}}])<>".dat";


(* ::Subsection:: *)
(*Definitions and Display forms of output*)


(* ::Subsubsection::Closed:: *)
(*Abbreviations*)


head=_LFA0|_LFA0i|_LFB0|_LFB0i|_LFC0|_LFC0i|_LFD0|_LFD0i;

sp=scalarproduct;
MT=metrictensor;
KD2=KroneckerDelta2;
LV2=Levicivita2;
xi[i_,j_]:=KD2[i,j]-1/3 Paulitau[i].Paulitau[j];
Si/:MakeBoxes[Si,TraditionalForm]:="\[CapitalSigma]";
De/:MakeBoxes[De,TraditionalForm]:="\[CapitalDelta]";


(* ::Subsubsection::Closed:: *)
(*Bare parameters*)


paraBare={mp,mn,md,gA,F,c1,c2,c3,c4,d1,d2,d3,d5,d14,d15,d18,h,g1,b3,b8,f1,f2,f4,f5};
m1/:MakeBoxes[m1,TraditionalForm]:=SubscriptBox[OverscriptBox["m","\[SmallCircle]"],"\[Pi]"];mp=m1;
m2/:MakeBoxes[m2,TraditionalForm]:=SubscriptBox[OverscriptBox["m","\[SmallCircle]"],"N"];mn=m2;
m3/:MakeBoxes[m3,TraditionalForm]:=SubscriptBox[OverscriptBox["m","\[SmallCircle]"],"\[CapitalDelta]"];md=m3;
gA/:MakeBoxes[gA,TraditionalForm]:=SubscriptBox[OverscriptBox["g","\[SmallCircle]"],"A"];
F;
c1/:MakeBoxes[c1,TraditionalForm]:=SubscriptBox["c","1"];
c2/:MakeBoxes[c2,TraditionalForm]:=SubscriptBox["c","2"];
c3/:MakeBoxes[c3,TraditionalForm]:=SubscriptBox["c","3"];
c4/:MakeBoxes[c4,TraditionalForm]:=SubscriptBox["c","4"];
d1/:MakeBoxes[d1,TraditionalForm]:=SubscriptBox["d","1"];
d2/:MakeBoxes[d2,TraditionalForm]:=SubscriptBox["d","2"];
d3/:MakeBoxes[d3,TraditionalForm]:=SubscriptBox["d","3"];
d5/:MakeBoxes[d5,TraditionalForm]:=SubscriptBox["d","5"];
d14/:MakeBoxes[d14,TraditionalForm]:=SubscriptBox["d","14"];
d15/:MakeBoxes[d15,TraditionalForm]:=SubscriptBox["d","15"];
d18/:MakeBoxes[d18,TraditionalForm]:=SubscriptBox["d","18"];
h/:MakeBoxes[h,TraditionalForm]:=SubscriptBox[OverscriptBox["g","\[SmallCircle]"],"\[Pi]N\[CapitalDelta]"];
g1/:MakeBoxes[g1,TraditionalForm]:=SubscriptBox["g","1"];
b3/:MakeBoxes[b3,TraditionalForm]:=SubscriptBox["b","3"];
b8/:MakeBoxes[b8,TraditionalForm]:=SubscriptBox["b","8"];
f1/:MakeBoxes[f1,TraditionalForm]:=SubscriptBox["f","1"];
f2/:MakeBoxes[f2,TraditionalForm]:=SubscriptBox["f","2"];
f4/:MakeBoxes[f4,TraditionalForm]:=SubscriptBox["f","4"];
f5/:MakeBoxes[f5,TraditionalForm]:=SubscriptBox["f","5"];


(* ::Subsubsection::Closed:: *)
(*Physical parameters*)


paraPhys={mpir,mnuc,mdel,gAr,Fpi,c1r,c2r,c3r,c4r,d1r,d2r,d3r,d5r,d14r,d15r,d18r,hr,g1r,b3r,b8r,f1r,f2r,f4r,f5r};
mpir/:MakeBoxes[mpir,TraditionalForm]:=SubscriptBox["m","\[Pi]"];mpr=mpir;
mnuc/:MakeBoxes[mnuc,TraditionalForm]:=SubscriptBox["m","N"];mnr=mnuc;
mdel/:MakeBoxes[mdel,TraditionalForm]:=SubscriptBox["m","\[CapitalDelta]"];mdr=mdel;
gAr/:MakeBoxes[gAr,TraditionalForm]:=SubscriptBox["g","A"];
Fpi/:MakeBoxes[Fpi,TraditionalForm]:=SubscriptBox["F","\[Pi]"];fpi=Fpi;
c1r/:MakeBoxes[c1r,TraditionalForm]:=SubsuperscriptBox["c","1","r"];
c2r/:MakeBoxes[c2r,TraditionalForm]:=SubsuperscriptBox["c","2","r"];
c3r/:MakeBoxes[c3r,TraditionalForm]:=SubsuperscriptBox["c","3","r"];
c4r/:MakeBoxes[c4r,TraditionalForm]:=SubsuperscriptBox["c","4","r"];
d1r/:MakeBoxes[d1r,TraditionalForm]:=SubsuperscriptBox["d","1","r"];
d2r/:MakeBoxes[d2r,TraditionalForm]:=SubsuperscriptBox["d","2","r"];
d3r/:MakeBoxes[d3r,TraditionalForm]:=SubsuperscriptBox["d","3","r"];
d5r/:MakeBoxes[d5r,TraditionalForm]:=SubsuperscriptBox["d","5","r"];
d14r/:MakeBoxes[d14r,TraditionalForm]:=SubsuperscriptBox["d","14","r"];
d15r/:MakeBoxes[d15r,TraditionalForm]:=SubsuperscriptBox["d","15","r"];
d18r/:MakeBoxes[d18r,TraditionalForm]:=SubsuperscriptBox["d","18","r"];
hr/:MakeBoxes[hr,TraditionalForm]:=SubscriptBox["g","\[Pi]N\[CapitalDelta]"];
g1r/:MakeBoxes[g1r,TraditionalForm]:=SubsuperscriptBox["g","1","r"];
b3r/:MakeBoxes[b3r,TraditionalForm]:=SubsuperscriptBox["b","3","r"];
b8r/:MakeBoxes[b8r,TraditionalForm]:=SubsuperscriptBox["b","8","r"];
f1r/:MakeBoxes[f1r,TraditionalForm]:=SubsuperscriptBox["f","1","r"];
f2r/:MakeBoxes[f2r,TraditionalForm]:=SubsuperscriptBox["f","2","r"];
f4r/:MakeBoxes[f4r,TraditionalForm]:=SubsuperscriptBox["f","4","r"];
f5r/:MakeBoxes[f5r,TraditionalForm]:=SubsuperscriptBox["f","5","r"];


(* ::Subsubsection::Closed:: *)
(*Mandelstam variables*)


MandelstamRules={scalarproduct[pi,pi]->mn^2,scalarproduct[pf,pf]->mn^2,scalarproduct[qa,qa]->mp^2,scalarproduct[qb,qb]->mp^2,scalarproduct[pi,qa]->(s-mn^2-mp^2)/2,scalarproduct[pf,qb]->(s-mn^2-mp^2)/2,scalarproduct[pi,qb]->(mn^2+mp^2-u)/2,scalarproduct[pf,qa]->(mn^2+mp^2-u)/2,scalarproduct[pi,pf]->(2mn^2-t)/2,scalarproduct[qa,qb]->(2mp^2-t)/2,scalarproduct[Si,Si]->s,scalarproduct[Si,pi]->(s+mn^2-mp^2)/2,scalarproduct[Si,qa]->(s-mn^2+mp^2)/2,scalarproduct[Si,pf]->(s+mn^2-mp^2)/2,scalarproduct[Si,qb]->(s-mn^2+mp^2)/2,scalarproduct[Si]->s,scalarproduct[De,De]->t,scalarproduct[De,pi]->t/2,scalarproduct[De,qa]->-(t/2),scalarproduct[De,pf]->-t/2,scalarproduct[De,qb]->t/2,scalarproduct[De]->t};


MandelstamRulesPhys={scalarproduct[pi,pi]->mnuc^2,scalarproduct[pf,pf]->mnuc^2,scalarproduct[qa,qa]->mpir^2,scalarproduct[qb,qb]->mpir^2,scalarproduct[pi,qa]->(s-mnuc^2-mpir^2)/2,scalarproduct[pf,qb]->(s-mnuc^2-mpir^2)/2,scalarproduct[pi,qb]->(mnuc^2+mpir^2-u)/2,scalarproduct[pf,qa]->(mnuc^2+mpir^2-u)/2,scalarproduct[pi,pf]->(2mnuc^2-t)/2,scalarproduct[qa,qb]->(2mpir^2-t)/2,scalarproduct[Si,Si]->s,scalarproduct[Si,pi]->(s+mnuc^2-mpir^2)/2,scalarproduct[Si,qa]->(s-mnuc^2+mpir^2)/2,scalarproduct[Si,pf]->(s+mnuc^2-mpir^2)/2,scalarproduct[Si,qb]->(s-mnuc^2+mpir^2)/2,scalarproduct[Si]->s,scalarproduct[De,De]->t,scalarproduct[De,pi]->t/2,scalarproduct[De,qa]->-(t/2),scalarproduct[De,pf]->-t/2,scalarproduct[De,qb]->t/2,scalarproduct[De]->t};



nu/:MakeBoxes[nu,TraditionalForm]:="\[Nu]";


(* ::Subsection:: *)
(*Feynman Rules for Scattering Amplitudes Calculation*)


(* ::Subsubsection::Closed:: *)
(*pure pion sector*)


PropP[{a_,k_},{b_,k_},Dirac]:=I FeynAmplDenominator[{k,mp}];
PropP[{a_,k_},{b_,k_},Isospin]:=KroneckerDelta2[a,b];
PropP[{a_,k_},{b_,k_}]:=Dot@@(PropP[{a,k},{b,k},#]&/@{Dirac,Isospin});


(*alternative definition*)
PropP[{a_,b_},k_,Dirac]:=I FeynAmplDenominator[{k,mp}];
PropP[{a_,b_},k_,Isospin]:=KroneckerDelta2[a,b];
PropP[{a_,b_},k_]:=Dot@@(PropP[{a,b},k,#]&/@{Dirac,Isospin});


V4\[Pi][2][{a_,pa_},{b_,pb_},{c_,pc_},{d_,pd_},case_]:=Module[{diracPart,isospinPart},
diracPart[{a1_,pa1_},{b1_,pb1_},{c1_,pc1_},{d1_,pd1_}]:=I/(3F^2) (2(scalarproduct[pa1,pb1]+scalarproduct[pc1,pd1])-scalarproduct[pa1+pb1,pc1+pd1]+mp^2);
isospinPart[{a1_,pa1_},{b1_,pb1_},{c1_,pc1_},{d1_,pd1_}]:=KroneckerDelta2[a1,b1].KroneckerDelta2[c1,d1];
Switch[case,Dirac,{diracPart[{a,pa},{b,pb},{c,pc},{d,pd}],diracPart[{a,pa},{c,pc},{b,pb},{d,pd}],diracPart[{a,pa},{d,pd},{b,pb},{c,pc}]},Isospin,{isospinPart[{a,pa},{b,pb},{c,pc},{d,pd}],isospinPart[{a,pa},{c,pc},{b,pb},{d,pd}],isospinPart[{a,pa},{d,pd},{b,pb},{c,pc}]},_,Print["V4\[Pi] false"]]]
V4\[Pi][2][{a_,pa_},{b_,pb_},{c_,pc_},{d_,pd_}]:=Sum[Dot@@(V4\[Pi][2][{a,pa},{b,pb},{c,pc},{d,pd},#][[int]]&/@{Dirac,Isospin}),{int,1,3}];


(*V4\[Pi][2][{a_,pa_},{b_,pb_},{c_,pc_},{d_,pd_}]:=I/(3F^2) (KroneckerDelta2[a,b].KroneckerDelta2[c,d].(2(scalarproduct[pa,pb]+scalarproduct[pc,pd])-scalarproduct[pa+pb,pc+pd]+mp^2)+KroneckerDelta2[a,c].KroneckerDelta2[b,d].(2(scalarproduct[pa,pc]+scalarproduct[pb,pd])-scalarproduct[pa+pc,pb+pd]+mp^2)+KroneckerDelta2[a,d].KroneckerDelta2[b,c].(2(scalarproduct[pa,pd]+scalarproduct[pb,pc])-scalarproduct[pa+pd,pb+pc]+mp^2));*)(*a,b,c,d,anti-clockwise*)


(* ::Subsubsection:: *)
(*pion-nucleon sector*)


PropN[k_,Dirac]:=I (Diracslash[k] +mn)FeynAmplDenominator[{k,mn}];
PropN[k_,Isospin]:=1;
PropN[k_]:=Dot@@(PropN[k,#]&/@{Dirac,Isospin});


VNN\[Pi][1][{a_,qa_},Dirac]:=-(gA/(2F))Diracslash[qa].Diracgamma5[];
VNN\[Pi][1][{a_,qa_},Isospin]:=Paulitau[a];
VNN\[Pi][1][{a_,qa_}]:=Dot@@(VNN\[Pi][1][{a,qa},#]&/@{Dirac,Isospin});
VNN\[Pi][1][{Pout_},{Pin_},{a_,qa_},x___]:=VNN\[Pi][1][{a,qa},x];


VNN2\[Pi][1][{a_,qa_},{b_,qb_},Dirac]:=1/(4F^2) (Diracslash[qa]-Diracslash[qb]);
VNN2\[Pi][1][{a_,qa_},{b_,qb_},Isospin]:=Levicivita2[a,b,uniquec=Unique[c]]Paulitau[uniquec];
VNN2\[Pi][1][{a_,qa_},{b_,qb_}]:=Dot@@(VNN2\[Pi][1][{a,qa},{b,qb},#]&/@{Dirac,Isospin});
VNN2\[Pi][1][{Pout_},{Pin_},{a_,qa_},{b_,qb_},x___]:=VNN2\[Pi][1][{a,qa},{b,qb},x];


VNN3\[Pi][1][{a_,qa_},{b_,qb_},{c_,qc_}]:=gA/(12F^3) (Paulitau[a].KroneckerDelta2[b,c].(2Diracslash[qa]-Diracslash[qb]-Diracslash[qc])+Paulitau[b].KroneckerDelta2[a,c].(2Diracslash[qb]-Diracslash[qa]-Diracslash[qc])+Paulitau[c].KroneckerDelta2[a,b].(2Diracslash[qc]-Diracslash[qa]-Diracslash[qb])).Diracgamma5[];
VNN3\[Pi][1][{a_,qa_},{b_,qb_},{c_,qc_},Dirac]:=gA/(12F^3) {(2Diracslash[qa]-Diracslash[qb]-Diracslash[qc]).Diracgamma5[],(2Diracslash[qb]-Diracslash[qa]-Diracslash[qc]).Diracgamma5[],(2Diracslash[qc]-Diracslash[qa]-Diracslash[qb]).Diracgamma5[]};
VNN3\[Pi][1][{a_,qa_},{b_,qb_},{c_,qc_},Isospin]:={Paulitau[a].KroneckerDelta2[b,c],Paulitau[b].KroneckerDelta2[a,c],Paulitau[c].KroneckerDelta2[a,b]};


VNN4\[Pi][1][{a_,qa_},{b_,qb_},{c_,qc_},{d_,qd_}]:=-(1/(24F^4))(KroneckerDelta2[a,b].Levicivita2[c,d,uniquee=Unique[e]].Paulitau[uniquee].(Diracslash[qc]-Diracslash[qd])+KroneckerDelta2[a,c].Levicivita2[b,d,uniquee=Unique[e]].Paulitau[uniquee].(Diracslash[qb]-Diracslash[qd])+KroneckerDelta2[a,d].Levicivita2[b,c,uniquee=Unique[e]].Paulitau[uniquee].(Diracslash[qb]-Diracslash[qc])+KroneckerDelta2[b,c].Levicivita2[a,d,uniquee=Unique[e]].Paulitau[uniquee].(Diracslash[qa]-Diracslash[qd])+KroneckerDelta2[b,d].Levicivita2[a,c,uniquee=Unique[e]].Paulitau[uniquee].(Diracslash[qa]-Diracslash[qc])+KroneckerDelta2[c,d].Levicivita2[a,b,uniquee=Unique[e]].Paulitau[uniquee].(Diracslash[qa]-Diracslash[qb]));


VNN2\[Pi][2][{Pout_},{Pin_},{a_,qa_},{b_,qb_},Isospin]:={KD2[a,b],KD2[a,b],KD2[a,b],LV2[a,b,uniquec=Unique[c]]Paulitau[uniquec]};
VNN2\[Pi][2][{Pout_},{Pin_},{a_,qa_},{b_,qb_},Dirac]:={-((4 I c1 mp^2)/F^2),-(I c2)/(F^2 mn^2) (scalarproduct[qa,Pout]scalarproduct[qb,Pout]+scalarproduct[qa,Pin]scalarproduct[qb,Pin]),-(2I c3)/F^2 scalarproduct[qa,qb],(I c4)/F^2 (I/2 (Diracslash[qa].Diracslash[qb]-Diracslash[qb].Diracslash[qa]))};
VNN2\[Pi][2][{Pout_},{Pin_},{a_,qa_},{b_,qb_}]:=-((4 I c1 mp^2)/F^2)KD2[a,b]-(I c2)/(F^2 mn^2) (scalarproduct[qa,Pout]scalarproduct[qb,Pout]+scalarproduct[qa,Pin]scalarproduct[qb,Pin])KD2[a,b]-(2I c3)/F^2 scalarproduct[qa,qb]KD2[a,b]+(I c4)/F^2 LV2[a,b,uniquec=Unique[c]]Paulitau[uniquec].(I/2 (Diracslash[qa].Diracslash[qb]-Diracslash[qb].Diracslash[qa]));


VNN\[Pi][3][{Pout_},{Pin_},{a_,qa_}]:=(d18-2d16)/F mp^2 Diracslash[qa].Diracgamma5[].Paulitau[a];
VNN\[Pi][3][{Pout_},{Pin_},{a_,qa_},Dirac]:=(d18-2d16)/F mp^2 Diracslash[qa].Diracgamma5[];
VNN\[Pi][3][{Pout_},{Pin_},{a_,qa_},Isospin]:=Paulitau[a];


VNN2\[Pi][3][{Pout_},{Pin_},{a_,qa_},{b_,qb_},Dirac]:={((d1+d2)/(mn F^2) scalarproduct[qa,qb]scalarproduct[qb-qa,Pout+Pin]+d3/(mn^3 F^2) (scalarproduct[qa,Pout]scalarproduct[qb,Pout]scalarproduct[qb-qa,Pout]+scalarproduct[qa,Pin]scalarproduct[qb,Pin]scalarproduct[qb-qa,Pin])-(2d5)/(mn F^2) mp^2 scalarproduct[qb-qa,Pout+Pin]),-(d14-d15)/(2mn F^2)*I/2 (Diracgamma[\[Mu]1234].Diracgamma[\[Nu]1234]-Diracgamma[\[Nu]1234].Diracgamma[\[Mu]1234]).(momentum[qa,\[Lambda]1234]momentum[qa,\[Mu]1234]momentum[qb,\[Nu]1234]+momentum[qa,\[Nu]1234]momentum[qb,\[Lambda]1234]momentum[qb,\[Mu]1234]).(momentum[Pout,\[Lambda]1234]+momentum[Pin,\[Lambda]1234])};
VNN2\[Pi][3][{Pout_},{Pin_},{a_,qa_},{b_,qb_},Isospin]:={LV2[a,b,uniquec=Unique[c]]Paulitau[uniquec],KD2[a,b]};

VNN2\[Pi][3][{Pout_},{Pin_},{a_,qa_},{b_,qb_}]:=LV2[a,b,uniquec=Unique[c]]Paulitau[uniquec].((d1+d2)/(mn F^2) scalarproduct[qa,qb]scalarproduct[qb-qa,Pout+Pin]+d3/(mn^3 F^2) (scalarproduct[qa,Pout]scalarproduct[qb,Pout]scalarproduct[qb-qa,Pout]+scalarproduct[qa,Pin]scalarproduct[qb,Pin]scalarproduct[qb-qa,Pin])-(2d5)/(mn F^2) mp^2 scalarproduct[qb-qa,Pout+Pin])-(d14-d15)/(2mn F^2)*I/2 KD2[a,b].(Diracgamma[\[Mu]1234].Diracgamma[\[Nu]1234]-Diracgamma[\[Nu]1234].Diracgamma[\[Mu]1234]).(momentum[qa,\[Lambda]1234]momentum[qa,\[Mu]1234]momentum[qb,\[Nu]1234]+momentum[qa,\[Nu]1234]momentum[qb,\[Lambda]1234]momentum[qb,\[Mu]1234]).(momentum[Pout,\[Lambda]1234]+momentum[Pin,\[Lambda]1234]);


VNN[2][{pf_},{pi_}]:=4I c1 mp^2;


(* ::Subsubsection::Closed:: *)
(*pion-nucleon-delta sector*)


(*the default values for the off-shell patameters*)
$z1=0;
$z2=0;
$z3=0;
g2=0;
g3=0;


PropDR[{i_,x_},{j_,y_},k_,Dirac]:=-I (-(1/(-1+D))Diracgamma[x].Diracgamma[y]-((-2+D) momentum[k,x] momentum[k,y])/((-1+D) md^2)-1/((-1+D) md) (-momentum[k,y] Diracgamma[x]+momentum[k,x] Diracgamma[y])+metrictensor[x,y]).(md+Diracslash[k])FeynAmplDenominator[{k,md}];
PropDR[{i_,x_},{j_,y_},k_,Isospin]:=xi[i,j];
PropDR[{i_,x_},{j_,y_},k_]:=Dot@@(PropDR[{i,x},{j,y},k,#]&/@{Dirac,Isospin});


PropDL[{i_,x_},{j_,y_},k_,Dirac]:=-I (Diracslash[k]+md).(metrictensor[x,y]-1/(D-1) Diracgamma[x].Diracgamma[y]+1/((D-1) md) (momentum[k,x]Diracgamma[y]-momentum[k,y]Diracgamma[x])-((D-2) momentum[k,x]momentum[k,y])/((D-1) md^2))FeynAmplDenominator[{k,md}];
PropDL[{i_,x_},{j_,y_},k_,Isospin]:=xi[i,j];
PropDL[{i_,x_},{j_,y_},k_]:=Dot@@(PropDL[{i,x},{j,y},k,#]&/@{Dirac,Isospin});


V\[CapitalDelta]\[CapitalDelta]\[Pi][1][{i_,\[Mu]_},{n_,\[Nu]_},{a_,qa_},Dirac]:=(1/(2 F)) (g1 metrictensor[\[Mu],\[Nu]].Diracslash[qa].Diracgamma5[]+g2 (Diracgamma[\[Mu]] .momentum[qa,\[Nu]]+Diracgamma[\[Nu]].momentum[qa,\[Mu]]).Diracgamma5[]+g3 Diracgamma[\[Mu]].Diracslash[qa].Diracgamma5[].Diracgamma[\[Nu]]);

V\[CapitalDelta]\[CapitalDelta]\[Pi][1][{i_,\[Mu]_},{n_,\[Nu]_},{a_,qa_},Isospin]:=xi[i,uniquej=Unique[jj]].Paulitau[a].xi[uniquej,n];

V\[CapitalDelta]\[CapitalDelta]\[Pi][1][{i_,\[Mu]_},{n_,\[Nu]_},{a_,qa_}]:=Dot@@( V\[CapitalDelta]\[CapitalDelta]\[Pi][1][{i,\[Mu]},{n,\[Nu]},{a,qa},#]&/@{Dirac,Isospin});


V\[CapitalDelta]\[CapitalDelta]\[Pi]\[Pi][1][{i_,\[Mu]_},{j_,\[Nu]_},{a_,qa_},{b_,qb_},Dirac]:=metrictensor[\[Mu],\[Nu]].Diracslash[qa-qb]-(Diracgamma[\[Mu]].momentum[qa-qb,\[Nu]]+momentum[qa-qb,\[Mu]].Diracgamma[\[Nu]])+Diracgamma[\[Mu]].Diracslash[qa-qb].Diracgamma[\[Nu]];
V\[CapitalDelta]\[CapitalDelta]\[Pi]\[Pi][1][{i_,\[Mu]_},{j_,\[Nu]_},{a_,qa_},{b_,qb_},Isospin]:=I/(2F^2) (xi[i,a].xi[b,j]-xi[i,b].xi[a,j])-1/(4F^2) xi[i,uniquen=Unique[n]].LV2[a,b,uniquec=Unique[c]].Paulitau[uniquec].xi[uniquen,j];
V\[CapitalDelta]\[CapitalDelta]\[Pi]\[Pi][1][{i_,\[Mu]_},{j_,\[Nu]_},{a_,qa_},{b_,qb_}]:=Dot@@(V\[CapitalDelta]\[CapitalDelta]\[Pi]\[Pi][1][{i,\[Mu]},{j,\[Nu]},{a,qa},{b,qb},#]&/@{Dirac,Isospin});


V\[CapitalDelta]\[CapitalDelta][2][{i_,\[Mu]_},{j_,\[Nu]_},Dirac]:=4 a1 I mp^2 theta[\[Mu],\[Mu]temp,0].theta[\[Mu]temp,\[Nu],0];
V\[CapitalDelta]\[CapitalDelta][2][{i_,\[Mu]_},{j_,\[Nu]_},Isospin]:=xi[i,j];
V\[CapitalDelta]\[CapitalDelta][2][{i_,\[Mu]_},{j_,\[Nu]_}]:=Dot@@(V\[CapitalDelta]\[CapitalDelta][2][{i,\[Mu]},{j,\[Nu]},#]&/@{Dirac,Isospin});


V\[CapitalDelta]N\[Pi][1][{i_,\[Mu]_},{nucleon_},{a_,qa_},Dirac]:=-(h/F) (momentum[qa,\[Mu]]+$z1 Diracgamma[\[Mu]].Diracslash[qa]);
V\[CapitalDelta]N\[Pi][1][{i_,\[Mu]_},{nucleon_},{a_,qa_},Isospin]:=xi[i,a];
V\[CapitalDelta]N\[Pi][1][{i_,\[Mu]_},{nucleon_},{a_,qa_}]:=Dot@@(V\[CapitalDelta]N\[Pi][1][{i,\[Mu]},{nucleon},{a,qa},#]&/@{Dirac,Isospin});


VN\[CapitalDelta]\[Pi][1][{nucleon_},{i_,\[Mu]_},{a_,qa_},Dirac]:=-(h/F) (momentum[qa,\[Mu]]+$z1 Diracslash[qa].Diracgamma[\[Mu]]) ;
VN\[CapitalDelta]\[Pi][1][{nucleon_},{i_,\[Mu]_},{a_,qa_},Isospin]:=xi[a,i];
VN\[CapitalDelta]\[Pi][1][{nucleon_},{i_,\[Mu]_},{a_,qa_}]:=Dot@@(VN\[CapitalDelta]\[Pi][1][{nucleon},{i,\[Mu]},{a,qa},#]&/@{Dirac,Isospin});


theta[mu_,nu_,z_]:=metrictensor[mu,nu]+z Diracgamma[mu].Diracgamma[nu];
V\[CapitalDelta]N\[Pi][2][{i_,\[Mu]_},{mom_},{a_,qa_},Dirac]:=-(1/F)theta[\[Mu],uniquenu=Unique[nu],$z2].momentum[qa,uniquenu].(b3 Diracslash[qa]+b8/mn scalarproduct[qa,mom]);
V\[CapitalDelta]N\[Pi][2][{i_,\[Mu]_},{mom_},{a_,qa_},Isospin]:=xi[i,a];
V\[CapitalDelta]N\[Pi][2][{i_,\[Mu]_},{mom_},{a_,qa_}]:=Dot@@(V\[CapitalDelta]N\[Pi][2][{i,\[Mu]},{mom},{a,qa},#]&/@{Dirac,Isospin});


VN\[CapitalDelta]\[Pi][2][{mom_},{i_,\[Mu]_},{a_,qa_},Dirac]:=1/F (b3 Diracslash[qa]+b8/mn scalarproduct[qa,mom]).momentum[qa,uniquenu=Unique[nu]].theta[uniquenu,\[Mu],$z2];
VN\[CapitalDelta]\[Pi][2][{mom_},{i_,\[Mu]_},{a_,qa_},Isospin]:=xi[a,i];
VN\[CapitalDelta]\[Pi][2][{mom_},{i_,\[Mu]_},{a_,qa_}]:=Dot@@(VN\[CapitalDelta]\[Pi][2][{mom},{i,\[Mu]},{a,qa},#]&/@{Dirac,Isospin});


V\[CapitalDelta]N\[Pi][3][{i_,\[Mu]_},{mom_},{a_,qa_},Dirac]:=1/F theta[\[Mu],uniquenu=Unique[nu],$z3].momentum[qa,uniquenu].((f1/mn Diracslash[qa]+f2/mn^2 scalarproduct[qa,mom])scalarproduct[qa,mom]-2mp^2 (2f4-f5));
V\[CapitalDelta]N\[Pi][3][{i_,\[Mu]_},{mom_},{a_,qa_},Isospin]:=xi[i,a];
V\[CapitalDelta]N\[Pi][3][{i_,\[Mu]_},{mom_},{a_,qa_}]:=Dot@@(V\[CapitalDelta]N\[Pi][3][{i,\[Mu]},{mom},{a,qa},#]&/@{Dirac,Isospin});


VN\[CapitalDelta]\[Pi][3][{mom_},{i_,\[Mu]_},{a_,qa_},Dirac]:=1/F ((f1/mn Diracslash[qa]+f2/mn^2 scalarproduct[qa,mom])scalarproduct[qa,mom]-2mp^2 (2f4-f5)).momentum[qa,uniquenu=Unique[nu]].theta[uniquenu,\[Mu],$z3];
VN\[CapitalDelta]\[Pi][3][{mom_},{i_,\[Mu]_},{a_,qa_},Isospin]:=xi[a,i];
VN\[CapitalDelta]\[Pi][3][{mom_},{i_,\[Mu]_},{a_,qa_}]:=Dot@@(VN\[CapitalDelta]\[Pi][3][{mom},{i,\[Mu]},{a,qa},#]&/@{Dirac,Isospin});


V\[CapitalDelta]N3\[Pi][1][{i_,\[Mu]_},{x_},{a_,qa_},{b_,qb_},{c_,qc_},case_]:=Module[{diracPart,isospinPart},
diracPart[{a1_,qa1_},{b1_,qb1_},{c1_,qc1_}]:=h/(6F^3) (momentum[2qa1-qb1-qc1,\[Mu]]+$z1 Diracgamma[\[Mu]].Diracslash[2qa1-qb1-qc1]);
isospinPart[{a1_,qa1_},{b1_,qb1_},{c1_,qc1_}]:=xi[i,a1].KD2[b1,c1];
Switch[case,
Dirac,
{diracPart[{a,qa},{b,qb},{c,qc}],diracPart[{b,qb},{c,qc},{a,qa}],diracPart[{c,qc},{a,qa},{b,qb}]},
Isospin,
{isospinPart[{a,qa},{b,qb},{c,qc}],isospinPart[{b,qb},{c,qc},{a,qa}],isospinPart[{c,qc},{a,qa},{b,qb}]},_,Print["V\[CapitalDelta]N3\[Pi] false"]]];
V\[CapitalDelta]N3\[Pi][1][{i_,\[Mu]_},{x_},{a_,qa_},{b_,qb_},{c_,qc_}]:=Sum[Dot@@(V\[CapitalDelta]N3\[Pi][1][{i,\[Mu]},{x},{a,qa},{b,qb},{c,qc},#][[i]]&/@{Dirac,Isospin}),{i,1,3}];


(*V\[CapitalDelta]N3\[Pi][1][{i_,\[Mu]_},{x_},{a_,qa_},{b_,qb_},{c_,qc_}]:=Module[{part},part[{a1_,qa1_},{b1_,qb1_},{c1_,qc1_}]:=h/(6F^3) xi[i,a1].KD2[b1,c1].(momentum[2qa1-qb1-qc1,\[Mu]]+$z Diracgamma[\[Mu]].Diracslash[2qa1-qb1-qc1]);
part[{a,qa},{b,qb},{c,qc}]+part[{b,qb},{c,qc},{a,qa}]+part[{c,qc},{a,qa},{b,qb}]]*)


VN\[CapitalDelta]3\[Pi][1][{x_},{i_,\[Mu]_},{a_,qa_},{b_,qb_},{c_,qc_},case_]:=Module[{diracPart,isospinPart},
diracPart[{a1_,qa1_},{b1_,qb1_},{c1_,qc1_}]:=h/(6F^3) (momentum[2qa1-qb1-qc1,\[Mu]]+$z1 Diracslash[2qa1-qb1-qc1]. Diracgamma[\[Mu]]);
isospinPart[{a1_,qa1_},{b1_,qb1_},{c1_,qc1_}]:=xi[a1,i].KD2[b1,c1];
Switch[case,Dirac,{diracPart[{a,qa},{b,qb},{c,qc}],diracPart[{b,qb},{c,qc},{a,qa}],diracPart[{c,qc},{a,qa},{b,qb}]},Isospin,{isospinPart[{a,qa},{b,qb},{c,qc}],isospinPart[{b,qb},{c,qc},{a,qa}],isospinPart[{c,qc},{a,qa},{b,qb}]},_,Print["V\[CapitalDelta]N3\[Pi] false"]]]
(*VN\[CapitalDelta]3\[Pi][1][{x_},{i_,\[Mu]_},{a_,qa_},{b_,qb_},{c_,qc_}]:=Dot@@(VN\[CapitalDelta]3\[Pi][1][{x},{i,\[Mu]},{a,qa},{b,qb},{c,qc},#]&/@{Dirac,Isospin});*)
VN\[CapitalDelta]3\[Pi][1][{x_},{i_,\[Mu]_},{a_,qa_},{b_,qb_},{c_,qc_}]:=Sum[Dot@@(VN\[CapitalDelta]3\[Pi][1][{x},{i,\[Mu]},{a,qa},{b,qb},{c,qc},#][[i]]&/@{Dirac,Isospin}),{i,1,3}];


(* ::Subsubsection::Closed:: *)
(*axial vector form factor*)


VNNA[1][{pf_},{pi_},{a_,\[Mu]_,qa_},Dirac]:=(I gA)/2 Diracgamma[\[Mu]].Diracgamma5[];
VNNA[1][{pf_},{pi_},{a_,\[Mu]_,qa_},Isospin]:=Paulitau[a];
VNNA[1][{pf_},{pi_},{a_,\[Mu]_,qa_}]:=Dot@@(VNNA[1][{pf},{pi},{a,\[Mu],qa},#]&/@{Dirac,Isospin});


VNNA\[Pi][1][{pf_},{pi_},{a_,\[Mu]_,qa_},{b_,qb_},Dirac]:=-(I/(2F))Diracgamma[\[Mu]];
VNNA\[Pi][1][{pf_},{pi_},{a_,\[Mu]_,qa_},{b_,qb_},Isospin]:=LV2[a,b,uniquec=Unique[c]].Paulitau[uniquec];
VNNA\[Pi][1][{pf_},{pi_},{a_,\[Mu]_,qa_},{b_,qb_}]:=Dot@@(VNNA\[Pi][1][{pf},{pi},{a,\[Mu],qa},{b,qb},#]&/@{Dirac,Isospin});


VNNA2\[Pi][1][{pf_},{pi_},{a_,\[Mu]_,qa_},{b_,qb_},{c_,qc_},Dirac]:=-((I gA)/(4F^2))Diracgamma[\[Mu]].Diracgamma5[];
VNNA2\[Pi][1][{pf_},{pi_},{a_,\[Mu]_,qa_},{b_,qb_},{c_,qc_},Isospin]:=(2Paulitau[a]KD2[b,c]-Paulitau[b]KD2[a,c]-Paulitau[c]KD2[a,b]);
VNNA2\[Pi][1][{pf_},{pi_},{a_,\[Mu]_,qa_},{b_,qb_},{c_,qc_}]:=Dot@@(VNNA2\[Pi][1][{pf},{pi},{a,\[Mu],qa},{b,qb},{c,qc},#]&/@{Dirac,Isospin});


VNNA[3][{pf_},{pi_},{a_,\[Mu]_,qa_}]:=I (2d16 mp^2 Diracgamma[\[Mu]].Diracgamma5[]+d22/2 (Diracgamma[\[Mu]].Diracgamma5[]scalarproduct[qa]-Diracslash[qa].Diracgamma5[]momentum[qa,\[Mu]])).Paulitau[a];


V\[CapitalDelta]NA[1][{i_,\[Mu]_},{pi_},{j_,\[Nu]_,qa_},Dirac]:=I h  theta[\[Mu],\[Nu],$z1];
V\[CapitalDelta]NA[1][{i_,\[Mu]_},{pi_},{j_,\[Nu]_,qa_},Isospin]:=xi[i,j];
V\[CapitalDelta]NA[1][{i_,\[Mu]_},{pi_},{j_,\[Nu]_,qa_}]:=Dot@@(V\[CapitalDelta]NA[1][{i,\[Mu]},{pi},{j,\[Nu],qa},#]&/@{Dirac,Isospin});


VN\[CapitalDelta]A[1][{pi_},{i_,\[Mu]_},{j_,\[Nu]_,qa_},Dirac]:=I h theta[\[Nu],\[Mu],$z1];
VN\[CapitalDelta]A[1][{pi_},{i_,\[Mu]_},{j_,\[Nu]_,qa_},Isospin]:=xi[j,i];
VN\[CapitalDelta]A[1][{pi_},{i_,\[Mu]_},{j_,\[Nu]_,qa_}]:=Dot@@(VN\[CapitalDelta]A[1][{pi},{i,\[Mu]},{j,\[Nu],qa},#]&/@{Dirac,Isospin});


V\[CapitalDelta]\[CapitalDelta]A[1][{i_,\[Mu]_},{j_,\[Nu]_},{a_,\[Alpha]_,qa_},Dirac]:=-I 1/2 (g1 Diracgamma[\[Alpha]].Diracgamma5[].metrictensor[\[Mu],\[Nu]]+g2 (Diracgamma[\[Mu]].metrictensor[\[Alpha],\[Nu]]+Diracgamma[\[Nu]].metrictensor[\[Alpha],\[Mu]]).Diracgamma5[]+g3 Diracgamma[\[Mu]].Diracgamma[\[Alpha]].Diracgamma5[].Diracgamma[\[Nu]]);

V\[CapitalDelta]\[CapitalDelta]A[1][{i_,\[Mu]_},{j_,\[Nu]_},{a_,\[Alpha]_,qa_},Isospin]:=xi[i,uniquen=Unique[n]].Paulitau[a].xi[uniquen,j];
V\[CapitalDelta]\[CapitalDelta]A[1][{i_,\[Mu]_},{j_,\[Nu]_},{a_,\[Alpha]_,qa_}]:=Dot@@(V\[CapitalDelta]\[CapitalDelta]A[1][{i,\[Mu]},{j,\[Nu]},{a,\[Alpha],qa},#]&/@{Dirac,Isospin})


(* ::Subsection:: *)
(*Scattering amplitudes calculating functions*)


(* ::Subsubsection::Closed:: *)
(*Auxilary functions*)


xDBForm[ABampl_List]:=Module[{nu=(s-(2mn^2+2mp^2-s-t))/(4mn),AB=ABampl},{{AB[[1,1]]+nu AB[[1,2]]//Expand,AB[[1,2]]},{AB[[2,1]]+nu AB[[2,2]]//Expand,AB[[2,2]]}}];


xDBFormPhys[ABampl_List]:=Module[{nu=(s-(2mnuc^2+2mpir^2-s-t))/(4mnuc),AB=ABampl},{{AB[[1,1]]+nu AB[[1,2]]//Expand,AB[[1,2]]},{AB[[2,1]]+nu AB[[2,2]]//Expand,AB[[2,2]]}}];


xABForm[DBampl_List]:=Module[{nu=(s-(2mn^2+2mp^2-s-t))/(4mn),DB=DBampl},{{DB[[1,1]]-nu DB[[1,2]]//Expand,DB[[1,2]]},{DB[[2,1]]-nu DB[[2,2]]//Expand,DB[[2,2]]}}];


xCrossing[ADBampl_List]:=Module[{xs,xu,crossing={{1,0},{0,-1}},sigma},crossing.ADBampl.crossing/.{s->xs,u->xu,xsigma->sigma}/.{xs->u,xu->s,sigma->xsigmau}/.u->2mn^2+2mp^2-s-t];


(*SetAttributes[xCollect,Listable]
xCollect[amp_]:=Module[{head},head=_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i;Collect[amp,head,Simplify]]
xCompare=Function[amp,Map[(xUniquePaVe@xTensorReduce[#])&,amp,{2}]//xCollect//Simplify//xPrintTime];*)


(*SetAttributes[xCollect,Listable]
xCollect[amp_]:=Module[{head,LFs},
head=_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i;
LFs=Cases[{amp},head,Infinity]//Union;
Collect[amp,LFs,Simplify@Expand[#]&]];*)


(*SetAttributes[xCollect2,Listable]
xCollect2[amp_]:=Module[{head},head=_LFA0|_LFB0|_LFC0|_LFD0|_LFA0i|_LFB0i|_LFC0i|_LFD0i;Collect[amp,head]];*)


xCompare=Function[amp,Map[(xUniquePaVe@xTensorReduce[#])&,amp,{2}]//xCollect//xPrintTime];


(* ::Subsubsection::Closed:: *)
(*tree amplitude*)


xABtree[exp_]:=Module[{amp,ampU,AA,BB,head,ABlist},
amp=xSU2Simplify@xDiracSimplify@xDiracContract@xDotSimplify[exp](*/.D->4*)/.FeynAmplDenominator[{p_,m_}]:>1/(scalarproduct[p]-m^2)/.MandelstamRulesPhys;
ampU=xDiracSimplify[DiracspinorU[pf,mnuc].(amp/.{Si->qa+pi,De->pi-pf}/.qb->qa+pi-pf).DiracspinorU[pi,mnuc]]/.MandelstamRulesPhys/.u->2mpir^2+2mnuc^2-s-t;
AA=ampU/.{Dotgamma[DiracspinorU[pf,mnuc],DiracspinorU[pi,mnuc]]->1,Dotgamma[DiracspinorU[pf,mnuc],Diracslash[qa],DiracspinorU[pi,mnuc]]->0};
BB=ampU/.{Dotgamma[DiracspinorU[pf,mnuc],DiracspinorU[pi,mnuc]]->0,Dotgamma[DiracspinorU[pf,mnuc],Diracslash[qa],DiracspinorU[pi,mnuc]]->1};
ABlist={Coefficient[#,KD2[a,b]]&/@{AA,BB},I*Coefficient[#,LV2[a,b,paulitau]]&/@{AA,BB}}
]


xABtree[expDirac_,expIsospin_]:=Module[{amp,ampU,AA,BB,ampIso,pp,mm,ABlist},
amp=xSU2Simplify@xDiracSimplify@xDiracContract@xDotSimplify[expDirac](*/.D->4*)/.FeynAmplDenominator[{p_,m_}]:>1/(scalarproduct[p]-m^2)/.MandelstamRulesPhys;
ampU=xDiracSimplify[DiracspinorU[pf,mnuc].(amp/.{Si->qa+pi,De->pi-pf}/.qb->qa+pi-pf).DiracspinorU[pi,mnuc]]/.MandelstamRulesPhys/.u->2mpir^2+2mnuc^2-s-t;
AA=ampU/.{Dotgamma[DiracspinorU[pf,mnuc],DiracspinorU[pi,mnuc]]->1,Dotgamma[DiracspinorU[pf,mnuc],Diracslash[qa],DiracspinorU[pi,mnuc]]->0};
BB=ampU/.{Dotgamma[DiracspinorU[pf,mnuc],DiracspinorU[pi,mnuc]]->0,Dotgamma[DiracspinorU[pf,mnuc],Diracslash[qa],DiracspinorU[pi,mnuc]]->1};
ampIso=expIsospin//xSU2Simplify;
pp=Coefficient[ampIso,KD2[a,b]];
mm=I*Coefficient[ampIso,LV2[a,b,paulitau]];
ABlist={{AA*pp,BB*pp},{AA*mm,BB*mm}}
]


(* ::Subsubsection::Closed:: *)
(*loop amplitude*)


Options[xABloop]={$TensorReduce->False};
xABloop[exp_,OptionsPattern[]]:=Module[{amp,ampU,AA,BB,head,ABlist},
amp=xLoopAmplitude[exp]/.propagator[p_,m_]:>1/(scalarproduct[p]-m^2)/.MandelstamRules;
ampU=xDiracSimplify[DiracspinorU[pf,mn].(amp/.{Si->qa+pi,De->pi-pf}/.qb->qa+pi-pf).DiracspinorU[pi,mn]]/.MandelstamRules/.u->2mp^2+2mn^2-s-t;
AA=ampU/.{Dotgamma[DiracspinorU[pf,mn],DiracspinorU[pi,mn]]->1,Dotgamma[DiracspinorU[pf,mn],Diracslash[qa],DiracspinorU[pi,mn]]->0};
BB=ampU/.{Dotgamma[DiracspinorU[pf,mn],DiracspinorU[pi,mn]]->0,Dotgamma[DiracspinorU[pf,mn],Diracslash[qa],DiracspinorU[pi,mn]]->1};
ABlist=If[OptionValue[$TensorReduce],xPrintTime[Map[xTensorReduce,{Coefficient[#,KD2[a,b]]&/@{AA,BB},I*Coefficient[#,LV2[a,b,paulitau]]&/@{AA,BB}},{2}],"TensorReduce..."]//xCollect,{Coefficient[#,KD2[a,b]]&/@{AA,BB},I*Coefficient[#,LV2[a,b,paulitau]]&/@{AA,BB}}//xCollect]
]


Options[xABloop2]={$TensorReduce->False};
xABloop2[expDirac_,expIsospin_,OptionsPattern[]]:=Module[{amp,ampU,AA,BB,ampIso,pp,mm,ABlist},
amp=xPrintTime[(*xSetDto4@*)xLoopAmplitude[expDirac]/.propagator[p_,m_]:>1/(scalarproduct[p]-m^2)/.MandelstamRules,"Intergrating...SetDto4..."];
ampU=xDiracSimplify[DiracspinorU[pf,mn].(amp/.{Si->qa+pi,De->pi-pf}/.qb->qa+pi-pf).DiracspinorU[pi,mn]]/.MandelstamRules/.u->2mp^2+2mn^2-s-t;
AA=ampU/.{Dotgamma[DiracspinorU[pf,mn],DiracspinorU[pi,mn]]->1,Dotgamma[DiracspinorU[pf,mn],Diracslash[qa],DiracspinorU[pi,mn]]->0};
BB=ampU/.{Dotgamma[DiracspinorU[pf,mn],DiracspinorU[pi,mn]]->0,Dotgamma[DiracspinorU[pf,mn],Diracslash[qa],DiracspinorU[pi,mn]]->1};
ampIso=expIsospin//xSU2Simplify;
pp=Coefficient[ampIso,KD2[a,b]];
mm=I*Coefficient[ampIso,LV2[a,b,paulitau]];
ABlist=If[OptionValue[$TensorReduce],xPrintTime[Map[xTensorReduce,{{AA*pp,BB*pp},{AA*mm,BB*mm}},{2}],"TensorReduce"],{{AA*pp,BB*pp},{AA*mm,BB*mm}}]
]
(*Options[xABloop2]={$TensorReduce->False};
xABloop2[expDirac_,expIsospin_,OptionsPattern[]]:=Module[{amp,ampU,AA,BB,ampIso,pp,mm,ABlist},
amp=xPrintTime[xLoopAmplitude[expDirac]/.propagator[p_,m_]:>1/(scalarproduct[p]-m^2)/.MandelstamRules,"Intergrating......"];
ampU=xDiracSimplify[DiracspinorU[pf,mn].(amp/.{Si->qa+pi,De->pi-pf}/.qb->qa+pi-pf).DiracspinorU[pi,mn]]/.MandelstamRules/.u->2mp^2+2mn^2-s-t;
AA=ampU/.{Dotgamma[DiracspinorU[pf,mn],DiracspinorU[pi,mn]]->1,Dotgamma[DiracspinorU[pf,mn],Diracslash[qa],DiracspinorU[pi,mn]]->0};
BB=ampU/.{Dotgamma[DiracspinorU[pf,mn],DiracspinorU[pi,mn]]->0,Dotgamma[DiracspinorU[pf,mn],Diracslash[qa],DiracspinorU[pi,mn]]->1};
ampIso=expIsospin//xSU2Simplify;
pp=Coefficient[ampIso,KD2[a,b]];
mm=I*Coefficient[ampIso,LV2[a,b,paulitau]];
ABlist=If[OptionValue[$TensorReduce],xPrintTime[Map[xTensorReduce,{{AA*pp,BB*pp},{AA*mm,BB*mm}},{2}],"TensorReduce"],{{AA*pp,BB*pp},{AA*mm,BB*mm}}]
]*)


(*mainly designed for graph l and g1, g2, can also be used to the others*)
Options[xABloop3]={$TensorReduce->False};
xABloop3[expDirac_,expIsospin_,OptionsPattern[]]:=Module[{amp,ds,ds2,ds2simplify,ampU,AA,BB,ampIso,pp,mm,ABlist},
amp=xPrintTime[(*xSetDto4@*)xLoopAmplitude[expDirac]/.propagator[p_,m_]:>1/(scalarproduct[p]-m^2)/.MandelstamRules,"Intergrating...SetDto4..."];
ds=xSeparate[amp,Diracslash];
ds2=ds[[2]]/.{Si->qa+pi,De->pi-pf}/.qb->qa+pi-pf;
ds2simplify=((xDiracSimplify[Dotgamma[DiracspinorU[pf,mn],#,DiracspinorU[pi,mn]]]/.MandelstamRules)&)/@ds2;
ampU=ds[[1]].ds2simplify/.u->2mp^2+2mn^2-s-t;
AA=ampU/.{Dotgamma[DiracspinorU[pf,mn],DiracspinorU[pi,mn]]->1,Dotgamma[DiracspinorU[pf,mn],Diracslash[qa],DiracspinorU[pi,mn]]->0};
BB=ampU/.{Dotgamma[DiracspinorU[pf,mn],DiracspinorU[pi,mn]]->0,Dotgamma[DiracspinorU[pf,mn],Diracslash[qa],DiracspinorU[pi,mn]]->1};
ampIso=xSU2Simplify/@(expIsospin//xDotSimplify//Expand);
pp=Coefficient[ampIso,KD2[a,b]];
mm=I*Coefficient[ampIso,LV2[a,b,paulitau]];
ABlist=If[OptionValue[$TensorReduce],xPrintTime[Map[xTensorReduce,{{AA*pp,BB*pp},{AA*mm,BB*mm}},{2}],"TensorReduce"],{{AA*pp,BB*pp},{AA*mm,BB*mm}}]
]


(* ::Subsubsection::Closed:: *)
(*renormalizaion of gA*)


AxialVectorPart[exp_]:=Coefficient[exp,Dotgamma[Diracgamma[\[Mu]],Diracgamma5[]]Paulitau[a]]


Options[getGA]={$tensorreduce->True};
getGA[expDirac_,expIsospin_,OptionsPattern[]]:=Module[{rule,loopDirac,loopDiracSim,loopIso,GAA},
rule={scalarproduct[pi]->mn^2,scalarproduct[pf]->mn^2,scalarproduct[pi,pf]->(2mn^2-t)/2};
loopDirac=xLoopAmplitude[expDirac]/.rule;
loopDiracSim=xDiracSimplify[DiracspinorU[pf,mn].loopDirac.DiracspinorU[pi,mn]]/.{DiracspinorU[pf,mn]->1,DiracspinorU[pi,mn]->1}/.rule//xDiracSimplify;
loopIso=expIsospin//xSU2Simplify;
GAA=Collect[If[OptionValue[$tensorreduce],loopDiracSim*loopIso//xTensorReduce//xUniquePaVe,loopDiracSim*loopIso],{Dotgamma[Diracgamma[\[Mu]],Diracgamma5[]],Diracgamma5[],Paulitau[a]},xCollect]
]


(* ::Subsection:: *)
(*Power counting breaking terms functions*)


(* ::Subsubsection::Closed:: *)
(*expanding parameters definitions*)


xalpha/:MakeBoxes[xalpha,TraditionalForm]:="\[Alpha]";
xOmiga/:MakeBoxes[xOmiga,TraditionalForm]:="\[CapitalOmega]";
xtau/:MakeBoxes[xtau,TraditionalForm]:="\[Tau]";
xdelta/:MakeBoxes[xdelta,TraditionalForm]:="\[Delta]";
xsigma/:MakeBoxes[xsigma,TraditionalForm]:="\[Sigma]";
xsigmau/:MakeBoxes[xsigmau,TraditionalForm]:=SubscriptBox["\[Sigma]","u"];


ExpandParameter={s->(2xalpha  xOmiga+1+xalpha^2) mn^2,mp->xalpha mn,t->xtau xalpha^2 mn^2,md->(xalpha xdelta+1)mn};
ExpandParameterReversed={xOmiga->(s-mn^2-mp^2)/(2mn mp),xalpha->mp/mn,xtau->t/mp^2,xdelta->(md-mn)/mp};


ExpandParameter0={s->(2xalpha xsigma+1) mn^2,mp->xalpha mn,t->xtau xalpha^2 mn^2,md->(xalpha xdelta+1)mn};
ExpandParameter0Reversed={xsigma->(s-mn^2)/(2mn mp),xalpha->mp/mn,xtau->t/mp^2,xdelta->(md-mn)/mp};


ExpandParameter1={s->xalpha xsigma+ mn^2,mp->xalpha mp,t->xalpha^2 t};
ExpandParameter1Reversed={xalpha->1,xsigma->s-mn^2};
(*ExpandParameter1={s->xalpha xsigma+ mn^2,mp->xalpha mp,t->xalpha^2 t,md->xalpha xdelta+mn};
ExpandParameter1Reversed={xalpha->1,xsigma->s-mn^2,xdelta->md-mn};*)


(* ::Subsubsection::Closed:: *)
(*regular parts of one-loop Feynmann integrals*)


xRegularPart[FP_List,fad_FeynAmplDenominator,ExpandPara_,power_]:=Module[{momint,momintSeries,FPint0,FPint,kappa,UVR,eps,FPintsep},
kappa[1]=mn^2 UVR;
kappa[2]=-(1+UVR);
kappa[3]=-(1/(2mn^2))(1+UVR)eps;
kappa[4]=-(1/(6mn^4))(1+UVR)(1+eps)eps;
momint=xMomentumIntegration[FP,fad]/.MandelstamRules/.ExpandPara/.{Gamma[alpha_-D/2]:>(kappa[alpha]*Gamma[alpha]*(mn^2)^(alpha-D/2))/(I Pi^(D/2))};
momintSeries=If[Head[power]===List,SeriesCoefficient[momint,{xalpha,0,power[[1]]}]xalpha^power[[1]],Series[momint,{xalpha,0,power}]//Normal];
(*FPint=If[Length[fad]>=2,Integrate[momintSeries,Sequence@@(Reverse[{FP[[#]],0,1}&/@Table[ik,{ik,1,Length[fad]-1}],1]),Assumptions->D>50],momintSeries];*)
FPint0[arg_]:=Integrate[arg,Sequence@@(Reverse[{FP[[#]],0,1}&/@Table[ik,{ik,1,Length[fad]-1}],1]),Assumptions->D>50];
FPint=If[Length[fad]>=2,If[Head[momintSeries]===Plus,FPint0/@momintSeries,FPint0[momintSeries]],momintSeries];
FPintsep=xSeparate[Series[FPint/.D->4-2eps,{eps,0,1}]//Normal,UVR,eps];
Collect[FPintsep[[1]].(FPintsep[[2]]/.UVR*eps->-1)/.{eps->0,UVR->0},\[Alpha],Simplify]+HIGHORDER xalpha^(Sequence@@Flatten[{power}]+1) UnitStep[-Length[power]]
(*Collect[FPint,\[Alpha],Simplify]*)
]


xgetRegular[fad0_FeynAmplDenominator,ExpandPara_]:=Module[{len=Length[fad0],$m,x1,x2,x3,reg},
$m=fad0[[All,2]]//Union;
If[Length[$m]===1&&$m[[1]]===mp,Return[0]];
reg=Switch[len,
1,xRegularPart[{x1,x2,x3},fad0,ExpandPara,6],
2,xRegularPart[{x1,x2,x3},fad0,ExpandPara,6],
3,xRegularPart[{x1,x2,x3},fad0,ExpandPara,5],
4,xRegularPart[{x1,x2,x3},fad0,ExpandPara,4],
_,Print["Error"]];
Return[reg];
]


xRegularRules[fad_List,ExpandPara_]:=Module[{getDropList,fadExpanded,fadSimplify,LFint},
getDropList[fad0_FeynAmplDenominator]:=xDrop[fad0,#]&/@Permutations[Table[int,{int,1,Length[fad0]}],Length[fad0]-1];

fadExpanded=getDropList[#]&/@fad//Flatten//Union;
fadSimplify=(xShiftK@xUniqueFAD[#]&/@fadExpanded//Union)/.{De->pi-pf}/.{pi-pf->De,pf-pi->-De,Si-pi->qa,pi-Si->-qa,Si-pf->qb,pf-Si->-qb}//Union;
LFint=(xUniquePaVe@xExpandPair@xTensorDecompositonPaVe[{},#]&/@fadSimplify)/.MandelstamRules;
{Table[ii,{ii,1,Length[fadSimplify]}],fadSimplify,LFint,xgetRegular[#,ExpandPara]&/@fadSimplify}
]


(* ::Subsubsection::Closed:: *)
(*PCB terms*)


xPCBterms[amp_,power_]:=Module[{ampReg,RegRules,pcb},
(*Clear[Ro3int];xLoad[Ro3int,fileaddressRegular];
Clear[Rodint];xLoad[Rodint,fileaddressRegular];*)
RegRules={Thread[Ro3int[[3]]->Ro3int[[4]]],Thread[Rodint[[3]]->Rodint[[4]]]}//Flatten//xOrderPaVe//Union;
ampReg=xOrderPaVe@xTensorReduce[amp]/.RegRules/.ExpandParameter1Reversed/.{HIGHORDER->HIGHORDER*xalpha^4}/.ExpandParameter1;
pcb=Normal@Series[ampReg,{xalpha,0,power-1}]]


Options[xPCBtermsDB]={ABtoDB->True};
xPCBtermsDB[ABamp_List,power_,OptionsPattern[]]:=Module[{DB,DBpcb},
DB=If[OptionValue[ABtoDB],xDBForm[ABamp],ABamp];
DBpcb={{xPCBterms[DB[[1,1]],power],xPCBterms[DB[[1,2]],power-2]},{xPCBterms[DB[[2,1]],power],xPCBterms[DB[[2,2]],power-2]}}//Simplify
]


xPCBtermsLoop[loop_Symbol,loopfile_String]:=Module[{PCBloop,PCBloopname},
PCBloopname="PCB"<>ToString[loop];
xLoad[loop,loopfile];
PCBloop=xPCBtermsDB[loop,3];
Put[PCBloop,loopfile<>PCBloopname<>".dat"];
Return[PCBloop]
]


(* ::Subsection:: *)
(*Numerical computation*)


(* ::Subsubsection::Closed:: *)
(*numerical values of parameters*)


paraInput={mnuc->0.939,mpir->0.139,mdel->1.232,gAr->1.267,Fpi->92.4/1000};


(*dataInput=Input[#]&/@paraPhys*)
FettesFit1=PlusMinus[Sequence@@#]&/@{{0.139,0},{0.938,0},{1.232,0},{1.26,0},{92.4/1000,0},{0.77,0.02},{-17.92,0.04},{20.19,0.04},{-15.58,0.05},{-5.91,0.07},{0,0},{7.68,0.07},{-1.07,0.04},{-5.18,0.21},{0,0},{-0.98,0.19},{1.32,0.01},{-1.42,0.03},{-12.03,0.11},{0,0},{29.30,0.97},{0,0},{40.17/2,0.73/2},{0,0}};


FettesFit2=PlusMinus[Sequence@@#]&/@{{0.139,0},{0.939,0},{1.232,0},{1.26,0},{0.0924,0},{-0.44,0.02},{-0.67,0.03},{-0.07,0.03},{-2.51,0.05},{0.03,0.05},{0,0},{-0.93,0.04},{0.75,0.03},{-0.45,0.15},{0,0},{-1.35,0.14},{0.98,0.06},{-1.1,0.05},{0.51,0.09},{0,0},{-19.14,0.58},{0,0},{-15.14,0.465},{0,0}};


(* ::Subsubsection::Closed:: *)
(*Partial wave amplitudes*)


xPartialwavePiN[orbital_Integer,isospin2_?(OddQ[#]&),total2_?(OddQ[#]&)][sq_,ABlist0_List,para_List]:=Block[{link,s,mn0,mp0,tmin,tmax,Ep,lambda,A,B,T,partailwave,ABlist,Nfactor=1/(16Pi^2)},
(*1. setting parameters and definitions*)
Thread[{mn0,mp0}->({mnuc,mpir}/.para)]/.Rule->Set;
s=sq*sq;
lambda[a_,b_,c_]:=a^2+b^2+c^2-2a*b-2a*c-2b*c;
tmin=-(lambda[s,mn0^2,mp0^2]/s)(*+10^-10*);
tmax=-10^-10;
Ep=(s+mn0^2-mp0^2)/(2Sqrt[s]);
(*2. isospin amplitudes*)
ABlist=Nfactor*ABlist0(*//xTensorReduce*)(*//xCollect2*)//xLTadapted//xLTForm;
A[1][t_]:=ABlist[[1,1]]+2ABlist[[2,1]]/.para;
A[3][t_]:=ABlist[[1,1]]-ABlist[[2,1]]/.para;
B[1][t_]:=ABlist[[1,2]]+2ABlist[[2,2]]/.para;
B[3][t_]:=ABlist[[1,2]]-ABlist[[2,2]]/.para;

(*3. partial wave amplidues*)
T[I_,l_][AorB_]:=(2s)/lambda[s,mn0^2,mp0^2]*NIntegrate[AorB[I][t]*LegendreP[l,1+(2 s t)/lambda[s,mn0^2,mp0^2]],{t,tmin,tmax}];
partailwave[l_Integer,I_?(OddQ[#]&),J_?(OddQ[#]&)]:=
Switch[l,
Round[(J-1)/2],
((Ep+mn0)/2) (T[I,l][A]+(Sqrt[s]-mn0)T[I,l][B])+((Ep-mn0)/2) (-T[I,l+1][A]+(Sqrt[s]+mn0)T[I,l+1][B]),
Round[(J+1)/2],
((Ep+mn0)/2) (T[I,l][A]+(Sqrt[s]-mn0)T[I,l][B])+((Ep-mn0)/2) (-T[I,l-1][A]+(Sqrt[s]+mn0)T[I,l-1][B]),
_,Print["this PW not exist"];Abort[]];
partailwave[orbital,isospin2,total2]
]


xPartialwavePiNAll[sq_,ABlist0_List,para_List]:=Block[{link,s,mn0,mp0,tmin,tmax,Ep,lambda,ABlist,Nfactor=1(*/(16Pi^2)*),A,B,T,A10,A11,A12,B10,B11,B12,A30,A31,A32,B30,B31,B32,TS11,TS31,TP11,TP13,TP31,TP33},
(*1. setting parameters and definitions*)
Thread[{mn0,mp0}->({mnuc,mpir}/.para)]/.Rule->Set;
s=sq*sq;
lambda[a_,b_,c_]:=a^2+b^2+c^2-2a*b-2a*c-2b*c;
tmin=-(lambda[s,mn0^2,mp0^2]/s)+10^-10;
tmax=-10^-10;
Ep=(s+mn0^2-mp0^2)/(2Sqrt[s]);
(*2. isospin amplitudes*)
ABlist=Nfactor*ABlist0(*//xTensorReduce*)(*//xCollect2*)//xLTadapted//xLTForm;
A[1][t_]:=ABlist[[1,1]]+2ABlist[[2,1]]/.para;
A[3][t_]:=ABlist[[1,1]]-ABlist[[2,1]]/.para;
B[1][t_]:=ABlist[[1,2]]+2ABlist[[2,2]]/.para;
B[3][t_]:=ABlist[[1,2]]-ABlist[[2,2]]/.para;

(*3. partial wave amplidues*)
T[I_,l_][AorB_]:=(2s)/lambda[s,mn0^2,mp0^2]*NIntegrate[AorB[I][t]*LegendreP[l,1+(2 s t)/lambda[s,mn0^2,mp0^2]],{t,tmin,tmax}];

A10=T[1,0][A];
B10=T[1,0][B];
A11=T[1,1][A];
B11=T[1,1][B];
A12=T[1,2][A];
B12=T[1,2][B];
A30=T[3,0][A];
B30=T[3,0][B];
A31=T[3,1][A];
B31=T[3,1][B];
A32=T[3,2][A];
B32=T[3,2][B];

TS11=(Ep+mn0)/2 (A10+(Sqrt[s]-mn0)*B10)+(Ep-mn0)/2 (-A11+(Sqrt[s]+mn0)*B11);
TS31=(Ep+mn0)/2 (A30+(Sqrt[s]-mn0)*B30)+(Ep-mn0)/2 (-A31+(Sqrt[s]+mn0)*B31);
TP11=(Ep+mn0)/2 (A11+(Sqrt[s]-mn0)*B11)+(Ep-mn0)/2 (-A10+(Sqrt[s]+mn0)*B10);
TP31=(Ep+mn0)/2 (A31+(Sqrt[s]-mn0)*B31)+(Ep-mn0)/2 (-A30+(Sqrt[s]+mn0)*B30);
TP13=(Ep+mn0)/2 (A11+(Sqrt[s]-mn0)*B11)+(Ep-mn0)/2 (-A12+(Sqrt[s]+mn0)*B12);
TP33=(Ep+mn0)/2 (A31+(Sqrt[s]-mn0)*B31)+(Ep-mn0)/2 (-A32+(Sqrt[s]+mn0)*B32);
{TS11,TS31,TP11,TP31,TP13,TP33}
]


Options[xPWsodloop]={$cross->False};
xPWsodloop[loop_Symbol,loopfile_String,OptionsPattern[]]:=Module[{paraInput,loopdataname,loopSU,PWall},
paraInput={mnuc->0.939,mpir->0.139,mdel->1.232,gAr->1.267,Fpi->92.4/1000};
loopdataname="NUM"<>ToString[loop];
xLoad[loop,loopfile];
loopSU=If[OptionValue[$cross],loop+xCrossing[loop],loop];
PWall=xPartialwavePiNAll[#,loopSU/.Thread[paraBare->paraPhys]/.{hr->1,g1r->1},paraInput]&/@Table[1.078+0.004int,{int,1,30}];
Put[PWall,loopfile<>loopdataname<>".txt"];
Return[PWall]
]


(* ::Subsubsection::Closed:: *)
(*partial wave shifts*)


xPWphaseshiftPiN[orbital_Integer,isospin2_?(OddQ[#]&),total2_?(OddQ[#]&)][sq_,ABlist_List,para_List]:=Block[{s,mn0,mp0,lambda,Absp},
Thread[{mn0,mp0}->({mnuc,mpir}/.para)]/.Rule->Set;
s=sq^2;
lambda[a_,b_,c_]:=a^2+b^2+c^2-2a*b-2a*c-2b*c;
Absp[ss_]:=Sqrt[lambda[ss,mn0^2,mp0^2]]/(2Sqrt[ss]);
180/Pi*Absp[s]/(8 Pi Sqrt[s])*Re[xPartialwavePiN[orbital,isospin2,total2][sq,ABlist,para]]
]


xPWphaseshiftPiNAll[sq_,ABlist_List,para_List]:=Block[{s,mn0,mp0,lambda,Absp},
Thread[{mn0,mp0}->({mnuc,mpir}/.para)]/.Rule->Set;
s=sq^2;
lambda[a_,b_,c_]:=a^2+b^2+c^2-2a*b-2a*c-2b*c;
Absp[ss_]:=Sqrt[lambda[ss,mn0^2,mp0^2]]/(2Sqrt[ss]);
180/Pi*Absp[s]/(8 Pi Sqrt[s])*(Re/@xPartialwavePiNAll[sq,ABlist,para])
]


xPhaseShift[PartialWaves_List]:=Block[{s,mn0=0.939,mp0=0.139,len=Length[PartialWaves],lambda,Absp},
s=Table[(1.078+int 0.004)^2,{int,1,len}];
lambda[a_,b_,c_]:=a^2+b^2+c^2-2a*b-2a*c-2b*c;
Absp[ss_]:=Sqrt[lambda[ss,mn0^2,mp0^2]]/(2Sqrt[ss]);
180/Pi*Absp[s[[#]]]/(8 Pi Sqrt[s[[#]]]) (Re[PartialWaves[[#]]])&/@Table[i,{i,1,len}]
]
