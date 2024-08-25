(* ::Package:: *)

(*
	INTSECA
	Intersection theory for differential equation of twisted integral
	Copyright (C) 2024 Yuhan Fu
	yuhanyfu@gmail.com
*)


(*BeginPackage["INTSECA`"];*)
Print["INTSECA 1.0.3"]

t::usage = "list to bracket";
tp::usage = "bracket to list";
simplexBasis::usage = "Automatically generates basis if all simplexes";
phiJList::usage = "Collect all nonzero \[CurlyPhi]\[LeftAngleBracket]J\[RightAngleBracket]";
Omega::usage = "\[Omega]";
OmegaV::usage = "Collect all nonzero \[Omega]\[Wedge]\[CurlyPhi]\[LeftAngleBracket]J-1\[RightAngleBracket]";
coordinate::usage = "Solve the coordinate of a vertex";
XXComp::usage = "Decomposes basis to canonical form of vertices, \[LeftAngleBracket]a,b,c,\[CenterDot]\[CenterDot]\[RightAngleBracket]";
DKinVertex::usage = "Lifts the external derivative of canonical form of vertex (in fiber) to canonical form of vertex in total space";
DKinCollect::usage = "Collects the \!\(\*SubscriptBox[\(\[Del]\), \(x\)]\)\!\(\*SubscriptBox[\(e\), \(i\)]\) in terms of canonical form of vertices in total space";
Cin::usage = "Remove the numerator as linear combination of Subscript[l, i]'s appears in the denominator";
DKinComp::usage = "Decomposes the \!\(\*SubscriptBox[\(\[Del]\), \(x\)]\)\!\(\*SubscriptBox[\(e\), \(i\)]\) in terms of canonical form of vertices in fiber";
IntSec::usage = "Intersection number computing: \[LeftAngleBracket]\!\(\*SubscriptBox[\(e\), \(i\)]\)|\[CenterDot]\[RightAngleBracket]";
CMatrix::usage = "Computes the intersection matrix of bases: \!\(\*SubscriptBox[\(C\), \(ij\)]\)=\[LeftAngleBracket]\!\(\*SubscriptBox[\(e\), \(i\)]\)|\!\(\*SubscriptBox[\(e\), \(j\)]\)\[RightAngleBracket]";
CiCoeff::usage = "Gives the linear coefficient for projecting Feynman integral into basis integrals";
AMatrix::usage = "Gives the connnection matrix A for each given kinematic variable.";
UMatrix::usage = "Gives the tranformation matrix that change the bases (\!\(\*SubscriptBox[\(e\), \(1\)]\),\[Ellipsis],\!\(\*SubscriptBox[\(e\), \(\[Nu]\)]\)) to (\[Phi],\[PartialD]\[Phi],\[Ellipsis],\!\(\*SuperscriptBox[\(\[PartialD]\), \(\[Nu] - 1\)]\)\[Phi])";
PicardFuchs::usage = "Gives the Picard-Fuchs operator for Feynman integral";
DEQ::usage = "Gives the coefficient of each order of derivatives in the differential equation for the Feynman integral.";




(*Begin["`Private`"];*)


(*----------import Global values----------*)

nkin:=Global`nkin;
kin:=Global`kin;
nplane:=Global`nplane;
powers:=Global`powers;
nu:=Global`nu;
Lplanes:=Global`Lplanes;
jacT:=Global`jacT;
permT:=Global`permT;
vertex:=Global`vertex;
orient:=Global`orient;


(*----------default settings----------*)
dim:=Global`dim;
(*Clear[c,jacT,permT];*)
{z[1],z[2],z[3],z[4]}={z1,z2,z3,z4}; 
Xproj:=Append[Table[z[i],{i,1,dim}],1];
t[{a__}]:=\[LeftAngleBracket]a\[RightAngleBracket] (*transform list to \[LeftAngleBracket]...\[RightAngleBracket] symbol*)
tp[f_]:=f/.\[LeftAngleBracket]a__\[RightAngleBracket]:>{a} (*transform \[LeftAngleBracket]...\[RightAngleBracket] symbol to list*)


(*----------automatically generate basis if all simplexes----------*)
simplexBasis[simplexes_List,dim_:dim]:=(
Nu=Length[simplexes];
Vertex=Table[Subsets[simplexes[[i]],{dim}]
,{i,1,Nu}];
Orient=Table[-(-1)^Range[Length[Vertex[[i]]]],{i,1,Nu}];
(*sort*)
Orient=Table[Orient[[i,j]]*Signature[Vertex[[i,j]]],{i,1,Nu},{j,1,Length[Vertex[[i]]]}];
Vertex=Table[Sort[Vertex[[i,j]]],{i,1,Nu},{j,1,Length[Vertex[[i]]]}];
Return[{Vertex,Orient}]
);


(*----------find \[CurlyPhi]\[LeftAngleBracket]J\[RightAngleBracket] basis----------*)
rules={Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]a__\[RightAngleBracket]]:>0,Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>If[OrderedQ[{{a},{b}}],Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],-Wedge[\[LeftAngleBracket]b\[RightAngleBracket],\[LeftAngleBracket]a\[RightAngleBracket]]],
Wedge[c_*\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>c*Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],d_*\[LeftAngleBracket]b__\[RightAngleBracket]]:>d*Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],Wedge[(c1_*term1_+rest_),(term2_)]:>Wedge[c1*term1,term2]+Wedge[rest,term2],
Wedge[c_,d_*\[LeftAngleBracket]b__\[RightAngleBracket]]:>c*d*\[LeftAngleBracket]b\[RightAngleBracket],Wedge[c_*\[LeftAngleBracket]a__\[RightAngleBracket],d_]:>c*d*\[LeftAngleBracket]a\[RightAngleBracket]};

wedgeToBracketRule={
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket],rest_]:>Wedge[\[LeftAngleBracket]a,b\[RightAngleBracket],rest],
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>Wedge[\[LeftAngleBracket]a,b\[RightAngleBracket]],
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket]]:>\[LeftAngleBracket]a\[RightAngleBracket]
};

sort={\[LeftAngleBracket]a__\[RightAngleBracket]:>Signature[{a}]*t[Sort[{a}]]};

(*verticesList(*[dim_:dim]*):=t/@Sort[Sort/@(Select[Flatten[With[{limits=Table[{Subscript[i,k],If[k==1,1,Subscript[i,k-1]+1],nplane},{k,1,dim}]},Table[Array[Subscript[i,#]&,dim],Evaluate[Sequence@@limits]]],dim-1],!Det[Jac[[All,#]]]===0&])];
*)
parallel=\[LeftAngleBracket]a__\[RightAngleBracket]/;Det[Jac[[All,{a}]]]===0->0;
parallelRemove[v_List]:=DeleteCases[v//.parallel,0];
phiJList[n_]:=t/@Sort[Sort/@(Flatten[With[{limits=Table[{Subscript[i,k],If[k==1,1,Subscript[i,k-1]+1],nplane},{k,1,n}]},Table[Array[Subscript[i,#]&,n],Evaluate[Sequence@@limits]]],n-1])];
(*verticesList:=Select[phiJList[dim],!Det[Jac[[All,#//tp]]]===0&];*)
verticesList:=phiJList[dim]//parallelRemove;
Omega:=powers . (t/@Array[{#}&,nplane]);
OmegaV[xi_List]:=Table[Wedge[Omega,xi[[i]]]//.rules//.wedgeToBracketRule//.sort,{i,1,Length[xi]}]//parallelRemove;

coordinate[Vertex_]:=
First@(Solve[Map[Lplanes[[#]]==0&,tp[Vertex]],{z1,z2,z3,z4}]//Simplify);

multiIntsec[vertexToIntsec_List]:=(
Hypers=Select[vertexToIntsec,Length[#]>1&];
Return[Table[Total[Hypers[[i]]]==0,{i,1,Length[Hypers]}]]
)


(*----------decompose to vertices----------*)
XXComp[Vertex_List,Coeff_List]:=Table[
Sum[Coeff[[i,ni]]*t[Vertex[[i,ni]]],{ni,1,Length[Vertex[[i]]]}]
,{i,1,Length[Vertex]}];


(*----------derivative w.r.t kinematic variables----------*)
JacT[Lplanes_List]:=Table[Join[Table[D[Lplanes[[i]],kin[[j]]],{j,1,nkin}],Table[D[Lplanes[[i]],z[j]],{j,1,dim}]],{i,1,Length[Lplanes]}];
PermT[dim_,nkin_]:=Table[Permutations[Join[{n},Range[nkin+1,nkin+dim]]],{n,1,nkin}];

(*it would be better if we generalize DKin functions for fibration use.*)
DKinVertex[Vertex_List(*,nkin_:nkin,dim_:dim*)]:=
Table[
Sum[
(
Signature[permT[[nkin,i]]]
(powers[[Ad]]/( Subscript[l, Ad] Product[Subscript[l, Vertex[[j]]],{j,1,dim}])) 
jacT[[Ad,permT[[n,i,1]]]] 
Product[jacT[[Vertex[[k]],permT[[n,i,1+k]]]],{k,1,dim}]
)
,{i,1,Length[permT[[1]]]},{Ad,1,nplane}]
,{n,1,nkin}];

DKinCollect(*[nkin_:nkin,nu_:nu]*):=(
DkinCollect=Table[Sum[orient[[i,j]] DKinVertex[vertex[[i,j]]],{j,1,Length[vertex[[i]]]}],{i,1,nu}];
Lindex=Table[{},{nkin},{nu}];Lcoeff=Table[{},{nkin},{nu}];
subL=Subsets[Range[nplane],{dim+1}];
Do[coeff=Coefficient[DkinCollect[[j,nKin]],1/Product[Subscript[l, subL[[i,k]]],{k,1,1+dim}]]//Simplify;If[Simplify[coeff]===0, None ,
(
Lindex[[nKin,j]]=Append[Lindex[[nKin,j]],i];
Lcoeff[[nKin,j]]=Append[Lcoeff[[nKin,j]],coeff];
)
]
,{i,1,Length[subL]},{j,1,nu},{nKin,1,nkin}];
Return[{Lindex,Lcoeff}]
)

Cin[VertexP_List,nume_]:=(
nume0=Sum[Subscript[c, VertexP[[i]]] Lplanes[[VertexP[[i]]]],{i,1,dim+1}]-nume//Simplify;sol=Solve[Append[Table[Coefficient[nume0,z[i]]==0,{i,1,dim+1}],(nume0/.Table[z[i]->0,{i,1,dim}])==0],Table[Subscript[c,VertexP[[i]]],{i,1,dim+1}]]//Quiet;
Return[First@sol]);

DKinComp[nKin_,DKinCollect_List]:=(
Lindex=DKinCollect[[1]];
Lcoeff=DKinCollect[[2]];
subL=Subsets[Range[nplane],{dim+1}];
cin=Table[Cin[subL[[Lindex[[nKin,i,j]]]],Lcoeff[[nKin,i,j]]],{i,1,nu},{j,1,Length[Lindex[[nKin,i,All]]]}];
DkinComp=Table[
Sum[vertexListT=subL[[Lindex[[nKin,i,j]]]];
Sum[vertexList=vertexListT[[Complement[Range[1+dim],{n}]]];
(
(Subscript[c, vertexListT[[n]]]/.cin[[i,j]]//Simplify)*(vertexList//t)
)
,{n,1,1+dim}]
,{j,1,Length[Lindex[[nKin,i,All]]]}]
,{i,1,nu}];

DkinComp=DkinComp/.Table[Subscript[c, i]->0,{i,1,nplane}];
rule:=\[LeftAngleBracket]a__\[RightAngleBracket]:>(1/Det[jacT[[{a},nkin+1;;nkin+dim]]])\[LeftAngleBracket]a\[RightAngleBracket];
DkinComp=DkinComp/.rule;
Return[DkinComp]
)


(*----------Intersection number computing----------*)
IntSec[XXComp_List(*,vertex_:vertex,orient_:orient*)]:=Table[
Sum[(1/Times@@powers[[vertex[[i,ni]]]])orient[[i,ni]]*Coefficient[XXComp[[j]],t[vertex[[i,ni]]]]//Simplify
,{ni,1,Length[vertex[[i]]]}]
,{i,1,Length[vertex]},{j,1,Length[XXComp]}];


(*----------CMatrix, CiCoeff and AMatrix----------*)
CMatrix[eiComp_List]:=IntSec[eiComp]//Simplify;
CiCoeff[phiComp_List,Cmatrix_List]:=Inverse[Cmatrix] . IntSec[phiComp]//Simplify;
AMatrix[dKinComp_List,Cmatrix_List]:=Transpose[IntSec[dKinComp]] . Inverse[Cmatrix]//Simplify//Apart;


(*----------Differential equation----------*)
UMatrix[Amatrix_List,Cicoeff_List,nKin_]:=(
s=kin[[nKin]];
U=ConstantArray[0,Length[Cicoeff]{1,1}];
U[[1,All]]=Cicoeff[[All,1]];
	Do[U[[i,All]]=D[U[[i-1,All]],s]+U[[i-1,All]] . Amatrix//Simplify
,{i,2,Length[Cicoeff]}];
Return[U]
);

PicardFuchs[Umatrix_List,Amatrix_List,nKin_]:=(
s=kin[[nKin]];
Uinv=Inverse[Umatrix]//Simplify;
Bmatrix=D[Umatrix,s] . Uinv+Umatrix . Amatrix . Uinv//Simplify;
Print[Bmatrix//MatrixForm];
clist=Append[Bmatrix[[Length[Amatrix],All]],-1]//Simplify;
Return[clist]
);

DEQ[Amatrix_List,Cicoeff_List,nKin_]:=(
Umatrix=UMatrix[Amatrix,Cicoeff,nKin];
If[MatrixRank[Umatrix]==Length[Cicoeff],
Return[PicardFuchs[Umatrix,Amatrix,nKin]],
(
Do[nuReduced=Subsets[Range[nu],{MatrixRank[Umatrix]}][[i]];If[MatrixRank[Umatrix[[nuReduced,nuReduced]]]==MatrixRank[Umatrix],
(
AmatrixReduced =Amatrix[[nuReduced,nuReduced]];
CicoeffReduced=Cicoeff[[nuReduced]];
UmatrixReduced=UMatrix[AmatrixReduced,CicoeffReduced,nKin];
Print["independent bases: ",nuReduced];
Break[]
)
,Clear[UmatrixReduced]]
,{i,1,Binomial[nu,MatrixRank[Umatrix]]}];
Return[PicardFuchs[UmatrixReduced,AmatrixReduced,nKin]]
)
];
)


(*End[];
EndPackage[];*)
