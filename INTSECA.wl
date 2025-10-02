(* ::Package:: *)

(* ::Subsubsection:: *)
(*Basic info*)


BeginPackage["INTSECA`"];
Print["INTSECA 1.2.3"]
(*Print["Author: Yuhan Fu"];*)

(*tools*)
t::usage = "list to bracket";
tp::usage = "bracket to list";
sort::usage = "sort \[LeftAngleBracket]J\[RightAngleBracket]";
initialize::usage = "Initialize the intermediate variables to be used in INTSECA";

(*basis*)
verticesList::usage = "Find the set of all \[LeftAngleBracket]J\[RightAngleBracket]";
multiRelations::usage = "Gives the relations from common intersection of multiple hyperplanes";
Sol::usage = "Sol";
(*Sol0::usage = "Sol on given set of vertices";*)
BdyBasis::usage = "{Bdy,Basis}";
BdyBasis0::usage = "Boundary structure for any given set of vertices";
funcTree::usage = "Plot the directed graph for basis";

(*A-matrix*)
AMatrix::usage = "A-matrix for each kinematic variable";
KineFlow::usage = "Kinematic flow for basis";
EquationFlow::usage = "{Flow,phiStoNum}, Differential equation of kinematic flow";
Needed::usage = "{basisNeed,AmatrixNeed}";
ATotal::usage = "total derivative A-matrix (for single twist): entries are the Log functions";
Letter::usage = "Collect all letter from the A-matrix (Log)";
APRT::usage = "Fully Apart the entries of A-matrix";


(* ::Section:: *)
(*Set-up*)


(*Global`powers={} (*define at first*)*)
Begin["`Private`"];


(* ::Subsection:: *)
(*Input*)


(*Input*)
dim = Global`dim;
nkin = Global`nkin;
kin = Global`kin;
nBplane = Global`nBplane;
nTplane = Global`nTplane;
powers = Global`powers;
B = Global`B;
T = Global`T;
psi = Global`psi;



(* ::Subsection:: *)
(*Intermediate variables*)


(*(*Initialize*)
initialize[] := (
nplane = nBplane+nTplane;
X = Append[Table[z[i] = Symbol["z" <> ToString[i]], {i, 1, dim}],1];
Lplanes = Join[Table[Global`B[i] . X, {i, nBplane}], Table[Global`T[i] . X, {i, nTplane}]];
jacT =JacT[Lplanes];
permT =PermT[dim,nkin];
Jac =Table[D[Lplanes[[i]],z[j]],{j,1,dim},{i,1,Length[Lplanes]}];

replaceTplane=Table[i->(i+nBplane),{i,1,nTplane}];
power=Join[ConstantArray[0,{nBplane}],powers];
(*power=powers; *)

(*dkin=Map["d"<>ToString[#]&,kin];*)
dkin = Map[Symbol["d" <> ToString[#]] &, kin];
);*)


initialize[] := (
  nplane = nBplane + nTplane;
  X = Append[Table[z[i] = Symbol["z" <> ToString[i]], {i, 1, dim}], 1];
  
  Lplanes = Join[
    Table[Global`B[i] . X, {i, 1, nBplane}],
    Table[Global`T[i] . X, {i, 1, nTplane}]
  ];
  
  jacT = JacT[Lplanes];
  permT = PermT[dim, nkin];
  
  Jac = Table[D[Lplanes[[i]], z[j]], {j, 1, dim}, {i, 1, Length[Lplanes]}];
  
  replaceTplane=Table[i->(i+nBplane),{i,1,nTplane}];
  
  (* handle nBplane=0 by making the constant array length 0 *)
  power = Join[
    If[nBplane > 0, ConstantArray[0, {nBplane}], {}],
    powers
  ];
  
  dkin = Map[Symbol["d" <> ToString[#]] &, kin];
);



(* ::Section:: *)
(*Functions*)


(* ::Subsubsection:: *)
(*Tools*)


t[{a__}] := \[LeftAngleBracket]a\[RightAngleBracket]; (* Transform list to \[LeftAngleBracket]...\[RightAngleBracket] symbol *)
tp[f_]:=f/.\[LeftAngleBracket]a__\[RightAngleBracket]:>{a} (*transform \[LeftAngleBracket]...\[RightAngleBracket] symbol to list*)
sort={\[LeftAngleBracket]a__\[RightAngleBracket]:>Signature[{a}]*t[Sort[{a}]]};


(* ::Subsubsection:: *)
(*Wedge product*)


rules={Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]a__\[RightAngleBracket]]:>0,Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>If[OrderedQ[{{a},{b}}],Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],-Wedge[\[LeftAngleBracket]b\[RightAngleBracket],\[LeftAngleBracket]a\[RightAngleBracket]]],
Wedge[c_*\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>c*Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],d_*\[LeftAngleBracket]b__\[RightAngleBracket]]:>d*Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],Wedge[(c1_*term1_+rest_),(term2_)]:>Wedge[c1*term1,term2]+Wedge[rest,term2],
Wedge[c_,d_*\[LeftAngleBracket]b__\[RightAngleBracket]]:>c*d*\[LeftAngleBracket]b\[RightAngleBracket],Wedge[c_*\[LeftAngleBracket]a__\[RightAngleBracket],d_]:>c*d*\[LeftAngleBracket]a\[RightAngleBracket]};

wedgeToBracketRule={
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket],rest_]:>Wedge[\[LeftAngleBracket]a,b\[RightAngleBracket],rest],
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>Wedge[\[LeftAngleBracket]a,b\[RightAngleBracket]],
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket]]:>\[LeftAngleBracket]a\[RightAngleBracket]
};

parallel:=\[LeftAngleBracket]a__\[RightAngleBracket]/;Det[Jac[[All,{a}]]]===0->0;
parallelRemove[v_List]:=DeleteCases[v//.parallel,0];


(* ::Subsubsection:: *)
(*Find basis*)


(* Function to collect all nonzero <J> *)
phiJList[n_] := 
  t /@ Sort[Sort/@
    Flatten[With[{limits = 
        Table[{Subscript[i, k], If[k == 1, 1, Subscript[i, k - 1] + 1], nplane}, {k, 1, n}]}, 
      Table[Array[Subscript[i, #] &, n], Evaluate[Sequence @@ limits]]], n - 1]];

verticesList:=phiJList[dim]//parallelRemove;

Omega:=powers . (t/@Array[{#+nBplane}&,nTplane]);
(*Omega:=powers . (t/@Range[nplane]);*)
OmegaV[xi_List]:=Table[Wedge[Omega,xi[[i]]]//.rules//.wedgeToBracketRule//.sort,{i,1,Length[xi]}]//parallelRemove;

coordinate[Vertex_]:=
First@(Solve[Map[Lplanes[[#]]==0&,tp[Vertex]],X[[1;;dim]]]//Simplify);

(*Relations*)
multiIntsec[vertexToIntsec_List]:=(
Hypers=Select[vertexToIntsec,Length[#]>1&];
Return[Table[Total[Hypers[[i]]]==0,{i,1,Length[Hypers]}]]
)

multiRelations[vertices_List]:=(
vertexToIntsec=GroupBy[vertices,coordinate];
multirelations=multiIntsec[vertexToIntsec//Values];
Return[multirelations]
)

Relations[vertices_List, mode_:1] :=(
omegaV=OmegaV[phiJList[dim-1]];
multirelations=If[mode==1,multiRelations[vertices],{}];
Return[Join[(#==0&/@omegaV),multirelations]]
)

Sol[mode_:1]:=(
vertices=verticesList;
relations=Relations[vertices,mode]// Simplify;
sol=Solve[relations,vertices]//First//Cancel//Simplify//Quiet;
Return[sol]
)

(*Sol0[vertices_List]:=(
relations=Relations[vertices];
sol=Solve[relations,vertices]//First//Cancel//Simplify//Quiet;
Return[sol]
)*)

(*Find basis*)
boundary[vertex_List]:=Complement[vertex,Range[nBplane+1,nplane]]
BdyphiJList[n_]:=(
t/@Sort[Sort/@(
Flatten[With[{limits=Table[{Subscript[i,k],If[k==1,1,Subscript[i,k-1]+1],nTplane},{k,1,n}]},Table[Array[Subscript[i,#]&,n],Evaluate[Sequence@@limits]]],n-1]
)])/.replaceTplane;

BdyBasis[mode_:1]:=(
vertices=verticesList;
sol=Sol[mode];
Basis=Complement[vertices,sol[[All,1]]];
bdyGrp=GroupBy[tp/@Basis,boundary];
Bdy=bdyGrp//Keys;
BdyVertices=Map[t,(bdyGrp//Values),{2}];
BdyVertices=BdyVertices[[Ordering[Bdy]]];
Bdy=Bdy//Sort;
Return[{Bdy,BdyVertices}]
)

BdyBasis0[vertices_List]:=(
bdyGrp=GroupBy[tp/@vertices,boundary];
Bdy=bdyGrp//Keys;
BdyVertices=Map[t,(bdyGrp//Values),{2}];
BdyVertices=BdyVertices[[Ordering[Bdy]]];
Bdy=Bdy//Sort;
Return[{Bdy,BdyVertices}]
)



(*Plot the boundary structure*)
funcTree[list_]:=Block[{graph,funcs,Nsite},
Nsite=Length@list[[-1]];
graph=ResourceFunction["HasseDiagram"][SubsetQ[#2,#1]&,list,VertexShapeFunction->"Name",GraphLayout->"LayeredDigraphEmbedding"];
funcs=Length@Cases[list,#]&/@Table[_,{i,0,Nsite},{j,i}];
Print[graph];
Grid[{Prepend[Table[i,{i,0,Nsite}],"# codimension"],
Prepend[funcs,"# boundaries"]},Frame->All]
]



(* ::Subsubsection:: *)
(*A-matrix via intersection theory*)


(*----------derivative w.r.t kinematic variables----------*)
JacT[Lplanes_List]:=Table[Join[Table[D[Lplanes[[i]],kin[[j]]],{j,1,nkin}],Table[D[Lplanes[[i]],z[j]],{j,1,dim}]],{i,1,Length[Lplanes]}];
PermT[dim_,nkin_]:=Table[Permutations[Join[{n},Range[nkin+1,nkin+dim]]],{n,1,nkin}];

(*it would be better if we generalize DKin functions for fibration use.*)
DKinVertex[Vertex_List(*,nkin_:nkin,dim_:dim*)]:=
Table[
Sum[
(
Signature[permT[[nkin,i]]]
(power[[Ad]]/( Subscript[l, Ad] Product[Subscript[l, Vertex[[j]]],{j,1,dim}])) 
jacT[[Ad,permT[[n,i,1]]]] 
Product[jacT[[Vertex[[k]],permT[[n,i,1+k]]]],{k,1,dim}]
)
,{i,1,Length[permT[[1]]]},{Ad,1,nplane}]
,{n,1,nkin}];

DKinCollect[Basis_List]:=(
nu=Basis//Length;
vertex={Basis//tp}//Transpose;
orient=ConstantArray[{1},nu];
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
nume0=Sum[Subscript[c, VertexP[[i]]] Lplanes[[VertexP[[i]]]],{i,1,dim+1}]-nume//Simplify;sol0=Solve[Append[Table[Coefficient[nume0,z[i]]==0,{i,1,dim+1}],(nume0/.Table[z[i]->0,{i,1,dim}])==0],Table[Subscript[c,VertexP[[i]]],{i,1,dim+1}]]//Quiet;
Return[First@sol0]);

DKinComp[nKin_,DKinCollect_List,sol_List]:=(
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
DkinComp=DkinComp/.sol//Simplify//Apart;
Return[DkinComp]
)

(*a thorough "Apart" for entries of A-matrix*)
APRT=expr_:>(Module[{terms},terms=If[Head[expr]===Plus,List@@expr,{expr}];
terms=Apart/@terms;
Total[terms]]);

AMatrix[mode_:1]:=(
sol=Sol[mode];
bdyBasis=BdyBasis[mode];
basis=bdyBasis[[2]]//Flatten;
nu=Length[basis];
dKinCollect=DKinCollect[basis];
Amatrix=Table[
dKinComp=DKinComp[nKin=i,dKinCollect,sol];
Table[Coefficient[dKinComp[[i]],basis[[j]]]//Apart/.APRT,{i,1,nu},{j,1,nu}](*//Apart*)
,{i,1,nkin}];
Return[Amatrix]
)

(*Kinematic flow from A-matrix*)
KineFlow[psi_,Basis_List,Amatrix_List]:=(
nu=Length[Amatrix];
ciCoeff=Table[Coefficient[psi,Basis[[i]]],{i,1,nu}];
nonzeroCi=Complement[Range[nu],Position[ciCoeff,x_/;x===0][[All,1]]];
level=nonzeroCi; (*level0: the starting level of the flow*)
EachLevel={};
nonzeroA[aMatrixi_List]:=Complement[Range[nu],Position[aMatrixi,x_/;x===0][[All,1]]];
While[level!={},
EachLevel=AppendTo[EachLevel,level];
nonzeroAij=Table[Amatrix[[level[[i]]]]//nonzeroA,{i,1,Length[level]}];
level=Complement[nonzeroAij//Flatten,EachLevel//Flatten];
];
Return[EachLevel]
)

Needed[Amatrix_List,psiSol_,basis_List]:=(
kineFlow=KineFlow[psiSol,basis,Amatrix];
basisNeeded=kineFlow//Flatten;
basisNeed=basis[[basisNeeded]];
AmatrixNeed=Amatrix[[basisNeeded,basisNeeded]];
(*Print[basisNeed];*)
Return[{basisNeed,AmatrixNeed}]
)


(*Total derivative A-matrix*)
toPositive=x_:>-x/;(First[x]//Length)==2;
toLogForm[expr_,i_]:=Module[
{terms},terms=If[Head[expr]===Plus,List@@expr,{expr}];(*Check if the input is a sum or a single term*)
terms//Simplify;
Table[Numerator[term]*Log[Denominator[term]/.toPositive]/Coefficient[Denominator[term],kin[[i]]]/. {ComplexInfinity->0,Indeterminate->0}//Quiet,{term,terms}](*Process each term individually and return the results as a list*)
]

Letter[amatrix_List]:=Module[{letterLog,letter},
letterLog=Cases[amatrix,_Log,Infinity]//Union;
letter=letterLog/. Log[x_]:>x;
(*Map[If[(First[#]//Length)==0,#,-#]&,letter]//Union*)
letter//Union]

splitPlus=If[MatchQ[#,_Plus],List@@#,{#}]&;
transformList=Flatten[splitPlus/@(FactorTerms/@#)]&;
ATotal[A_List,twists_List]:=Module[{result},
result=Map[transformList[#]&,Map[MapIndexed[toLogForm[#1,First@#2]&,#]&,MapThread[List,Coefficient[A,twists[[1]]],2],{2}],{3}];
Sum[
twist*Map[Total[Union[Flatten[#]]]&,result,{2}],{twist,twists}
]]//Quiet;


EquationFlow[Amatrix_List,kineFlow_List]:=(
phiS=Table["\[CurlyPhi]"<>ToString[j],{j,1,Length[Amatrix]}];
phiStoNum=Thread[phiS->Range[Length[Amatrix]]];
Flow=Table[Table[Amatrix[[kineFlow[[level,i]]]] . phiS,{i,1,Length[kineFlow[[level]]]}],{level,1,Length[kineFlow]}];
Return[{Flow/Global`e//Apart,phiStoNum}]
)


End[];

EndPackage[];

