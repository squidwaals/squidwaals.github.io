(* ::Package:: *)

BeginPackage["QuantumSimplificationPackage`"]


Begin["Global`"]


myPlusQ[x_]:=Head[x]===Ket ||Head[x]===Bra||Head[x]===CircleTimes|| Head[x]===KroneckerDelta||MemberQ[Map[Head[#]&,Level[x,1]],Ket]||MemberQ[Map[Head[#]&,Level[x,1]],Bra]||MemberQ[Map[Head[#]&,Level[x,1]],CircleTimes]||MemberQ[Map[Head[#]&,Level[x,1]],KroneckerDelta]
DeltaandNumQ[x_] := NumericQ[x]||Head[x]===KroneckerDelta||(AllTrue[Map[Head[#]&,Level[x,1]],#===KroneckerDelta&]&&Not[Level[x,1]==={}])

Unprotect[Plus]
Plus/:HoldPattern[Plus[x__?myPlusQ]]HoldPattern[Plus[y__]]:=Total@Map[# Plus[y]&,{x}]
Plus/:HoldPattern[CircleTimes[Plus[x__?myPlusQ],Plus[y__]]]:=Total@Map[CircleTimes[#, Plus[y]]&,{x}]
Plus/:HoldPattern[CircleTimes[Plus[x__?myPlusQ],y__]]:=Total@Map[CircleTimes[#, y]&,{x}]
Plus/:HoldPattern[Plus[x__]]HoldPattern[Plus[y__?myPlusQ]]:=Total@Map[Plus[x]#&,{y}]
Plus/:HoldPattern[CircleTimes[Plus[x__],Plus[y__?myPlusQ]]]:=Total@Map[CircleTimes[Plus[x],#]&,{y}]
Plus/:HoldPattern[CircleTimes[x__,Plus[y__?myPlusQ]]]:=Total@Map[CircleTimes[x,#]&,{y}]
Plus/:HoldPattern[Times[x__,Plus[y__?myPlusQ]]]:=Total@Map[Times[x,#]&,{y}]
Plus/:HoldPattern[ConjugateTranspose[Plus[x__?myPlusQ]]]:=Total@Map[ConjugateTranspose[#]&,{x}]
Protect[Plus]
Unprotect[Times]
Times/:HoldPattern[ConjugateTranspose[Times[c__,Ket[x__]]]]:=Times[Conjugate[c],Bra[x]]
Times/:HoldPattern[ConjugateTranspose[Times[c__,Bra[x__]]]]:=Times[Conjugate[c],Ket[x]]
Times/:HoldPattern[ConjugateTranspose[Times[c__,CircleTimes[Ket[x__],Bra[y__]]]]]:=Times[Conjugate[c],CircleTimes[Ket[y],Bra[x]]]
Protect[Times]
Unprotect[Conjugate]
Conjugate/:Conjugate[x_,y__]:=Times[Conjugate[x],Times@@Map[Conjugate[#]&,{y}]]
Protect[Conjugate]


CircleTimes[x_?DeltaandNumQ,y_]:=Times[x,y]
CircleTimes[x_,y_?DeltaandNumQ]:=Times[y,x]
CircleTimes/:CircleTimes[x_,y_]HoldPattern[Plus[z__?myPlusQ]]:=Total@Map[CircleTimes[x,y]#&,{z}]
CircleTimes/:HoldPattern[Plus[z__?myPlusQ]]CircleTimes[x_,y_]:=Total@Map[# CircleTimes[x,y]&,{z}]
CircleTimes/:HoldPattern[CircleTimes[Times[c__,x__?myPlusQ],y__?myPlusQ]]:=Times[c,CircleTimes[x,y]]
CircleTimes/:HoldPattern[CircleTimes[x__?myPlusQ,Times[c__,y__?myPlusQ]]]:=Times[c,CircleTimes[x,y]]
CircleTimes/:HoldPattern[CircleTimes[Times[c__,x__?myPlusQ],Times[d__,y__?myPlusQ]]]:=Times[c,d,CircleTimes[x,y]]
CircleTimes/:CircleTimes[CircleTimes[Ket[x1__],Bra[y1__]],CircleTimes[Ket[x2__],Bra[y2__]]]:=CircleTimes[Ket[x1,x2],Bra[y1,y2]]
CircleTimes/:CircleTimes[CircleTimes[Ket[x1__],Bra[y1__]],Times[c__,CircleTimes[Ket[x2__],Bra[y2__]]]]:=Times[c,CircleTimes[Ket[x1,x2],Bra[y1,y2]]]
CircleTimes/:CircleTimes[Times[c__,CircleTimes[Ket[x1__],Bra[y1__]]],CircleTimes[Ket[x2__],Bra[y2__]]]:=Times[c,CircleTimes[Ket[x1,x2],Bra[y1,y2]]]
CircleTimes/:CircleTimes[Times[c__,CircleTimes[Ket[x1__],Bra[y1__]]],Times[d__,CircleTimes[Ket[x2__],Bra[y2__]]]]:=Times[c,d,CircleTimes[Ket[x1,x2],Bra[y1,y2]]]
CircleTimes/:CircleTimes[Ket[x__],Ket[y__]]:=Ket[x,y]
CircleTimes/:CircleTimes[Bra[x__],Bra[y__]]:=Bra[x,y]
CircleTimes/:HoldPattern[ConjugateTranspose[CircleTimes[Ket[x__],Bra[y__]]]]:=CircleTimes[Ket[y],Bra[x]]


Ket/:Bra[x__]  Ket[y__]:=Times@@MapThread[KroneckerDelta,{{x},{y}}]
Ket/:HoldPattern[CircleTimes[x_,z_]Ket[y__]]:=CircleTimes[x,z Ket[y]]
Bra/:Bra[x__]HoldPattern[CircleTimes[y_,z_]]:=CircleTimes[Bra[x]y, z]
Ket/:HoldPattern[Plus[x__]]Ket[y__]:=Total@Map[# Ket[y]&,{x}]
Bra/:Bra[x__]HoldPattern[Plus[y__]]:=Total@Map[Bra[x]#&,{y}]
Ket/:HoldPattern[ConjugateTranspose[Ket[x__]]]:=Bra[x]
Bra/:HoldPattern[ConjugateTranspose[Bra[x__]]]:=Ket[x]


End[]


EndPackage[]


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)
