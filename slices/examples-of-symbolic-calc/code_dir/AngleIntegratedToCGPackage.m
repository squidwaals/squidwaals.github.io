(* ::Package:: *)

BeginPackage["AngleIntegratedToCGPackage`"]


Begin["Global`"]


myintorhalfintQ[x_]:=Element[x,Integers]||(Mod[2x,1]==0)

Int/:Int[SPH[l1_,m1_]\[Conjugate],SPH[l2_,m2_]]:=KroneckerDelta[l1,l2]KroneckerDelta[m1,m2]
Int/:Int[SPH[l1_,m1_],SPH[l2_,m2_]]:=(-1)^m1 KroneckerDelta[l1,l2]KroneckerDelta[-m1,m2]
Int/:Int[SPH[l1_,m1_]\[Conjugate],SPH[l2_,m2_],SPH[l3_,m3_]]:=Sqrt[(2l3+1)(2l2+1)/(4Pi(2l1+1))]\!\(\*SubscriptBox[\(CG\), \({{l3, 0, l2, 0}, {l1, 0}}\)]\) \!\(\*SubscriptBox[\(CG\), \({{l3, m3, l2, m2}, {l1, m1}}\)]\)  
Int/:Int[SPH[l1_,m1_],SPH[l2_,m2_],SPH[l3_,m3_]]:=(-1)^(m1)Sqrt[(2l3+1)(2l2+1)/(4Pi(2l1+1))]\!\(\*SubscriptBox[\(CG\), \({{l3, 0, l2, 0}, {l1, 0}}\)]\) \!\(\*SubscriptBox[\(CG\), \({{l3, m3, l2, m2}, {l1, \(-m1\)}}\)]\)  
Int/:Int[SPH[l1_,m1_]\[Conjugate],Times[c__,SPH[l2_,m2_]],SPH[l3_,m3_]]:=Times[c,Sqrt[(2l3+1)(2l2+1)/(4Pi(2l1+1))]\!\(\*SubscriptBox[\(CG\), \({{l3, 0, l2, 0}, {l1, 0}}\)]\) \!\(\*SubscriptBox[\(CG\), \({{l3, m3, l2, m2}, {l1, m1}}\)]\)  ]
Int/:Int[SPH[l1_,m1_],Times[c__,SPH[l2_,m2_]],SPH[l3_,m3_]]:=Times[c,(-1)^(m1)Sqrt[(2l3+1)(2l2+1)/(4Pi(2l1+1))]\!\(\*SubscriptBox[\(CG\), \({{l3, 0, l2, 0}, {l1, 0}}\)]\) \!\(\*SubscriptBox[\(CG\), \({{l3, m3, l2, m2}, {l1, \(-m1\)}}\)]\)  ]
Int/:Int[SPH[l1_,m1_]\[Conjugate],Plus[c__,d_],SPH[l3_,m3_]]:=Int[SPH[l1,m1]\[Conjugate],c,SPH[l3,m3]]+Int[SPH[l1,m1]\[Conjugate],d,SPH[l3,m3]]
Int/:Int[SPH[l1_,m1_],Plus[c__,d_],SPH[l3_,m3_]]:=Int[SPH[l1,m1],c,SPH[l3,m3]]+Int[SPH[l1,m1],d,SPH[l3,m3]]
CG/:\!\(\*SubscriptBox[\(CG\), \({{l1_?myintorhalfintQ, m1_?myintorhalfintQ, l2_?myintorhalfintQ, m2_?myintorhalfintQ}, {l3_?myintorhalfintQ, m3_?myintorhalfintQ}}\)]\)  :=ClebschGordan[{l1,m1},{l2,m2},{l3,m3}]
CG/:\!\(\*SubscriptBox[\(CG\), \({{a_, b_, 0, 0}, {c_, d_}}\)]\):=KroneckerDelta[a,c]KroneckerDelta[b,d]
CG/:\!\(\*SubscriptBox[\(CG\), \({{0, 0, a_, b_}, {c_, d_}}\)]\):=KroneckerDelta[a,c]KroneckerDelta[b,d]


End[]


EndPackage[]
