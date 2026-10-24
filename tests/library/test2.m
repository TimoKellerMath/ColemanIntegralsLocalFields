load "isrational.m";
load "auxpolys.m";
load "cohobasis.m";
load "frobenius.m";
load "reduction.m";
load "coercion.m";
load "expansion.m";
load "integrals.m";



SetLogFile("tests/library/test2.log" : Overwrite);


// test 2 (rational field)
// A genus-3 curve (a smooth plane quartic) at p=5, whose six endpoints are all bad: P1=(1,1),
// P2=(0,0) and P3=(1,0) lie over roots of r, and P4, P5, P6 are the three points (1:1:0),
// (0:1:0), (1:0:0) at infinity. These are unramified over x=infinity (local parameter 1/x) and
// not on the affine model, so they are given by their coordinates in the integral basis
// b^infinity, and no single b_i^infinity separates them (b_1^infinity=y/x^2 vanishes at P4 and
// P6, b_2^infinity at P5 and P6). The minimal polynomials of these b_i^infinity over K(1/x)
// therefore have multiple roots at 1/x=0, and the local expansions are the branches that
// separate only at a higher order in t (cf. hensel_lift and local_coord).

L:=ext<Rationals()|Polynomial([0,1]):DoLinearExtension>;
Lx<x>:=PolynomialRing(L);
Lxy<y>:=PolynomialRing(Lx);
OL:=MaximalOrder(L);

P:=ideal<OL|5>;
N:=10;
Q:=y^3+(-x^2-x)*y^2+x^3*y-x^2+x;
data:=coleman_data(Q,L,P,N);
P1:=set_point(1,1,data);
P2:=set_point(0,0,data);
P3:=set_point(1,0,data);
P4:=set_bad_point(0,[1,0,-1],true,data);
P5:=set_bad_point(0,[1,1,0],true,data);
P6:=set_bad_point(0,[1,0,0],true,data);
I12,N12:=coleman_integrals_on_basis(P1,P2,data); I12; N12;
"holomorphic integrals P1->P2 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I12,data);
I13,N13:=coleman_integrals_on_basis(P1,P3,data); I13; N13;
"holomorphic integrals P1->P3 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I13,data);
I14,N14:=coleman_integrals_on_basis(P1,P4,data); I14; N14;
"holomorphic integrals P1->P4 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I14,data);
I15,N15:=coleman_integrals_on_basis(P1,P5,data); I15; N15;
"holomorphic integrals P1->P5 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I15,data);
I16,N16:=coleman_integrals_on_basis(P1,P6,data); I16; N16;
"holomorphic integrals P1->P6 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I16,data);

// Consistency checks. Note: the forms omega_4, omega_5, omega_6 of the basis have poles at P4,
// P5 and P6, so their integrals to these points are regularized: the constant term of their
// Laurent primitive in the local parameter at the point is taken to be 0 (see (3)).

print "";
print "consistency checks:";

// (1) The expansions of x (resp. 1/x) and of the b_i at the six bad points are computed
// independently, each from its own minimal polynomial; they belong to one point iff they satisfy
// the relations of the integral basis and the curve equation.
pts:=[* P1,P2,P3,P4,P5,P6 *];
for k:=1 to #pts do
  eP,index:=local_data(pts[k],data);
  ok,tprec:=local_expansions_consistent(pts[k],60,data);
  printf "P%o (e_P = %o, local parameter index %o): local expansions consistent: %o (to t-adic precision %o of 60)\n", k, eP, index, ok, tprec;
  assert ok and tprec ge 40;
end for;

// (2) Additivity across the singular points at infinity. The integrals from P1 use e=21, those
// between two points at infinity e=11, so the sides of P4, P5, P6 are computed from different
// near-boundary points in the two integrals.
I45,N45:=coleman_integrals_on_basis(P4,P5,data:verbose:=false);
I56,N56:=coleman_integrals_on_basis(P5,P6,data:verbose:=false);
for chk in [* <"I(P1,P4)+I(P4,P5) = I(P1,P5)",I14+I45-I15,Minimum([N14,N45,N15])>,
              <"I(P1,P5)+I(P5,P6) = I(P1,P6)",I15+I56-I16,Minimum([N15,N56,N16])> *] do
  ok:=&and[Valuation(c) ge chk[3]:c in Eltseq(chk[2])];
  printf "additivity %o to precision %o: %o\n", chk[1], chk[3], ok;
  assert ok;
end for;

// (3) Another local parameter at P4: b_1^infinity and b_2^infinity+1 are integral local
// parameters there as well, and the whole computation of I(P1,P4) (near-boundary point, tiny
// integrals) is redone in them. The holomorphic integrals do not change; the regularized ones
// change by tiny_t(P4->R)-tiny_t'(P4->R), for R in the residue disc of P4 (here 1/x(R)=5).
e:=21; // the e of I(P1,P4)
T:=tadicprec(data,e);
xt,bt:=local_coord(P4,T,data);
R:=set_bad_point(data`K!5,[Evaluate(bt[i],data`K!5):i in [1..3]],true,data);
tR,NtR:=tiny_integrals_on_basis(P4,R,data:prec:=T);
for j in [2,3] do
  data:=update_minpolys(data,true,j);
  P4j:=P4;
  P4j`xt,P4j`bt,P4j`index:=local_coord(P4,T,data:index:=j); // cached, so used throughout
  ok,tprec:=local_expansions_consistent(P4j,T,data:index:=j);
  assert ok;
  I4j,N4j:=coleman_integrals_on_basis(P1,P4j,data:e:=e,verbose:=false);
  tRj,NtRj:=tiny_integrals_on_basis(P4j,R,data:prec:=T);
  n:=Minimum([N14,N4j,NtR,NtRj]);
  ok:=holomorphic_integrals_weakly_zero(I4j,data) and &and[Valuation(c) ge n:c in Eltseq(I14-I4j+tR-tRj)];
  printf "local parameter b_%o^infinity-b_%o^infinity(P4): I(P1,P4) agrees up to the regularization, to precision %o: %o\n", j-1, j-1, n, ok;
  assert ok;
end for;

// (4) Agreement with N=15.
data15:=coleman_data(Q,L,P,15:verbose:=false);
toQ:=function(v,dt)
  minv:=Inverse(dt`m);
  return [Rationals()!minv(c):c in Eltseq(v)];
end function;
for chk in [* <"P4",[1,0,-1],I14,N14>, <"P5",[1,1,0],I15,N15>, <"P6",[1,0,0],I16,N16> *] do
  J,NJ:=coleman_integrals_on_basis(set_point(1,1,data15),set_bad_point(0,chk[2],true,data15),data15:verbose:=false);
  a:=toQ(chk[3],data); b:=toQ(J,data15);
  ok:=&and[Valuation(a[i]-b[i],5) ge chk[4]:i in [1..#a]];
  printf "N=15 (precision %o): I(P1,%o) agrees with N=10 to precision %o: %o\n", NJ, chk[1], chk[4], ok;
  assert ok;
end for;

printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
