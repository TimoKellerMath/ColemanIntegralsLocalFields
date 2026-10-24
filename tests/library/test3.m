load "isrational.m";
load "auxpolys.m";
load "cohobasis.m";
load "frobenius.m";
load "reduction.m";
load "coercion.m";
load "expansion.m";
load "integrals.m";

SetLogFile("tests/library/test3.log" : Overwrite);

//test 3
// A genus-4 curve at p=7, of degree 5 over the x-line and totally ramified over x=0 and
// x=infinity. The endpoints are the good point P1=(1,1) and the two ramification points: P2, the
// singular point (0,0) of the plane model, and P3 at infinity, with the local parameters b_3^0
// and b_4^infinity (e_P=5). At P2 the minimal polynomials of b_1^0=y and b_2^0=y^2 over K(b_3^0)
// have a 13-fold root at b_3^0=0 (the zeros of b_3^0=y^3/x all have y=0), and the branch through
// P2 separates from the others only at t^4 resp. t^8 (cf. hensel_lift and local_coord).

L:=ext<Rationals()|Polynomial([0,1]):DoLinearExtension>;
Lx<x>:=PolynomialRing(L);
Lxy<y>:=PolynomialRing(Lx);
OL:=MaximalOrder(L);
  
P:=ideal<OL|7>;
N:=10;
Q:=y^5+12*x^2*y^3-14*x^2*y^2+(13*x^4+6*x^2)*y-(11*x^6+6*x^4+x^2);
data:=coleman_data(Q,L,P,N);
data`W0;
//ord_0_mat(data`W)+1;
//ord_0_mat(Winf)+1;
P1:=set_point(1,1,data);
P2:=set_bad_point(0,[1,0,0,0,0],false,data);
P3:=set_bad_point(0,[1,0,0,0,0],true,data);
I12,N12:=coleman_integrals_on_basis(P1,P2,data); I12; N12;
"holomorphic integrals P1->P2 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I12,data);
I13,N13:=coleman_integrals_on_basis(P1,P3,data); I13; N13;
"holomorphic integrals P1->P3 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I13,data);

// Consistency checks. Note: the forms omega_5,...,omega_8 of the basis have poles at P3, so
// their integrals to P3 are regularized: the constant term of their Laurent primitive in the
// local parameter at P3 is taken to be 0.

print "";
print "consistency checks:";

// (1) The expansions of x (resp. 1/x) and of the b_i, each computed from its own minimal
// polynomial (from the plane model at the good point P1), belong to one point.
pts:=[* P1,P2,P3 *];
for k:=1 to #pts do
  eP,index:=local_data(pts[k],data);
  ok,tprec:=local_expansions_consistent(pts[k],100,data);
  printf "P%o (e_P = %o, local parameter index %o): local expansions consistent: %o (to t-adic precision %o of 100)\n", k, eP, index, ok, tprec;
  assert ok and tprec ge 50;
end for;

// (2) div(x)=5*P2-5*P3, so P2-P3 is torsion: the holomorphic integrals from P2 to P3 vanish.
// Additivity: I(P1,P2) and I(P1,P3) use e=71, I(P2,P3) is computed with e=101, so the sides
// of P2 and P3 come from different near-boundary points in the two integrals.
I23,N23:=coleman_integrals_on_basis(P2,P3,data:e:=101,verbose:=false);
ok:=holomorphic_integrals_weakly_zero(I23,data);
printf "holomorphic integrals P2->P3 weakly zero (5*(P2-P3) = div(x)): %o\n", ok;
assert ok;
n:=Minimum([N12,N23,N13]);
ok:=&and[Valuation(c) ge n:c in Eltseq(I12+I23-I13)];
printf "additivity I(P1,P2)+I(P2,P3) = I(P1,P3) to precision %o: %o\n", n, ok;
assert ok;

// (3) Agreement with N=15.
data15:=coleman_data(Q,L,P,15:verbose:=false);
toQ:=function(v,dt)
  minv:=Inverse(dt`m);
  return [Rationals()!minv(c):c in Eltseq(v)];
end function;
Q1:=set_point(1,1,data15);
for chk in [* <"P2",set_bad_point(0,[1,0,0,0,0],false,data15),I12,N12>,
              <"P3",set_bad_point(0,[1,0,0,0,0],true,data15),I13,N13> *] do
  J,NJ:=coleman_integrals_on_basis(Q1,chk[2],data15:verbose:=false);
  a:=toQ(chk[3],data); b:=toQ(J,data15);
  ok:=&and[Valuation(a[i]-b[i],7) ge chk[4]:i in [1..#a]];
  printf "N=15 (precision %o): I(P1,%o) agrees with N=10 to precision %o: %o\n", NJ, chk[1], chk[4], ok;
  assert ok;
end for;

printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
