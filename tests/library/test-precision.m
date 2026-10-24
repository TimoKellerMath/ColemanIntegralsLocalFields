SetColumns(0);
load "isrational.m";
load "auxpolys.m";
load "cohobasis.m";
load "frobenius.m";
load "reduction.m";
load "coercion.m";
load "expansion.m";
load "integrals.m";
load "tests/magma/results.m";

SetLogFile("tests/library/test-precision.log" : Overwrite);
RF := "tests/library/test-precision.results"; // the numbers below, compared within their precision
results_start(RF);

// Library test of the precision bounds of the article: the working precision N_max
// (the proposition on the precision of the reduction process and the remark after it, max_prec) and the
// certified precision of the integrals (the proposition on the precision of f_0, f_inf, f_end
// at a point, evalf0_list).
//
// 1. y^2 = x^5-2x^2+x+11 over K = Q_5 with N = 11: e_K = 1,
//    e_0 = e_inf = 2, ord_0(W) = ord_inf(W^(-1)) = -3, so h_1 = 0, h_2 = 1, and c_end = 0.
//    The article's rule gives N_max = 14. (Testing only the level m = N_max, with
//    h_0(N_max-1) instead of h_0(N_max) and without c_end, would give 13; then the omitted
//    term j = 63 may have valuation 13 and lose floor(log_5(126)) = 3 digits in the finite
//    reduction, so only precision 10 < N would be guaranteed.)
// 2. The integrals between (0,+-sqrt(11)), (1,sqrt(11)) and the point at infinity at N = 11
//    agree with those at N = 20 to the precision reported at N = 11, and satisfy
//    int_P^{iota(P)} = 2*int_P^infinity (iota the hyperelliptic involution, which fixes the
//    point at infinity and acts by -1 on the basis forms x^i dx/y). The points are defined
//    over L = Q(sqrt(11)), in which 5 splits, so K = L_P = Q_5. At the near-boundary point S
//    in the disc at infinity, f_inf(S) is correct to N+min{q(ord_0(W)+1),ord_inf(W^(-1))+1}
//    *v_K(1/x(S)) + ... (part (2) of the proposition on f_0, f_inf, f_end), which costs the last two
//    entries of the integral to infinity one digit.
// 3. T_0(P) (f0_tail_prec) for p = q_tau = 3,
//    e_K = e_0 = 1, N_max = 13 (j_0 = 36), v_K(r(P)) = 1/7: T_0(P) = 10-38/7, below
//    N-(j_0-1)v_K(r(P)) = 10-35/7.
// 4. Finitely bad endpoints, where T_0(P) and the pole order j_0-1 enter the precision of
//    f_0(P) at the near-boundary points: y^2 = x^5-2x^2+x = x(x-1)(x^3+x^2+x-1) over K = Q_5
//    (the curve of 1. with constant term 0; same N_max), from the good point R = (2,sqrt(26))
//    to the Weierstrass points (0,0) and (1,0), at N = 11 against N = 20 (L = Q(sqrt(26)), in
//    which 5 splits). With the default e = 2*q*e_P+1 = 21, v_K(r(S)) = 2/21 at the
//    near-boundary points S, and T_0(S) is the smaller entry. The integrals also satisfy
//    int_R^{iota(R)} = 2*int_R^W for both Weierstrass points W.
// 5. coleman_integral for the forms x^k dx/y (coefficient vector [0, x^k] w.r.t. b^0 dx/z,
//    z = f), of the second kind (their poles lie at the single point at infinity), from R to
//    iota(R) on the curve of 4.: the infinite reduction starts at the level
//    mu = -ord_inf(w) - deg(r) + 1 and loses e_K*floor(log_5(mu*e_inf)) digits (the
//    proposition on the infinite reduction), so the certified precision decreases with k; at
//    N = 11 the integrals agree with those at N = 20 to that precision.

// the entries of the integral vector I (reported precision NI) agree with the reference Iref
// over Kref to absolute precision NI
agree:=function(I,NI,Iref,Kref)
  vals:=[Valuation(Kref!I[i]-Iref[i]):i in [1..#Eltseq(I)]];
  return &and[v ge NI:v in vals], vals;
end function;

Nlow:=11;
Nref:=20;

print "==== 1. N_max for y^2 = x^5-2x^2+x+11 over Q_5 ====";

Qx<X>:=PolynomialRing(Rationals());
L<s>:=NumberField(X^2-11);
Lx<x>:=PolynomialRing(L);
Lxy<y>:=PolynomialRing(Lx);
OL:=MaximalOrder(L);
P:=Decomposition(OL,5)[1][1];
assert InertiaDegree(P) eq 1 and RamificationIndex(P) eq 1; // K = L_P = Q_5

Q:=y^2-(x^5-2*x^2+x+11);

data:=coleman_data(Q,L,P,Nlow:verbose:=false);
dataref:=coleman_data(Q,L,P,Nref:verbose:=false);
printf "N = %o: c_end = %o, Nmax = %o (the article's rule: 14)\n", Nlow, data`cend, data`Nmax;
printf "N = %o: c_end = %o, Nmax = %o\n", Nref, dataref`cend, dataref`Nmax;
assert data`cend eq 0 and data`Nmax eq 14;
record_result(RF, "1. N_max and c_end at N = 11", [data`Nmax, data`cend]);
record_result(RF, "1. N_max and c_end at N = 20", [dataref`Nmax, dataref`cend]);

print "";
print "==== 2. integrals at N = 11 against N = 20 ====";

pts:=[* <"(0,sqrt(11))",0,s>, <"(1,sqrt(11))",1,s>, <"(0,-sqrt(11))",0,-s>, <"infinity"> *];
mkpt:=function(t,D)
  if #t eq 1 then
    return set_bad_point(0,[1,0],true,D); // the point at infinity, b^inf = [1,0]
  end if;
  return set_point(t[2],t[3],D);
end function;

res:=[];
for j:=2 to 4 do
  I,NI:=coleman_integrals_on_basis(mkpt(pts[1],data),mkpt(pts[j],data),data:verbose:=false);
  Iref,NIref:=coleman_integrals_on_basis(mkpt(pts[1],dataref),mkpt(pts[j],dataref),dataref:verbose:=false);
  ok,vals:=agree(I,NI,Iref,dataref`K);
  printf "%o -> %o:\n  N = %o: %o, precision %o\n  N = %o: precision %o\n", pts[1][1], pts[j][1], Nlow, I, NI, Nref, NIref;
  printf "  valuations of the differences: %o; agree to precision %o: %o\n", vals, NI, ok;
  assert NIref ge NI and ok;
  record_result(RF, Sprintf("2. int_%o^%o at N = %o", pts[1][1], pts[j][1], Nlow), I : precision := NI);
  record_result(RF, Sprintf("2. int_%o^%o at N = %o", pts[1][1], pts[j][1], Nref), Iref : precision := NIref);
  Append(~res,<I,NI>);
end for;

// int_{P1}^{iota(P1)} = 2*int_{P1}^{infinity}, for all four basis forms
I13,N13:=Explode(res[2]);
I1inf,N1inf:=Explode(res[3]);
vinv:=[Valuation(I13[i]-2*I1inf[i]):i in [1..#Eltseq(I13)]];
printf "int_P1^iota(P1) - 2*int_P1^infinity: valuations %o (precision %o)\n", vinv, Minimum(N13,N1inf);
assert &and[v ge Minimum(N13,N1inf):v in vinv];

print "";
print "==== 3. T_0(P) for p = q_tau = 3, e_K = e_0 = 1, N = 10, N_max = 13, v_K(r(P)) = 1/7 ====";

L3:=ext<Rationals()|Polynomial([0,1]):DoLinearExtension>;
fmt:=recformat<p,eK,e0,P,qtau,eKred,Nmaxred,Nmax>;
toy:=rec<fmt|p:=3,eK:=1,e0:=1,P:=ideal<MaximalOrder(L3)|3>,qtau:=3,eKred:=1,Nmaxred:=13,Nmax:=13>;
j0:=f0_pole_bound(toy);
T0:=f0_tail_prec(toy,1/7);
printf "j_0 = %o, T_0(P) = %o = 10-38/7, N-(j_0-1)v_K(r(P)) = %o\n", j0, T0, 10-(j0-1)/7;
assert j0 eq 36 and T0 eq 10-38/7;
record_result(RF, "3. j_0 and T_0(P)", [* j0, T0 *]);

print "";
print "==== 4. finitely bad endpoints: y^2 = x^5-2x^2+x over Q_5 ====";

L1<s1>:=NumberField(X^2-26);
L1x<x>:=PolynomialRing(L1);
L1xy<y>:=PolynomialRing(L1x);
P1:=Decomposition(MaximalOrder(L1),5)[1][1];
assert InertiaDegree(P1) eq 1 and RamificationIndex(P1) eq 1; // K = L_P = Q_5
Q1:=y^2-(x^5-2*x^2+x);

data:=coleman_data(Q1,L1,P1,Nlow:verbose:=false);
dataref:=coleman_data(Q1,L1,P1,Nref:verbose:=false);
printf "N = %o: c_end = %o, Nmax = %o; N = %o: c_end = %o, Nmax = %o\n", Nlow, data`cend, data`Nmax, Nref, dataref`cend, dataref`Nmax;
vr:=2/21; // v_K(r(S)) = e_P/e at the near-boundary points, e_P = 2, e = 21
j0:=f0_pole_bound(data);
printf "at v_K(r(S)) = %o: j_0 = %o, T_0(S) = %o, N-(j_0-1)v_K(r(S)) = %o\n", vr, j0, f0_tail_prec(data,vr), Nlow-(j0-1)*vr;
assert f0_tail_prec(data,vr) lt Nlow-(j0-1)*vr; // here T_0(S) is the smaller entry

wpts:=[* <"(2,sqrt(26))",2,s1,false>, <"(0,0)",0,0,true>, <"(1,0)",1,0,true>, <"(2,-sqrt(26))",2,-s1,false> *];
mkwpt:=func<t,D | t[4] select set_bad_point(t[2],[1,0],false,D) else set_point(t[2],t[3],D)>;
res:=[];
for j:=2 to 4 do
  I,NI:=coleman_integrals_on_basis(mkwpt(wpts[1],data),mkwpt(wpts[j],data),data:verbose:=false);
  Iref,NIref:=coleman_integrals_on_basis(mkwpt(wpts[1],dataref),mkwpt(wpts[j],dataref),dataref:verbose:=false);
  ok,vals:=agree(I,NI,Iref,dataref`K);
  printf "%o -> %o:\n  N = %o: %o, precision %o\n  N = %o: precision %o\n", wpts[1][1], wpts[j][1], Nlow, I, NI, Nref, NIref;
  printf "  valuations of the differences: %o; agree to precision %o: %o\n", vals, NI, ok;
  assert NI gt 0 and NIref ge NI and ok;
  record_result(RF, Sprintf("4. int_%o^%o at N = %o", wpts[1][1], wpts[j][1], Nlow), I : precision := NI);
  record_result(RF, Sprintf("4. int_%o^%o at N = %o", wpts[1][1], wpts[j][1], Nref), Iref : precision := NIref);
  Append(~res,<I,NI>);
end for;

// int_R^{iota(R)} = 2*int_R^(0,0) = 2*int_R^(1,0)
Iiota,Niota:=Explode(res[3]);
for j:=1 to 2 do
  I,NI:=Explode(res[j]);
  vinv:=[Valuation(Iiota[i]-2*I[i]):i in [1..#Eltseq(I)]];
  printf "int_R^iota(R) - 2*int_R^%o: valuations %o (precision %o)\n", wpts[j+1][1], vinv, Minimum(NI,Niota);
  assert &and[v ge Minimum(NI,Niota):v in vinv];
end for;

print "\n==== 5. coleman_integral of x^k dx/y: the loss of the infinite reduction ====";
R:=mkwpt(wpts[1],data); iR:=mkwpt(wpts[4],data);
Rref:=mkwpt(wpts[1],dataref); iRref:=mkwpt(wpts[4],dataref);
IRR,NRR:=coleman_integrals_on_basis(R,iR,data:verbose:=false);
IRRref,NRRref:=coleman_integrals_on_basis(Rref,iRref,dataref:verbose:=false);
precs5:=[];
for k in [0,10,40] do
  J,NJ:=coleman_integral(R,iR,[Lx|0,x^k],data:IP1P2:=IRR,NIP1P2:=NRR);
  Jref,NJref:=coleman_integral(Rref,iRref,[Lx|0,x^k],dataref:IP1P2:=IRRref,NIP1P2:=NRRref);
  v:=Valuation(dataref`K!J-Jref);
  printf "k = %o: precision %o at N = %o, %o at N = %o; valuation of the difference %o\n", k, NJ, Nlow, NJref, Nref, v;
  assert NJ gt 0 and v ge NJ;
  Append(~precs5,NJ);
  record_result(RF, Sprintf("5. int x^%o dx/y at N = %o", k, Nlow), J : precision := NJ);
  record_result(RF, Sprintf("5. int x^%o dx/y at N = %o", k, Nref), Jref : precision := NJref);
end for;
assert precs5[1] gt precs5[3]; // the loss of the infinite reduction grows with the pole order

printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
