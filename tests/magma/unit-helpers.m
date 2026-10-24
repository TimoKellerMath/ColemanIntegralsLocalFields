// tests/magma/unit-helpers.m   [unit test: helper functions checked directly]
//
//     magma -b tests/magma/unit-helpers.m        (from the repository root)
//
// Helpers of frobenius.m, coercion.m, expansion.m and integrals.m that the other tests only
// reach indirectly, each against an independent computation:
//   * frobenius.m: the rings O_L/P^N[x]((z))[y] (getrings); the radix-r normal form, the
//     remainder modulo Q, powers modulo Q and the substitution x -> x^q, through the value of
//     an element after z = r(x) (radix_reduce, reduce_mod_Q, pow_mod_Q, substitute_xq); the
//     coefficient twists (twist_pol, twist_polxy, twist_mat) by complex conjugation of Q(i);
//   * coercion.m: series over O_K/pi^N and over K (series_K_to_Oq, series_Oq_to_K,
//     series_inverse), Taylor shifts and evaluations (taylor_shift_K, eval_frac_shift,
//     polL_eval_Oq, fracL_eval_Oq), coefficient maps between L and K (coer_plseries,
//     approx_inL, approx_plseriesinL, approx_polypseriesinL);
//   * expansion.m: divide_by_tpower, the Newton steps of hensel_lift (hensel_newton_Oq,
//     hensel_newton_K) for sqrt(1+t), mod_P_prec, and the expansion modulo P of a function at a
//     place (mod_P_expansion);
//   * integrals.m: precisions (known_digits, change_abs_precision*, round_to_K, auxiliary_e,
//     final_reduction_loss, tiny_integral_prec against its formula), powtab, point_to_K,
//     matrix_over_Q, map_coefficients_K, twisted_maps, cached_minpoly, find_bad_point_in_disc,
//     evalfend;
//   * solver.m: the maps of polynomials and matrices from L to K (Lx_to_Kx, L_or_Lx_to_Kx,
//     evaluate_matrix_K), reduced_basis, search_small_points, integrals_from_first.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
SetColumns(0);
SetLogFile("tests/magma/unit-helpers.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

// ---- frobenius.m: the rings of the Frobenius lift
O5, Ox, S, R := getrings(Integers(), 7, 5);
check("getrings: O = Z/7^5, Ox = O[x], S = Ox((z)), R = S[y]",
      #O5 eq 7^5 and BaseRing(Ox) cmpeq O5 and BaseRing(S) cmpeq Ox and BaseRing(R) cmpeq S, ~nfail);
xO := Ox.1; zS := S.1; yR := R.1;
r := xO^3 + 2*xO + 1;                                     // monic
OXY := PolynomialRing(Ox);                                // O[x][y]
// the value of an element of R without negative powers of z, after z = r(x), in O[x][y]
value := function(f)
  out := OXY!0;
  for i := 1 to #Coefficients(f) do
    c := Coefficients(f)[i];
    if c ne 0 then
      out +:= &+[OXY | Coefficient(c, k)*r^k : k in [Valuation(c)..Valuation(c) + #Coefficients(c) - 1]] * OXY.1^(i-1);
    end if;
  end for;
  return out;
end function;
lowdeg := func< f | forall{c : c in Coefficients(f) | c eq 0 or forall{a : a in Coefficients(c) | Degree(a) lt Degree(r)}} >;
f1 := (xO^7 + 3*xO^2 + 1)*yR + xO^5*zS + 2*xO^4;
f1r := radix_reduce(f1, r);
check("radix_reduce: the same value after z = r(x), all coefficients of x-degree < deg r",
      value(f1r) eq value(f1) and lowdeg(f1r), ~nfail);
Q := yR^2 - (xO^3 + xO + 2);
f2 := yR^3 + xO*yR + 1;
f2r := reduce_mod_Q(f2, Q, r);
check("reduce_mod_Q: y-degree < deg_y Q, and the values are congruent modulo Q",
      Degree(f2r) lt 2 and (value(f2) - value(f2r)) mod value(Q) eq 0, ~nfail);
f3 := yR + xO;
check("pow_mod_Q: (y + x)^9 modulo Q", (value(pow_mod_Q(f3, 9, Q, r)) - value(f3)^9) mod value(Q) eq 0, ~nfail);
xq := pow_mod_Q(R!xO, 7, Q, r);
f4 := (xO^2 + 3)*yR + xO;
check("substitute_xq: f(x^7, y) modulo Q",
      (value(substitute_xq(f4, xq, r)) - Evaluate(value(f4), [OXY | xO^7, OXY.1]) ) mod value(Q) eq 0
      where Evaluate := func< h, s | &+[OXY | Evaluate(Coefficient(h, j), s[1])*s[2]^j : j in [0..Degree(h)]] >, ~nfail);

// coefficient twists by the conjugation of Q(i) (the Frobenius at a prime inert in Q(i))
Qz<zq> := PolynomialRing(Rationals());
Li<i> := NumberField(zq^2 + 1);
conj := hom< Li -> Li | -i >;
Lix<xi> := PolynomialRing(Li); Lixy<yi> := PolynomialRing(Lix);
check("twist_pol, twist_polxy, twist_mat: coefficientwise conjugation; tau = 0 is the identity",
      twist_pol(i*xi^2 + 3, conj) eq -i*xi^2 + 3 and twist_pol(i*xi, 0) eq i*xi
      and twist_polxy((i*xi)*yi^2 + 1, conj) eq (-i*xi)*yi^2 + 1
      and twist_mat(Matrix(Li, 1, 2, [i, 1 + i]), conj) eq Matrix(Li, 1, 2, [-i, 1 - i]), ~nfail);

// ---- coercion.m: series over O_K/pi^N and over K
K := pAdicField(7, 12); OK := RingOfIntegers(K);
Kt<t> := PowerSeriesRing(K, 30);
Oq := quo< OK | UniformizingElement(K)^12 >;
St<s> := LaurentSeriesRing(Oq, 30);
u := 1 + 2*t + 7*t^3 - t^5 + O(t^30);
uS := series_K_to_Oq(u, St, OK);
uK := series_Oq_to_K(uS, LaurentSeriesRing(K, 30), OK);
check("series_K_to_Oq, series_Oq_to_K: the round trip returns the series",
      forall{k : k in [0..29] | IsWeaklyZero(Coefficient(uK, k) - Coefficient(u, k))}, ~nfail);
inv := series_inverse(uS);
check("series_inverse: u*(1/u) = 1 to the precision of the series over O_K/7^12",
      IsWeaklyZero(uS*inv - 1) and AbsolutePrecision(inv) eq AbsolutePrecision(uS), ~nfail);
Kx<X> := PolynomialRing(K);
gK := 3*X^3 - X + 5;
ts := taylor_shift_K(gK, K!2);
check("taylor_shift_K: the coefficients of g(2+t) are g(2), g'(2), g''(2)/2, g'''(2)/6",
      [IsWeaklyZero(ts[k] - c) : k -> c in [K | 27, 35, 18, 3]] eq [true : k in [1..4]], ~nfail);
QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
Kc, mc := Completion(QQ, P7 : Precision := 12);
Kc := ChangePrecision(Kc, 12); mc := mc*Coercion(Codomain(mc), Kc);
OKc := RingOfIntegers(Kc);
Oqc := quo< OKc | UniformizingElement(Kc)^12 >;
Stc<sc> := LaurentSeriesRing(Oqc, 20);
Qx<x> := PolynomialRing(QQ);
xS := Stc!(2 + sc);                                   // x = 2 + t
ev1 := polL_eval_Oq(x^3 + 7*x, mc, OKc, xS);
ev2 := fracL_eval_Oq((x^2 + 1)/(x - 1), mc, OKc, xS);
check("polL_eval_Oq, fracL_eval_Oq: x^3+7x and (x^2+1)/(x-1) at x = 2+t",
      ev1 eq (2 + sc)^3 + 7*(2 + sc) and IsWeaklyZero(ev2*(1 + sc) - ((2 + sc)^2 + 1)), ~nfail);
Ktc<tc> := LaurentSeriesRing(Kc, 20);
fs := eval_frac_shift((x^2 + 1)/(x - 1), QQ, Kc, mc, Kc!2, Ktc, Stc, OKc);
check("eval_frac_shift: (x^2+1)/(x-1) at x = 2+t as a series over K",
      forall{k : k in [0..15] | IsWeaklyZero(Coefficient(fs*(1 + tc) - ((2 + tc)^2 + 1), k))}, ~nfail);
QQt<tq> := PowerSeriesRing(QQ, 10);
cs := coer_plseries(1/3 + tq/7 + 5*tq^2 + O(tq^10), QQ, Kc, mc);
check("coer_plseries: the coefficients mapped to K, with the same t-adic precision",
      IsWeaklyZero(Coefficient(cs, 0) - mc(1/3)) and IsWeaklyZero(Coefficient(cs, 1) - mc(1/7)) and AbsolutePrecision(cs) eq 10, ~nfail);
a := mc(1/3 + 7^4);
check("approx_inL: an element of L whose image is the given p-adic number",
      IsWeaklyZero(mc(approx_inL(a, Kc, QQ, mc)) - a), ~nfail);
sK := Ktc!(mc(1/3) + mc(2/5)*tc + O(tc^5));
sL := approx_plseriesinL(sK, Kc, QQ, mc);
check("approx_plseriesinL, approx_polypseriesinL: series and polynomials of series over K back in L",
      forall{k : k in [0, 1] | IsWeaklyZero(mc(Coefficient(sL, k)) - Coefficient(sK, k))}
      and Degree(approx_polypseriesinL(PolynomialRing(PowerSeriesRing(Kc, 5))![mc(1/3), 1], Kc, QQ, mc)) eq 1, ~nfail);

// ---- expansion.m
Kt2<t2> := PowerSeriesRing(K, 40);
h := 7*t2^3 + O(t2^40);
check("divide_by_tpower: (t^3 h')/t^3 = h', the coefficients below t^3 dropped",
      Coefficient(divide_by_tpower(O(K!7^10) + h, 3), 0) eq 7, ~nfail);
Kty<Y> := PolynomialRing(Kt2);
fy := Y^2 - (1 + t2);                                 // the root sqrt(1+t) = 1 + t/2 - t^2/8 + ...
rootO := hensel_newton_Oq(fy, Kt2!1 + O(t2), [2, 4, 8, 16, 32, 40], 0);
rootK := hensel_newton_K(fy, Kt2!1 + O(t2), [2, 4, 8, 16, 32, 40], 0);
check("hensel_newton_Oq, hensel_newton_K: sqrt(1+t) to t-adic precision 40, the same over O_K/7^12 and over K",
      forall{k : k in [0..30] | IsWeaklyZero(Coefficient(rootO^2 - (1 + t2), k))}
      and forall{k : k in [0..30] | IsWeaklyZero(Coefficient(rootO - rootK, k))}, ~nfail);
check("mod_P_prec: roots that agree modulo t (+-t*sqrt(1+t)) need more t-adic precision than distinct ones (+-sqrt(1+t))",
      mod_P_prec(Y^2 - t2^2*(1 + t2), QQ, K, mc) gt mod_P_prec(fy, QQ, K, mc), ~nfail);
F7 := GF(7); F7x<x7> := PolynomialRing(F7); F7xy<y7> := PolynomialRing(F7x);
FF7 := FunctionField(y7^2 - x7);
pl := [P : P in Places(FF7, 1) | Evaluate(FF7!F7x.1, P) eq 2 and Evaluate(FF7.1, P) eq 3][1]; // (2, 3): 3^2 = 2
ex := mod_P_expansion(FF7.1, pl, FF7!F7x.1 - 2, 6);
check("mod_P_expansion: y = sqrt(x) at (2,3) on y^2 = x over F_7 in the parameter x - 2",
      Parent(ex) cmpne 0 and forall{k : k in [0..5] | Coefficient(ex^2, k) eq Coefficient(2 + PowerSeriesRing(F7)!PowerSeriesRing(F7).1, k)}, ~nfail);

// ---- integrals.m: precisions and helpers
check("known_digits: the relative precision of 3*7^2 + O(7^10), the absolute one of O(7^4)",
      known_digits(K!147 + O(K!7^10)) eq 8 and known_digits(O(K!7^4)) eq 4, ~nfail);
cx, cn := change_abs_precision(K!5 + O(K!7^9), 6);
cy, cm := change_abs_precision(K!5 + O(K!7^4), 6);
check("change_abs_precision: 9 -> 6 digits; 4 digits stay 4 (no digits are manufactured)",
      cn eq 6 and AbsolutePrecision(cx) eq 6 and cm eq 4 and AbsolutePrecision(cy) eq 4, ~nfail);
_, vn := change_abs_precision_vec(Vector(K, [K!1 + O(K!7^9), K!2 + O(K!7^5)]), 7);
_, mn := change_abs_precision_mat(Matrix(K, 1, 2, [K!1 + O(K!7^9), K!2 + O(K!7^8)]), 7);
check("change_abs_precision_vec, change_abs_precision_mat: the minimal precision achieved", vn eq 5 and mn eq 7, ~nfail);
Ku<uu> := PolynomialRing(K);
Ke<ue> := TotallyRamifiedExtension(K, uu^3 - 7);
V, rem := round_to_K(Vector(Ke, [Ke!3, Ke!(2*7^2)]), K);
V2, rem2 := round_to_K(Vector(Ke, [Ke!3 + 7*ue, Ke!1]), K);
check("round_to_K: elements of K come back with nothing left over; a u-component of v_K 4/3 is reported",
      IsWeaklyZero(V[1] - 3) and IsWeaklyZero(V[2] - 98) and rem cmpeq Infinity()
      and IsWeaklyZero(V2[1] - 3) and rem2 eq 4/3, ~nfail);
T, lo := powtab(K!3, -2, 4);
check("powtab: T[k-lo+1] = 3^k for -2 <= k <= 4", lo eq -2 and forall{k : k in [-2..4] | IsWeaklyZero(T[k+3] - (K!3)^k)}, ~nfail);

Lx<xx> := PolynomialRing(QQ); Lxy<yy> := PolynomialRing(Lx);
fpol := xx*(xx-1)*(xx+1)*(xx-2)*(xx+3);
data := coleman_data(yy^2 - fpol, QQ, P7, 10 : verbose := false);
Kd := data`K;
check("final_reduction_loss: c_end of the data (0 here)",
      final_reduction_loss(data`monomial_to_basis, data`exact_primitives, data`p) eq data`cend and data`cend eq 0, ~nfail);
okW := matrix_over_Q(data`Winf, RationalFunctionField(Rationals()));
okI := matrix_over_Q(Matrix(FieldOfFractions(Lix), 1, 1, [i*xi + 1/2]), RationalFunctionField(Rationals()));
check("matrix_over_Q: true for Winf (rational coefficients), false for a matrix with the coefficient i",
      okW and not okI, ~nfail);
Mb := [data`m(QQ.1^(k-1)) : k in [1..Degree(QQ)]];
check("map_coefficients_K: the same images as the completion map, and 0 for 0",
      forall{k : k -> c in map_coefficients_K([QQ | 1/3, 5, 0], Mb) | IsWeaklyZero(c - data`m([QQ | 1/3, 5, 0][k]))}, ~nfail);
mks := twisted_maps(data);
check("twisted_maps: for the q-power lift (n_tau = 1) both maps are the completion map",
      #mks eq 2 and IsWeaklyZero(mks[1](QQ!5/7) - data`m(5/7)) and IsWeaklyZero(mks[2](QQ!5/7) - data`m(5/7)), ~nfail);
Pt := set_point(3, 12, data);
Pc := rec< Format(Pt) | x := ChangePrecision(Kd, 20)!3, b := [ChangePrecision(Kd, 20)!c : c in Pt`b], inf := false, r := Pt`r >;
check("point_to_K: the coordinates of a point over another copy of K, coerced into K",
      Parent(point_to_K(Pc, Kd)`x) cmpeq Kd and IsWeaklyZero(point_to_K(Pc, Kd)`x - 3), ~nfail);
FF, Lt := model_function_field(data);
mp1 := cached_minpoly(data, 1, 1, 3, FF!Lt.1, FF.1);   // row 1: over L(x); column 3: b^0_2 = y
check("cached_minpoly: the minimal polynomial of y over L(x) has degree 2 and annihilates y",
      Degree(mp1) eq 2 and IsZero(Evaluate(mp1, FF.1)) where Evaluate := func< m, v | &+[FF | Evaluate(Coefficient(m, j), FF!Lt.1)*v^j : j in [0..Degree(m)]] >, ~nfail);
R294 := set_bad_point(data`m(QQ!294), [Kd!1, Sqrt(data`m(Evaluate(fpol, 294)))], false, data); // in the disc of (0,0)
W := find_bad_point_in_disc(R294, data);
check("find_bad_point_in_disc: the very bad point of the disc of x = 294 = 6*7^2 is (0,0)",
      IsWeaklyZero(W`x) and IsWeaklyZero(W`b[2]) and is_very_bad(W, data), ~nfail);
check("auxiliary_e: 2*q*e_P + 1 = 29 for a bad endpoint (e_P = 2), a given e > q*e_P is kept, 1 without bad endpoints",
      auxiliary_e(0, Pt, W, false, true, data, false) eq 29 and auxiliary_e(15, Pt, W, false, true, data, false) eq 15
      and auxiliary_e(0, Pt, Pt, false, false, data, false) eq 1, ~nfail);
v, Nv := evalfend([Lx | xx^2, 3], Pt, data);
check("evalfend: f_end = x^2*b^0_1 + 3*b^0_2 at (3,12) is 9 + 36 = 45",
      IsWeaklyZero(v - 45) and Nv ge data`N, ~nfail);
// tiny_integral_prec(prec, e, maxpoleorder, maxdegree, mindegree, val, NPP, data): for e = 1,
// val = 1, no poles and 100 terms the bound is N_max - 1 (the terms of positive order and the
// constant term lose val = 1); a pole of order 3 costs 3 + floor(log_7(2)) = 3 more digits
Nm := data`Nmax;
check("tiny_integral_prec: N_max - 1 without poles, N_max - 4 with a pole of order 3",
      tiny_integral_prec(0, 1, 0, 100, 100, 1, Nm, data) eq Nm - 1 and tiny_integral_prec(0, 1, 3, 100, 100, 1, Nm, data) eq Nm - 4, ~nfail);

// ---- solver.m
Kx := PolynomialRing(Kd);
check("Lx_to_Kx, L_or_Lx_to_Kx: x^2/3 + 7 over L, and the constant 5/7, as polynomials over K",
      forall{k : k in [0..2] | IsWeaklyZero(Coefficient(Lx_to_Kx(xx^2/3 + 7, data`m, Kx), k) - data`m([QQ | 7, 0, 1/3][k+1]))}
      and IsWeaklyZero(Coefficient(L_or_Lx_to_Kx(QQ!5/7, Kx, data`m), 0) - data`m(5/7)), ~nfail);
EK := evaluate_matrix_K(Matrix(FieldOfFractions(Lx), 1, 2, [xx/(xx + 1), xx^2]), Kd, Kd!2, data`m);
check("evaluate_matrix_K: (x/(x+1), x^2) at x = 2", IsWeaklyZero(EK[1,1] - data`m(2/3)) and IsWeaklyZero(EK[1,2] - 4), ~nfail);
FFq, mmq, Fqx, red_ratfun := reduced_function_field(data);
rb := reduced_basis(FFq, data`W0, red_ratfun);
check("reduced_basis: the reductions of b^0 = (1, y) are 1 and the generator of the reduced function field",
      rb[1] eq 1 and rb[2] eq FFq.1, ~nfail);
sp := search_small_points(data`Q, 3, data`L);
check("search_small_points: the points (0,0), (+-1,0), (2,0), (-3,0), (3,+-12) with x of height <= 3",
      {[Rationals() | c : c in pt] : pt in sp} eq {[Rationals() | 0,0], [1,0], [-1,0], [2,0], [-3,0], [3,12], [3,-12]}, ~nfail);
Pts := [set_point(3, 12, data), set_point(3, -12, data), set_point(0, 0, data)];
Ifirst, Nfirst := integrals_from_first(Pts, data, "unit-helpers");
I2, N2 := coleman_integrals_on_basis(Pts[1], Pts[3], data : verbose := false);
check("integrals_from_first: the integrals from the first point, as coleman_integrals_on_basis computes them",
      #Ifirst eq 2 and Nfirst[2] eq N2 and forall{i : i in [1..2] | IsWeaklyZero(Ifirst[2][i] - I2[i])}, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
