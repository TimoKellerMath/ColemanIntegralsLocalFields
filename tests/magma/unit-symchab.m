// tests/magma/unit-symchab.m   [unit test: the helpers of symmetric_chabauty.m]
//
//     magma -b tests/magma/unit-symchab.m        (from the repository root)
//
// The helpers of the symmetric Chabauty recovery checked on systems with known solutions:
//   * power_sums: p_j = t1^j + t2^j as polynomials in sigma1 = t1 + t2, sigma2 = t1*t2, and
//     their derivatives, against Magma's symbolic derivatives;
//   * series_coefficients, symmetric_x (x1 + x2 and x1*x2 from sigma1, sigma2);
//   * newton_symmetric and newton_pair: the zero of a system built from chosen parameters
//     t1, t2 in 7*Z_7 is found (as sigma1, sigma2, resp. t1, t2); the Jacobian tests
//     diagonal_jacobian_invertible and newton_jacobian_invertible on an invertible and a
//     singular leading matrix;
//   * diff_coeffs, differentials_are_saturated, saturate_differentials (the lattice
//     spanned by v and v + 7w is not saturated, its saturation contains w);
//   * reduce_L_scalar, reduce_Lpoly_to_Fq, eval_Fq_poly, on_curve_degree2.
// The curve is y^2 = x(x-1)(x+1)(x-2)(x+3) over Q at 7, as in unit-integrals.m.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
load "symmetric_chabauty.m";
SetColumns(0);
SetLogFile("tests/magma/unit-symchab.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

// ---- power sums
R2<s1,s2> := PolynomialRing(Rationals(), 2);
p, d1, d2 := power_sums(s1, s2, 6);
Rt<t1,t2> := PolynomialRing(Rationals(), 2);
to_t := hom< R2 -> Rt | t1 + t2, t1*t2 >;
check("power_sums: p_j(t1 + t2, t1*t2) = t1^j + t2^j for j = 0..6",
      forall{j : j in [0..6] | to_t(p[j+1]) eq t1^j + t2^j}, ~nfail);
check("power_sums: the derivatives by sigma1 and sigma2",
      forall{j : j in [0..6] | d1[j+1] eq Derivative(p[j+1], 1) and d2[j+1] eq Derivative(p[j+1], 2)}, ~nfail);

// ---- series_coefficients, symmetric_x
K := pAdicField(7, 15);
Kt<t> := PowerSeriesRing(K, 20);
check("series_coefficients: the known coefficients, zeros beyond them",
      series_coefficients(3*t^2 + t^4 + O(t^6), 7) eq [K | 0, 0, 3, 0, 1, 0, 0, 0], ~nfail);
xt := 3 + t + 5*t^2 - t^3 + O(t^20);
a1 := K!7; a2 := K!14;                               // t1 = 7, t2 = 14
xa := Evaluate(xt, a1); xb := Evaluate(xt, a2);
e1, e2 := symmetric_x(xt, a1 + a2, a1*a2);
check("symmetric_x: x(t1) + x(t2) and x(t1)*x(t2) from sigma1 = t1 + t2, sigma2 = t1*t2",
      Valuation(e1 - (xa + xb)) ge 12 and Valuation(e2 - xa*xb) ge 12, ~nfail);

// ---- the Newton steps on systems with a known zero
s := [Kt | 2 + t + 3*t^2 + 7*t^3 + O(t^20), 1 + 2*t + t^2 + t^3 + O(t^20)];
I := [ -((Evaluate(s[k], a1) - Coefficient(s[k], 0)) + (Evaluate(s[k], a2) - Coefficient(s[k], 0))) : k in [1..2] ];
check("diagonal_jacobian_invertible: [[a_11, -2a_12], [a_21, -2a_22]] = [[1, -6], [2, -2]] is invertible mod 7",
      diagonal_jacobian_invertible(s, K), ~nfail);
check("diagonal_jacobian_invertible: [[1, -2], [2, -4]] is singular",
      not diagonal_jacobian_invertible([Kt | t + t^2 + O(t^20), 2*t + 2*t^2 + O(t^20)], K), ~nfail);
sig1, sig2 := newton_symmetric(I, s, K);
check("newton_symmetric: the zero (sigma1, sigma2) = (t1 + t2, t1*t2) = (21, 98)",
      Valuation(sig1 - 21) ge 12 and Valuation(sig2 - 98) ge 12, ~nfail);
// a Jacobian that is singular modulo 7 ([[1, -6], [2, 2]], det 14): the iteration may meet a
// Jacobian whose determinant is an inexact zero; it stops instead of failing
ssing := [Kt | 2 + t + 3*t^2 + 7*t^3 + O(t^20), 1 + 2*t - t^2 + t^3 + O(t^20)];
Ising := [ -((Evaluate(ssing[k], a1) - Coefficient(ssing[k], 0)) + (Evaluate(ssing[k], a2) - Coefficient(ssing[k], 0))) : k in [1..2] ];
okn := true;
try
  _, _ := newton_symmetric(Ising, ssing, K);
catch e
  okn := false;
end try;
check("newton_symmetric with a Jacobian singular modulo 7: no failure", okn, ~nfail);
sA := s; sB := [Kt | 5 + 3*t + t^2 + O(t^20), 4 + t + 2*t^2 + O(t^20)];
IP := [ -((Evaluate(sA[k], a1) - Coefficient(sA[k], 0)) + (Evaluate(sB[k], a2) - Coefficient(sB[k], 0))) : k in [1..2] ];
check("newton_jacobian_invertible: the leading matrix [[1, 3], [2, 1]] is invertible mod 7",
      newton_jacobian_invertible(sA, sB, K) and not newton_jacobian_invertible(sA, sA, K), ~nfail);
u1, u2 := newton_pair(IP, sA, sB, K);
check("newton_pair: the zero (t1, t2) = (7, 14)", Valuation(u1 - 7) ge 12 and Valuation(u2 - 14) ge 12, ~nfail);

// ---- the differentials
QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
f := x*(x-1)*(x+1)*(x-2)*(x+3);
data := coleman_data(y^2 - f, QQ, Decomposition(MaximalOrder(QQ), 7)[1][1], 10 : verbose := false);
Kd := data`K;
A := Matrix(Kd, 2, 3, [1, 2, 3, 4, 5, 6]);
check("diff_coeffs: the coefficients of v[1]*omega_1 + v[2]*omega_2 from those of the basis forms",
      forall{l : l -> c in diff_coeffs(A, [Kd | 2, -1], data) | IsWeaklyZero(c - [-2, -1, 0][l])}, ~nfail);
v := [Kd | 1, 2]; w := [Kd | 0, 1];
V := [v, [v[j] + 7*w[j] : j in [1..2]]];
check("differentials_are_saturated: {v, w} yes, {v, v + 7w} no",
      differentials_are_saturated([v, w], data) and not differentials_are_saturated(V, data), ~nfail);
Vs := saturate_differentials([[Kd | 1, 2, 0][1..2]], data);
check("saturate_differentials: a single primitive vector stays (up to a unit), the saturated basis of a rank-1 lattice",
      #Vs eq 1 and differentials_are_saturated(Vs, data), ~nfail);

// ---- reductions
Fq := ResidueClassField(RingOfIntegers(Kd));
Fqx<xq> := PolynomialRing(Fq);
check("reduce_L_scalar: 1/3 reduces to 5 in F_7", reduce_L_scalar(QQ!1/3, data) eq Fq!5, ~nfail);
check("reduce_Lpoly_to_Fq: x^2/2 + 7x - 1 reduces to 4x^2 - 1",
      reduce_Lpoly_to_Fq(x^2/2 + 7*x - 1, data, Fqx) eq 4*xq^2 - 1, ~nfail);
F49<w49> := GF(49);
check("eval_Fq_poly: the value of x^2 + 1 at a generator of F_49", eval_Fq_poly(xq^2 + 1, w49) eq w49^2 + 1, ~nfail);
check("on_curve_degree2: x^2 + 3x (the points x = 0 and x = -3, y = 0) lies on the curve; x^2 - 7 does not",
      on_curve_degree2(x^2 + 3*x, data) and not on_curve_degree2(x^2 - 7, data), ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
