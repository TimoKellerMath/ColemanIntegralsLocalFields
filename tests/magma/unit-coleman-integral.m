// tests/magma/unit-coleman-integral.m   [unit test: coleman_integral for an arbitrary form]
//
//     magma -b tests/magma/unit-coleman-integral.m        (from the repository root)
//
// coleman_integral(P1,P2,dif,data) integrates a form of the second kind given like the
// entries of data`basis: dif in L[x]^d stands for sum_i dif_i b^0_i dx/z, z = r/lc(r)
// (README). It is checked on two curves, a curve over Q (the rational branch of coleman_data)
// and a curve with non-rational coefficients over the ramified K = Q_7(sqrt 7):
//   * a basis form and a linear combination of basis forms: the integrals must agree with the
//     entries of coleman_integrals_on_basis;
//   * the exact form dy = d(b^0_1) (here W0 = 1, so b^0 = (1,y)), whose coefficient vector is
//     the second row of z*G0: int_P^R dy = y(R) - y(P).
// A runtime error in coleman_integral is reported as a failure of the check.
// Then the form of the third kind dx/x = [f/x, 0] (residues at the points above x = 0 and
// x = infinity, which are points of X - U) with the basis of H^1_dR(U) (useU): its integral is
// log x(R) - log x(P) on Iwasawa's branch (log 7 = 0), between good points (from (3,12) to a
// point with x = 10) and to the point R with x = 294 = 6*7^2 in the bad disc of (0,0), where the
// tiny integrals from the very bad point contribute the logarithmic terms res*log(t(S)):
// int_(3,12)^R dx/x = log(294/3) = log 2.
// The integrals are recorded in unit-coleman-integral.results (tests/magma/results.m), to the
// precisions that the functions return.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/magma/unit-coleman-integral.log" : Overwrite);
RF := "tests/magma/unit-coleman-integral.results";
results_start(RF);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

// coleman_integral with the integrals on the basis supplied, catching runtime errors; the
// integral is recorded under the name
integrate := function(P, R, dif, data, I, N, name)
  try
    J, NJ := coleman_integral(P, R, dif, data : IP1P2:=I, NIP1P2:=N);
    record_result(RF, name, J : precision := NJ);
    return true, J, "";
  catch e
    return false, 0, e`Object;
  end try;
end function;

run_checks := procedure(label, data, P, R, ~nfail)
  I, N := coleman_integrals_on_basis(P, R, data : verbose:=false);
  record_result(RF, label cat ": the integrals on the basis", I : precision := N);
  basis := data`basis; g := data`g; d := Degree(data`Q);
  check(label cat ": the integrals on the basis are not all zero",
        not &and[ IsWeaklyZero(I[i]) : i in [1..2*g] ], ~nfail);

  // a basis form
  ok, J, err := integrate(P, R, basis[1], data, I, N, label cat ": int omega_1");
  check(label cat ": int omega_1 = (coleman_integrals_on_basis)[1]" cat (ok select "" else " -- error: " cat err),
        ok and IsWeaklyZero(J - I[1]), ~nfail);

  // a linear combination of basis forms
  ok, J, err := integrate(P, R, 2*basis[1] - basis[g+1], data, I, N, label cat ": int (2*omega_1 - omega_(g+1))");
  check(label cat ": int (2*omega_1 - omega_(g+1)) = 2*I[1] - I[g+1]" cat (ok select "" else " -- error: " cat err),
        ok and IsWeaklyZero(J - (2*I[1] - I[g+1])), ~nfail);

  // the exact form dy = d(b^0_1): coefficient vector z*G0[2] w.r.t. b^0 dx/z
  z := data`r/LeadingCoefficient(data`r);
  dy := Parent(basis[1])![ Numerator(z*data`G0[2,j]) : j in [1..d] ];
  ok, J, err := integrate(P, R, dy, data, I, N, label cat ": int dy");
  check(label cat ": int dy = y(R) - y(P)" cat (ok select "" else " -- error: " cat err),
        ok and IsWeaklyZero(J - (R`b[2] - P`b[2])), ~nfail);
end procedure;

// ---- 1. y^2 = x(x-1)(x+1)(x-2)(x+3) over Q, at 7: the rational branch of coleman_data
QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - x*(x-1)*(x+1)*(x-2)*(x+3);
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
data := coleman_data(Q, QQ, P7, 10 : verbose := false);
run_checks("curve over Q at 7", data, set_point(3, 12, data), set_point(3, -12, data), ~nfail);

// ---- 2. y^2 = x^5 + sqrt(7)*x^2 + 1 over Q(sqrt 7), at the ramified prime above 7
X := PolynomialRing(Rationals()).1;
L3<w> := NumberField(X^2 - 7);
L3x<x3> := PolynomialRing(L3); L3xy<y3> := PolynomialRing(L3x);
Q3 := y3^2 - (x3^5 + w*x3^2 + 1);
P3 := Decomposition(MaximalOrder(L3), 7)[1][1];
data3 := coleman_data(Q3, L3, P3, 12 : verbose := false);
run_checks("curve over Q(sqrt 7) at the prime above 7", data3, set_point(0, 1, data3), set_point(0, -1, data3), ~nfail);

// ---- 3. a form of the third kind
dataU := coleman_data(Q, QQ, P7, 10 : verbose := false, useU := true);
KU := dataU`K; f := x*(x-1)*(x+1)*(x-2)*(x+3);
PU := set_point(3, 12, dataU);
_, y10 := IsSquare(dataU`m(Evaluate(f, 10)));
R10 := set_bad_point(dataU`m(QQ!10), [KU!1, y10], false, dataU);   // a good point over K
_, y294 := IsSquare(dataU`m(Evaluate(f, 294)));
R294 := set_bad_point(dataU`m(QQ!294), [KU!1, y294], false, dataU); // in the bad disc of (0,0)
J10, N10 := coleman_integral(PU, R10, [Lx | f div x, 0], dataU);
check("useU: int dx/x from (3,12) to the point with x = 10 is log(10/3)",
      N10 ge 8 and Valuation(J10 - Log(KU!10) + Log(KU!3)) ge N10, ~nfail);
J294, N294 := coleman_integral(PU, R294, [Lx | f div x, 0], dataU);
record_result(RF, "useU: int dx/x from (3,12) to x = 10", J10 : precision := N10);
record_result(RF, "useU: int dx/x from (3,12) to x = 294", J294 : precision := N294);
check("useU: int dx/x from (3,12) into the bad disc of (0,0), x = 294: log 2 (the logarithmic terms of the tiny integrals)",
      N294 ge 4 and Valuation(J294 - Log(KU!2)) ge N294 and is_bad(R294, dataU), ~nfail);
check("log_iwasawa: log(294) = log(6) (log 7 = 0)", IsWeaklyZero(log_iwasawa(KU!294) - Log(KU!6)), ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
