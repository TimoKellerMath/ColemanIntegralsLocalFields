// tests/magma/unit-teichmueller.m   [unit test: the Teichmueller point of a residue disc]
//
//     magma -b tests/magma/unit-teichmueller.m        (from the repository root)
//
// teichmueller_pt(P,data) returns the point T in the residue disc of a good point P whose
// x-coordinate is the Teichmueller representative of x(P) mod pi. On y^2 = x^5 + c*x^2 + 1:
//   1. c = sqrt(2) over K = Q_7 (7 splits in Q(sqrt 2)), with the integral basis
//      b^0 = (1, x+y) (W0 = [[1,0],[x,1]]), at a good point P whose x-coordinate is not a
//      Teichmueller representative: x(T)^7 = x(T); T lies on the curve, with
//      y(T) = b^0_1(T) - x(T); T`r = z(x(T));
//   2. c = sqrt(3) over K = Q_49 (7 inert in Q(sqrt 3)): x(T)^49 = x(T);
//   3. c = sqrt(7) over the ramified K = Q_7(sqrt 7): x(T)^7 = x(T).
// A runtime error is reported as a failure of the check.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
SetColumns(0);
SetLogFile("tests/magma/unit-teichmueller.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

teich := function(P, data)
  try
    return true, teichmueller_pt(P, data), "";
  catch e
    return false, 0, e`Object;
  end try;
end function;

X := PolynomialRing(Rationals()).1;

// the curve y^2 = x^5 + c*x^2 + 1 over Q(sqrt d) at a prime above 7, optionally with b^0 = (1, x+y),
// and a good point with x in [2..6] and the values of b^0 there
setup := function(d, W0shift)
  L<c> := NumberField(X^2 - d);
  Lx<x> := PolynomialRing(L); Lxy<y> := PolynomialRing(Lx);
  Q := y^2 - (x^5 + c*x^2 + 1);
  P := Decomposition(MaximalOrder(L), 7)[1][1];
  if W0shift then
    data := coleman_data(Q, L, P, 10 : verbose := false, W0 := Matrix(FieldOfFractions(Lx), 2, 2, [1, 0, x, 1]));
  else
    data := coleman_data(Q, L, P, 10 : verbose := false);
  end if;
  K := data`K; m := data`m;
  f := func< t | t^5 + m(c)*t^2 + 1 >;
  z := PolynomialRing(K)![ m(a) : a in Coefficients(data`r/LeadingCoefficient(data`r)) ];
  x0 := [ K!a : a in [2..6] | IsSquare(f(K!a)) and Valuation(Evaluate(z, K!a)) eq 0 ][1];
  y0 := Sqrt(f(x0));
  b := W0shift select [K!1, x0 + y0] else [K!1, y0];
  return data, set_bad_point(x0, b, false, data), f, z;
end function;

// ---- 1. K = Q_7, b^0 = (1, x+y)
data, P, f, z := setup(2, true);
K := data`K;
ok, T, err := teich(P, data);
check("Q_7: x(T)^7 = x(T) and x(T) = x(P) mod pi" cat (ok select "" else " -- error: " cat err),
      ok and IsWeaklyZero(T`x^7 - T`x) and Valuation(T`x - P`x) ge 1, ~nfail);
check("Q_7: T lies on the curve, y(T)^2 = f(x(T)) with y(T) = b^0_1(T) - x(T)" cat (ok select "" else " -- error"),
      ok and IsWeaklyZero((T`b[2] - T`x)^2 - f(T`x)), ~nfail);
check("Q_7: T`r = z(x(T))" cat (ok select "" else " -- error"),
      ok and IsWeaklyZero(T`r - Evaluate(z, T`x)), ~nfail);

// ---- 2. K = Q_49
data, P, f, z := setup(3, false);
ok, T, err := teich(P, data);
check("Q_49: x(T)^49 = x(T) and x(T) = x(P) mod pi" cat (ok select "" else " -- error: " cat err),
      ok and IsWeaklyZero(T`x^49 - T`x) and Valuation(T`x - P`x) ge 1, ~nfail);

// ---- 3. K = Q_7(sqrt 7), ramified
data, P, f, z := setup(7, false);
ok, T, err := teich(P, data);
check("Q_7(sqrt 7): x(T)^7 = x(T) and x(T) = x(P) mod pi" cat (ok select "" else " -- error: " cat err),
      ok and IsWeaklyZero(T`x^7 - T`x) and Valuation(T`x - P`x) ge 1, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
