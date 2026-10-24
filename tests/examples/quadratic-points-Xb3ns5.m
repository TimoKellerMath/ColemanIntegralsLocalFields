// tests/examples/quadratic-points-Xb3ns5.m   [example: all quadratic points of X(b3,ns5) over Q(sqrt 5)]
//
//     magma -b tests/examples/quadratic-points-Xb3ns5.m        (from the repository root)
//
// The genus-2 curve X(b3,ns5): y^2 = f(x) = 9x^6 - 6x^5 - 35x^4 + 40x^2 + 12x - 8 over
// F = Q(sqrt 5), whose Jacobian has rank 0 over F. curve_quadratic_points (quadratic_points.m)
// runs symmetric Chabauty at the prime P above 11 (split in F, so F_P = Q_11) over the
// unramified quadratic extension K = Q_(11^2) of F_P, from the base divisor
// D0 = ((s-1)/2, 5(s-1)/2) + ((-s-1)/2, 5(s+1)/2) alone (s = sqrt 5):
//   1. 146 residue discs in three models: the model, and two Moebius patches x = t + 1/x' that
//      carry the two discs at infinity; the six Weierstrass discs are treated at their
//      Weierstrass point, in the model and in the patches. Of the 171 Frobenius-stable residue
//      classes, 79 contain an F-rational effective divisor of degree 2 outside the
//      hyperelliptic family (D0 and 78 recovered ones: 40 points of degree 2 with 20
//      x-polynomials, and 39 sums of two F-rational points), 12 are classes of pullbacks (the
//      hyperelliptic family), and 80 have a p-adic zero that is not recognized;
//   2. every divisor is verified independently of the function field: the x-polynomial of a
//      point of degree 2 is irreducible over F and f(x) is a square in F[x]/(x-polynomial);
//   3. completeness: rank J(F) = rank J(Q) + rank J^(5)(Q) = 0, and #J(F)_tors divides #J(k_v)
//      for the good primes v of odd residue characteristic, whose gcd is 80. The 79 divisors
//      and the canonical class are 80 distinct elements of Pic^2(C)(F), which J(F) acts on
//      simply transitively, so #J(F) = 80 and the 79 divisors are all F-rational effective
//      divisors of degree 2 outside the family: the 80 unresolved classes are empty. (For
//      dim V = 2 no single prime can show this: almost every class has a p-adic zero.)
//   4. the six x-polynomials that quadratic_points_split finds over Q_11 in the split, diagonal
//      and bad disc-pairs (test-symchab-Xb3ns5) are among the 20, which are stable under
//      Gal(F/Q);
//   5. with the ten places of degree 2 above the first five of them as further known
//      divisors: the four of them that are ramified at P (no points over K) lie in diagonal
//      classes, and all eleven known divisors are in certified classes; the same 79 divisors;
//   6. with primes := 2 at the default primes (both primes above 11; for no good prime of norm
//      <= 50 does p divide #J(F_q), so no class is excluded and no prime gives a complete
//      result): the divisors of the first prime are known at the second, the same 79 divisors.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
load "symmetric_chabauty.m"; load "models.m"; load "quadratic_points.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/examples/quadratic-points-Xb3ns5.log" : Overwrite);
RF := "tests/examples/quadratic-points-Xb3ns5.results"; // the outcomes, see record_run
results_start(RF);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
// the number of classes of every status
counts := func< res | [ #[ c : c in res`classes | c`status eq st ] : st in ["excluded", "known", "recovered", "family", "unresolved"] ] >;
// records the outcome of curve_quadratic_points under the label: the numbers of discs, classes
// of every status and divisors, and the x-polynomials of the divisors (sorted, as strings)
record_run := procedure(label, res)
  record_result(RF, label cat ": norms of the primes", [Norm(P) : P in res`primes]);
  record_result(RF, label cat ": discs", #res`discs);
  record_result(RF, label cat ": classes", #res`classes);
  record_result(RF, label cat ": excluded, known, recovered, family, unresolved", counts(res));
  record_result(RF, label cat ": divisors", #res`divisors);
  record_result(RF, label cat ": x-polynomials", Sort([Sprint(f) : f in res`xpolys]));
  record_result(RF, label cat ": complete", res`complete);
end procedure;

_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
OF := MaximalOrder(F);
Fx<X> := PolynomialRing(F);
A2<a,b> := AffineSpace(F, 2);
fX := 9*X^6 - 6*X^5 - 35*X^4 + 40*X^2 + 12*X - 8;
C := Curve(A2, b^2 - Evaluate(fX, a));
P := Decomposition(OF, 11)[1][1];
D0 := [C![(s-1)/2, 5*(s-1)/2], C![(-s-1)/2, 5*(s+1)/2]];

// ---- 1. the quadratic points from D0 alone
res := curve_quadratic_points(C, [D0] : P := P, N := 12, improve := false, rank_check := true);
record_run("1. from D0", res);
quad := [ j : j in [1..#res`divisors] | #Support(res`divisors[j]) eq 1 and Degree(Support(res`divisors[j])[1]) eq 2 ];
xquad := { res`xpolys[j] : j in quad };
check("1. 146 discs in 3 models (the model and two Moebius patches), 171 classes, all covered",
      #res`discs eq 146 and #res`models eq 3 and #res`classes eq 171 and res`uncovered eq 0 and res`unseen eq 0, ~nfail);
check("1. classes: 0 excluded, 1 with the known divisor D0, 78 recovered, 12 of pullbacks, 80 unresolved",
      counts(res) eq [0, 1, 78, 12, 80], ~nfail);
check("1. 79 divisors: 40 points of degree 2 (20 x-polynomials) and 39 sums of two F-rational points",
      #res`divisors eq 79 and #quad eq 40 and #xquad eq 20, ~nfail);
check("1. the unresolved classes have a p-adic zero that is not recognized",
      forall{ c : c in res`classes | c`status ne "unresolved" or c`note eq "zero not recognized" }, ~nfail);
check("1. rank_check: 0 <= rank J(F) <= 0 (2-descent over F), so V annihilates J(F)",
      res`rank eq [0, 0] and res`annihilating, ~nfail);

// ---- 2. independent verification of the divisors
square_mod := func< mp | IsSquare(Evaluate(fX, quo<Fx | mp>.1)) >;
FF0 := FunctionField(C);
Dinf := &+[ -Valuation(FF0!a, pl)*Divisor(pl) : pl in Poles(FF0!a) ];   // x^*(infinity), the hyperelliptic class
check("2. the divisors are distinct, effective of degree 2, and none is in the hyperelliptic family (D - x^*(oo) not principal)",
      #Set(res`divisors) eq #res`divisors and forall{ D : D in res`divisors | IsEffective(D) and Degree(D) eq 2 }
      and forall{ D : D in res`divisors | not IsPrincipal(D - Dinf) }, ~nfail);
check("2. every x-polynomial of a point of degree 2 is irreducible over F, with f(x) a square in F[x]/(mp)",
      forall{ mp : mp in xquad | IsIrreducible(mp) and square_mod(mp) }, ~nfail);

// ---- 3. completeness: rank 0 and the torsion bound
_<xQ> := PolynomialRing(Rationals());
H := HyperellipticCurve(9*xQ^6 - 6*xQ^5 - 35*xQ^4 + 40*xQ^2 + 12*xQ - 8);
_, h0 := RankBounds(Jacobian(H));
_, h5 := RankBounds(Jacobian(QuadraticTwist(H, 5)));
check("3. rank J(F) = rank J(Q) + rank J^(5)(Q) = 0", h0 + h5 eq 0, ~nfail);
M := res`model;
vs := [ v : v in good_primes(M : bound := 100) | IsOdd(Minimum(v)) ];
orders := [ Evaluate(LPolynomial(reduced_curve_function_field(M, v)), 1) : v in vs ];
bound := GCD(orders);
record_result(RF, "3. gcd of #J(k_v)", bound);
check(Sprintf("3. #J(F)_tors divides gcd #J(k_v) = 80 (%o good primes v of norm <= 100)", #vs), bound eq 80, ~nfail);
check("3. 79 divisors + the canonical class = 80 elements of J(F): the 79 divisors are all, the 80 unresolved classes are empty",
      #res`divisors + 1 eq bound, ~nfail);

// ---- 4. the five x-polynomials of the split and diagonal classes over Q_11
five := [ X^2 + 1/6*(3*s + 1)*X + 1/3*(2*s - 3), X^2 + 1/6*(-3*s + 11)*X + 1/3*(3*s - 8), X^2 + 5/3*X + 1,
          X^2 + 1/6*(3*s - 5)*X + 1/3*(s - 7), X^2 + 1/6*(-s + 1)*X + 1/6*(-3*s - 1) ];
conj := hom< F -> F | -s >;
cpoly := func< f | Fx![ conj(c) : c in Coefficients(f) ] >;
six := five cat [ X^2 + 1/6*(-3*s - 5)*X + 1/6*(3*s + 1) ];
check("4. the six x-polynomials of test-symchab-Xb3ns5 are among the 20, which are stable under Gal(F/Q)",
      forall{ f : f in six | f in xquad } and forall{ f : f in xquad | cpoly(f) in xquad }, ~nfail);

// ---- 5. the ten places above the five x-polynomials as further known divisors
FF := FunctionField(C);
known := [* D0 *] cat [* pl : pl in Zeros(Evaluate(mp, FF!a)), mp in five | Degree(pl) eq 2 *];
res5 := curve_quadratic_points(C, known : P := P, N := 12, improve := false, verbose := false);
record_run("5. with the known points", res5);
ramified := [ j : j in [2..#known] | #point_records(res5`model, res5`data, [known[j]]) eq 0 ];
diag := [ c : c in res5`classes | c`status eq "known" and c`kind eq "diagonal" ];
check("5. 11 known divisors, 4 of them ramified at P (no points over K), each in a certified diagonal class",
      #known eq 11 and #ramified eq 4 and #diag eq 4 and Set([c`divisor : c in diag]) eq Set(ramified), ~nfail);
check("5. all 11 known divisors lie in certified classes, and the same 79 divisors are found",
      counts(res5) eq [0, 11, 68, 12, 80] and Set(res5`divisors) eq Set(res`divisors), ~nfail);

// ---- 6. two primes (no good prime of norm <= 50 has p | #J(F_q), so none excludes a class)
res6 := curve_quadratic_points(C, [D0] : N := 12, improve := false, primes := 2, verbose := false);
record_run("6. two primes", res6);
check("6. primes := 2: both primes above 11 (by norm), D0 known, the same 78 new divisors, not complete",
      [Norm(Q) : Q in res6`primes] eq [11, 11] and res6`primes[1] ne res6`primes[2] and res6`known eq [1]
      and #res6`new eq 78 and Set(res6`divisors) eq Set(res`divisors) and not res6`complete, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
