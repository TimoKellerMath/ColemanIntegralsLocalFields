// tests/examples/quadratic-points-over-F.m   [example: a curve genuinely defined over Q(sqrt 5)]
//
//     magma -b tests/examples/quadratic-points-over-F.m        (from the repository root)
//
// The genus-2 curve C: y^2 = s*x*(x-1)*(x+1)*(x-2)*(x+3) over F = Q(sqrt 5), s = sqrt 5, the
// twist by s of the curve of the README. It is not isomorphic over F to its Galois conjugate
// y^2 = -s*x*(x-1)*(x+1)*(x-2)*(x+3), so it is not the base change of a curve over Q, and its
// model has coefficients outside Q. Its six Weierstrass points (x = 0, 1, -1, 2, -3, infinity)
// are F-rational, and rank J(F) = 0 (2-descent, RankBound):
//   1. curve_quadratic_points from the base divisor D0 = (0,0) + (1,0) alone, at the default
//      prime: the prime P above 11 with 11 dividing #J(F_11) = 176 (the other prime above 11 has
//      #J(F_11) = 80), over K = Q_(11^2). There the integrals to 160 of the 187 classes are
//      units, which excludes them; the other classes contain D0 or one of the 14 recovered
//      divisors, the 15 sums W_i + W_j of two distinct Weierstrass points, or are classes of
//      pullbacks (the Weierstrass discs, the pairs {Pb, iota(Pb)}): the result is complete,
//      i.e. these are all F-rational effective divisors of degree 2 outside the hyperelliptic
//      family -- C has no quadratic points outside it; with rank_check the driver also shows
//      that V annihilates J(F) (rank J(F) <= 0 by 2-descent);
//   2. the same from the torsion: J(F)[2] has order 2^4 = 16 (the six Weierstrass points are
//      rational), and 16 = gcd #J(k_v) over the good primes v of odd residue characteristic, so
//      J(F) = J(F)[2] (rank 0), whose 16 elements are the 15 divisors and the canonical class;
//   3. at the other prime above 11, where 11 does not divide #J(F_11): no class is excluded
//      (the integrals to the classes lie in pi*O_K), the same 15 divisors, 64 classes with a
//      p-adic zero that is not recognized, not complete;
//   4. without the auxiliary extension (aux := false, K = Q_11): only the split and diagonal
//      classes, the same 15 divisors, and the classes of points of degree 2 of the reduction are
//      reported as not seen (not complete);
//   5. the curve C2: y^2 = (x+1)*(x^2 + w)*(x^2 - w*x + 1), w = (1+s)/2, also genuinely over F
//      and of rank 0, with the points of degree 2 above the two quadratic factors (Weierstrass
//      points over quadratic extensions of F) as known divisors: at 11 (where 11 does not
//      divide #J(F_11) = 96) their classes, of two Frobenius-conjugate Weierstrass discs, are
//      certified, and the sum of the two F-rational Weierstrass points is recovered; these three
//      and the canonical class are the 4 = gcd #J(k_v) = #J(F)[2] elements of J(F).
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
load "symmetric_chabauty.m"; load "models.m"; load "quadratic_points.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/examples/quadratic-points-over-F.log" : Overwrite);
RF := "tests/examples/quadratic-points-over-F.results";
results_start(RF);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
counts := func< res | [ #[ c : c in res`classes | c`status eq st ] : st in ["excluded", "known", "recovered", "family", "unresolved"] ] >;
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
Fx<X> := PolynomialRing(F);
A2<a,b> := AffineSpace(F, 2);
fX := s*X*(X-1)*(X+1)*(X-2)*(X+3);
C := Curve(A2, b^2 - Evaluate(fX, a));
FF := FunctionField(C);
conj := hom< F -> F | -s >;
H := HyperellipticCurve(fX);
check("the curve is not isomorphic over F to its Galois conjugate (not a base change from Q)",
      not IsIsomorphic(H, HyperellipticCurve(Fx![conj(c) : c in Coefficients(fX)])), ~nfail);
check("rank J(F) = 0 (RankBound, 2-descent over F)", RankBound(Jacobian(H)) eq 0, ~nfail);

// the six Weierstrass points as places, and the 15 sums of two of them
W := [ Place(C![x0, 0]) : x0 in [0, 1, -1, 2, -3] ] cat [ Poles(FF!a)[1] ];
pairs := { Divisor(W[i]) + Divisor(W[j]) : j in [i+1..6], i in [1..6] };

// ---- 1. from D0 alone at the default prime
D0 := [C![0, 0], C![1, 0]];
res := curve_quadratic_points(C, [D0] : N := 12, rank_check := true);
record_run("1. from D0", res);
P11 := Decomposition(MaximalOrder(F), 11);
nJ := func< P | Evaluate(LPolynomial(reduced_curve_function_field(res`model, P)), 1) >;
check("1. the default prime: the prime above 11 with 11 | #J(F_11) = 176 (the other one has #J(F_11) = 80), over K = Q_(11^2)",
      Norm(res`prime) eq 11 and nJ(res`prime) eq 176 and {nJ(Q[1]) : Q in P11} eq {80, 176}
      and #ResidueClassField(RingOfIntegers(res`data`K)) eq 121, ~nfail);
check("1. 187 classes: 160 excluded (a unit integral), D0 and 14 recovered divisors, 12 of pullbacks, none unresolved",
      #res`classes eq 187 and counts(res) eq [160, 1, 14, 12, 0]
      and forall{ c : c in res`classes | c`status ne "excluded" or c`note eq "a unit integral" }, ~nfail);
check("1. the 15 divisors are the sums of two distinct Weierstrass points, and the result is complete",
      Set(res`divisors) eq pairs and #res`divisors eq 15 and res`complete, ~nfail);
check("1. rank_check: 0 <= rank J(F) <= 0 (2-descent), so V (all holomorphic forms) annihilates J(F)",
      res`rank eq [0, 0] and res`annihilating, ~nfail);

// ---- 2. completeness from the torsion
M := res`model;
vs := [ v : v in good_primes(M : bound := 100) | IsOdd(Minimum(v)) ];
bound := GCD([ Evaluate(LPolynomial(reduced_curve_function_field(M, v)), 1) : v in vs ]);
record_result(RF, "2. gcd of #J(k_v)", bound);
check("2. gcd #J(k_v) = 16 = #J(F)[2], so J(F) = J(F)[2] (rank 0)", bound eq 16, ~nfail);
check("2. the 15 divisors and the canonical class are the 16 elements of J(F): no other divisors outside the family",
      #res`divisors + 1 eq bound, ~nfail);

// ---- 3. the other prime above 11
P2 := [ Q[1] : Q in P11 | nJ(Q[1]) eq 80 ][1];
res3 := curve_quadratic_points(C, [D0] : N := 12, P := P2, verbose := false);
record_run("3. the other prime above 11", res3);
check("3. at the prime above 11 with #J(F_11) = 80: no class excluded, the same 15 divisors, 64 classes unresolved (not complete)",
      counts(res3) eq [0, 1, 14, 12, 64] and Set(res3`divisors) eq pairs and not res3`complete
      and forall{ c : c in res3`classes | c`status ne "unresolved" or c`note eq "zero not recognized" }, ~nfail);

// ---- 4. without the auxiliary extension
res4 := curve_quadratic_points(C, [D0] : N := 12, aux := false, verbose := false);
record_run("4. without aux", res4);
check("4. aux := false: K = Q_11, only split and diagonal classes, the same 15 divisors, the degree-2 classes not seen",
      #ResidueClassField(RingOfIntegers(res4`data`K)) eq 11 and forall{ c : c in res4`classes | c`kind ne "conjugate" }
      and Set(res4`divisors) eq pairs and res4`unseen gt 0 and not res4`complete, ~nfail);

// ---- 5. points of degree 2 as known divisors, on another curve
w := (1 + s)/2;
fX2 := (X + 1)*(X^2 + w)*(X^2 - w*X + 1);
H2 := HyperellipticCurve(fX2);
check("5. C2 is not isomorphic to its Galois conjugate, and rank J2(F) = 0",
      not IsIsomorphic(H2, HyperellipticCurve(Fx![conj(c) : c in Coefficients(fX2)])) and RankBound(Jacobian(H2)) eq 0, ~nfail);
C2 := Curve(A2, b^2 - Evaluate(fX2, a));
FF2 := FunctionField(C2);
quads := [ pl : pl in Zeros(Evaluate(mp, FF2!a)), mp in [X^2 + w, X^2 - w*X + 1] | Degree(pl) eq 2 ];
res5 := curve_quadratic_points(C2, quads : N := 12, verbose := false);
record_run("5. C2", res5);
D5 := Divisor(Place(C2![-1, 0])) + Divisor(Poles(FF2!a)[1]);
M2 := res5`model;
bound2 := GCD([ Evaluate(LPolynomial(reduced_curve_function_field(M2, v)), 1) : v in good_primes(M2 : bound := 100) | IsOdd(Minimum(v)) ]);
record_result(RF, "5. gcd of #J2(k_v)", bound2);
check("5. at 11: the two points of degree 2 in certified classes, (-1,0) + infinity recovered; gcd #J2(k_v) = 4, so these are all",
      Norm(res5`prime) eq 11 and #quads eq 2 and counts(res5)[2..3] eq [2, 1]
      and Set(res5`divisors) eq {Divisor(q) : q in quads} join {D5} and bound2 eq 4 and #res5`divisors + 1 eq bound2, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
