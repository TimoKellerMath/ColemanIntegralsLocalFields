// tests/library/test-ros-chabauty.m   [library test: Chabauty-Coleman for the restriction of scalars]
//
//     magma -b tests/library/test-ros-chabauty.m        (from the repository root)
//
// The genus-2 curve X: y^2 = x^5 - 2x^3 - 2x^2 + x + 1 over Q: its Jacobian has rank 1
// (RankBounds), (0,1) - infinity has infinite order, and X has good reduction at 3 with
// #X(F_3) = 3, #J(F_3) = 8. Over a quadratic field L the rank of J(L) is 1 plus the rank of
// the quadratic twist of X. ros_chabauty (solver.m) uses the completions of L at the primes
// above 3 at once (Siksek's restriction of scalars): it needs rank J(L) <= (g-1)*2 = 2.
//   1. L = Q(sqrt -2) (the twist has rank 0, so rank J(L) = 1; 3 splits): with both primes
//      the 3 vanishing functionals settle the 9 residue polydiscs (3 with a known point, 6
//      empty): X(L) = {infinity, (0,1), (0,-1)}. Without (0,-1) among the known points its
//      polydisc has exactly one common zero of the functionals, recognized as (0,-1).
//   2. L = Q(sqrt 7) (the twist has rank 1, with the point (3, 5 sqrt 7) of X(L); 3 splits):
//      rank J(L) = 2 = g, so no single completion suffices (effective_chabauty finds no
//      vanishing differential, ros_chabauty with one prime too few functionals). With both
//      primes: 2 functionals; 5 polydiscs with a known point, 4 empty: X(L) = {infinity,
//      (0,+-1), (3,+-5 sqrt 7)}.
//   3. L = Q(i) (the twist has rank 1; 3 is inert, K = Q_9, polydiscs of dimension 2 over
//      Q_3): the known points infinity, (0,+-1), (+-1,+-i), (-2,+-5i). The four further points
//      (i,+-(i+2)), (-i,+-(i-2)) are found and recognized; the two polydiscs with two known
//      points each ((1,i) and (-2,-5i) agree modulo 3, as do (1,-i) and (-2,5i)) stay
//      unresolved, since a polydisc with a unique common zero contains at most one of them;
//      two polydiscs have a unique common zero that is not L-rational: the Weierstrass points
//      ((1+-sqrt 5)/2, 0) of X(Q_9), whose difference with infinity is torsion (excluding
//      them needs another argument, e.g. a Mordell-Weil sieve).
//   4. L = Q(sqrt 5) (the twist has rank 0; 3 inert): the known points infinity, (0,+-1) and
//      the Weierstrass points ((1+-sqrt 5)/2, 0): 5 polydiscs with a known point, 6 empty;
//      the 2 polydiscs of the points (1,+-i) of X(Q_9) stay unresolved: there the linear
//      terms of the functionals are degenerate modulo 3 (the criterion needs a left inverse
//      B of them with B times the higher terms divisible by 3).
// The outcome for every polydisc is recorded in test-ros-chabauty.results (tests/magma/results.m).
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/library/test-ros-chabauty.log" : Overwrite);
RF := "tests/library/test-ros-chabauty.results";
results_start(RF);
SetVerbose("User1", 1); // the progress of the solver (verbosity level 1 of the library's flag)

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
// whether the call raises an error whose message contains phrase
raises := function(f, phrase)
  try
    _ := f();
  catch e
    return Position(e`Object, phrase) gt 0;
  end try;
  return false;
end function;

Qz<z> := PolynomialRing(Rationals());
// the data at the primes above 3 of L = Q(sqrt d), and the known points: pairs [x0, y0] (y0
// = a + b*sqrt d given as [x0, a, b]) and "inf" for the point at infinity (its point
// records at the primes)
setup := function(d, pts)
  L<s> := NumberField(z^2 - d);
  Lu<u> := PolynomialRing(L); Luv<v> := PolynomialRing(Lu);
  Q := v^2 - (u^5 - 2*u^3 - 2*u^2 + u + 1);
  datas := [coleman_data(Q, L, P[1], 15 : verbose := false) : P in Decomposition(MaximalOrder(L), 3)];
  known := [* (pt cmpeq "inf") select [* set_bad_point(0, [1, 0], true, D) : D in datas *]
                                  else [L | pt[1], pt[2] + pt[3]*s] : pt in pts *];
  return L, datas, known;
end function;
statuses := func<res | [#[P : P in res`polydiscs | P`status eq s] : s in ["known", "empty", "one", "unresolved"]]>;
pair := func<pt | Sprintf("(%o, %o)", pt[1], pt[2])>;
// prints the outcome and records it under the label
show := procedure(label, res)
  printf "%o functional(s); polydiscs (known, empty, one, unresolved) = %o; complete: %o\n",
         Nrows(res`functionals), statuses(res), res`complete;
  record_result(RF, label cat ": functionals", Nrows(res`functionals));
  for P in res`polydiscs do
    printf "  discs %o: %-10o known points %o%o\n", P`discs, P`status, P`known,
           #P`point gt 0 select Sprintf(", recognized as %o", pair(P`point)) else "";
    record_result(RF, Sprintf("%o: polydisc %o", label, P`discs),
                  Sprintf("%o, known points %o%o", P`status, P`known, #P`point gt 0 select ", " cat pair(P`point) else ""));
  end for;
  record_result(RF, label cat ": complete", res`complete);
end procedure;

// ---- 1. rank 1 over Q(sqrt -2)
print "\n---- 1. L = Q(sqrt -2), rank 1, 3 split";
L1, datas1, known1 := setup(-2, [* [0,1,0], [0,-1,0], "inf" *]);
res1 := ros_chabauty(datas1, known1);
show("1. Q(sqrt -2)", res1);
check("Q(sqrt -2): 3 functionals; 3 known, 6 empty polydiscs: the 3 known points are all (complete)",
      #datas1 eq 2 and Nrows(res1`functionals) eq 3 and statuses(res1) eq [3, 6, 0, 0] and res1`complete and #res1`new eq 0, ~nfail);
res1b := ros_chabauty(datas1, known1[[1,3]]);
show("1. Q(sqrt -2) without (0,-1)", res1b);
check("Q(sqrt -2) without (0,-1): its polydisc has one zero, recognized as (0,-1); complete",
      statuses(res1b) eq [2, 6, 1, 0] and res1b`new eq [[L1 | 0, -1]] and res1b`complete, ~nfail);

// ---- 2. rank 2 over Q(sqrt 7)
print "\n---- 2. L = Q(sqrt 7), rank 2 = g, 3 split";
_, datas2, known2 := setup(7, [* [0,1,0], [0,-1,0], "inf", [3,0,5], [3,0,-5] *]);
check("Q(sqrt 7), one completion: effective_chabauty finds no vanishing differential",
      raises(func< | effective_chabauty(datas2[1] : Kpoints := [as_point(known2[i], datas2[1], "test") : i in [1,2,4,5]]) >, "kernel is zero"), ~nfail);
check("Q(sqrt 7), ros_chabauty with one prime: too few functionals",
      raises(func< | ros_chabauty(datas2[[1]], [* known2[i] : i in [1,2,4,5] *]) >, "fewer than the dimension"), ~nfail);
res2 := ros_chabauty(datas2, known2);
show("2. Q(sqrt 7)", res2);
check("Q(sqrt 7), both primes: 2 functionals; 5 known, 4 empty polydiscs: the 5 known points are all (complete)",
      Nrows(res2`functionals) eq 2 and statuses(res2) eq [5, 4, 0, 0] and res2`complete, ~nfail);

// ---- 3. rank 2 over Q(i), 3 inert
print "\n---- 3. L = Q(i), rank 2, 3 inert (K = Q_9)";
L3, datas3, known3 := setup(-1, [* [0,1,0], [0,-1,0], "inf", [1,0,1], [1,0,-1], [-1,0,1], [-1,0,-1], [-2,0,5], [-2,0,-5] *]);
res3 := ros_chabauty(datas3, known3);
show("3. Q(i)", res3);
i := L3.1;
check("Q(i): one prime of degree 2, 2 functionals, 13 polydiscs",
      #datas3 eq 1 and Nrows(res3`functionals) eq 2 and #res3`polydiscs eq 13, ~nfail);
check("Q(i): the four points (i,+-(i+2)), (-i,+-(i-2)) are found and recognized",
      Seqset(res3`new) eq {[i, i+2], [i, -i-2], [-i, i-2], [-i, -i+2]}, ~nfail);
check("Q(i): the polydiscs with two known points ((1,i),(-2,-5i) and (1,-i),(-2,5i)) are unresolved",
      {Seqset(P`known) : P in res3`polydiscs | P`status eq "unresolved"} eq {{4, 9}, {5, 8}} and not res3`complete, ~nfail);
weierstrass := func<R | not R`inf and IsWeaklyZero(R`x^2 - R`x - 1) and IsWeaklyZero(R`b[2])>;
check("Q(i): the 2 zeros that are not recognized are the Weierstrass points ((1+-sqrt 5)/2, 0) of X(Q_9)",
      #[P : P in res3`polydiscs | P`status eq "one" and #P`point eq 0] eq 2
      and forall{P : P in res3`polydiscs | P`status ne "one" or #P`point gt 0 or weierstrass(P`points[1])}, ~nfail);

// ---- 4. rank 1 over Q(sqrt 5), 3 inert
print "\n---- 4. L = Q(sqrt 5), rank 1, 3 inert (K = Q_9)";
L4, datas4, known4 := setup(5, [* [0,1,0], [0,-1,0], "inf" *]);
s5 := L4.1;
known4 cat:= [* [(1+s5)/2, 0], [(1-s5)/2, 0] *];
res4 := ros_chabauty(datas4, known4);
show("4. Q(sqrt 5)", res4);
check("Q(sqrt 5): 3 functionals; 5 known, 6 empty polydiscs",
      Nrows(res4`functionals) eq 3 and statuses(res4)[[1,2]] eq [5, 6], ~nfail);
check("Q(sqrt 5): the 2 unresolved polydiscs are those of the points (1,+-i) of X(Q_9)",
      #[P : P in res4`polydiscs | P`status eq "unresolved"] eq 2
      and forall{P : P in res4`polydiscs | P`status ne "unresolved" or Valuation(res4`discs[1][P`discs[1]]`x - 1) ge 1}, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
