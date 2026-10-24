// tests/library/test-curve-chabauty.m   [library test: Chabauty-Coleman for a Curve]
//
//     magma -b tests/library/test-curve-chabauty.m        (from the repository root)
//
// The genus-2 curve 971.a.971.1 (LMFDB), y^2 + y = x^5 - 2x^3 + x over Q: its Jacobian has
// Mordell-Weil rank 1 < g = 2, and it has the seven rational points (-1,-1), (-1,0), (0,-1),
// (0,0), (1,-1), (1,0) and the point at infinity.
//   1. curve_chabauty (models.m) from the Curve and its known points: it chooses the model
//      and the prime (7: the smallest good prime p with p not dividing #J(F_p)), runs
//      effective_chabauty, and finds the seven known points among the candidates, plus two
//      7-adic points in the residue discs of x = -1 that are not rational;
//   2. effective_chabauty with the known points searched by K_points (a bound instead of the
//      points): the same candidates;
//   3. torsion_packet of the point at infinity: the 2-torsion of J(Q) is trivial, but the
//      torsion packet over Q_7 contains the points whose difference with infinity is torsion;
//      among them the Weierstrass point at infinity itself;
//   4. with rank_check: the rank of the Jacobian is 1 < 2 (RankBounds); a single prime cannot
//      exclude the two extra 7-adic candidates (for rank g - 1 the integral of the vanishing
//      differential has a zero in almost every residue disc). The curve 249.a.249.1,
//      y^2 + (x^3+1)y = x^2 + x, has rank 0 and the five rational points of its LMFDB entry:
//      at 5 there is one extra candidate, at 11 every candidate is a known point, so with up to
//      three primes curve_chabauty proves that the five points are all (complete);
//   5. curve_chabauty without the known point (1,0): it is found again as a candidate whose x
//      is recognized as the rational number 1 with the rational points (1,0), (1,-1) above it;
//   6. with N := 3 the computation for 249.a.249.1 at 5 fails for lack of precision and is
//      repeated with N = 6 (the option maxN of curve_chabauty); with patches := true the
//      bad disc of (-1,0) (e_P = 2 for the model) is treated in an affine patch where it is
//      good, with the vanishing differentials transported through the function field: the
//      same six candidates, two of them computed in the patch;
//   7. over L = Q(sqrt -3), where 249.a.249.1 still has rank 0 (its twist by -3 has rank 0):
//      without the point (zeta^2, -1) (zeta = (-1 + sqrt -3)/2) among the known points, it is
//      found as a candidate and its x is recognized as an element of L (recognize_in_F).
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
load "models.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/library/test-curve-chabauty.log" : Overwrite);
RF := "tests/library/test-curve-chabauty.results"; // the outcomes, see record_run
results_start(RF);
SetVerbose("User1", 1); // the progress of the solver (verbosity level 1 of the library's flag)

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
// records the outcome of curve_chabauty under the label: the model, the primes, the numbers of
// candidates, the known points they match, the recognized x, the rank bounds, completeness
record_run := procedure(label, res)
  record_result(RF, label cat ": model", Sprint(res`model`Q));
  record_result(RF, label cat ": norms of the primes", [Norm(P) : P in res`primes]);
  record_result(RF, label cat ": candidates", #res`candidates);
  record_result(RF, label cat ": matched", res`matched);
  record_result(RF, label cat ": recognized x", [Sprint(r[2]) : r in res`recognized]);
  record_result(RF, label cat ": rank bounds", res`rank);
  record_result(RF, label cat ": complete", res`complete);
end procedure;

A2<a,b> := AffineSpace(Rationals(), 2);
C := Curve(A2, b^2 + b - (a^5 - 2*a^3 + a));
pts := PointSearch(ProjectiveClosure(C), 10);
print "known points:", pts;

// ---- 1. curve_chabauty
res := curve_chabauty(C, pts : N := 10, bound := 20, verbose := true);
record_run("1. 971.a", res);
check("curve_chabauty: the model y^2 + y - x^5 + 2x^3 - x at the prime 7",
      Sprint(res`model`Q) eq "y^2 + y - x^5 + 2*x^3 - x" and Norm(res`prime) eq 7, ~nfail);
check("curve_chabauty: 9 candidates, the 7 known points among them (each exactly once)",
      #res`candidates eq 9 and #res`known eq 7 and Seqset(res`matched) eq {0..7} and #res`new eq 2, ~nfail);
check("curve_chabauty: the 2 other candidates lie in the residue discs of x = -1 and are not rational",
      &and[ Valuation(res`candidates[i]`x + 1) ge 1 : i in res`new ] and #res`recognized eq 0, ~nfail);

// ---- 2. effective_chabauty with a point search
data := res`data;
cands := effective_chabauty(data : bound := 2);
check("effective_chabauty with K_points(data, 2): 9 candidates", #cands eq 9, ~nfail);

// ---- 3. torsion_packet
inf := [ R : R in res`known | R`inf ][1];
packet := torsion_packet(inf, data);
check("torsion_packet of the point at infinity contains the point at infinity",
      exists{ R : R in packet | R`inf and IsWeaklyZero(R`x - inf`x) }, ~nfail);
printf "torsion packet of infinity over Q_7: %o point(s)\n", #packet;

// ---- 4. the rank, and a second prime
res2 := curve_chabauty(C, pts : N := 10, bound := 20, rank_check := true, verbose := true);
record_run("4. 971.a with rank_check", res2);
check("rank_check: 1 <= rank J(Q) <= 1 < g = 2; the two extra candidates at 7 remain (not complete)",
      res2`rank eq [1,1] and not res2`complete and #res2`new eq 2, ~nfail);
C249 := Curve(A2, b^2 + (a^3 + 1)*b - (a^2 + a));
pts249 := PointSearch(ProjectiveClosure(C249), 10);
res249 := curve_chabauty(C249, pts249 : N := 10, bound := 30, primes := 3, rank_check := true, verbose := true);
record_run("4. 249.a, three primes", res249);
check("249.a.249.1: rank 0; one extra candidate at 5, none at 11: the 5 rational points are all (complete)",
      #pts249 eq 5 and res249`rank eq [0,0] and #res249`new eq 1 and res249`complete
      and [Norm(P) : P in res249`primes] eq [5, 11], ~nfail);

// ---- 5. a point that is not among the known points is recognized
pts5 := [ R : R in pts | not (R[3] ne 0 and R[1]/R[3] eq 1 and R[2]/R[3] eq 0) ];
res5 := curve_chabauty(C, pts5 : N := 10, bound := 20, verbose := true);
record_run("5. 971.a without (1,0)", res5);
check("curve_chabauty without (1,0): the candidate x = 1 is recognized, with y in {0, -1}",
      #pts5 eq 6 and exists{ r : r in res5`recognized | r[2] eq 1 and Seqset(r[3]) eq {0, -1} }, ~nfail);

// ---- 6. a larger precision when it does not suffice
res3 := curve_chabauty(C249, pts249 : N := 3, bound := 30, improve := false, verbose := true);
record_run("6. 249.a with N = 3", res3);
check("N := 3 does not suffice at 5: repeated with N = 6, the same candidates", res3`data`N eq 6 and #res3`candidates eq 6, ~nfail);
res4 := curve_chabauty(C249, pts249 : N := 10, bound := 30, improve := false, patches := true, verbose := true);
record_run("6. 249.a with patches", res4);
check("patches := true: the six candidates (five known points, one new), those of the bad disc of (-1,0) computed in a patch",
      #res4`candidates eq 6 and Seqset(res4`matched) eq {0..5} and #res4`new eq 1 and #res4`models eq 2
      and #[ i : i in res4`model_index | i eq 2 ] eq 2, ~nfail);

// ---- 7. a point over a number field is recognized
L<w> := NumberField(PolynomialRing(Rationals()).1^2 + 3);
zeta := (w - 1)/2;
AL<aL,bL> := AffineSpace(L, 2);
CL := Curve(AL, bL^2 + (aL^3 + 1)*bL - (aL^2 + aL));
PCL := ProjectiveClosure(CL);
ptsL := [PCL![0,-1,1], PCL![0,1,0], PCL![0,0,1], PCL![-1,0,1], PCL![1,0,0], PCL![zeta,-1,1]];
resL := curve_chabauty(CL, ptsL : N := 10, bound := 20, improve := false, verbose := true);
record_run("7. 249.a over Q(sqrt -3)", resL);
check("over Q(sqrt -3): the missing point (zeta^2, -1) is recognized, x = (-1 - sqrt -3)/2 in L",
      exists{ r : r in resL`recognized | r[2] eq zeta^2 and r[3] eq [L | -1] }, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
