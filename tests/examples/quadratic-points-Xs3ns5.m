// tests/examples/quadratic-points-Xs3ns5.m   [example: the quadratic points of X(s3,ns5) over Q(sqrt 5) at one prime]
//
//     magma -b tests/examples/quadratic-points-Xs3ns5.m        (from the repository root; about 4 minutes)
//
// The smooth plane quartic X(s3,ns5) over F = Q(sqrt 5), of genus 3 with rank J(F) = 1 (Example 8.4
// and Appendix A of the article). curve_quadratic_points runs symmetric Chabauty at the prime P
// above 19 (split in F, so F_P = Q_19) over K = Q_(19^2), from the base divisor
// D0 = (1,0) + (7,-3), the generator (-1/2,-1/2) - (1,0) of J(F) modulo torsion (so that V, of
// dimension g - 1 = 2, annihilates J(F)), and the bielliptic involution sigma, for which V is the
// space of trace-zero differentials (trace_zero):
//   1. 434 residue discs over F_361 (431 good in the model, 3 at infinity) in four models: the
//      model, two linear patches for the discs at infinity (affine_patches) and a further patch for
//      a pair of discs that are good in no common model; 459 Frobenius-stable classes;
//   2. the 36 sporadic quadratic points of Appendix A are recovered: the 35 affine ones (Example
//      8.4) and the point of degree 2 at infinity of the model, together with the 32 sums of two
//      F-rational points that are not pullbacks along the bielliptic map phi : C -> E (the eight
//      points of C(F) form four sigma-orbits); D0 = phi^*(O_E) itself lies in one of the 21 classes
//      of pullbacks;
//   3. the remaining classes: 24 rank-drop classes (the "cross" classes of
//      symmetric_chabauty_classify at 19, see test-symchab-Xs3ns5) and 346 classes with a p-adic
//      zero that is not recognized. For dim V = 2 a single prime does not prove completeness;
//      Appendix A of the article does it with a Mordell-Weil sieve (appendix-A-sieve.m), and its
//      result -- exactly these 36 sporadic points -- is what is found here.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
load "symmetric_chabauty.m"; load "models.m"; load "quadratic_points.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/examples/quadratic-points-Xs3ns5.log" : Overwrite);
RF := "tests/examples/quadratic-points-Xs3ns5.results";
results_start(RF);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
counts := func< res | [ #[ c : c in res`classes | c`status eq st ] : st in ["excluded", "known", "recovered", "family", "unresolved"] ] >;

_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
OF := MaximalOrder(F);
Fx<x> := PolynomialRing(F); Fxy<y> := PolynomialRing(Fx);
Q := y^4 - 2*y^3*x - y^2*x^2 - 8*y^3 - 2*y^2*x + 2*y*x^2 + x^3 + 3*y^2 + 3*y*x - 3*x^2 - 2*y + 3*x - 1;
P := Decomposition(OF, 19)[1][1];
sigma := Matrix(F, 3, 3, [1,8,-8, 1,3,2, -2,4,1]);   // the bielliptic involution, (x:y:z) -> sigma*(x,y,z)^t

// ---- 1. the sweep
res := curve_quadratic_points(Q, [[[1,0],[7,-3]]] : generators := [[[[-1/2,-1/2]],[[1,0]]]], P := P, N := 16,
         improve := false, htbound := 10^6, sigma := sigma, trace_zero := true);
record_result(RF, "discs", #res`discs);
record_result(RF, "models", #res`models);
record_result(RF, "classes", #res`classes);
record_result(RF, "excluded, known, recovered, family, unresolved", counts(res));
record_result(RF, "divisors", #res`divisors);
record_result(RF, "x-polynomials", Sort([Sprint(f) : f in res`xpolys]));
check("1. 434 discs over F_361 in 4 models (the model, 3 linear patches), 459 classes, all treated in some model",
      #res`discs eq 434 and #res`models eq 4 and #res`classes eq 459
      and forall{ c : c in res`classes | c`model gt 0 } and res`uncovered eq 0, ~nfail);
check("1. classes: 0 excluded, 68 recovered, 21 of pullbacks (D0 = phi^*(O_E) among them), 370 unresolved",
      counts(res) eq [0, 0, 68, 21, 370], ~nfail);

// ---- 2. the 36 sporadic points and the sums of two F-rational points
Fpol<XF> := PolynomialRing(F);
pub := [ Fpol |
 XF^2 - 11*XF - 47, XF^2 - XF - 2*s - 2, XF^2 - XF + 2*s - 2, XF^2 - 3/2*XF + 63/2,
 XF^2 - 59/7*XF + 25/7, XF^2 - 27/28*XF + 1/4, XF^2 - 23/7*XF + 47/28,
 XF^2 + (s+6)*XF + 8*s + 4, XF^2 + (-s+6)*XF - 8*s + 4,
 XF^2 + (6*s-4)*XF - 12*s + 19, XF^2 + (-6*s-4)*XF + 12*s + 19,
 XF^2 + (11*s-47)/8*XF - 4*s + 9, XF^2 + (14*s-27)/3*XF - 6*s + 14,
 XF^2 + (-11*s-47)/8*XF + 4*s + 9, XF^2 + (-14*s-27)/3*XF + 6*s + 14,
 XF^2 + (7*s+17)/2*XF - 62*s - 146, XF^2 + (33*s-68)/2*XF - 33*s + 69,
 XF^2 + (-7*s+17)/2*XF + 62*s - 146, XF^2 + (-33*s-68)/2*XF + 33*s + 69,
 XF^2 + (-2*s-19)/2*XF + (s+25)/4, XF^2 + (2*s-19)/2*XF + (-s+25)/4,
 XF^2 + (3*s-7)/6*XF + (-6*s-10)/3, XF^2 + (-3*s-7)/6*XF + (6*s-10)/3,
 XF^2 + (5*s-17)/2*XF + (67*s-149)/2, XF^2 + (-5*s-17)/2*XF + (-67*s-149)/2,
 XF^2 + (7*s-176)/79*XF + (76*s+256)/79, XF^2 + (-51*s+97)/62*XF + (147*s-327)/62,
 XF^2 + (51*s+97)/62*XF + (-147*s-327)/62, XF^2 + (-7*s-176)/79*XF + (-76*s+256)/79,
 XF^2 + (-137*s-223)/82*XF + (59*s+603)/82, XF^2 + (137*s-223)/82*XF + (-59*s+603)/82,
 XF^2 + (-283*s+479)/24*XF + (181*s-179)/24, XF^2 + (283*s+479)/24*XF + (-181*s-179)/24,
 XF^2 + (-793*s-1663)/82*XF + (991*s+2123)/82, XF^2 + (793*s-1663)/82*XF + (-991*s+2123)/82 ];
M := res`model; FF := M`FF;
deg2 := [ j : j in [1..#res`divisors] | #Support(res`divisors[j]) eq 1 and Degree(Support(res`divisors[j])[1]) eq 2 ];
affine := { Fpol!res`xpolys[j] : j in deg2 | res`xpolys[j] ne 0 };
atinf := [ j : j in deg2 | res`xpolys[j] eq 0 ];
check("2. 36 points of degree 2: the 35 affine sporadic points of Example 8.4 and one point at infinity of the model",
      #deg2 eq 36 and affine eq Set(pub) and #atinf eq 1 and Valuation(M`xf, Support(res`divisors[atinf[1]])[1]) lt 0, ~nfail);
onQ := function(mp)   // Q(x, Y) has a root over F(x) = F[X]/(mp)
  A := ext< F | mp >;
  return #Roots(PolynomialRing(A)![ Evaluate(Coefficient(Q, i), A.1) : i in [0..4] ]) gt 0;
end function;
check("2. every affine point of degree 2 is verified: its x-polynomial is irreducible over F, and Q(x, Y) has a root in F[x]/(mp)",
      forall{ mp : mp in affine | IsIrreducible(mp) and onQ(mp) }, ~nfail);
pairs := [ D : D in res`divisors | forall{ pl : pl in Support(D) | Degree(pl) eq 1 } ];
ratpts := { pl : pl in Support(D), D in pairs };
check("2. 33 sums of two F-rational points (D0 and 32 recovered ones), supported on the eight points of C(F)",
      #pairs eq 33 and #ratpts eq 8 and #res`divisors eq 36 + 33, ~nfail);

// ---- 3. the remaining classes
notes := {* c`note : c in res`classes | c`status eq "unresolved" *};
check("3. the unresolved classes: 24 rank-drop (cross) classes and 346 with a p-adic zero that is not recognized",
      notes eq {* "rank drop"^^24, "zero not recognized"^^346 *}, ~nfail);
check("3. not complete at one prime (dim V = 2): a Mordell-Weil sieve is needed (Appendix A)", not res`complete, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
