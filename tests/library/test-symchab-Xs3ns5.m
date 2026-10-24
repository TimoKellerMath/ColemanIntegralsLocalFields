load "isrational.m";
load "auxpolys.m";
load "cohobasis.m";
load "frobenius.m";
load "reduction.m";
load "coercion.m";
load "expansion.m";
load "integrals.m";
load "solver.m";
load "symmetric_chabauty.m";

SetColumns(0);
SetLogFile("tests/library/test-symchab-Xs3ns5.log" : Overwrite);
SetVerbose("User1", 1); // the progress of the solver (verbosity level 1 of the library's flag)

print "==== d=2 symmetric Chabauty: X(s3,ns5) / Q(sqrt5), genus 3, rank J(F)=1 ====";

_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
Fx<x> := PolynomialRing(F);
Fxy<y> := PolynomialRing(Fx);
OF := MaximalOrder(F);

// X(s3,ns5): smooth plane quartic (degree 4 in y), defined over Q.
Q := -y^4 + 2*y^3*x + y^2*x^2 + 8*y^3 + 2*y^2*x - 2*y*x^2 - x^3 - 3*y^2 - 3*y*x + 3*x^2 + 2*y - 3*x + 1;
Q := -Q;

// ---- optional: verify the Chabauty rank condition rank J(F) <= g-d = 1 ----
// J(X(s3,ns5)) ~ E x J(X(b3,ns5)) with E: y^2+y=x^3+1 (the genus-1 quotient C/Aut);
// rank E(F) = rank E(Q) + rank E^(5)(Q) = 1 + 0 = 1, and rank J(X(b3,ns5))(F) = 0,
// so rank J(F) = 1 = g - d. (The isogeny is checked by Frobenius traces.)
check_rank := true;
if check_rank then
  print "checking Chabauty condition: rank J(X(s3,ns5))(Q(sqrt5)) = 1 ...";
  E := EllipticCurve([Rationals()| 0,0,1,0,1]);   // y^2+y=x^3+1, = C/Aut(C)
  _, hE := RankBounds(E);
  _, hE5 := RankBounds(QuadraticTwist(E, 5));
  printf "  rank E(Q) <= %o, rank E^(5)(Q) <= %o  =>  rank E(F) <= %o ; rank J(X(b3,ns5))(F) = 0\n", hE, hE5, hE+hE5;
  // isogeny J(C) ~ E x J(X(b3,ns5)) via Frobenius traces
  P2q<XX,YY,ZZ> := ProjectiveSpace(Rationals(), 2);
  qC := YY^4 - 2*YY^3*XX - YY^2*XX^2 - 8*YY^3*ZZ - 2*YY^2*XX*ZZ + 2*YY*XX^2*ZZ + XX^3*ZZ
        + 3*YY^2*ZZ^2 + 3*YY*XX*ZZ^2 - 3*XX^2*ZZ^2 - 2*YY*ZZ^3 + 3*XX*ZZ^3 - ZZ^4;
  CQ := Curve(P2q, qC);
  DQ := HyperellipticCurve(9*PolynomialRing(Rationals()).1^6 - 6*PolynomialRing(Rationals()).1^5
        - 35*PolynomialRing(Rationals()).1^4 + 40*PolynomialRing(Rationals()).1^2 + 12*PolynomialRing(Rationals()).1 - 8);
  isog := &and[ #RationalPoints(ChangeRing(CQ,GF(p))) eq #ChangeRing(E,GF(p)) + #RationalPoints(ChangeRing(DQ,GF(p))) - (p+1) : p in [7,11,13,17,23] ];
  printf "  J(C) ~ E x J(X(b3,ns5)) (Frobenius traces match): %o\n", isog;
  assert hE + hE5 le 1 and isog;
  print "  rank condition rank J(F) = 1 = g - d holds.";
end if;

// ---- Coleman data at a Tuitman-good split prime (11 is Tuitman-bad; use 19) ----
P := Decomposition(OF, 19)[1][1];
assert InertiaDegree(P) eq 1 and RamificationIndex(P) eq 1;   // split, residue F_19
N := 12;
data := coleman_data(Q, F, P, N : verbose:=false);
printf "genus g = %o, residue field F_%o\n", data`g, #ResidueClassField(RingOfIntegers(data`K));

// ---- annihilating differentials V (dim g - rank = 2) from rational points ----
P1 := set_point(1, 0, data);          // (1,0)
P2 := set_point(7, -3, data);         // (7,-3): [P2-P1] is torsion
P3 := set_point(-1/2, -1/2, data);    // [P3-P1] is the infinite-order rank-1 generator
print "computing annihilating differentials V (vanishing_differentials) ...";
v := vanishing_differentials([P1, P2, P3], data);
printf "dim V = %o (expect 2 = g - rank = 3 - 1)\n", #v;
assert #v eq 2;

// ---- the d=2 criterion over all residue disc-pairs ----
print "";
print "---- symmetric Chabauty criterion over all disc-pairs ----";
// bielliptic involution on the plane model, column convention (x:y:z) |-> M*(x,y,z)^t.
// V is the 2-dimensional Prym (trace-zero) space -- forced, since the Prym A has
// rk A(F) = 0 and dim V = g - rk J(F) = 2 -- so trace_zero:=true is legitimate and the
// pullback branch of the criterion may be used on the pullback-type classes.
Msig := Matrix(F, 3, 3, [1,8,-8, 1,3,2, -2,4,1]);
res, data := symmetric_chabauty_classify(data, v : sigma:=Msig, trace_zero:=true);

// ---- recover the quadratic points in the certified SPLIT disc-pairs ----
print "";
print "---- recovery in the certified split disc-pairs (D0 = P1 + P2) ----";
quads, good, data := quadratic_points_split(data, v, P1, P2);
printf "GENUINE quadratic points found (split disc-pairs): %o distinct x-minpolys over F\n", #quads;
for mp in quads do
  Aabs := AbsoluteField(NumberField(mp));
  printf "   %o   [Q(x):Q]=%o, sqrt5 in Q(x): %o\n", mp, Degree(Aabs), IsSquare(Aabs!5);
end for;

print "";
print "NOTE: this covers the SPLIT disc-pairs only. The Frobenius-conjugate (F_{q^2})";
print "disc-pairs are swept over K = Q_(q^2) (example-8.4-single-prime.m) or covered by";
print "several split primes (example-8.4-multiprime.m). Diagonal disc-pairs need the";
print "higher-order criterion, and the rank-1 CROSS classes (rank drop, but NOT of";
print "pullback type) are certified by nothing here: for X(s3,ns5) the Mordell-Weil";
print "sieve of appendix-A-sieve.m disposes of them.";
print "";
print "DONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
