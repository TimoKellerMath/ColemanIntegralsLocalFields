load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
load "solver.m"; load "symmetric_chabauty.m";
SetColumns(0);
SetLogFile("example-8.4-multiprime.log" : Overwrite);
SetVerbose("User1", 1); // the progress of the solver (verbosity level 1 of the library's flag)

print "==== multi-prime split recovery: quadratic points on X(s3,ns5)/Q(sqrt5) ====";
_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
Fx<x> := PolynomialRing(F); Fxy<y> := PolynomialRing(Fx); OF := MaximalOrder(F);
FXc<XX> := PolynomialRing(F);   // common ring to hold minpolys across primes
Q := -y^4 + 2*y^3*x + y^2*x^2 + 8*y^3 + 2*y^2*x - 2*y*x^2 - x^3 - 3*y^2 - 3*y*x + 3*x^2 + 2*y - 3*x + 1; Q := -Q;
N := 12;

// split, Tuitman-good primes of F = Q(sqrt5)
primes := [19, 29, 31, 41, 59, 61, 71, 79];
allquads := {FXc | };
perprime := [];
for p in primes do
  try
    P := Decomposition(OF, p)[1][1];
    if InertiaDegree(P) ne 1 then printf "p=%o not split, skip\n", p; continue; end if;
    tt := Cputime();
    data := coleman_data(Q, F, P, N : verbose:=false);
    P1 := set_point(1, 0, data); P2 := set_point(7, -3, data); P3 := set_point(-1/2, -1/2, data);
    v := vanishing_differentials([P1,P2,P3], data);
    quads := quadratic_points_split(data, v, P1, P2 : verbose:=false);
    quads := { FXc!mp : mp in quads };
    new := quads diff allquads;
    allquads := allquads join quads;
    Append(~perprime, <p, #quads, #new, #allquads>);
    printf "p=%-3o: %2o found, %2o new, running union %2o  (%o s)\n", p, #quads, #new, #allquads, Cputime(tt);
  catch e
    printf "p=%o: FAILED (%o)\n", p, e`Object;
  end try;
end for;

print "";
printf "==== UNION over %o primes: %o distinct quadratic points (x-minpoly over F) ====\n", #perprime, #allquads;
// numbered as the 35 affine sporadic divisors in the table of the article (the list mps of
// appendix-A-common.m), further points after them by length (a fixed order, independent of
// the order in which the primes find the points)
Fold := F;
load "appendix-A-common.m";
table := [FXc | [Fold | Eltseq(c) : c in Coefficients(mp)] : mp in mps];
printf "the union is the set of the 35 divisors of the table of the article: %o\n", Seqset(table) eq allquads;
sorted := [mp : mp in table | mp in allquads] cat Sort([mp : mp in allquads | mp notin table], func< a,b | #Sprint(a) - #Sprint(b) >);
i := 0;
for mp in sorted do
  i +:= 1;
  Aabs := AbsoluteField(NumberField(mp));
  printf "%2o: %o   [Q(x):Q]=%o, sqrt5: %o\n", i, mp, Degree(Aabs), IsSquare(Aabs!5);
end for;

print "";
print "stabilization (new points added per prime):";
for t in perprime do printf "  p=%-3o: +%o new (union %o)\n", t[1], t[3], t[4]; end for;
print "DONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
