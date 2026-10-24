SetColumns(0);
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

SetLogFile("tests/library/test-symchab-Xb3ns5.log" : Overwrite);

print "==== d=2 symmetric Chabauty: X(b3,ns5) / Q(sqrt5), rank J(F)=0 ====";

_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
Fx<x> := PolynomialRing(F);
Fxy<y> := PolynomialRing(Fx);
OF := MaximalOrder(F);

P := Decomposition(OF, 11)[1][1];   // 11 splits in F: residue F_11, F_P = Q_11 (f=1)
assert InertiaDegree(P) eq 1 and RamificationIndex(P) eq 1;
N := 15;

Q := y^2 - (9*x^6 - 6*x^5 - 35*x^4 + 40*x^2 + 12*x - 8);   // genus 2, /Q

// ---- optional: verify the Chabauty rank condition rank J(F) <= g-2 = 0 ----
// rank J(Q(sqrt5)) = rank J(Q) + rank J^{(5)}(Q) (quadratic-twist decomposition).
check_rank := true;
if check_rank then
  print "checking Chabauty condition: rank J(Q(sqrt5)) = 0 ...";
  Qx<xQ> := PolynomialRing(Rationals());
  fQ := 9*xQ^6 - 6*xQ^5 - 35*xQ^4 + 40*xQ^2 + 12*xQ - 8;
  CQ := HyperellipticCurve(fQ);
  _, h0 := RankBounds(Jacobian(CQ));
  _, h5 := RankBounds(Jacobian(QuadraticTwist(CQ, 5)));
  printf "  rank J(Q) <= %o, rank J^{(5)}(Q) <= %o  =>  rank J(Q(sqrt5)) <= %o\n", h0, h5, h0+h5;
  assert h0 + h5 le 0;  // need rank <= g-2 = 0
  print "  rank condition rank J(F) = 0 holds (V = full holomorphic space).";
end if;

data := coleman_data(Q, F, P, N : verbose:=false);

res, data := quadratic_points_genus2_rank0(data);

print "";
print "---- per-pair classification ----";
printf "certified (<=1 quadratic point) : %o disc-pair(s)\n", #res`certified;
printf "pullback locus (rank drop)      : %o disc-pair(s)\n", #res`pullback;
for t in res`pullback do
  printf "   pullback %o: discs (%o,%o), x mod P = %o\n",
     t[1], t[2], t[3], res`xbar[t[2]];
end for;

print "";
print "---- Phase 2: Frobenius-conjugate (F_{q^2}) disc-pairs ----";
ncert, npull, nbadc, ninfc, pull := conjugate_disc_criterion(data);
printf "conjugate: %o certified, %o pullback (rank drop), %o bad, %o infinite\n",
   ncert, npull, nbadc, ninfc;
print "pullback (rank-drop) conjugate places -- expect all 'type-b' (x0 in F_q):";
for t in pull do
  printf "   x0 = %o,  x0 in F_q (inert hyperelliptic pair) = %o\n", t[1], t[2];
end for;

print "";
print "---- combined classification over X(b3,ns5)/Q(sqrt5) at P|11 ----";
printf "certified disc-pairs (<=1 quadratic point): %o (split+diag) + %o (conjugate) = %o\n",
   #res`certified, ncert, #res`certified + ncert;
printf "pullback-locus disc-pairs (parametrised family): %o (split) + %o (conjugate) = %o\n",
   #res`pullback, npull, #res`pullback + npull;
printf "remaining gap: %o bad/infinite finite-disc(s) + %o bad/inf degree-2 place(s)\n",
   res`nbad, nbadc + ninfc;

print "";
print "---- Phase 3: recovery -- find the quadratic points in the certified split/diagonal disc-pairs ----";
// base divisor D0 = R1 + R2, two F-rational GOOD points with distinct x
// (from the 9 points of C(F): x = (s-1)/2 and (-s-1)/2, y != 0).
R1 := set_point((s-1)/2,  5*(s-1)/2, data);
R2 := set_point((-s-1)/2, 5*(s+1)/2, data);
printf "base divisor D0 = R1 + R2 with x(R1)=(s-1)/2, x(R2)=(-s-1)/2\n";

cand := recovery_candidates_rank0(data, res, R1, R2);
fF := PolynomialRing(F)![Coefficient(9*x^6 - 6*x^5 - 35*x^4 + 40*x^2 + 12*x - 8, i) : i in [0..6]];
quads := {}; rats := {}; spur := 0; unrec := 0;
for t in cand do
  found, mp, knd := recover_point_in_pair(t, res`good, data, fF);
  if not found then if knd eq "spurious" then spur +:= 1; else unrec +:= 1; end if; continue; end if;
  if knd eq "quadratic" then Include(~quads, mp); else Include(~rats, mp); end if;
end for;
printf "recovered from %o certified split/diagonal disc-pairs: %o genuine quadratic, %o rational-pair classes, %o spurious, %o unrecognized.\n",
   #cand, #quads, #rats, spur, unrec;
print "GENUINE sporadic quadratic points (x-minpoly over F, f(x) verified square):";
for mp in quads do
  Aabs := AbsoluteField(NumberField(mp));
  printf "   %o   [Q(x):Q]=%o, sqrt5 in Q(x): %o\n", mp, Degree(Aabs), IsSquare(Aabs!5);
end for;
print "rational-pair classes (sums of two F-points): ", rats;

print "";
print "---- Phase 4: the general driver quadratic_points_split (V = all holomorphic forms), also in the finite bad discs ----";
// the diagonal disc-pairs are solved in the symmetric functions of the disc parameters; with
// include_bad the four finite bad discs (the Weierstrass discs of y^2 = f mod 11) are added,
// which gives a sixth point, x^2 - (3s+5)/6*x + (3s+1)/6, in the pair of a good and a bad disc
quadsB, goodB := quadratic_points_split(data, [[1,0],[0,1]], R1, R2 : include_bad := true);
Fpol := PolynomialRing(F);
verified := func< mp | IsSquare(Evaluate(fF, quo< Fpol | Fpol!mp >.1)) >;
printf "%o genuine quadratic points in the split, diagonal and bad disc-pairs (%o discs), all verified on the curve: %o\n",
   #quadsB, #goodB, &and[ verified(mp) : mp in quadsB ];
for mp in quadsB do printf "   %o\n", mp; end for;
assert #quadsB eq 6 and &and[ verified(mp) : mp in quadsB ];
assert { Fpol!mp : mp in quads } subset { Fpol!mp : mp in quadsB };  // Phase 3's points are among them

print "";
print "NOTE: the 62 Frobenius-conjugate (F_{q^2}) disc-pairs and the infinite discs are treated by";
print "curve_quadratic_points over K = Q_(11^2), see tests/examples/quadratic-points-Xb3ns5.m.";
print "";
print "DONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
