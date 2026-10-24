// appendix-A-rational-points.m        [C(F) for C = X(s3,ns5), F = Q(sqrt 5)]
//
// C(Q) = { (1,0), (7,-3), (-1/2,-1/2), (1:0:0) }.  Over F there are FOUR MORE points,
// in two Galois-conjugate pairs over Q:
//
//     ((s-1)/2, 2-s)        ((-s-1)/2, s+2)
//     ((-3s+9)/2, (s-1)/2)  ((3s+9)/2, (-s-1)/2)
//
// so #C(F) = 8.  In particular the two points whose sum is the torsion class D_6 are
// individually F-rational, and the set of splitting divisors { P+Q : P,Q in C(F) } has
// binom(8,2)+8 = 36 elements rather than 10.  The Mordell-Weil sieve of appendix-A-sieve.m
// needs all of them: without them, it would leave classes whose reductions are of the shape
// (1:0:0) + (an affine rational point).
//
// The search is over x = (a + b*sqrt5)/c; for each x the quartic f(x,Y) is factored
// over F and every linear factor gives a point.  Points at infinity are read off
// separately: f(X,Y,0) = Y^2*(Y^2 - 2XY - X^2), giving (1:0:0) in C(F) and the
// conjugate pair (1 : 1 +- sqrt2 : 0) = D_infty, which is not F-rational pointwise.
SetColumns(0); SetLogFile("appendix-A-rational-points.log" : Overwrite);
load "appendix-A-common.m";

A := 40; B := 25; Cd := 12;
Fy<Y> := PolynomialRing(F);
found := {};
for c in [1..Cd] do
  for a in [-A..A] do
    for b in [-B..B] do
      x0 := (a + b*s)/c;
      f := qaff(x0, Y);
      if f eq 0 then continue; end if;
      for fac in Factorisation(f) do
        if Degree(fac[1]) eq 1 then
          Include(~found, <x0, -Coefficient(fac[1],0)/Coefficient(fac[1],1)>);
        end if;
      end for;
    end for;
  end for;
end for;
printf "search over x = (a+b*sqrt5)/c with |a| <= %o, |b| <= %o, c <= %o\n", A, B, Cd;
printf "affine points of C(F): %o\n", #found;
for P in found do
  assert qaff(P[1], P[2]) eq 0;
  printf "   (%o, %o)%o\n", P[1], P[2],
     (P[1] in Rationals() and P[2] in Rationals()) select "   [in C(Q)]" else "";
end for;

P2F<X,Yv,Z> := ProjectiveSpace(F,2);
CF := Curve(P2F, qcoef(X,Yv,Z));
printf "\npoints at infinity (Z = 0) that are F-rational: %o\n",
   [ Eltseq(pt) : pt in Points(Scheme(CF, Z)) ];
printf "=> #C(F) = %o (%o affine + the point at infinity (1:0:0))\n", #found+1, #found;
printf "   of these, %o lie in C(Q).\n",
   #[ P : P in found | P[1] in Rationals() and P[2] in Rationals() ] + 1;

// the eight points as used by appendix-A-common.m
printf "\nCFpts of appendix-A-common.m reproduces exactly this set: %o\n",
   { <P[1],P[2]> : P in found } eq
   { <c[1]/c[3], c[2]/c[3]> : c in CFpts | c[3] ne 0 }
   and #[ c : c in CFpts | c[3] eq 0 ] eq 1;
print "DONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
