// ---------------------------------------------------------------------------
// example-8.4-single-prime.m
//
// SINGLE-PRIME complete recovery of the sporadic quadratic points of
// C = X(s3,ns5) over F = Q(sqrt5), including the Frobenius-conjugate ("inert")
// residue disc-pairs, by running the symmetric-Chabauty recovery over the
// UNRAMIFIED QUADRATIC EXTENSION K = Q_{19^2} of F_r = Q_19.
//
// Over K a conjugate disc-pair is an ordinary split disc-pair, so the whole
// disc-pair sweep -- F_r-split and F_r-conjugate alike -- is done at the single
// prime r | 19. This is impossible with Coleman integration over Q_p only, and
// replaces the eight-prime covering of example-8.4-multiprime.m (each quadratic point
// splits at only about half the primes, so no finite set of split primes proves
// completeness).
//
// The auxiliary field only has to realise K: any L = F(sqrt u) with u a
// non-residue mod 19 works, independently of the points to be found. We take
// u = 2.  The recognition target is O_F: the symmetric functions x1+x2, x1*x2
// of an F-rational degree-2 divisor are Galois-fixed, hence lie in F.
// ---------------------------------------------------------------------------

load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
load "solver.m"; load "symmetric_chabauty.m";

SetColumns(0);
SetLogFile("example-8.4-single-prime.log" : Overwrite);
SetVerbose("User1", 1); // the progress of the solver (verbosity level 1 of the library's flag)

_<T> := PolynomialRing(Rationals());
F<s0> := NumberField(T^2-5); OF := MaximalOrder(F);
Frel := ext<F | PolynomialRing(F).1^2 - 2>;        // 2 is a non-residue mod 19
L<tL> := AbsoluteField(Frel); OL := MaximalOrder(L);
sL := [ rr[1] : rr in Roots(PolynomialRing(L)![-5,0,1]) ][1];
Dec := [ dd[1] : dd in Decomposition(OL,19) | RamificationDegree(dd[1]) eq 1 and InertiaDegree(dd[1]) eq 2 ];
PP := Dec[1];
printf "L = %o ;  P | 19 with (e,f) = (%o,%o)  ==>  K = Q_(19^2)\n",
   DefiningPolynomial(L), RamificationDegree(PP), InertiaDegree(PP);

Lx<x> := PolynomialRing(L); Lxy<y> := PolynomialRing(Lx);
Q := -y^4 + 2*y^3*x + y^2*x^2 + 8*y^3 + 2*y^2*x - 2*y*x^2 - x^3 - 3*y^2 - 3*y*x + 3*x^2 + 2*y - 3*x + 1;
Q := -Q;

N := 16;
tt := Cputime();
data := coleman_data(Q, L, PP, N : verbose:=false);
printf "coleman_data: %o s ; g = %o ; residue field F_%o\n",
   Cputime(tt), data`g, #ResidueClassField(RingOfIntegers(data`K));

P1 := set_point(L!1, L!0, data);
P2 := set_point(L!7, L!(-3), data);
P3 := set_point(L!(-1/2), L!(-1/2), data);
V := vanishing_differentials([P1,P2,P3], data);
printf "dim V = %o\n", #V;
assert #V eq 2;

basisF := [ L | 1, (1+sL)/2 ];      // Z-basis of O_F inside L

tt := Cputime();
quads, good, data := quadratic_points_split(data, V, P1, P2 : basis:=basisF, htbound:=10^6);
printf "\nrecovery: %o s ; %o distinct x-minpolys over F\n", Cputime(tt), #quads;

// report: rewrite the F-rational coefficients in terms of s = sqrt5, and split
// the points into F_r-split and F_r-conjugate (= inert) disc-pairs at r | 19.
Fpol<XF> := PolynomialRing(F);
V2 := VectorSpace(Rationals(), Degree(L));
Mat := Matrix(Rationals(), [ Eltseq(L!1), Eltseq(sL) ]);
toF := function(c)
  ok, sol := IsConsistent(Mat, V2 ! Eltseq(L!c));
  error if not ok, "coefficient is not in F";
  return F ! (sol[1] + sol[2]*s0);
end function;
r19 := Decomposition(OF,19)[1][1];
k19, red19 := ResidueClassField(RingOfIntegers(F) !! r19);
mpsF := []; nsplit := 0; nconj := 0;
for mp in quads do
  m2 := Fpol ! [ toF(c) : c in Coefficients(mp) ];
  Append(~mpsF, m2);
  dsc := Discriminant(m2);
  isspl := (Valuation(dsc, r19) eq 0) and IsSquare(red19(dsc));
  if isspl then nsplit +:= 1; else nconj +:= 1; end if;
  printf "  %-52o  disc-pair at 19: %o\n", m2, isspl select "split" else "CONJUGATE (inert)";
end for;
printf "\n%o quadratic points recovered at the single prime 19:  %o in split disc-pairs, %o in Frobenius-conjugate disc-pairs\n",
   #mpsF, nsplit, nconj;
printf "(the %o conjugate ones are exactly those invisible to the Q_p-only recovery)\n", nconj;

// cross-check against the published list of 35 affine sporadic points (Section 9),
// as a Gal(F/Q)-stable set
pub := [ Fpol |
 XF^2 - 11*XF - 47, XF^2 - XF - 2*s0 - 2, XF^2 - XF + 2*s0 - 2, XF^2 - 3/2*XF + 63/2,
 XF^2 - 59/7*XF + 25/7, XF^2 - 27/28*XF + 1/4, XF^2 - 23/7*XF + 47/28,
 XF^2 + (s0+6)*XF + 8*s0 + 4, XF^2 + (-s0+6)*XF - 8*s0 + 4,
 XF^2 + (6*s0-4)*XF - 12*s0 + 19, XF^2 + (-6*s0-4)*XF + 12*s0 + 19,
 XF^2 + (11*s0-47)/8*XF - 4*s0 + 9, XF^2 + (14*s0-27)/3*XF - 6*s0 + 14,
 XF^2 + (-11*s0-47)/8*XF + 4*s0 + 9, XF^2 + (-14*s0-27)/3*XF + 6*s0 + 14,
 XF^2 + (7*s0+17)/2*XF - 62*s0 - 146, XF^2 + (33*s0-68)/2*XF - 33*s0 + 69,
 XF^2 + (-7*s0+17)/2*XF + 62*s0 - 146, XF^2 + (-33*s0-68)/2*XF + 33*s0 + 69,
 XF^2 + (-2*s0-19)/2*XF + (s0+25)/4, XF^2 + (2*s0-19)/2*XF + (-s0+25)/4,
 XF^2 + (3*s0-7)/6*XF + (-6*s0-10)/3, XF^2 + (-3*s0-7)/6*XF + (6*s0-10)/3,
 XF^2 + (5*s0-17)/2*XF + (67*s0-149)/2, XF^2 + (-5*s0-17)/2*XF + (-67*s0-149)/2,
 XF^2 + (7*s0-176)/79*XF + (76*s0+256)/79, XF^2 + (-51*s0+97)/62*XF + (147*s0-327)/62,
 XF^2 + (51*s0+97)/62*XF + (-147*s0-327)/62, XF^2 + (-7*s0-176)/79*XF + (-76*s0+256)/79,
 XF^2 + (-137*s0-223)/82*XF + (59*s0+603)/82, XF^2 + (137*s0-223)/82*XF + (-59*s0+603)/82,
 XF^2 + (-283*s0+479)/24*XF + (181*s0-179)/24, XF^2 + (283*s0+479)/24*XF + (-181*s0-179)/24,
 XF^2 + (-793*s0-1663)/82*XF + (991*s0+2123)/82, XF^2 + (793*s0-1663)/82*XF + (-991*s0+2123)/82 ];
conj := hom< F -> F | -s0 >;
cpoly := func< f | Fpol ! [ conj(c) : c in Coefficients(f) ] >;
pubset := { f : f in pub } join { cpoly(f) : f in pub };
found := { f : f in mpsF };
printf "\nfound but NOT in the published 35 (or their conjugates): %o\n", found diff pubset;
printf "published-35 members recovered at 19 alone: %o of 35\n",
   #{ f : f in pub | (f in found) or (cpoly(f) in found) };
printf "\nDONE\n";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
