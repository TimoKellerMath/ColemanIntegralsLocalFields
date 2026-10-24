// appendix-A-covering.m     [Appendix A: the bielliptic covering phi : C -> E and the
//                        pullbacks D_0 = phi^*(O_E) and phi^*(P_E) = "fam"]
//
// C = X(s3,ns5) is the smooth plane quartic of the example over F = Q(sqrt 5),
// sigma the bielliptic involution induced by M = [[1,8,-8],[1,3,2],[-2,4,1]]
// (M^2 = 25*I), and E = C/<sigma> the elliptic curve y^2 + y = x^3 + 1 (225a1).
//
// phi is written down explicitly, by diagonalising sigma on the canonical plane
// instead of calling CurveQuotient:
//
//   * sigma acts on points by p |-> M*p, hence on linear forms by l |-> l*M.  The
//     row eigenvectors of M are l_1 = X + 4Y and l_2 = 2Y + Z (eigenvalue 5) and
//     l_3 = X - 2Y + 2Z (eigenvalue -5), so in the coordinates
//         (u : v : w) = (l_1 : l_2 : l_3)
//     one has sigma(u:v:w) = (u:v:-w) and the quartic becomes EVEN in w:
//        3w^4 - (46u^2-96uv+84v^2)w^2 - (43u^4-336u^3v+1012u^2v^2-1344uv^3+688v^4) = 0.
//   * completing the square in w^2, with
//         eta := (3w^2 - 23u^2 + 48uv - 42v^2)/10,
//     that relation reads  eta^2 = 4u^4 - 12u^3v + 12u^2v^2 - 3v^4.  Hence
//         C --> H : Y^2 = -3z^4 + 12z^2 - 12z + 4,     z = v/u,  Y = eta/u^2,
//     is the quotient map by sigma, onto a genus-1 curve H.
//   * P_1 = (1,0) has (u:v:w) = (1:1:3) and eta = 1, so its image on H is (z,Y) = (1,1);
//     taking THAT point as the origin puts H in Weierstrass form with phi(P_1) = O_E,
//     and the minimal model is exactly y^2 + y = x^3 + 1.
//
// A quotient map determines E only up to the choice of an origin and up to [-1].
// Both choices are pinned down here:
//        phi(P_1) = O_E     and     phi^*(P_E) = the divisor "fam" below,
// P_E = ((-3s+5)/2, 3s-8) being the free generator of E(F).  The script verifies
//        D_0 := phi^*(O_E)  = (1,0) + (7,-3),
//        phi^*(P_E)         = { x^2 - (6s+34)x - 18s - 26 = 0,  y = ((s-1)x - 2s - 2)/8 },
// the second being fam_mp of appendix-A-common.m.  It also prints phi^*(-P_E), the
// divisor one gets from the other choice of sign (its class is -D_fam).
//
// Run:  magma appendix-A-covering.m        (output: appendix-A-covering.log)

SetColumns(0); SetLogFile("appendix-A-covering.log" : Overwrite);

Qt<T>  := PolynomialRing(Rationals());
F<s>   := NumberField(T^2 - 5);
Fx<xx> := PolynomialRing(F);

// ---------------------------------------------------------------- 1. C and sigma
P2<X,Y,Z> := ProjectiveSpace(F,2);
qcoef := func< X,Y,Z | Y^4 - 2*Y^3*X - Y^2*X^2 - 8*Y^3*Z - 2*Y^2*X*Z + 2*Y*X^2*Z + X^3*Z
      + 3*Y^2*Z^2 + 3*Y*X*Z^2 - 3*X^2*Z^2 - 2*Y*Z^3 + 3*X*Z^3 - Z^4 >;
C := Curve(P2, qcoef(X,Y,Z));
printf "genus(C) = %o\n", Genus(C);
assert Genus(C) eq 3;

MM := Matrix(Rationals(),3,3,[1,8,-8, 1,3,2, -2,4,1]);
assert MM^2 eq 25*IdentityMatrix(Rationals(),3);
sig := iso< C -> C | [ X + 8*Y - 8*Z, X + 3*Y + 2*Z, -2*X + 4*Y + Z ],
                     [ X + 8*Y - 8*Z, X + 3*Y + 2*Z, -2*X + 4*Y + Z ] >;
printf "sigma^2 = id : %o\n", (sig*sig) eq IdentityMap(C);

printf "row eigenvectors of M (l |-> l*M):\n";
for lam in [5,-5] do
  printf "  eigenvalue %o : %o\n", lam,
     [ Eltseq(b) : b in Basis(Kernel(MM - lam*IdentityMatrix(Rationals(),3))) ];
end for;
u := X + 4*Y;          // l_1, eigenvalue  5
v := 2*Y + Z;          // l_2, eigenvalue  5
w := X - 2*Y + 2*Z;    // l_3, eigenvalue -5
p0 := [F| -4, 1, -2 ];                       // isolated fixed point of sigma
assert Evaluate(u,p0) eq 0 and Evaluate(v,p0) eq 0 and Evaluate(w,p0) ne 0;
assert Evaluate(qcoef(X,Y,Z), p0) ne 0;
printf "p_0 = (-4:1:-2) is the common zero of <l_1,l_2> and is not on C\n";

// ---------------------------------------------------------------- 2. the quotient
eta := (3*w^2 - 23*u^2 + 48*u*v - 42*v^2)/10;
printf "eta^2 = 4u^4-12u^3v+12u^2v^2-3v^4 holds on C : %o\n",
   (eta^2 - (4*u^4 - 12*u^3*v + 12*u^2*v^2 - 3*v^4)) in Ideal(C);

H := HyperellipticCurve(-3*xx^4 + 12*xx^2 - 12*xx + 4);
printf "genus(H) = %o\n", Genus(H);
// H sits in P(1,2,1) with coordinates (x : Y : z); C -> H, (X:Y:Z) |-> (uv : eta*u^2 : u^2)
psi := map< C -> H | [ u*v, eta*u^2, u^2 ] >;
P1 := C![1,0,1];  P2p := C![7,-3,1];
assert sig(P1) eq P2p;
printf "psi(P_1) = %o   (the origin we use on H)\n", psi(P1);

EW,   mEW  := EllipticCurve(H, H![1,1,1]);        // origin = psi(P_1)
E,    mmin := MinimalModel(EW);
printf "C/<sigma> = %o\n", E;
printf "a-invariants %o ; equals y^2+y=x^3+1 : %o\n",
   aInvariants(E), aInvariants(E) eq [F| 0,0,1,0,1 ];
EQ := EllipticCurve([Rationals()| 0,0,1,0,1]);
printf "over Q : conductor %o, Cremona %o\n", Conductor(EQ), CremonaReference(EQ);

// the remaining [-1]-ambiguity; the sign below is the one matching fam_mp
AE  := Ambient(E);
neg := map< E -> E | [ AE.1, -AE.2 - AE.3, AE.3 ] >;     // (x:y:z) |-> (x:-y-z:z)
phi := Expand(psi * mEW * mmin * neg);
printf "\ndeg(phi) = %o ; phi o sigma = phi : %o ; phi(P_1) = %o\n",
   Degree(phi), Expand(sig*phi) eq phi, phi(P1);
printf "defining polynomials of phi:\n";
for g in DefiningPolynomials(phi) do printf "   %o\n", g; end for;
// the same map in closed form, off the line X + 2Y - Z = 0:
//    x = -(X^2+3XY+Y^2-4XZ-2YZ+2Z^2)/(X+2Y-Z)^2,
//    y = -(X^3+9X^2Y+21XY^2+12Y^3-3X^2Z-18XYZ-12Y^2Z+6YZ^2+Z^3)/(X+2Y-Z)^3.
R3<XX3,YY3,ZZ3> := PolynomialRing(F,3);
den  := XX3 + 2*YY3 - ZZ3;
numx := -(XX3^2 + 3*XX3*YY3 + YY3^2 - 4*XX3*ZZ3 - 2*YY3*ZZ3 + 2*ZZ3^2);
numy := -(XX3^3 + 9*XX3^2*YY3 + 21*XX3*YY3^2 + 12*YY3^3 - 3*XX3^2*ZZ3 - 18*XX3*YY3*ZZ3
          - 12*YY3^2*ZZ3 + 6*YY3*ZZ3^2 + ZZ3^3);
dps := [ Evaluate(g, [XX3,YY3,ZZ3]) : g in DefiningPolynomials(phi) ];
printf "closed form agrees with DefiningPolynomials(phi) : %o\n",
   dps eq [ numx*den, numy, den^3 ];
CFpts := [ [F| 1,0,1], [F| 7,-3,1], [F| -1,-1,2], [F| 1,0,0],
           [F| (s-1)/2, -s+2, 1],    [F| (3*s+9)/2, (-s-1)/2, 1],
           [F| (-3*s+9)/2, (s-1)/2, 1], [F| (-s-1)/2, s+2, 1] ];
printf "phi on C(F) (closed form vs. Magma):\n";
for P in CFpts do
  dd := Evaluate(den, P);
  if dd eq 0 then
    printf "   %o -> O_E (on the line X+2Y-Z = 0) ; Magma: %o\n", P, phi(C!P);
  else
    ptE := E ! [ Evaluate(numx,P)/dd^2, Evaluate(numy,P)/dd^3 ];
    printf "   %o -> %o ; agrees: %o\n", P, ptE, ptE eq phi(C!P);
    assert ptE eq phi(C!P);
  end if;
end for;

// ---------------------------------------------------------------- 3. the pullbacks
xminpoly := function(pl)
  pt := RepresentativePoint(pl);
  mp := MinimalPolynomial(pt[1]/pt[3], F);
  return mp / LeadingCoefficient(mp);
end function;
describe := procedure(D)
  for t in Decomposition(D) do
    pl := t[1]; pt := RepresentativePoint(pl);
    if Degree(pl) eq 1 then
      printf "      rational point (%o, %o), multiplicity %o\n", pt[1]/pt[3], pt[2]/pt[3], t[2];
    else
      // y as a polynomial in x: the coordinates are given in the power basis of the
      // residue field, whose generator need NOT be x (so printing cs[1] + cs[2]*xx would
      // be wrong).
      xs := Eltseq(pt[1]/pt[3]); ys := Eltseq(pt[2]/pt[3]);
      assert #xs eq 2 and xs[2] ne 0;
      printf "      degree-2 place: x-minpoly %o ,  y = %o\n", xminpoly(pl),
             ys[1] + ys[2]*(xx - xs[1])/xs[2];
    end if;
  end for;
end procedure;

PE := E![ (-3*s+5)/2, 3*s-8 ];          // free generator of E(F)
TE := E![ 0, (-s-1)/2 ];                // 3-torsion generator
G, mG := MordellWeilGroup(E);
printf "\nE(F) = %o ; ord(P_E) = %o ; ord(T_E) = %o\n", Invariants(G), Order(PE), Order(TE);

D0 := Pullback(phi, Place(Identity(E)));
printf "\nD_0 = phi^*(O_E), degree %o :\n", Degree(D0);  describe(D0);
printf "   phi^*(O_E) = (1,0) + (7,-3) : %o\n", D0 eq Place(P1) + Place(P2p);
assert D0 eq Place(P1) + Place(P2p);

famtarget := xx^2 - (6*s+34)*xx - 18*s - 26;          // fam_mp of appendix-A-common.m
for t in [ <"P_E", PE>, <"-P_E", -PE> ] do
  D   := Pullback(phi, Place(t[2]));
  dec := Decomposition(D);
  printf "\nphi^*(%o) = phi^*(%o), degree %o :\n", t[1], t[2], Degree(D);  describe(D);
  printf "   x-minpoly = x^2-(6s+34)x-18s-26 (= fam_mp) : %o\n",
     #dec eq 1 and Degree(dec[1][1]) eq 2 and xminpoly(dec[1][1]) eq famtarget;
end for;
DF := Pullback(phi, Place(PE));
assert xminpoly(Decomposition(DF)[1][1]) eq famtarget;
printf "\n[phi^*(P_E) - D_0] + [phi^*(-P_E) - D_0] is principal : %o\n",
   IsPrincipal(DF + Pullback(phi, Place(-PE)) - 2*D0);

// ---------------------------------------------------------------- 4. summary
printf "\n=== summary ===\n";
printf "  phi : C -> E : y^2+y = x^3+1 is the composite\n";
printf "        (X:Y:Z) |-> (z, xi) = ( (2Y+Z)/(X+4Y),  eta/(X+4Y)^2 )  in H,\n";
printf "        eta = (3(X-2Y+2Z)^2 - 23(X+4Y)^2 + 48(X+4Y)(2Y+Z) - 42(2Y+Z)^2)/10,\n";
printf "        followed by the Weierstrass map of H : Y^2 = -3z^4+12z^2-12z+4 based\n";
printf "        at the image (1,1) of P_1, and by [-1].\n";
printf "  D_0 := phi^*(O_E) = (1,0) + (7,-3) = P_1 + P_2, P_2 = sigma(P_1);\n";
printf "  phi^*(P_E) = the degree-2 divisor  x^2 - (6s+34)x - 18s - 26 = 0,  y = ((s-1)x - 2s - 2)/8;\n";
printf "  D_fam = [phi^*(P_E) - D_0] = phi^*([P_E - O_E]);\n";
printf "  closed form:  x = -(X^2+3XY+Y^2-4XZ-2YZ+2Z^2)/(X+2Y-Z)^2,\n";
printf "                y = -(X^3+9X^2Y+21XY^2+12Y^3-3X^2Z-18XYZ-12Y^2Z+6YZ^2+Z^3)/(X+2Y-Z)^3.\n";
printf "\nDONE\n";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
