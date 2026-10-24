// appendix-A-common.m
//
// Shared setup for the scripts belonging to Appendix A, Proposition A.5 (the symmetric-Chabauty /
// Mordell-Weil-sieve determination of C^(2)(F) for C = X(s3,ns5), F = Q(sqrt 5)).
//
//     load "appendix-A-common.m";
//
// It collects, once and for all, the data shared by the scripts of Appendix A:
//
//   * the plane quartic model of C and the bielliptic involution sigma;
//   * the base point p0 of the pencil of trace-zero differentials;
//   * the known F-rational divisors (C(F), D_6, Delta_20, the fibre of P_E, D_infty,
//     and the 35 affine sporadic divisors);
//   * LocalData(q): everything attached to a split prime q -- the reduction
//     C_q/F_q, its class group, the reductions of all the global classes above,
//     the subgroup H_q = red_q(Gamma) and the index-safe group
//     H_q^rob = { y : 2y in H_q } (which contains red_q(J(C)(F)) whichever of the
//     two possible values [J(C)(F):Gamma] has);
//   * DegreeTwoData(L): the classification of C_q^(2)(F_q) into the types
//     (a) / (b) / (c) of the example.

Qt<TT> := PolynomialRing(Rationals());
F<s>   := NumberField(TT^2 - 5);
OF     := MaximalOrder(F);
Fx<x>  := PolynomialRing(F);

// ---------------------------------------------------------------- the curve
qcoef := func< X,Y,Z | Y^4 - 2*Y^3*X - Y^2*X^2 - 8*Y^3*Z - 2*Y^2*X*Z + 2*Y*X^2*Z + X^3*Z
      + 3*Y^2*Z^2 + 3*Y*X*Z^2 - 3*X^2*Z^2 - 2*Y*Z^3 + 3*X*Z^3 - Z^4 >;
qaff  := func< X,Y | Y^4 - 2*Y^3*X - Y^2*X^2 - 8*Y^3 - 2*Y^2*X + 2*Y*X^2 + X^3
      + 3*Y^2 + 3*Y*X - 3*X^2 - 2*Y + 3*X - 1 >;

// sigma on (X:Y:Z) (row-vector convention: a linear form ell has ell -> ell*MM)
MM  := Matrix(Rationals(),3,3,[1,8,-8, 1,3,2, -2,4,1]);
// the unique base point of the pencil { ell : ell(p0) = 0 } = Ker(Tr_phi)
p0Q := [Rationals() | -4, 1, -2 ];

// ---------------------------------------------------------------- known F-rational data
// C(F) has EIGHT points, not four.  The list { P1, P2, P3, Pinf } of the article is
// C(Q): the four further points have coordinates in F \ Q and come in two
// Galois-conjugate pairs over Q.  They were found by a search over
// x = (a + b*sqrt5)/c, |a| <= 40, |b| <= 25, c <= 12, and in particular the two points
// making up the class D_6 are individually F-rational, so D_6 is a splitting class.
// Missing them is what left the Mordell-Weil sieve with unaccounted classes whose
// reduction was always of the shape (1:0:0) + (an affine rational point).
CFpts  := [ [F| 1,0,1], [F| 7,-3,1], [F| -1,-1,2], [F| 1,0,0],
            [F| (s-1)/2, -s+2, 1],     [F| (3*s+9)/2, (-s-1)/2, 1],
            [F| (-3*s+9)/2, (s-1)/2, 1], [F| (-s-1)/2, s+2, 1] ];
// D_0 = P1 + P2 = phi^*(O_E), with phi normalised by phi(P1) = O_E (appendix-A-covering.m)
D0pts  := [ [F| 1,0,1], [F| 7,-3,1] ];
// D_6 = the conjugate pair of the two quadratic points of the 3-torsion fibre
D6pts  := [ [F| (s-1)/2, -s+2, 1], [F| (3*s+9)/2, (-s-1)/2, 1] ];

// Delta_20 (the sporadic divisor used as c_spor) and the fibre phi^*(P_E) (fam)
cspor_mp := x^2 + (-2*s-19)/2*x + (s+25)/4;
fam_mp   := x^2 + (-6*s-34)*x - 18*s - 26;

// the 35 affine sporadic divisors of the example, by their x-coordinate minimal polynomial
mps := [ x^2 - 11*x - 47, x^2 - x - 2*s - 2, x^2 - x + 2*s - 2, x^2 - 3/2*x + 63/2,
  x^2 - 59/7*x + 25/7, x^2 - 27/28*x + 1/4, x^2 - 23/7*x + 47/28, x^2 + (s+6)*x + 8*s + 4,
  x^2 + (-s+6)*x - 8*s + 4, x^2 + (6*s-4)*x - 12*s + 19, x^2 + (-6*s-4)*x + 12*s + 19,
  x^2 + (11*s-47)/8*x - 4*s + 9, x^2 + (14*s-27)/3*x - 6*s + 14, x^2 + (-11*s-47)/8*x + 4*s + 9,
  x^2 + (-14*s-27)/3*x + 6*s + 14, x^2 + (7*s+17)/2*x - 62*s - 146, x^2 + (33*s-68)/2*x - 33*s + 69,
  x^2 + (-7*s+17)/2*x + 62*s - 146, x^2 + (-33*s-68)/2*x + 33*s + 69, x^2 + (-2*s-19)/2*x + (s+25)/4,
  x^2 + (2*s-19)/2*x + (-s+25)/4, x^2 + (3*s-7)/6*x + (-6*s-10)/3, x^2 + (-3*s-7)/6*x + (6*s-10)/3,
  x^2 + (5*s-17)/2*x + (67*s-149)/2, x^2 + (-5*s-17)/2*x + (-67*s-149)/2, x^2 + (7*s-176)/79*x + (76*s+256)/79,
  x^2 + (-51*s+97)/62*x + (147*s-327)/62, x^2 + (51*s+97)/62*x + (-147*s-327)/62, x^2 + (-7*s-176)/79*x + (-76*s+256)/79,
  x^2 + (-137*s-223)/82*x + (59*s+603)/82, x^2 + (137*s-223)/82*x + (-59*s+603)/82, x^2 + (-283*s+479)/24*x + (181*s-179)/24,
  x^2 + (283*s+479)/24*x + (-181*s-179)/24, x^2 + (-793*s-1663)/82*x + (991*s+2123)/82, x^2 + (793*s-1663)/82*x + (-991*s+2123)/82 ];

// D_infty = (1 : 1+sqrt2 : 0) + (1 : 1-sqrt2 : 0).  On C the line Z = 0 cuts out
// 2*(1:0:0) + D_infty, which is how D_infty is reduced below -- no square root needed.

// (x0,y0) with y0 = c0 + c1*x0 for a root x0 of mp: the standard encoding of a
// degree-2 divisor of C by its x-coordinate minimal polynomial.
yparts := function(mp)
  L<al> := ext<F|mp>;
  yr := Roots(qaff(al, PolynomialRing(L).1));
  ys := Eltseq(yr[1][1]);
  return ys[1], (#ys ge 2 select ys[2] else F!0);
end function;
c0cs, c1cs := yparts(cspor_mp);
c0fm, c1fm := yparts(fam_mp);


// ---------------------------------------------------------------- local data at a split prime
LocFmt := recformat< q, ok, k, mk, P2k, Cq, Cl, mCl, D0q, rd, rpt, reddeg2,
                     t10, D6, cspor, fam, ztor, tors, Hp, Hrob, Dinf, ratclasses,
                     cspor_ok, fam_ok >;

// LocalData(q): q must be split in F and of good reduction for C (q <> 3,5).  The
// prime of F above q is chosen so that Delta_20 splits in the residue field (the
// sieve wants c_spor to have a split reduction).
LocalData := function(qq)
  discc := ((-2*s-19)/2)^2 - 4*(s+25)/4;
  if qq in {2,3,5} or LegendreSymbol(5,qq) ne 1 then
    return rec< LocFmt | q := qq, ok := false >;      // not a split prime of good reduction
  end if;
  Decs  := Decomposition(OF, qq);
  rdsq := function(P)
    k0, mk0 := ResidueClassField(P);
    den := LCM([ Denominator(co) : co in Eltseq(discc) ]);
    return IsSquare(mk0(OF!(discc*den))/(k0!den));
  end function;
  // Prefer the prime above q for which Delta_20 splits in the residue field; if
  // neither does, any of the two will do -- the
  // projective reduction reddeg2 below handles an inert Delta_20 as well.
  Pp := Decs[1][1];
  if not rdsq(Pp) then Pp := Decs[2][1]; end if;
  if not rdsq(Pp) then Pp := Decs[1][1]; end if;
  k, mk := ResidueClassField(Pp);
  P2k := ProjectiveSpace(k,2);
  Cq  := Curve(P2k, qcoef(P2k.1,P2k.2,P2k.3));
  if not IsNonsingular(Cq) then return rec< LocFmt | q := qq, ok := false >; end if;
  Cl, mCl := ClassGroup(Cq);
  R1 := Cq![1,0,1]; R2 := Cq![7,-3,1];
  D0q := 1*Place(R1) + 1*Place(R2);

  rd := function(c)
    den := LCM([ Denominator(co) : co in Eltseq(c) ]);
    return mk(OF!(c*den))/(k!den);
  end function;
  rpt := function(P) return Cq![ rd(P[1]), rd(P[2]), rd(P[3]) ]; end function;

  // ---- reduction of a degree-2 divisor, done PROJECTIVELY -----------------------
  // The divisor { mp(x) = 0, y = c0 + c1*x } is the complete intersection
  //     G1 = X^2 + a*X*Z + b*Z^2 = 0,   G2 = Y - c1*X - c0*Z = 0
  // inside P^2.  Reducing the two forms after scaling them to be PRIMITIVE at the
  // prime Pp (content of valuation 0) reduces the schematic closure, so this also
  // works when the x-coordinate has a pole at Pp (the divisor then meets the line at
  // infinity) and when mp acquires a double root mod q (the divisor becomes 2*point).
  // (A naive affine reduction fails in both cases.)
  _, pi := IsPrincipal(Pp);           // F = Q(sqrt5) has class number 1
  primred := function(cfs)            // reduce a list of coefficients of F, primitively
    D := LCM([ Integers() | LCM([ Denominator(co) : co in Eltseq(c) ]) : c in cfs ]);
    ints := [ OF | c*D : c in cfs ];
    m := Min([ Valuation(c, Pp) : c in ints | c ne 0 ]);
    return [ mk(OF!(c/pi^m)) : c in ints ];
  end function;
  reddeg2 := function(mp)
    c0, c1 := yparts(mp);
    g1 := primred([ F | 1, Coefficient(mp,1), Coefficient(mp,0) ]);       // X^2, XZ, Z^2
    g2 := primred([ F | 1, -c1, -c0 ]);                                   // Y, X, Z
    XX := P2k.1; YY := P2k.2; ZZ := P2k.3;
    G1 := g1[1]*XX^2 + g1[2]*XX*ZZ + g1[3]*ZZ^2;
    G2 := g2[1]*YY + g2[2]*XX + g2[3]*ZZ;
    Sc := Scheme(P2k, [G1, G2]);
    if Dimension(Sc) ne 0 then return Cl!0, false; end if;
    Dv := Divisor(Cq, Sc);
    if Degree(Dv) ne 2 then return Cl!0, false; end if;
    return (Dv - D0q)@@mCl, true;
  end function;

  t10 := (1*Place(R2) - 1*Place(R1))@@mCl;
  D6  := (1*Place(rpt(D6pts[1])) + 1*Place(rpt(D6pts[2])) - D0q)@@mCl;
  cspor, cok := reddeg2(cspor_mp);
  fam,   fok := reddeg2(fam_mp);
  ztor  := cspor + fam;                   // the torsion class of order 120 (see appendix-A-generators.m)
  // D_6 is NOT needed as a generator: ord(z) = 120 is divisible by 3 and the 3-primary
  // part of J(C)(F)_tors = Z/2 + Z/120 is cyclic, so D_6 (of order 3) lies in <z>.
  // Hence J(C)(F)_tors = <t_10, z> and Gamma = <t_10, z, c_spor> (fam = z - c_spor).
  tors  := sub< Cl | t10, ztor >;         // = red_q(J(C)(F)_tors)
  Hp    := sub< Cl | t10, ztor, cspor >;  // = red_q(Gamma)
  assert D6 in tors;
  // H_q^rob = { y : 2y in red_q(Gamma) } contains red_q(J(C)(F)) whether the index
  // [J(C)(F) : Gamma] is 1 or 2 (appendix-A-generators.m); it is the index-safe ambient group.
  QH, mQH := quo< Cl | Hp >;
  Hrob := Kernel(hom< Cl -> QH | [ mQH(2*Cl.i) : i in [1..Ngens(Cl)] ] >);

  // D_infty = div(Z) - 2*(1:0:0)
  Dinf := (Divisor(Cq, Scheme(P2k, P2k.3)) - 2*Place(Cq![1,0,0]) - D0q)@@mCl;

  // the classes of the ten sums P+Q with P,Q in C(F)
  rp := [ rpt(P) : P in CFpts ];
  ratclasses := { (1*Place(rp[i]) + 1*Place(rp[j]) - D0q)@@mCl
                  : i in [1..#CFpts], j in [1..#CFpts] | i le j };

  return rec< LocFmt |
    q := qq, ok := true, k := k, mk := mk, P2k := P2k, Cq := Cq, Cl := Cl, mCl := mCl,
    D0q := D0q, rd := rd, rpt := rpt, reddeg2 := reddeg2,
    t10 := t10, D6 := D6, cspor := cspor, fam := fam, ztor := ztor,
    cspor_ok := cok, fam_ok := fok,
    tors := tors, Hp := Hp, Hrob := Hrob, Dinf := Dinf, ratclasses := ratclasses >;
end function;

// ---------------------------------------------------------------- the type (a)/(b)/(c) split
// For a degree-2 effective divisor Dt on C_q, write Dt = Q1 + Q2 over Fqbar.  Then
//   rk A(Dt) = 1  <=>  p0, Q1, Q2 are collinear     (tangency convention if Q1 = Q2)
//   Dt is a pullback  <=>  Q2 = sigma(Q1)
// (Step (ii) of the proof of Proposition A.5.)  Since gon(C_q) > 2, the Abel-Jacobi map
// C_q^(2)(F_q) -> Pic^2(C_q)(F_q) is injective, so the type is a property of the class.
//
// Returns: Aq (all classes of effective degree-2 divisors), famcl (type (b)), crosscl
// (type (c)), typ (AssociativeArray class -> "a"/"b"/"c"), tag (AssociativeArray
// class -> "split"/"diagonal"/"conjugate"), inf (AssociativeArray class -> at infinity?).
DegreeTwoData := function(L)
  k := L`k; Cq := L`Cq; Cl := L`Cl; mCl := L`mCl; D0q := L`D0q; P2k := L`P2k;
  Mk := ChangeRing(MM, k);
  sigpt := function(P)
    return Eltseq(Vector(Universe(P),P) * Transpose(ChangeRing(Mk, Universe(P))));
  end function;
  prop := function(a,b) return Rank(Matrix(Universe(a),2,3, a cat b)) eq 1; end function;
  coll := function(a,b,c) return Determinant(Matrix(Universe(a),3,3, a cat b cat c)) eq 0; end function;
  p0 := [ k | c : c in p0Q ];
  assert Evaluate(qcoef(P2k.1,P2k.2,P2k.3), p0) ne 0;   // p0 is not on C_q

  RR<XX,YY,ZZ> := PolynomialRing(k,3);
  fh   := qcoef(XX,YY,ZZ);
  grad := [ Derivative(fh,i) : i in [1..3] ];

  pls1 := Places(Cq,1); pls2 := Places(Cq,2);
  Aq := {}; famcl := {}; crosscl := {};
  typ := AssociativeArray(); tag := AssociativeArray(); inf := AssociativeArray();
  record := procedure(D, rk1, ispull, tg, atinf, ~Aq, ~famcl, ~crosscl, ~typ, ~tag, ~inf)
    c := (D - D0q)@@mCl;
    Include(~Aq, c);
    typ[c] := (not rk1) select "a" else (ispull select "b" else "c");
    tag[c] := tg; inf[c] := atinf;
    if rk1 and ispull then Include(~famcl, c); end if;
    if rk1 and not ispull then Include(~crosscl, c); end if;
  end procedure;
  isinf := function(pl) return Eltseq(RepresentativePoint(pl))[3] eq 0; end function;

  for i in [1..#pls1] do
    Pi := Eltseq(RepresentativePoint(pls1[i]));
    for j in [i+1..#pls1] do
      Pj := Eltseq(RepresentativePoint(pls1[j]));
      record(1*pls1[i]+1*pls1[j], coll(p0,Pi,Pj), prop(sigpt(Pi),Pj), "split",
             isinf(pls1[i]) or isinf(pls1[j]), ~Aq, ~famcl, ~crosscl, ~typ, ~tag, ~inf);
    end for;
    // the diagonal 2*P: rk <= 1 iff the tangent to C_q at P passes through p0
    gp := [ Evaluate(g, Pi) : g in grad ];
    record(2*pls1[i], (&+[ gp[t]*p0[t] : t in [1..3] ]) eq 0, prop(sigpt(Pi),Pi),
           "diagonal", isinf(pls1[i]), ~Aq, ~famcl, ~crosscl, ~typ, ~tag, ~inf);
  end for;
  for pl in pls2 do
    Q  := Eltseq(RepresentativePoint(pl)); F2 := Universe(Q);
    Qf := [ c^(#k) : c in Q ];
    record(1*pl, coll([F2|c : c in p0], Q, Qf), prop(sigpt(Q),Qf), "conjugate",
           isinf(pl), ~Aq, ~famcl, ~crosscl, ~typ, ~tag, ~inf);
  end for;
  return Aq, famcl, crosscl, typ, tag, inf;
end function;

// ---------------------------------------------------------------- known degree-2 divisors
// KnownList(L): the classes [D - D_0] of the elements of
//    K_2 = { P+Q : P,Q in C(F) }  u  { Delta_1,...,Delta_35 }  u  { D_infty },
// as a SEQUENCE, in a fixed order that is the same at every prime, so that a divisor
// can be followed from one prime to the next:
//    1..36  the 36 sums P+Q with P,Q in C(F)  (#C(F) = 8)
//    37     D_infty
//    38..72 Delta_1,...,Delta_35
// Each entry is < class, ok >; ok is false only if the reduction degenerated.
// KnownNames[j] names KnownList(L)[j].  The 36 sums are listed by NESTED LOOPS, exactly
// as in KnownList.  (Not as the comprehension [ ... : i in [1..8], j in [1..8] | i le j ]:
// in Magma the FIRST variable of a comprehension varies fastest, so it would list
// (1,1),(1,2),(2,2),(1,3),... and attach wrong names to 30 of the 36 sums.)
KnownNames := [];
for i in [1..#CFpts] do for j in [i..#CFpts] do
  Append(~KnownNames, "P" cat IntegerToString(i) cat "+P" cat IntegerToString(j));
end for; end for;
KnownNames := KnownNames cat [ "D_infty" ] cat [ "Delta_" cat IntegerToString(i) : i in [1..35] ];
KnownList := function(L)
  rp := [ L`rpt(P) : P in CFpts ];
  out := [];
  for i in [1..#CFpts] do for j in [i..#CFpts] do
    Append(~out, < (1*Place(rp[i]) + 1*Place(rp[j]) - L`D0q)@@L`mCl, true >);
  end for; end for;
  Append(~out, < L`Dinf, true >);
  for mp in mps do
    z, ok := L`reddeg2(mp);
    Append(~out, < z, ok >);
  end for;
  return out;
end function;

// KnownClasses(L): the same thing as a set, plus "did every divisor reduce well".
KnownClasses := function(L)
  KL := KnownList(L);
  return { e[1] : e in KL | e[2] }, &and[ e[2] : e in KL ];
end function;
