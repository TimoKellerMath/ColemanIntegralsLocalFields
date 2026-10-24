// tests/magma/unit-frobenius.m   [unit test: the Frobenius matrix of coleman_data]
//
//     magma -b tests/magma/unit-frobenius.m          (from the repository root; about 40 s)
//     magma -b quick:=1 tests/magma/unit-frobenius.m (cases 1-3 only; about 1 s)
//
// The matrix F of the q-power Frobenius on H^1_dR(X) computed by coleman_data must have
// characteristic polynomial T^(2g) L(1/T), where L(T) is the numerator of the zeta function
// of the reduction of X over the residue field F_q of K.  coleman_data itself only checks
// that the characteristic polynomial is rational, satisfies the functional equation and has
// det = +-q^g; here it is compared with L(T) computed independently by Magma's point counting.
// Cases: K = Q_p; K unramified of degree 2 (the p-power lift and its semilinear composition);
// K ramified of degree 2 with a curve whose coefficients are not rational; a plane quartic.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
SetColumns(0);
SetLogFile(assigned quick select "tests/magma/unit-frobenius-quick.log" else "tests/magma/unit-frobenius.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

// compare the characteristic polynomial of data`F (top-left 2g x 2g block) with T^(2g) L(1/T),
// coefficientwise up to valuation thresh in K
compare := function(data, Lpoly)
  g := data`g;
  FK := ChangeRing(Submatrix(data`F, 1, 1, 2*g, 2*g), data`m);
  cp := CharacteristicPolynomial(FK);
  thresh := Maximum(1, data`N div 2);          // genuine errors show up at small valuation
  a := Coefficients(Lpoly) cat [0 : i in [1..2*g+1]];
  worst := Infinity();
  for k in [0..2*g] do
    v := Valuation(Coefficient(cp, 2*g-k) - a[k+1]);
    worst := Minimum(worst, v);
  end for;
  return worst ge thresh, worst, thresh;
end function;

Qx<X> := PolynomialRing(Rationals());

// ---- 1. genus 2 over Q_7
QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
f := x*(x-1)*(x+1)*(x-2)*(x+3);
Q := y^2 - f;
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
data := coleman_data(Q, QQ, P7, 10 : verbose := false);
Lp := LPolynomial(HyperellipticCurve(PolynomialRing(GF(7))!Eltseq(f)));
ok, v, t := compare(data, Lp);
check("genus 2 over Q_7: charpoly(F) = T^4 L(1/T)" cat (ok select "" else Sprintf("  (agreement only to v = %o < %o)", v, t)), ok, ~nfail);

// ---- 2. the same curve over K = Q_49 (7 inert in Q(sqrt 3)): F is the 49-power Frobenius
L2<s> := NumberField(X^2 - 3);
L2x<x2> := PolynomialRing(L2); L2xy<y2> := PolynomialRing(L2x);
Q2 := y2^2 - x2*(x2-1)*(x2+1)*(x2-2)*(x2+3);
P49 := Decomposition(MaximalOrder(L2), 7)[1][1];
assert InertiaDegree(P49) eq 2;
data2 := coleman_data(Q2, L2, P49, 10 : verbose := false);
Lp2 := LPolynomial(HyperellipticCurve(PolynomialRing(GF(49))!Eltseq(f)));
ok, v, t := compare(data2, Lp2);
check("genus 2 over Q_49 (f_K = 2): charpoly(F_q) = T^4 L(1/T) over F_49" cat (ok select "" else Sprintf("  (agreement only to v = %o < %o)", v, t)), ok, ~nfail);

// ---- 3. a curve with non-rational coefficients over a ramified K = Q_7(sqrt 7)
L3<w> := NumberField(X^2 - 7);
L3x<x3> := PolynomialRing(L3); L3xy<y3> := PolynomialRing(L3x);
Q3 := y3^2 - (x3^5 + w*x3^2 + 1);                 // reduction mod sqrt 7: y^2 = x^5 + 1 over F_7
P3 := Decomposition(MaximalOrder(L3), 7)[1][1];
assert RamificationDegree(P3) eq 2;
data3 := coleman_data(Q3, L3, P3, 12 : verbose := false);
Lp3 := LPolynomial(HyperellipticCurve(PolynomialRing(GF(7))![1,0,0,0,0,1]));
ok, v, t := compare(data3, Lp3);
check("genus 2 over Q_7(sqrt 7) (e_K = 2): charpoly(F) = T^4 L(1/T) of y^2 = x^5+1" cat (ok select "" else Sprintf("  (agreement only to v = %o < %o)", v, t)), ok, ~nfail);

// ---- 4. a plane quartic (genus 3) over Q_19: the model of X(s3,ns5) from Appendix A (19 is a
//      good prime for it).  Skipped in quick mode (magma -b quick:=1 ...).
if not assigned quick then
Q4 := y^4 - 2*x*y^3 - x^2*y^2 - 8*y^3 - 2*x*y^2 + 2*x^2*y + x^3 + 3*y^2 + 3*x*y - 3*x^2 - 2*y + 3*x - 1;
P19 := Decomposition(MaximalOrder(QQ), 19)[1][1];
data4 := coleman_data(Q4, QQ, P19, 6 : verbose := false);
P2<XX,YY,ZZ> := ProjectiveSpace(GF(19), 2);
C19 := Curve(P2, YY^4 - 2*XX*YY^3 - XX^2*YY^2 - 8*YY^3*ZZ - 2*XX*YY^2*ZZ + 2*XX^2*YY*ZZ + XX^3*ZZ
       + 3*YY^2*ZZ^2 + 3*XX*YY*ZZ^2 - 3*XX^2*ZZ^2 - 2*YY*ZZ^3 + 3*XX*ZZ^3 - ZZ^4);
Lp4 := Numerator(ZetaFunction(C19));
ok, v, t := compare(data4, Lp4);
check("plane quartic (genus 3) over Q_19: charpoly(F) = T^6 L(1/T)" cat (ok select "" else Sprintf("  (agreement only to v = %o < %o)", v, t)), ok, ~nfail);
end if;

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
