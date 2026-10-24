// ---------------------------------------------------------------------------
// test-plift.m
//
// The p-power (tau-semilinear) Frobenius lift over a number field L that has NO
// automorphism inducing the Frobenius at P (L/Q not Galois). Then coleman_data applies
// the Frobenius tau of K = L_P through the completion, modulo P^(Nmax+1)
// (frobenius_aut_local), instead of falling back to the q-power lift. The Coleman
// integrals must agree with those of the q-power lift to the reported precision.
//
//  (1) L = Q(b), b^3 = b+1 (discriminant -23, not Galois), 3 inert: K = Q_27, f_K = 3.
//      The nodal model y^2 = (x-b)^2 (x^5-x+b^2) has W^0 = diag(1, 1/(x-b)), so the
//      conjugation of W^0 in froblift meets a denominator with a non-rational root.
//  (2) L = Q(2^(1/3)) at the prime of degree 2 above 5 (5 = P1*P2): K = Q_25, f_K = 2,
//      with a second prime above p; y^2 = x^5-x+b^2, including the endpoint at infinity.
//  (3) The map sigma_N itself: on the field of (1) it induces tau and sigma_N^3 = id
//      modulo P^prec, also for elements with v_P < 0; on the cyclic cubic Q(zeta_7)^+
//      (3 inert) it agrees with the global Frobenius automorphism, and the integrals
//      computed with either ("p" and "plocal") agree.
// The integrals of all lifts are recorded in test-plift.results (tests/magma/results.m).
// ---------------------------------------------------------------------------
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/library/test-plift.log" : Overwrite);
RF := "tests/library/test-plift.results";
results_start(RF);

Qx0<T0> := PolynomialRing(Rationals());

// coleman_data with the lift "lf", and the integrals from the first point to the others
// (and to the point at infinity if withinf)
lift_integrals := function(Q, L, PP, N, lf, pts, withinf)
  p := Characteristic(ResidueClassField(PP)); f := InertiaDegree(PP);
  data := coleman_data(Q, L, PP, N : verbose:=false, lift:=lf);
  printf "lift \"%o\": x -> x^%o, n_tau = %o, Frobenius of K applied %o; Nmax = %o\n", lf, data`qtau, data`ntau,
    (data`ntau eq 1) select "nowhere (q-power lift)" else
    ((data`tauprec gt 0) select Sprintf("through the completion modulo P^%o", data`tauprec) else "by an automorphism of L"),
    data`Nmax;
  if lf eq "q" then
    assert data`ntau eq 1 and data`qtau eq p^f;
  else
    assert data`ntau eq f and data`qtau eq p;
    assert (data`tauprec gt 0) eq ((lf eq "plocal") or #Automorphisms(L) eq 1);
  end if;
  P := [ set_point(pt[1], pt[2], data) : pt in pts ];
  tgts := P[2..#P];
  if withinf then
    Append(~tgts, set_bad_point(0, [1] cat [0 : i in [2..Degree(Q)]], true, data));
  end if;
  res := [* *];
  sd := 0;
  for T in tgts do
    I, NI, sd := coleman_integrals_on_basis(P[1], T, data : side1:=sd, return_side:=true, verbose:=false);
    Append(~res, <I, NI>);
  end for;
  return data, res;
end function;

// v_K(I1 - I2) for integral vectors computed over two copies of K (different Nmax):
// the second one is lifted to L and mapped into the first copy
vdiff := function(I1, data1, I2, data2)
  return Minimum([ Valuation((data1`K!I1[i]) - data1`m((data2`K!I2[i]) @@ data2`m)) : i in [1..#Eltseq(I1)] ]);
end function;

compare := function(name, Q, L, PP, N, lifts, pts, withinf)
  p := Characteristic(ResidueClassField(PP)); f := InertiaDegree(PP);
  printf "\n==== %o ====\n", name;
  printf "L = Q[T]/(%o), #Aut(L) = %o, p = %o, decomposition (e,f) = %o, K = L_P = Q_(%o^%o)\n",
    DefiningPolynomial(L), #Automorphisms(L), p,
    [ <RamificationDegree(d[1]),InertiaDegree(d[1])> : d in Decomposition(MaximalOrder(L),p) ], p, f;
  out := [* *];
  for lf in lifts do
    data, res := lift_integrals(Q, L, PP, N, lf, pts, withinf);
    Append(~out, <lf, data, res>);
  end for;
  printf "W^0 = %o\n", out[1][2]`W0;
  // print the integrals of the first lift, and compare all others with it
  _, data1, res1 := Explode(out[1]);
  for j in [1..#res1] do
    I1, N1 := Explode(res1[j]);
    target := (withinf and j eq #res1) select "infinity" else "P"*IntegerToString(j+1);
    record_result(RF, Sprintf("%o: int_P1^%o, lift %o", name, target, out[1][1]), I1 : precision := N1);
    printf "int_{P1}^{%o} (lift \"%o\", precision %o):\n", target, out[1][1], N1;
    for i in [1..#Eltseq(I1)] do
      printf "   omega_%o : %o\n", i, I1[i];
    end for;
    for k in [2..#out] do
      I2, N2 := Explode(out[k][3][j]);
      record_result(RF, Sprintf("%o: int_P1^%o, lift %o", name, target, out[k][1]), I2 : precision := N2);
      Nc := Minimum(N1, N2);
      v := vdiff(I1, data1, I2, out[k][2]);
      printf "   lift \"%o\": precision %o; v_K(difference) >= %o: %o\n", out[k][1], N2, Nc, v ge Nc;
      assert Nc ge 1 and v ge Nc;
    end for;
  end for;
  return true;
end function;

// (1) non-Galois cubic, f_K = 3, nodal model
L<b> := NumberField(T0^3-T0-1); OL := MaximalOrder(L);
PP := [ d[1] : d in Decomposition(OL,3) | InertiaDegree(d[1]) eq 3 ][1];
Lx<x> := PolynomialRing(L); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - (x-b)^2*(x^5-x+b^2);
pts := [ [L|0,b^2], [L|1,(1-b)*b], [L|-1,(1+b)*b], [L|0,-b^2], [L|1,-(1-b)*b] ];
_ := compare("(1) Q(b), b^3=b+1, P = (3), y^2 = (x-b)^2(x^5-x+b^2)", Q, L, PP, 10, ["p","q"], pts, false);

// (2) Q(2^(1/3)) at the prime of degree 2 above 5
L<b> := NumberField(T0^3-2); OL := MaximalOrder(L);
PP := [ d[1] : d in Decomposition(OL,5) | InertiaDegree(d[1]) eq 2 ][1];
Lx<x> := PolynomialRing(L); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - (x^5-x+b^2);
pts := [ [L|0,b], [L|1,b], [L|-1,b], [L|0,-b] ];
_ := compare("(2) Q(2^(1/3)), P | 5 of degree 2, y^2 = x^5-x+b^2", Q, L, PP, 10, ["p","q"], pts, true);

// (3) sigma_N itself
print "\n==== (3) the local Frobenius sigma_N ====";
prec := 12;
for fld in [ <T0^3-T0-1, "Q(b), b^3=b+1">, <T0^3+T0^2-2*T0-1, "Q(zeta_7)^+"> ] do
  L<b> := NumberField(fld[1]); OL := MaximalOrder(L);
  PP := [ d[1] : d in Decomposition(OL,3) | InertiaDegree(d[1]) eq 3 ][1];
  sig := frobenius_aut_local(L, PP, prec);
  glob := frobenius_aut(L, PP);
  K1, m1 := Completion(L, PP : Precision:=prec+10); // an independent copy of K, at higher precision
  els := [ L | 1, b, b^2-b+1, 1/(b+2), (b^2-b+5)/7, b/3, (1+b)^4/9, 3^5*b, 1/(b^2+3) ];
  ok := true;
  for c in els do
    v := Minimum(Valuation(m1(c)), 0);
    ok := ok and Valuation(m1(sig(c)) - FrobeniusImage(m1(c))) ge prec+v;   // sigma_N induces tau
    ok := ok and Valuation(m1(sig(sig(sig(c)))) - m1(c)) ge prec+v;          // sigma_N^3 = id
    if Type(glob) ne RngIntElt then
      ok := ok and Valuation(m1(sig(c) - glob(c))) ge prec+v;                // = the global automorphism
    end if;
  end for;
  printf "%o: global Frobenius automorphism %o; sigma_N (prec %o) = tau, sigma_N^3 = id%o on %o elements: %o\n",
    fld[2], (Type(glob) eq RngIntElt) select "does not exist" else "exists", prec,
    (Type(glob) eq RngIntElt) select "" else ", sigma_N = sigma", #els, ok;
  assert ok;
end for;
L<b> := NumberField(T0^3+T0^2-2*T0-1); OL := MaximalOrder(L);
PP := [ d[1] : d in Decomposition(OL,3) | InertiaDegree(d[1]) eq 3 ][1];
Lx<x> := PolynomialRing(L); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - (x-b)^2*(x^5-x+b^2);
pts := [ [L|0,b^2], [L|1,(1-b)*b], [L|-1,(1+b)*b], [L|0,-b^2] ];
_ := compare("(3) Q(zeta_7)^+, P = (3): global automorphism vs sigma_N", Q, L, PP, 10, ["p","plocal"], pts, false);

print "\nDONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
