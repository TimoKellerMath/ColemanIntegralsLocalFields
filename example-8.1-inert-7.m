// ---------------------------------------------------------------------------
// example-8.1-inert-7.m
//
// Example 8.1 recomputed at an INERT prime, where it is a genuine f_K = 3 problem.
//
// The curve and points of Example 8.1 are exactly Section 6 of Siksek, "Explicit
// Chabauty over number fields": C_s over K = Q(2^(1/3)), with Mordell-Weil
// generators (for s = 1)
//     D1 = (-t^2-t-1, -(40t^2+53t+67)) - infty,   D2 = (-1, 3t+3) - infty,
// used to solve the GENERALIZED FERMAT equation x^2 + y^3 = z^10.  His criterion
// T n = A z (mod p^{2s}) is built from the period integrals tau_j = int_{D_j} omega
// over the completion K_v -- these are NOT tiny integrals.
//
// Example 8.1 as printed uses P | 109, which is TOTALLY SPLIT, so K_v = Q_109 and
// the computation never leaves Q_p. Here we take P | 7, which is INERT in
// Z[2^(1/3)], so K_v = Q_(7^3) and the tau_j are genuinely K-valued with f_K = 3.
//
// coleman_data uses the 7-power (tau-semilinear) Frobenius lift, three steps of which
// compose to the 343-power lift. Q(2^(1/3))/Q is not Galois, so the Frobenius tau of
// K_v = Q_(7^3) is not induced by an automorphism of the number field (L in the code);
// it is applied through the completion, modulo P^Nmax (frobenius_aut_local in
// frobenius.m). The 343-power lift (lift:="q") gives the same integrals to the same
// precision, but takes about 45 s instead of under a second.
// ---------------------------------------------------------------------------
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
SetColumns(0);
SetLogFile("example-8.1-inert-7.log" : Overwrite);
Qx0<T0> := PolynomialRing(Rationals());
L<a> := NumberField(T0^3-2);
OL := MaximalOrder(L);
for p in [7,13,19,37] do
  D := Decomposition(OL,p);
  printf "p = %o : (e,f) = %o\n", p, [<RamificationDegree(d[1]),InertiaDegree(d[1])> : d in D];
end for;
PP := [ d[1] : d in Decomposition(OL,7) | InertiaDegree(d[1]) eq 3 ][1];
Lx<x> := PolynomialRing(L); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - 3*(4*(1-a)^(-1)*x^5 - (1-a)^2);
N := 12;
tt := Cputime();
data := coleman_data(Q, L, PP, N : verbose:=false);
printf "coleman_data: %o s ; genus %o ; residue field F_%o ; [K:Q_7] = %o\n",
  Cputime(tt), data`g, #ResidueClassField(RingOfIntegers(data`K)), AbsoluteDegree(data`K);
printf "Frobenius lift: x -> x^%o, n_tau = %o; the Frobenius of K is applied %o\n", data`qtau, data`ntau,
  (data`ntau eq 1) select "nowhere (q-power lift)" else
  ((data`tauprec gt 0) select Sprintf("through the completion, modulo P^%o (no automorphism of L induces it)", data`tauprec)
  else "by an automorphism of L");
P1  := set_point(-a^2-a-1, 40*a^2+53*a+67, data);
P1d := set_point(-a^2-a-1, -(40*a^2+53*a+67), data);
P2  := set_point(-1, 3*a+3, data);
P2d := set_point(-1, -(3*a+3), data);
printf "is_bad: P1 %o, P1' %o, P2 %o, P2' %o\n", is_bad(P1,data), is_bad(P1d,data), is_bad(P2,data), is_bad(P2d,data);
g := data`g;
print "\n---- Siksek's period integrals tau_j, now over K = Q_(7^3) ----";
sd := 0;
for nmpt in [<"P1'",P1d>, <"P2",P2>, <"P2'",P2d>] do
  I, NI, sd := coleman_integrals_on_basis(P1, nmpt[2], data : side1:=sd, return_side:=true, verbose:=false);
  printf "int_{P1}^{%o} (precision %o):\n", nmpt[1], NI;
  for i in [1..g] do
    e := Eltseq(data`K ! I[i]);
    printf "   omega_%o : %o\n            in Q_7: %o ; weakly zero: %o\n",
       i, I[i], &and[ IsWeaklyZero(e[j]) : j in [2..#e] ], IsWeaklyZero(I[i]);
  end for;
end for;
print "\nDONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
