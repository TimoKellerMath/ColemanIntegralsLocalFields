// appendix-A-generators.m          [Appendix A, steps (i) and (iii): generators of J(C)(F)]
//
// Determines J(C)(F)_tors and the subgroup Gamma of the Mordell-Weil sieve, for
// C = X(s3,ns5) over F = Q(sqrt 5).
//
//   t_10 has order 10 and the class
//        z := c_spor + fam = [ Delta_20 + phi^*(P_E) - 2 D_0 ]
//   is TORSION of order exactly 120 -- this is proved here, not guessed:
//   IsPrincipal(120*z) is verified on C over F itself, and red_q(z) has order 120.
//   TWO generators suffice.  Since 5*t_10, the element of order 2 in <t_10>, is not
//   in <z> after reduction,
//        T := < t_10, z >    has order  at least  2 * 120 = 240,
//   while |J(C)(F)_tors| divides gcd_q |J(C)(F_q)| = 240 over the split primes.  Hence
//        J(C)(F)_tors = < t_10, c_spor + fam >  =  Z/2 + Z/120.
//   Neither D_6 nor the Steiner 2-torsion class eta is needed as a generator: both are
//   automatically contained in T (D_6 has order 3 and the 3-primary part Z/3 of T is
//   cyclic, hence inside <z>), so the sieve needs no computation of bitangents.
//
//   Because z is torsion, c_spor and fam are equal up to sign and torsion, so
//        Gamma := Z c_spor + J(C)(F)_tors = < t_10, z, c_spor >
//   already contains every known class.  Writing J(C)(F)/tors = Z*ghat and
//   c_spor = beta*ghat, fam = -beta*ghat (mod torsion), the identity
//   phi_* phi^* = 2 forces  beta * gamma = -2  where phi_*(ghat) = gamma*P_E.
//   Therefore
//        [ J(C)(F) : Gamma ] = |beta|  divides 2,
//   which is exactly what the sieve needs (the map j = 2*iota_2 lands in Gamma).
//   The script also runs the local 2-divisibility test that would rule out the
//   value 2; it does not, so the index is left as "1 or 2" and the sieve keeps the
//   safe multiplier I = 2.
SetColumns(0); SetLogFile("appendix-A-generators.log" : Overwrite);
load "appendix-A-common.m";

// ================================================================ 0.  rk J(C)(F) = 1
E := EllipticCurve([Rationals()| 0,0,1,0,1]);        // y^2 + y = x^3 + 1, Cremona 225a1
EF := BaseChange(E, F);
GE, mGE := MordellWeilGroup(EF);
printf "E(F) = %o  (rank %o, torsion %o)\n", Invariants(GE), Rank(EF), Invariants(TorsionSubgroup(EF));
assert Rank(EF) eq 1;
// J(C) ~ E x E_75a x E_75c with rk E_75a(F) = rk E_75c(F) = 0 (see the article), so
printf "=> rk J(C)(F) = 1, and the Chabauty condition g - rk = 3 - 1 = 2 holds.\n\n";

// ================================================================ 1.  the global classes
P2F<X,Y,Z> := ProjectiveSpace(F,2);
CF := Curve(P2F, qcoef(X,Y,Z));
pt := function(P) return CF ! [ P[1], P[2], P[3] ]; end function;
mkdiv := function(mp)                   // the degree-2 divisor { mp(x)=0, y = c0+c1 x }
  c0, c1 := yparts(mp);
  return Divisor(CF, Scheme(P2F, [ Coefficient(mp,0)*Z^2 + Coefficient(mp,1)*X*Z + X^2,
                                   Y - c0*Z - c1*X ]));
end function;
D0    := Divisor(pt(D0pts[1])) + Divisor(pt(D0pts[2]));
Dt10  := Divisor(pt(CFpts[2])) - Divisor(pt(CFpts[1]));                 // t_10
DD6   := Divisor(pt(D6pts[1])) + Divisor(pt(D6pts[2])) - D0;            // D_6
Dspor := mkdiv(cspor_mp) - D0;                                          // c_spor
Dfam  := mkdiv(fam_mp)   - D0;                                          // fam
Dz    := Dspor + Dfam;                                                  // z
assert &and[ Degree(D) eq 0 : D in [Dt10, DD6, Dspor, Dfam, Dz] ];

printf "=== orders of the torsion generators, certified on C over F ===\n";
// D_6 is NOT a generator (it lies in <z>; see below), but its order is cheap to certify
// and the divisor is used as a known class of K_2, so it is checked here as well.
for tp in [ <"t_10", Dt10, 10>, <"z = c_spor + fam", Dz, 120>, <"D_6 (redundant)", DD6, 3> ] do
  t0 := Cputime();
  ok := IsPrincipal(tp[3]*tp[2]);
  printf "  %o * (%o) is principal: %o   (%o s)\n", tp[3], tp[1], ok, Cputime(t0);
  assert ok;
end for;
printf "  => t_10, z are torsion of order dividing 10, 120 (and D_6 of order dividing 3).\n";
printf "  (c_spor and fam themselves have infinite order: see the growing orders below.)\n\n";

// ================================================================ 2.  the torsion subgroup
printf "=== J(C)(F)_tors: lower bound from T = <t_10, z>, upper bound from reduction ===\n";
ords := []; Tinv := []; ok240 := true; ntest := 0; nfail := 0; failq := [];
for qq in PrimesInInterval(11,300) do
  if qq eq 5 or LegendreSymbol(5,qq) ne 1 then continue; end if;
  L := LocalData(qq);
  if not (L`ok and L`cspor_ok and L`fam_ok) then continue; end if;
  Cl := L`Cl;
  nJ := #TorsionSubgroup(Cl);          // Pic^0(C_q)(F_q) = J(C_q)(F_q); Cl itself has a Z-factor
  Append(~ords, nJ);
  T := L`tors;
  Append(~Tinv, Invariants(T));
  Zz := sub< Cl | L`ztor >;
  printf "  q=%-4o |J(C)(F_q)|=%-9o ord(t_10)=%-3o ord(z)=%-4o 5*t_10 in <z>: %-5o D_6 in <z>: %-5o |T|=%-4o T=%o ord(c_spor)=%o\n",
     qq, nJ, Order(L`t10), Order(L`ztor), 5*L`t10 in Zz, L`D6 in Zz, #T, Invariants(T), Order(L`cspor);
  assert (5*L`t10 notin Zz) and (L`D6 in Zz);
  if #T ne 240 then ok240 := false; end if;
  // local 2-divisibility test for the index (used in part 3 below)
  twoJ := sub< Cl | [ 2*h : h in Generators(Cl) ] >;
  S2 := sub< Cl | Setseq(Generators(twoJ)) cat Setseq(Generators(T)) >;
  ntest +:= 1;
  if not (L`cspor in S2) then nfail +:= 1; Append(~failq, qq); end if;
end for;
g := GCD(ords);
printf "\n  gcd of |J(C)(F_q)| over the split good primes q < 300 : %o\n", g;
printf "  |red_q(T)| = 240 at every one of them             : %o\n", ok240;
printf "  all invariants equal                              : %o  (%o)\n",
   #{ Sprint(i) : i in Tinv } eq 1, Tinv[1];
assert g eq 240 and ok240;
printf "\n  Reduction is injective on the torsion of an abelian variety with good\n";
printf "  reduction at an odd unramified prime, so |J(C)(F)_tors| divides %o; and T is\n", g;
printf "  a subgroup of J(C)(F)_tors whose reduction already has order 240.  Hence\n";
printf "  ==>  J(C)(F)_tors = T = < t_10, c_spor + fam >  =  %o   (order 240)\n", Tinv[1];
printf "  (5*t_10 is not in <z> at any of these primes, so |T| >= 2*120 = 240; and D_6,\n";
printf "   of order 3, always lies in <z>, so it is redundant as a generator.)\n\n";
printf "  In particular J(C)(F)[2] = (Z/2)^2, and the Steiner class eta, a 2-torsion\n";
printf "  class, lies in T: it is NOT an extra generator.\n\n";

// ================================================================ 3.  Gamma and its index
printf "=== Gamma = Z c_spor + J(C)(F)_tors ===\n";
printf "  z = c_spor + fam is torsion, so fam = -c_spor + z lies in Gamma:\n";
printf "  Gamma = < t_10, z, c_spor > = < t_10, D_6, c_spor, fam > contains every known\n";
printf "  Mordell-Weil class (D_6 in <z> and fam = -c_spor + z).\n";
printf "  Write J(C)(F)/tors = Z*ghat, c_spor = beta*ghat, phi_*(ghat) = gamma*P_E.\n";
printf "  phi_* phi^* = 2 gives phi_*(fam) = 2*P_E + tors, and fam = -c_spor + tors,\n";
printf "  so beta*gamma = -2 and therefore  [J(C)(F) : Gamma] = |beta| divides 2.\n\n";
printf "  local 2-divisibility test (would give index 1 if it ever failed):\n";
for qq in failq do printf "    q=%-4o c_spor NOT in 2*J(C)(F_q) + tors  =>  index 1\n", qq; end for;
printf "    %o split primes tested, %o of them rule out index 2.\n", ntest, nfail;
if nfail eq 0 then
  printf "    => the index is not decided locally; the sieve keeps the SAFE multiplier I = 2,\n";
  printf "       i.e. j = 2*iota_2 : C^(2)(F) -> Gamma, and takes\n";
  printf "          H_q^rob := { y in J(C)(F_q) : 2y in red_q(Gamma) }  as the ambient group,\n";
  printf "       which contains red_q(J(C)(F)) whichever of the two values the index has.\n";
else
  printf "    => [J(C)(F) : Gamma] = 1, so the multiplier 2 in jmath = 2*iota_2 and the\n";
  printf "       passage to H_q^rob would both be unnecessary.\n";
end if;
print "\nDONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
