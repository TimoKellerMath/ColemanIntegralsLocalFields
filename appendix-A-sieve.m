// appendix-A-sieve.m       [Appendix A, steps (iv)-(vii): the Mordell-Weil sieve]
//
// Gamma  := Z*c_spor + J(C)(F)_tors  =  < c_spor, t_10, z >,  z = c_spor + fam,
//          ~  Z + Z/2 + Z/120,   [J(C)(F) : Gamma] divides 2   (appendix-A-generators.m),
// jmath  := 2 * iota_2 : C^(2)(F) -> Gamma,   D |-> 2[D - D_0],
// H      := intersection of the kernels of rho_q : Gamma -> J(C_q)(F_q), q in P',
// B      := Gamma/H,
// Y_q    := jmath_q(M_q) = { 2c : c in R_q^rob },
// W      := intersection over q of lambda_{H,q}^{-1}(Y_q).
//
// Only the INDEX-SAFE variant is run: [J(C)(F) : Gamma] is known only to divide 2, so
//   * the multiplier is 2, since 2*J(C)(F) <= Gamma makes jmath land in Gamma, and
//   * M_q is built from H_q^rob = { y : 2y in red_q(Gamma) }, which contains
//     red_q(J(C)(F)) for either value of the index:
//         R_q^rob := ( A_q cap H_q^rob ) \ iota_{2,q}( phi_q^*(E_q(F_q)) ),
//         Y_q     := { 2c : c in R_q^rob }   subset  red_q(Gamma).
// Doubling alone would NOT be safe: red_q(iota_2(D)) for a global D need not lie in
// red_q(Gamma).  (A sharper variant, with multiplier 1 and ambient red_q(Gamma), would
// only be valid if the index is 1; the index-safe run proves the result on its own.)
//
// STEP (vii), the identification of the surviving classes, uses NO point search.  For
// x in W and q in P' put
//     F_q(x) := { Dt in M_q : jmath_q(Dt) = rho_q(x) } .
// If every element of F_q(x) is of type (a) AND is the reduction of one of the known
// divisors of K_2, then x is settled: a global D with q_H(jmath(D)) = x reduces into
// one of those residue discs, the disc is of type (a) and therefore holds at most one
// F-rational degree-2 divisor, and it already holds a known one -- so D is that known
// divisor and lies in T_0.  This is checked for EVERY x in W, not only for the
// x outside the image of K_2: a class in that image can have further elements in its
// fibre, which have to be disposed of as well.
//
// "Of type (a)" is decided on the REDUCED divisor (for Dt = 2*Rt by the jet
// (a_0(Rt), a_1(Rt))), whereas the criterion cited in the article collects the
// multiplicities of the base point before reduction; the two differ when a known divisor
// R_1 + R_2 with R_1 <> R_2 reduces to 2*Rt.  Step (vii) is therefore
// also run with the cited criterion read literally -- see "collisions" below -- and it
// still settles every class of W, at q = 19, 61 and 79 even with one prime each.
//
// The point search quadratic_points_split is NOT used for this: over Q_p it examines
// only pairs of distinct GOOD (Tuitman) affine discs -- no diagonal pairs, no
// Frobenius-conjugate pairs (those need f_K = 2), no bad discs (6 of the 40 at q = 41) --
// and its LLL recognition can fail ("unrecognized") without that being a proof of
// absence.  The search is how the 35 sporadic divisors were FOUND, not part of the proof
// that there are no others.
//
// All of the curve-side work is done once and for all by appendix-A-localdata.m, which
// writes appendix-A-local-<q>.dat; this script only manipulates finite abelian groups and
// therefore runs in seconds.  Note that
//   * the torsion of Gamma is the full J(C)(F)_tors, of order 240;
//   * the 35 sporadic divisors are reduced projectively, so none is skipped, also
//     where a point has a pole at q or the two points of a divisor collide;
//   * an element of B is identified by the TUPLE of its local images, not by its
//     image at a single prime.
SetColumns(0); SetLogFile("appendix-A-sieve.log" : Overwrite);

// P' is ENLARGED here from the {41,79,89} of the article to all nine split primes at
// which the local data have been computed, i.e. the three primes of the article plus
// the remaining recovery primes of example-8.4-multiprime.m.  This matters twice over:
//   * the sieve itself is stronger;
//   * step (vii) may only use primes of P'.  A class x lives in B = Gamma/H with
//     H = intersection of the ker(rho_q) for q in P', so rho_q(x) is well defined
//     exactly for q in P'; at a prime outside P' the fibre F_q(x) depends on the
//     representative of x and carries no information.
primes := [41, 79, 89, 19, 29, 31, 59, 61, 71];
load "appendix-A-local-41.dat"; Rel1 := LocalRel; AH1 := LocalAH; Kn1 := LocalKnown; assert LocalQ eq 41;
load "appendix-A-local-79.dat"; Rel2 := LocalRel; AH2 := LocalAH; Kn2 := LocalKnown; assert LocalQ eq 79;
load "appendix-A-local-89.dat"; Rel3 := LocalRel; AH3 := LocalAH; Kn3 := LocalKnown; assert LocalQ eq 89;
load "appendix-A-local-19.dat"; Rel4 := LocalRel; AH4 := LocalAH; Kn4 := LocalKnown; assert LocalQ eq 19;
load "appendix-A-local-29.dat"; Rel5 := LocalRel; AH5 := LocalAH; Kn5 := LocalKnown; assert LocalQ eq 29;
load "appendix-A-local-31.dat"; Rel6 := LocalRel; AH6 := LocalAH; Kn6 := LocalKnown; assert LocalQ eq 31;
load "appendix-A-local-59.dat"; Rel7 := LocalRel; AH7 := LocalAH; Kn7 := LocalKnown; assert LocalQ eq 59;
load "appendix-A-local-61.dat"; Rel8 := LocalRel; AH8 := LocalAH; Kn8 := LocalKnown; assert LocalQ eq 61;
load "appendix-A-local-71.dat"; Rel9 := LocalRel; AH9 := LocalAH; Kn9 := LocalKnown; assert LocalQ eq 71;
Rels := [* Rel1, Rel2, Rel3, Rel4, Rel5, Rel6, Rel7, Rel8, Rel9 *];
AHs  := [* AH1,  AH2,  AH3,  AH4,  AH5,  AH6,  AH7,  AH8,  AH9  *];
Kns  := [* Kn1,  Kn2,  Kn3,  Kn4,  Kn5,  Kn6,  Kn7,  Kn8,  Kn9  *];
nsieve := #primes;

// Further primes do not help: q = 101, for instance (with the superset S_q = A_q cap H_q
// of R_q, found by testing effectivity with Riemann-Roch on H_q instead of enumerating
// C_q^(2)(F_q)), multiplies M -- and hence #B -- by 17 while cutting only a few per cent
// of the classes.

// ---------------------------------------------------------------- rebuild H_q = Z^3/Rel
// The basis of Z^3 is (t_10, z, c_spor), in that order.  An entry of LocalAH is
//   < vec(2c), type, tag, at infinity, pullback, description, c in H_q, vec(c) or 0 >
// and c runs through A_q cap H_q^rob.  The last two fields identify the residue class c
// itself, which is needed to recognise the reductions of the known divisors: those all
// lie in red_q(Gamma) (asserted below), so a class with e[7] = false is
// certainly not the reduction of a known divisor.
Z3 := FreeAbelianGroup(3);
Hs := [* *]; mqs := [* *]; cs := [* *]; tor := [* *];
Ysafe := [* *]; Fsafe := [* *]; Cls := [* *];
for i in [1..#primes] do
  Hq, mq := quo< Z3 | [ Z3 ! v : v in Rels[i] ] >;
  Append(~Hs, Hq); Append(~mqs, mq);
  Append(~cs,  mq(Z3.3));                                     // rho_q(c_spor)
  Append(~tor, sub< Hq | mq(Z3.1), mq(Z3.2) >);               // rho_q(J(C)(F)_tors)
  Ys := {}; FIa := AssociativeArray(); npull := 0; nrob := 0;
  for e in AHs[i] do
    if e[5] then npull +:= 1; continue; end if;      // a pullback class: removed from M_q
    nrob +:= 1;
    y := mq(Z3 ! e[1]);                              // rho_q(2c) = jmath_q of the class
    Include(~Ys, y);
    if not IsDefined(FIa, y) then FIa[y] := []; end if;
    //  < type, tag, at infinity, divisor, the class c itself or "not in red_q(Gamma)" >
    Append(~(FIa[y]), < e[2], e[3], e[4], e[6], e[7], e[7] select mq(Z3 ! e[8]) else Hq!0 >);
  end for;
  Append(~Ysafe, Ys); Append(~Fsafe, FIa); Append(~Cls, Hq);
  printf "q=%-3o |H_q|=%-6o %-14o #(A_q cap H_q^rob)=%-4o #Fam=%-3o #R_q^rob=%-4o #Y_q=%-4o ord(rho_q(c_spor))=%o\n",
     primes[i], #Hq, Sprint(Invariants(Hq)), #AHs[i], npull, nrob, #Ys, Order(mq(Z3.3));
end for;
M := LCM([ Order(cs[i]) : i in [1..nsieve] ]);
printf "|J(C)(F)_tors| = %o ; sieve modulus M = lcm of the orders of rho_q(c_spor) = %o\n",
   #tor[1], M;
assert #tor[1] eq 240;

// a transversal of J(C)(F)_tors = < t_10 > + < z >, read off at q = 41 (reduction is
// injective on torsion)
Tel := []; seen := {};
for a in [0..9], b in [0..119] do
  e := a*mqs[1](Z3.1) + b*mqs[1](Z3.2);
  if e notin seen then Include(~seen, e); Append(~Tel, <a,b>); end if;
end for;
assert #Tel eq 240;
tval := function(i, t) return t[1]*mqs[i](Z3.1) + t[2]*mqs[i](Z3.2); end function;
key  := function(n, t) return < n*cs[i] + tval(i, t) : i in [1..nsieve] >; end function;

// ---------------------------------------------------------------- the sieve
// For each torsion shift t the admissible residues n mod ord(rho_q(c_spor)) are
// collected at every prime and then combined by the Chinese remainder theorem.  This
// costs sum_q ord_q group additions per t instead of M of them, which matters as soon
// as one extra prime pushes M up (q = 101 multiplies it by 17).
sieve := function(cond)
  W := {}; npairs := 0; rep := AssociativeArray();
  ords := [ Order(cs[i]) : i in [1..nsieve] ];
  combine := function(Ns)                       // CRT-intersect the residue sets
    Sort(~Ns, func< U,V | #U[2]-#V[2] >);
    curL := Ns[1][1]; cur := Ns[1][2];
    for j in [2..#Ns] do
      m2 := Ns[j][1]; B := Ns[j][2]; g := GCD(curL,m2); newc := {Integers()|};
      for a in cur do for b in B do
        if (a-b) mod g eq 0 then Include(~newc, CRT([a,b],[curL,m2])); end if;
      end for; end for;
      curL := LCM(curL,m2); cur := newc;
      if #cur eq 0 then break; end if;
    end for;
    return cur, curL;
  end function;
  for t in Tel do
    Ns := []; ok := true;
    for i in [1..nsieve] do
      acc := tval(i, t); N := {Integers()|};
      for n in [0..ords[i]-1] do
        if acc in cond[i] then Include(~N, n); end if;
        acc +:= cs[i];
      end for;
      if #N eq 0 then ok := false; break; end if;
      Append(~Ns, <ords[i], N>);
    end for;
    if ok then
      cur := combine(Ns);
      for n in cur do npairs +:= 1; kk := key(n,t); Include(~W, kk);
        if not IsDefined(rep, kk) then rep[kk] := <n,t>; end if; end for;
    end if;
  end for;
  return W, npairs, rep;
end function;

printf "\n=== the surviving classes ===\n";
W, npairs, Rep := sieve(Ysafe);
printf "  %o pairs (n mod %o, t) survive, #W = %o classes of B.\n", npairs, M, #W;

// ---------------------------------------------------------------- the known classes
// The classes of the known divisors, both as elements of B (for the bookkeeping below)
// and, prime by prime, as residue classes in C_q^(2)(F_q) (for step (vii)).
// A divisor D in K_2 need NOT survive the sieve: the containment
// red_q^(2)(C^(2)(F)\T_0) subset M_q is only claimed for D outside T_0, and K_2 is
// inside T_0.  If red_q^(2)(D) is a PULLBACK class at every q then it is removed from
// R_q^rob and D drops out.
// The order is that of KnownList in appendix-A-common.m (nested loops).  Do NOT write this as
// [ ... : i in [1..8], j in [1..8] | i le j ]: in Magma the FIRST variable of a
// comprehension varies fastest, so that would attach wrong names to 30 of the 36 sums.
KnownNames := []; isdouble := [];
for i in [1..8] do for j in [i..8] do
  Append(~KnownNames, "P" cat IntegerToString(i) cat "+P" cat IntegerToString(j));
  Append(~isdouble, i eq j);                       // the divisor 2P with P in C(F)
end for; end for;
KnownNames := KnownNames cat [ "D_infty" ] cat [ "Delta_" cat IntegerToString(i) : i in [1..35] ];
isdouble   := isdouble cat [ false : j in [37..#KnownNames] ];
printf "\n=== the classes coming from K_2 ===\n";
Wknown := {}; nbad := 0; lost := [];
KnownCl := [* *];                       // KnownCl[i] = { red_q(iota_2(D)) : D in K_2 }
for i in [1..nsieve] do Append(~KnownCl, {}); end for;
for j in [1..#KnownNames] do
  if not &and[ Kns[i][j][2] : i in [1..nsieve] ] then nbad +:= 1; continue; end if;
  k := < mqs[i](Z3 ! Kns[i][j][1]) : i in [1..nsieve] >;            // rho_q(2[D-D_0])
  Include(~Wknown, k);
  assert &and[ Kns[i][j][3] : i in [1..nsieve] ];   // every known class is in red_q(Gamma)
  for i in [1..nsieve] do Include(~KnownCl[i], mqs[i](Z3 ! Kns[i][j][4])); end for;
  if k notin W then Append(~lost, KnownNames[j]); end if;
end for;
printf "  %o known divisors of K_2; %o failed to reduce somewhere.\n", #KnownNames, nbad;
printf "  #W_known = %o, #(W cap W_known) = %o\n", #Wknown, #(W meet Wknown);
printf "  their reductions give %o distinct residue classes at each prime: %o\n",
   #KnownCl[1], [ #KnownCl[i] : i in [1..nsieve] ];
printf "  known divisors NOT surviving the sieve: %o  %o\n", #lost, lost;
assert #[ e : e in lost | e[1] eq "D" ] eq 0;         // no Delta_i and no D_infty lost
assert Set(lost) eq { "P1+P2", "P3+P4", "P5+P6", "P7+P8" };
printf "  (these are the four sigma-pairs, i.e. the pullbacks phi^*(R) in K_2; they are\n";
printf "   removed from R_q^rob at every prime by construction; none of the 35 sporadic\n";
printf "   divisors and not D_infty is lost.)\n";

// ---------------------------------------------------------------- collisions
// The type (a)/(b)/(c) of a residue class is computed from the REDUCED divisor Dt
// (DegreeTwoData in appendix-A-common.m): for a diagonal class Dt = 2*Rt the matrix is the
// jet ( a_0(Rt), a_1(Rt) ), i.e. multiplicities are collected AFTER reduction.  The
// symmetric-Chabauty criterion as cited in the article (Box-Gajovic-Goodman, Thm 2.6)
// forms its matrix from a base point D_* in the disc, collecting multiplicities BEFORE
// reduction.  The two matrices agree unless Dt = 2*Rt and D_* = R_1 + R_2 with
// R_1 <> R_2 -- a "collision": a sporadic divisor, or a sum of two distinct points of
// C(F), whose two points have the same reduction.  The cited matrix is then
// ( a_0(Rt), a_0(Rt) ), of rank <= 1, and the cited criterion says nothing about the disc.
// Split classes Rt_1 + Rt_2 with Rt_1 <> Rt_2 and Frobenius-conjugate
// classes admit no collision: every divisor in such a disc has two distinct points with
// the two distinct reductions.
//
// The jet criterion is nevertheless valid for colliding divisors too (formal immersion
// at Dt: with t a local parameter at Rt, s_1 = t_1 + t_2 and s_2 = t_1*t_2 are
// coordinates in p*Z_p on the whole disc of 2*Rt, colliding divisors included, and the
// linear part of D |-> int_{2R_0}^{D} omega in (s_1, s_2) is a_0*s_1 - a_1*s_2), but that
// argument is not in the cited source.  So step (vii) is run twice below: with the jet
// criterion, and with the cited criterion read literally, which may use a diagonal
// class only if the known divisor reducing to it is a double 2P, P in C(F) -- for the
// base point D_* = 2P the cited matrix IS the jet.
printf "\n=== known divisors with a diagonal reduction 2*Rt ===\n";
KnownClCF := [* *];       // KnownClCF[i] = reductions of the known divisors that do not collide
ncoll := [ 0 : i in [1..nsieve] ];
for i in [1..nsieve] do
  tagOf := AssociativeArray();
  for e in AHs[i] do if e[7] then tagOf[mqs[i](Z3 ! e[8])] := e[3]; end if; end for;
  cf := {}; coll := []; dbl := [];
  for j in [1..#KnownNames] do
    c := mqs[i](Z3 ! Kns[i][j][4]);
    assert IsDefined(tagOf, c);         // a known class is an effective class in red_q(Gamma)
    if tagOf[c] eq "diagonal" then
      if isdouble[j] then Append(~dbl, KnownNames[j]); else Append(~coll, KnownNames[j]); continue; end if;
    else
      assert not isdouble[j];           // 2P always reduces to a diagonal class
    end if;
    Include(~cf, c);
  end for;
  Append(~KnownClCF, cf); ncoll[i] := #coll;
  printf "  q=%-3o %o doubles 2P (no collision); colliding: %o\n", primes[i], #dbl, coll;
end for;

// ---------------------------------------------------------------- step (vii)
// For x in W and a prime q put F_q(x) = { Dt in M_q : jmath_q(Dt) = rho_q(x) }.  If
// every element of F_q(x) is of type (a) and is the reduction of a known divisor of
// K_2, then no D in C^(2)(F) \ T_0 can have q_H(jmath(D)) = x: such a D would reduce
// into one of these residue discs, which is of type (a) and hence contains at most one
// F-rational effective divisor of degree 2 -- and it already contains a known one.
// No point search enters; see the note at the top of the file.
printf "\n=== step (vii): identification of the surviving classes ===\n";
// settles(i, fib, Kn): the prime primes[i] settles a class whose fibre is fib, using the
// residue classes Kn of known divisors -- Kn = KnownCl[i] for the jet criterion,
// Kn = KnownClCF[i] for the cited criterion read literally (see "collisions" above).
settles := func< fib, Kn | &and[ c[1] eq "a" and c[5] and (c[6] in Kn) : c in fib ] >;
nres := 0; left := []; byprime := AssociativeArray();
nrescf := 0; leftcf := []; byprimecf := AssociativeArray();
for i in [1..nsieve] do byprime[primes[i]] := 0; byprimecf[primes[i]] := 0; end for;
nempty := 0; alltypea := 0;
for x in W do
  nt := Rep[x]; n := nt[1]; t := nt[2];
  wit := 0; witcf := 0; typea := true;
  for i in [1..nsieve] do
    xi := n*cs[i] + tval(i, t);                      // = lambda_{H,q}(x) = rho_q(x)
    fib := IsDefined(Fsafe[i], xi) select Fsafe[i][xi] else [];
    if #fib eq 0 then
      nempty +:= 1;
      if wit eq 0 then wit := primes[i]; end if;
      if witcf eq 0 then witcf := primes[i]; end if;
      continue;
    end if;
    for c in fib do if c[1] ne "a" then typea := false; end if; end for;
    // every element of the fibre is of type (a) and is the reduction of a known divisor
    if wit eq 0 and settles(fib, KnownCl[i]) then wit := primes[i]; end if;
    // ... and, for a diagonal element, that known divisor is a double 2P
    if witcf eq 0 and settles(fib, KnownClCF[i]) then witcf := primes[i]; end if;
  end for;
  if typea then alltypea +:= 1; end if;
  if wit ne 0 then nres +:= 1; byprime[wit] +:= 1; else Append(~left, x); end if;
  if witcf ne 0 then nrescf +:= 1; byprimecf[witcf] +:= 1; else Append(~leftcf, x); end if;
end for;
printf "  every divisor above a surviving class is of type (a)                     : %o of %o\n",
   alltypea, #W;
printf "  settled (whole fibre of type (a) and made up of reductions of known divisors): %o of %o\n",
   nres, #W;
printf "     first witnessing prime: %o\n",
   [ <p, byprime[p]> : p in Sort(primes) | byprime[p] gt 0 ];
printf "  settled with the cited criterion (no diagonal element reduced from a collision): %o of %o\n",
   nrescf, #W;
printf "     first witnessing prime: %o\n",
   [ <p, byprimecf[p]> : p in Sort(primes) | byprimecf[p] gt 0 ];
printf "  fibres that were empty at some prime (cannot happen for x in W): %o\n", nempty;

// Why 41 and 79 and not the others: a fibre usually contains residue classes BESIDES
// the reduction of the known divisor, and those are what has to be ruled out.  The
// table below counts, per prime, the classes of W whose fibre is entirely made of
// type-(a) reductions of known divisors, and records how large the fibres get.
// The columns "diagonal" and "colliding" count the classes x of W whose fibre at q
// contains a diagonal class 2*Rt, resp. a diagonal class that is the reduction of a
// colliding known divisor; "cited" is "settles" for the cited criterion read literally.
printf "\n  per prime (over the %o classes of W):\n", #W;
solo := []; solocf := [];
printf "    %-5o %-10o %-8o %-12o %-12o %-32o %-10o %o\n", "q", "settles", "cited", "max #fibre",
   "mean #fibre", "fibres with an unknown element", "diagonal", "colliding";
for i in [1..nsieve] do
  nset := 0; nsetcf := 0; mx := 0; tot := 0; nunk := 0; ndiag := 0; ncol := 0;
  for x in W do
    nt := Rep[x]; xi := nt[1]*cs[i] + tval(i, nt[2]);
    fib := IsDefined(Fsafe[i], xi) select Fsafe[i][xi] else [];
    mx := Max(mx, #fib); tot +:= #fib;
    if settles(fib, KnownCl[i]) then nset +:= 1; else nunk +:= 1; end if;
    if settles(fib, KnownClCF[i]) then nsetcf +:= 1; end if;
    if exists{ c : c in fib | c[2] eq "diagonal" } then ndiag +:= 1; end if;
    if exists{ c : c in fib | c[2] eq "diagonal" and c[5] and c[6] in KnownCl[i]
                              and c[6] notin KnownClCF[i] } then ncol +:= 1; end if;
  end for;
  printf "    %-5o %-10o %-8o %-12o %-12o %-32o %-10o %o\n", primes[i], nset, nsetcf, mx,
     RealField(3)!(tot/#W), nunk, ndiag, ncol;
  if nset eq #W then Append(~solo, primes[i]); end if;
  if nsetcf eq #W then Append(~solocf, primes[i]); end if;
end for;
printf "    a single prime already settles ALL of W at q = %o\n", solo;
printf "    ... and with the cited criterion read literally at q = %o\n", solocf;
printf "  left over: %o (jet criterion), %o (cited criterion)\n", #left, #leftcf;
for x in leftcf do                  // left contains leftcf
  nt := Rep[x]; n := nt[1]; t := nt[2];
  printf "     fibres%o:", x in left select "" else " (settled by the jet criterion only)";
  for i in [1..nsieve] do
    xi := n*cs[i] + tval(i, t);
    fib := IsDefined(Fsafe[i], xi) select Fsafe[i][xi] else [];
    printf "  q=%o %o", primes[i],
       [ <c[1], c[2], c[3], c[5] and (c[6] in KnownCl[i]), c[5] and (c[6] in KnownClCF[i])> : c in fib ];
  end for;
  printf "\n";
end for;
assert #left eq 0 and #leftcf eq 0;

printf "\n=== conclusion ===\n";
printf "  Every class of W is settled, so C^(2)(F) = T_0: the only degree-2 points of\n";
printf "  C over F are the 36 sums of the eight F-rational points, D_infty, the 35\n";
printf "  sporadic divisors and the pullback family phi^*(E(F)).\n";
printf "  This uses no point search: only the type-(a) branch of the symmetric-Chabauty\n";
printf "  criterion at residue discs that already contain a known divisor, and it holds\n";
printf "  with the criterion read literally (multiplicities collected before reduction).\n";
print "\nDONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
