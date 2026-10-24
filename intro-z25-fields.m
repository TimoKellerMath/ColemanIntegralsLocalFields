// intro-z25-fields.m   [Introduction of the article: the table of the smallest primes
//                       splitting completely in the sextic fields K_i of x^2+y^3=z^25]
SetColumns(0); SetLogFile("intro-z25-fields.log" : Overwrite);
// The five sextic coefficient fields K of the open equations H_i(u,v) = w^5 in
// arXiv:2506.10667 (x^2+y^3=z^25).  The genus-2 curves Y^2 = X^5 + A whose
// L-rational points are undetermined live over L, a QUADRATIC extension of K,
// so [L:Q] = 12.  Question: how does a totally split prime compare with a prime
// of large residue degree, for restriction-of-scalars Chabauty over such a field?
_<x> := PolynomialRing(Rationals());
polys := [ <5,  x^6 + 10*x^3 + 24*x + 5>,
           <6,  x^6 - 2*x^5 - 6*x - 3>,
           <16, x^6 + 10*x^3 - 15*x^2 + 18*x - 10>,
           <22, x^6 + 3*x^5 - 10*x^3 + 12*x - 4>,
           <24, x^6 - 10*x^3 - 6*x + 5> ];
printf "%-4o %-10o %-12o %-14o %-12o %-14o %o\n", "i", "Gal deg", "tot.split p", "(p+1)^6", "best f", "p, q_K=p^f", "ratio";
for pr in polys do
  K := NumberField(pr[2]); O := MaximalOrder(K); d := Degree(K);
  G := GaloisGroup(pr[2]);
  ts := 0;
  for p in PrimesUpTo(20000) do
    if Valuation(Discriminant(O),p) ne 0 then continue; end if;
    D := Decomposition(O,p);
    if #D eq d then ts := p; break; end if;
  end for;
  bf := 0; bp := 0;
  for p in [q : q in PrimesUpTo(200) | q ge 5] do
    if Valuation(Discriminant(O),p) ne 0 then continue; end if;
    D := Decomposition(O,p);
    f := Maximum([ InertiaDegree(y[1]) : y in D | RamificationDegree(y[1]) eq 1 ] cat [0]);
    if f gt bf then bf := f; bp := p; end if;
    if bf eq d then break; end if;
  end for;
  split := (ts eq 0) select "none<20000" else Sprint(ts);
  cnt   := (ts eq 0) select "-" else Sprint((ts+1)^d);
  rat   := (ts eq 0 or bp eq 0) select "-" else Sprint(RealField(3)!((ts+1)^d/(bp^bf)));
  printf "%-4o %-10o %-12o %-14o %-12o %-14o %o\n", pr[1], #G, split, cnt, bf, Sprintf("%o, %o", bp, bp^bf), rat;
end for;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
