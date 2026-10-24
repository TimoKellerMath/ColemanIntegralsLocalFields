SetColumns(0);
SetLogFile("appendix-A-rank-E.log" : Overwrite);
_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
OF := MaximalOrder(F);

// Clean model of the bielliptic quotient E = C/sigma  (memory: y^2+y = x^3+1)
E := EllipticCurve([F| 0,0,1,0,1]);
E := MinimalModel(E);
print "E =", E;
// the conductor by the norms of its prime factors and their exponents: printing the prime
// ideals themselves shows a generator whose sign Magma chooses at random ([1,-2] or [-1,2])
print "Conductor(E) = product of primes of norms (with exponents)",
      Sort([ <Norm(f[1]), f[2]> : f in Factorization(Conductor(E)) ]);

// rank over F via the 5-twist decomposition done over Q (Magma RankBounds is Q-only-friendly)
EQ := EllipticCurve([Rationals()| 0,0,1,0,1]);
print "rank E(Q) bounds   =", RankBounds(EQ);
EQ5 := QuadraticTwist(EQ, 5);
print "rank E^(5)(Q) bounds =", RankBounds(EQ5);
// rank E(F) = rank E(Q) + rank E^(5)(Q)

// direct: try MordellWeil over F on the minimal model
rb := RankBounds(E);
print "RankBounds E(F) =", rb;
G, mG, fl1, fl2 := MordellWeilGroup(E : Effort:=1);
printf "E(F) = %o   provable_rank=%o saturated=%o\n", G, fl1, fl2;
print "torsion =", TorsionSubgroup(E);
for g in Generators(G) do print "gen:", mG(g), "  order", Order(g); end for;

// confirm bielliptic degree-2 map exists: point counts  #C(F_p) =? #E(F_p)+#Xb3ns5(F_p)-(p+1)
// Xb3ns5: y^2 = 9x^6-6x^5-35x^4+40x^2+12x-8
P2<X,Y,Z> := ProjectiveSpace(F,2);
qC := Y^4 - 2*Y^3*X - Y^2*X^2 - 8*Y^3*Z - 2*Y^2*X*Z + 2*Y*X^2*Z + X^3*Z
      + 3*Y^2*Z^2 + 3*Y*X*Z^2 - 3*X^2*Z^2 - 2*Y*Z^3 + 3*X*Z^3 - Z^4;
C := Curve(P2, qC);
H := HyperellipticCurve(9*PolynomialRing(F).1^6-6*PolynomialRing(F).1^5-35*PolynomialRing(F).1^4+40*PolynomialRing(F).1^2+12*PolynomialRing(F).1-8);
print "point-count isogeny check #C = #E + #H - (q+1):";
for p in [11,29,31,41] do        // split primes, residue field F_p
  Pp := Decomposition(OF,p)[1][1];
  k, mk := ResidueClassField(Pp);   // F_p
  Cp := ChangeRing(C, k); Ep := ChangeRing(E, k); Hp := ChangeRing(H, k);
  printf "  p=%o: #C=%o, #E+#H-(p+1)=%o  match=%o\n",
     p, #Points(Cp), #Ep + #Points(Hp) - (#k+1), #Points(Cp) eq #Ep + #Points(Hp) - (#k+1);
end for;

print "DONE";
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
