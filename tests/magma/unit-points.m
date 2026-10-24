// tests/magma/unit-points.m   [unit test: the classification of points and residue discs]
//
//     magma -b tests/magma/unit-points.m        (from the repository root)
//
// On y^2 = x(x-1)(x+1)(x-2)(x+3) over Q_7 (b^0 = (1,y), b^inf = (1,y/x^3)): is_bad and
// is_very_bad (article: the definition of bad and good points) and lie_in_same_disc, which
// tiny_integrals_on_basis uses to reject endpoints in different residue discs. Two points lie
// in the same residue disc iff their reductions agree, i.e. iff x (resp. 1/x) and all values
// of b^0 (resp. b^inf) agree modulo pi.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
SetColumns(0);
SetLogFile("tests/magma/unit-points.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - x*(x-1)*(x+1)*(x-2)*(x+3);
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
data := coleman_data(Q, QQ, P7, 10 : verbose := false);

P   := set_point(3, 12, data);
Pi  := set_point(3, -12, data);
W0  := set_point(0, 0, data);
W1  := set_point(1, 0, data);
Inf := set_bad_point(0, [1, 0], true, data);     // the point at infinity: 1/x = 0, b^inf = (1,0)

check("(3,12) is good", not is_bad(P, data), ~nfail);
check("(0,0) is bad and very bad", is_bad(W0, data) and is_very_bad(W0, data), ~nfail);
check("the point at infinity is bad and very bad", is_bad(Inf, data) and is_very_bad(Inf, data), ~nfail);
check("(3,12) and itself lie in the same residue disc", lie_in_same_disc(P, P, data), ~nfail);
check("(3,12) and (3,-12) lie in different residue discs", not lie_in_same_disc(P, Pi, data), ~nfail);
check("(0,0) and the point at infinity lie in different residue discs", not lie_in_same_disc(W0, Inf, data), ~nfail);
check("(0,0) and (1,0) lie in different residue discs", not lie_in_same_disc(W0, W1, data), ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
