// tests/magma/unit-integrals.m   [unit test: identities of Coleman integrals]
//
//     magma -b tests/magma/unit-integrals.m        (from the repository root)
//
// On the genus-2 curve y^2 = x(x-1)(x+1)(x-2)(x+3) over Q_7, with the six rational
// Weierstrass points W (five finite ones are bad points of the model, one is very infinite)
// and the good points P = (3,12), iota(P) = (3,-12), the Coleman integrals computed by
// coleman_integrals_on_basis must satisfy:
//   * antisymmetry          int_P^R = - int_R^P;
//   * additivity            int_P^W + int_W^R = int_P^R  through a bad endpoint W;
//   * torsion               the holomorphic integrals between two Weierstrass points vanish,
//                           since [W - W'] is 2-torsion;
//   * the involution        int_P^{iota P} omega = 2 int_P^W omega for the holomorphic
//                           (iota-anti-invariant) omega, since iota fixes W.
// The first g entries of an integral vector are the holomorphic integrals (cf.
// holomorphic_integrals_weakly_zero); the identities with all 2g entries are only checked
// where both endpoints are good, because the second-kind forms may have poles at W.
// Then the cached base point (return_side, side1) on the curve 249.a.249.1,
// y^2 + (x^3+1)y = x^2 + x, of rank 0 at 5: the side of (0,-1) cached from an integral to a
// point at infinity (e_P = 1, e = 11) is not reused for the bad point (-1,0) with e_P = 2,
// which needs e = 21 for its digits; the integrals are as precise as without the cache, and
// the holomorphic integrals vanish (rank 0). With target := 8 the integral is recomputed with
// e = 43, which loses fewer digits at the point near the boundary (precision 8 instead of 4).
// The integrals are recorded in unit-integrals.results (tests/magma/results.m), to the
// precision that the computation certifies (only the holomorphic ones if an endpoint is a
// Weierstrass point, where the other forms have poles).
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/magma/unit-integrals.log" : Overwrite);
RF := "tests/magma/unit-integrals.results";
results_start(RF);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
zero := func< v, idx | &and[ IsWeaklyZero(v[i]) : i in idx ] >;

QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - x*(x-1)*(x+1)*(x-2)*(x+3);
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
data := coleman_data(Q, QQ, P7, 10 : verbose := false);
g := data`g; hol := [1..g]; all := [1..2*g];

P  := set_point(3, 12, data);
Pi := set_point(3, -12, data);                   // iota(P)
W0 := set_point(0, 0, data);
W1 := set_point(1, 0, data);
W2 := set_point(2, 0, data);

I_P_Pi,  N_P_Pi  := coleman_integrals_on_basis(P, Pi, data);
I_Pi_P,  N_Pi_P  := coleman_integrals_on_basis(Pi, P, data);
I_P_W0,  N_P_W0  := coleman_integrals_on_basis(P, W0, data);
I_W0_Pi, N_W0_Pi := coleman_integrals_on_basis(W0, Pi, data);
I_W0_W1, N_W0_W1 := coleman_integrals_on_basis(W0, W1, data);
I_W1_W2, N_W1_W2 := coleman_integrals_on_basis(W1, W2, data);
record_result(RF, "int_P^iotaP", I_P_Pi : precision := N_P_Pi);
record_result(RF, "int_iotaP^P", I_Pi_P : precision := N_Pi_P);
record_result(RF, "int_P^W0 (holomorphic)", [I_P_W0[i] : i in hol] : precision := N_P_W0);
record_result(RF, "int_W0^iotaP (holomorphic)", [I_W0_Pi[i] : i in hol] : precision := N_W0_Pi);
record_result(RF, "int_W0^W1 (holomorphic)", [I_W0_W1[i] : i in hol] : precision := N_W0_W1);
record_result(RF, "int_W1^W2 (holomorphic)", [I_W1_W2[i] : i in hol] : precision := N_W1_W2);

check("antisymmetry: int_P^{iota P} = - int_{iota P}^P (all 2g forms)",
      zero([ I_P_Pi[i] + I_Pi_P[i] : i in all ], all), ~nfail);
check("additivity through the Weierstrass point W0 (holomorphic forms)",
      zero([ I_P_W0[i] + I_W0_Pi[i] - I_P_Pi[i] : i in hol ], [1..#hol]), ~nfail);
check("2-torsion: holomorphic integrals from W0 to W1 vanish", zero(I_W0_W1, hol), ~nfail);
check("2-torsion: holomorphic integrals from W1 to W2 vanish", zero(I_W1_W2, hol), ~nfail);
check("involution: int_P^{iota P} = 2 int_P^{W0} (holomorphic forms)",
      zero([ I_P_Pi[i] - 2*I_P_W0[i] : i in hol ], [1..#hol]), ~nfail);
check("[P - iota P] is not torsion: some holomorphic integral is nonzero",
      not zero(I_P_Pi, hol), ~nfail);

// ---- the cached base point
Q2 := y^2 + (x^3 + 1)*y - (x^2 + x);
P5 := Decomposition(MaximalOrder(QQ), 5)[1][1];
data2 := coleman_data(Q2, QQ, P5, 10 : verbose := false);
A := set_point(0, -1, data2);
Winf := set_bad_point(0, [1, 0], true, data2); // a point at infinity, e_P = 1
B := set_point(-1, 0, data2);                  // very bad, e_P = 2
I_AB, N_AB := coleman_integrals_on_basis(A, B, data2 : verbose := false);
_, _, side := coleman_integrals_on_basis(A, Winf, data2 : verbose := false, return_side := true);
I_ABc, N_ABc := coleman_integrals_on_basis(A, B, data2 : verbose := false, side1 := side);
check("the integral to the bad point (-1,0) with the cached side of (0,-1): as precise as without the cache",
      N_ABc eq N_AB and N_AB ge 4, ~nfail);
check("rank 0: the holomorphic integrals from (0,-1) to (-1,0) vanish, with and without the cache",
      zero(I_AB, [1..data2`g]) and zero(I_ABc, [1..data2`g]), ~nfail);
I_ABt, N_ABt := coleman_integrals_on_basis(A, B, data2 : verbose := false, target := 8);
record_result(RF, "249.a: int_(0,-1)^(-1,0) (holomorphic)", [I_AB[i] : i in [1..data2`g]] : precision := N_AB);
record_result(RF, "249.a: int_(0,-1)^(-1,0) with the cached side (holomorphic)", [I_ABc[i] : i in [1..data2`g]] : precision := N_ABc);
record_result(RF, "249.a: int_(0,-1)^(-1,0) with target 8 (holomorphic)", [I_ABt[i] : i in [1..data2`g]] : precision := N_ABt);
check("target := 8: a larger e gives precision >= 8, and the same integrals to precision 4",
      N_ABt ge 8 and &and[ Valuation(I_ABt[i] - I_AB[i]) ge N_AB : i in [1..2*data2`g] ], ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
