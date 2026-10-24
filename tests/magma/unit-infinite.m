// tests/magma/unit-infinite.m   [unit test: Coleman integrals at infinite endpoints]
//
//     magma -b tests/magma/unit-infinite.m        (from the repository root)
//
// (1) The image of a point near infinity under Frobenius satisfies
//     b_i(F_q(S)) = b_i(S)^q mod pi, with equality of valuations if b_i(P_inf)^q - b_i(P_inf)
//     has valuation 1. On y^2 = 4x^6 + x + 1 at p = 3 the points at infinity have
//     b_1^inf = y/x^3 = +-2, and 2^3 - 2 = 6. The integrals to them must exist, must not
//     depend on the auxiliary e, and must be compatible with the hyperelliptic involution.
// (2) frobenius_pt_inf (F_q^*(t) = t^q*U(t), U = 1 mod pi): at a K-rational point R with
//     v_K(t(R)) = 1 in a ramified disc at infinity (y^2 = x^5 - x + 1, p = 3, e_P = 2), the
//     congruence mod pi leaves two roots. The image found in the local parameter t has
//     t(F_q(R)) = t(R)^q mod pi*t(R)^q, lies on the curve, and is what frobenius_pt returns
//     when it is given the point at infinity. In an unramified disc, where the congruence
//     determines the root, both methods agree.
// (3) The option direct_inf: the integrals to R and to
//     the very infinite point agree with those of the default route over K(pi^(1/e)) to the
//     certified precision of both: on the ramified disc of (2), on the unramified discs of
//     y^2 = x^6 + 2x^3 + x + 1 at p = 7, and on the quartic of test2 at p = 5, whose
//     coordinates b_i^inf do not separate the points at infinity. Also with the direct
//     endpoint first, and with its side cached for a second integral.
// The integrals and the Frobenius image are recorded in unit-infinite.results
// (tests/magma/results.m), to their certified precisions.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
load "tests/magma/results.m";
SetColumns(0);
SetLogFile("tests/magma/unit-infinite.log" : Overwrite);
RF := "tests/magma/unit-infinite.results";
results_start(RF);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
agree := func< u, v, idx, n | &and[ Valuation(u[i] - v[i]) ge n : i in idx ] >;

QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
prime := func< p | Decomposition(MaximalOrder(QQ), p)[1][1] >;

// the very infinite point W with its expansions in the local parameter t at W
with_expansions := function(W, data)
  _, index := local_data(W, data);
  data := update_minpolys(data, true, index);
  W`xt, W`bt, W`index := local_coord(W, Precision(data`K) + 2, data);
  return W;
end function;

// the point of the disc of W with t = t0
point_in_disc := function(W, t0, data)
  K := data`K;
  return set_bad_point(eval_series_Ke(W`xt, K!t0, K), [ eval_series_Ke(W`bt[i], K!t0, K) : i in [1..#W`bt] ],
                       true, data : check := false);
end function;

// a good point over K with x = x0, the root of Q(x0,y) near y0
good_point_K := function(x0, y0, data)
  K := data`K; L := data`L; m := data`m; Q := data`Q; d := Degree(Q);
  f := PolynomialRing(K)![ K!Evaluate(coer_poly(Coefficient(Q, i), L, K, m), x0) : i in [0..d] ];
  yK := HenselLift(f, K!y0);
  b := Eltseq(Vector([ yK^(i-1) : i in [1..d] ]) * Transpose(eval_mat(data`W0, L, K, m, x0)));
  return set_bad_point(x0, b, false, data);
end function;

// the minimal valuation of the minimal polynomials of the b_i^inf over K(1/x) at an infinite point
residual := function(Pt, data)
  K := data`K; L := data`L; m := data`m; v := Infinity();
  for i := 1 to Degree(data`Q) do
    C := Coefficients(data`minpolys[2][1, i+1]);
    val := &+[ eval_frac(C[j], L, K, m, Pt`x) * Pt`b[i]^(j-1) : j in [1..#C] ];
    if not IsWeaklyZero(val) then v := Minimum(v, Valuation(val)); end if;
  end for;
  return v;
end function;

// number of roots for b_1^inf(F_q(S)) that are congruent to b_1^inf(S)^q mod pi
roots_mod_pi := function(S, data)
  K := data`K; L := data`L; m := data`m; q := #ResidueClassField(data`P);
  fy := PolynomialRing(K)![ eval_frac(c, L, K, m, S`x^q) : c in Coefficients(data`minpolys[2][1, 2+1]) ];
  return #[ rt : rt in Roots(fy) | Valuation(rt[1] - S`b[2]^q) ge 1 ];
end function;

same_point := func< P1, P2 | IsWeaklyZero(P1`x - P2`x) and &and[ IsWeaklyZero(P1`b[i] - P2`b[i]) : i in [1..#P1`b] ] >;

// (3) direct route against the default route, with P good and W very infinite
compare := procedure(label, data, P, W, tR, ~nfail)
  idx := [1..#data`basis];
  R := point_in_disc(W, tR, data);
  for pt in [* <"R (t(R) = " cat Sprint(tR) cat ")", R>, <"the very infinite point", W> *] do
    I, N := coleman_integrals_on_basis(P, pt[2], data : verbose := false);
    J, NJ := coleman_integrals_on_basis(P, pt[2], data : verbose := false, direct_inf := true);
    record_result(RF, Sprintf("(3) %o, int_P^%o", label, pt[1]), I : precision := N);
    record_result(RF, Sprintf("(3) %o, int_P^%o, direct route", label, pt[1]), J : precision := NJ);
    check(Sprintf("%o, int_P^%o: direct route (%o digits) = default route (%o digits)", label, pt[1], NJ, N),
          NJ ge 1 and agree(I, J, idx, Minimum(N, NJ)), ~nfail);
  end for;
end procedure;


print "\n(1) y^2 = 4x^6 + x + 1, p = 3: b_1^inf = +-2 at infinity";
data := coleman_data(y^2 - (4*x^6 + x + 1), QQ, prime(3), 10 : verbose := false);
hol2 := [1..2*data`g];
Wp := set_bad_point(0, [1, 2], true, data);
Wm := set_bad_point(0, [1, -2], true, data);
check("v_K(b_1^inf(W+)^q - b_1^inf(W+)) = 1", Valuation(data`K!(2^3 - 2)) eq 1, ~nfail);
I1, N1 := coleman_integrals_on_basis(set_point(0, 1, data), Wp, data : verbose := false);
I2, N2 := coleman_integrals_on_basis(set_point(0, 1, data), Wp, data : e := 13, verbose := false);
Im, Nm := coleman_integrals_on_basis(set_point(0, -1, data), Wm, data : verbose := false);
record_result(RF, "(1) int_(0,1)^W+", I1 : precision := N1);
record_result(RF, "(1) int_(0,1)^W+ with e = 13", I2 : precision := N2);
record_result(RF, "(1) int_(0,-1)^W-", Im : precision := Nm);
check(Sprintf("int_(0,1)^W+ is computed (%o digits)", N1), N1 ge 1, ~nfail);
check("int_(0,1)^W+ does not depend on e (e = 7 and e = 13)", agree(I1, I2, hol2, Minimum(N1, N2)), ~nfail);
check("involution: int_(0,-1)^W- = -int_(0,1)^W+", agree(I1, -Im, hol2, Minimum(N1, Nm)), ~nfail);


print "\n(2) y^2 = x^5 - x + 1, p = 3: a ramified disc at infinity";
dataA := coleman_data(y^2 - (x^5 - x + 1), QQ, prime(3), 25 : verbose := false);
K := dataA`K; q := #ResidueClassField(dataA`P);
WA := with_expansions(set_bad_point(0, [1, 0], true, dataA), dataA);
eP := local_data(WA, dataA);
R := point_in_disc(WA, 3, dataA);
FR := frobenius_pt_inf(R, WA, dataA);
tR := R`b[WA`index] - WA`b[WA`index]; tFR := FR`b[WA`index] - WA`b[WA`index];
record_result(RF, "(2) t(F_q(R)) for t(R) = 3", tFR : precision := dataA`N);
check(Sprintf("e_P = %o, local parameter b_%o^inf", eP, WA`index - 1), eP eq 2 and WA`index eq 2, ~nfail);
check("the congruence mod pi leaves two roots for b_1^inf(F_q(R))", roots_mod_pi(R, dataA) eq 2, ~nfail);
check("t(F_q(R)) = t(R)^q mod pi*t(R)^q", Valuation(tFR - tR^q) gt q*Valuation(tR), ~nfail);
res := residual(FR, dataA);
check(Sprintf("F_q(R) lies on the curve (residual valuation %o)", res), res ge dataA`N, ~nfail);
check("frobenius_pt with the point at infinity returns F_q(R)",
      same_point(frobenius_pt(R, dataA : center := WA), FR), ~nfail);

dataB := coleman_data(y^2 - (x^6 + 2*x^3 + x + 1), QQ, prime(7), 30 : verbose := false);
WB := with_expansions(set_bad_point(0, [1, 1], true, dataB), dataB);
RB := point_in_disc(WB, 7, dataB);
check("unramified disc: the congruence mod pi determines F_q(R), and frobenius_pt_inf agrees",
      roots_mod_pi(RB, dataB) eq 1 and same_point(frobenius_pt(RB, dataB), frobenius_pt_inf(RB, WB, dataB)), ~nfail);


print "\n(3) the option direct_inf";
PA := set_point(0, 1, dataA);
compare("y^2 = x^5 - x + 1, p = 3", dataA, PA, WA, 3, ~nfail);
compare("y^2 = x^6 + 2x^3 + x + 1, p = 7", dataB, set_point(0, 1, dataB), WB, 7, ~nfail);
dataD := coleman_data(y^3 + (-x^2-x)*y^2 + x^3*y - x^2 + x, QQ, prime(5), 20 : verbose := false);
WD := with_expansions(set_bad_point(0, [1, 0, -1], true, dataD), dataD);
check("quartic of test2: the congruence mod pi leaves two roots for b_1^inf at t = 5",
      roots_mod_pi(point_in_disc(WD, 5, dataD), dataD) eq 2, ~nfail);
compare("quartic of test2, p = 5", dataD, good_point_K(dataD`K!2, 3, dataD), WD, 5, ~nfail);

// the direct endpoint first, and its side cached for a second integral
idx := [1..#dataA`basis];
I, N := coleman_integrals_on_basis(PA, R, dataA : verbose := false, direct_inf := true);
J, NJ, sd := coleman_integrals_on_basis(R, PA, dataA : verbose := false, direct_inf := true, return_side := true);
check("antisymmetry: int_R^P = -int_P^R on the direct route", agree(I, -J, idx, Minimum(N, NJ)), ~nfail);
PA2 := set_point(1, 1, dataA);
J2, NJ2 := coleman_integrals_on_basis(R, PA2, dataA : verbose := false, direct_inf := true, side1 := sd);
I12, N12 := coleman_integrals_on_basis(PA, PA2, dataA : verbose := false);
record_result(RF, "(3) int_R^P2 with the cached direct side", J2 : precision := NJ2);
record_result(RF, "(3) int_P^P2", I12 : precision := N12);
check("additivity with the cached direct side: int_R^P2 - int_R^P = int_P^P2",
      agree(J2 - J, I12, idx, Minimum([NJ, NJ2, N12])), ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
