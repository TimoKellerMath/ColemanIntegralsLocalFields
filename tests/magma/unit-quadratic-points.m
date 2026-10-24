// tests/magma/unit-quadratic-points.m   [unit test: quadratic_points.m]
//
//     magma -b tests/magma/unit-quadratic-points.m        (from the repository root)
//
// The internal functions of curve_quadratic_points (quadratic_points.m), on the genus-2 curve
// X(b3,ns5): y^2 = 9x^6 - 6x^5 - 35x^4 + 40x^2 + 12x - 8 over F = Q(sqrt 5) at the prime P
// above 11, over the unramified quadratic extension K = Q_(11^2) (aux): the sweep of models
// and residue discs, the transfer of points between the model and its Moebius patches (also
// of a Weierstrass point, which is a very bad point of every model), the hyperelliptic
// involution, the known divisors in their accepted forms, the Frobenius-stable residue classes,
// the reduction of a point of degree 2 ramified at P (place_key), and verify_divisor.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
load "symmetric_chabauty.m"; load "models.m"; load "quadratic_points.m";
SetColumns(0);
SetLogFile("tests/magma/unit-quadratic-points.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
// whether the call raises an error whose message contains the phrase
raises := function(f, phrase)
  try
    _ := f();
  catch e
    return Position(e`Object, phrase) gt 0;
  end try;
  return false;
end function;

_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
OF := MaximalOrder(F);
Fx<X> := PolynomialRing(F);
A2<a,b> := AffineSpace(F, 2);
C := Curve(A2, b^2 - (9*a^6 - 6*a^5 - 35*a^4 + 40*a^2 + 12*a - 8));
FF := FunctionField(C);
M := curve_model(C);
P := Decomposition(OF, 11)[1][1];

// ---- 1. the sweep: models and residue discs
sweep, discs, uncovered, unseen := sweep_setup(M, P, 8, true, true, false);
dataM := sweep[1]`data; KM := dataM`K;
check("sweep_setup: the model and two Moebius patches x = t + 1/x' (t = 0, 1), every disc covered",
      [S`kind : S in sweep] eq ["model", "mobius", "mobius"] and [sweep[h]`t : h in [2, 3]] eq [0, 1]
      and uncovered eq 0 and unseen eq 0, ~nfail);
check("sweep_setup: 146 discs over F_121, 138 good and 6 Weierstrass discs in the model, the 2 at infinity in the first patch",
      #discs eq 146 and #ResidueClassField(RingOfIntegers(KM)) eq 121
      and #[D : D in discs | D`home eq 1 and not D`bad] eq 138 and #[D : D in discs | D`home eq 1 and D`bad] eq 6
      and #[D : D in discs | D`home eq 2] eq 2, ~nfail);
frob := [D`frob : D in discs];
check("frobenius_images: an involution of the discs with 14 fixed points (the discs of the points of the reduction over F_11)",
      forall{i : i in [1..#discs] | frob[frob[i]] eq i} and #[i : i in [1..#discs] | frob[i] eq i] eq 14, ~nfail);
cls := frobenius_stable_classes(frob);
check("frobenius_stable_classes: 14 diagonal, 91 split and 66 conjugate classes",
      #[c : c in cls | c[3] eq "diagonal"] eq 14 and #[c : c in cls | c[3] eq "split"] eq 91
      and #[c : c in cls | c[3] eq "conjugate"] eq 66, ~nfail);
check("frobenius_stable_classes on (1 2)(3)(4): <3,3>, <4,4>, <3,4> and the conjugate <1,2>",
      frobenius_stable_classes([2, 1, 3, 4]) eq [<3, 3, "diagonal">, <4, 4, "diagonal">, <3, 4, "split">, <1, 2, "conjugate">], ~nfail);

// ---- 2. p-adic numbers and point records between the data of the models
d2 := sweep[2]`data;
z := KM!dataM`m(dataM`L!s) + O(dataM`pi^5);
z2 := K_to_K(z, dataM, d2);
check("K_to_K: an element of K with absolute precision 5 into the K of a patch, with the same precision, through L",
      Parent(z2) cmpeq d2`K and AbsolutePrecision(z2) eq 5 and IsWeaklyZero(z2 - d2`m(d2`L!s)), ~nfail);
check("K_to_K: an inexact zero stays an inexact zero of the same precision",
      IsWeaklyZero(K_to_K(O(dataM`pi^4), dataM, d2)) and AbsolutePrecision(K_to_K(O(dataM`pi^4), dataM, d2)) eq 4, ~nfail);
R := discs[1]`centre;
yR := y_of_record(R, dataM);
check("y_of_record, record_from_xy: the record of (x, y) is the record itself",
      lie_in_same_disc(record_from_xy(R`x, yR, dataM), R, dataM)
      and IsWeaklyZero(record_from_xy(R`x, yR, dataM)`b[2] - R`b[2]), ~nfail);
check("hyperelliptic_involution: (x, y) -> (x, -y), an involution",
      IsWeaklyZero(y_of_record(hyperelliptic_involution(R, dataM), dataM) + yR)
      and IsWeaklyZero(y_of_record(hyperelliptic_involution(hyperelliptic_involution(R, dataM), dataM), dataM) - yR), ~nfail);
i0 := [i : i in [1..#discs] | discs[i]`home eq 1 and not discs[i]`bad and Valuation(discs[i]`centre`x) eq 0
                              and Valuation(discs[i]`centre`x - 1) eq 0][1];
R0 := discs[i0]`centre;
ok2, R2 := transfer_point(R0, sweep[1], sweep[2]);
okb, Rb := transfer_point(R2, sweep[2], sweep[1]);
check("transfer_point: a good point of the model to the patch x = 1/x' (x' = 1/x) and back",
      ok2 and okb and IsWeaklyZero(K_to_K(R2`x, d2, dataM) - 1/R0`x) and IsWeaklyZero(Rb`x - R0`x)
      and IsWeaklyZero(Rb`b[2] - R0`b[2]), ~nfail);
ok3, R3 := transfer_point(R2, sweep[2], sweep[3]);
check("transfer_point between the two Moebius patches: x'' = x'/(1 - x') = 1/(x - 1)",
      ok3 and IsWeaklyZero(K_to_K(R3`x, sweep[3]`data, dataM) - 1/(R0`x - 1)), ~nfail);
iW := [i : i in [1..#discs] | discs[i]`bad and discs[i]`home eq 1 and Valuation(discs[i]`centre`x) eq 0][1];
W := discs[iW]`centre;
okW := transfer_point(W, sweep[1], sweep[2]);
okW1, RW1 := transfer_point(W, sweep[1], sweep[2] : very_bad := true);
check("transfer_point: a Weierstrass point (bad in every model) is refused, and accepted with very_bad",
      not okW and okW1, ~nfail);
check("transfer_point with very_bad: the image of the Weierstrass point is very bad in the patch, with y' = 0",
      is_very_bad(RW1, d2) and IsWeaklyZero(y_of_record(RW1, d2)), ~nfail);

// ---- 3. the known divisors in their accepted forms
R1 := C![(s-1)/2, 5*(s-1)/2]; R2pt := C![(-s-1)/2, 5*(s+1)/2];
pl1 := Place(R1); pl2 := Place(R2pt);
check("known_places: a pair of points of C(F) gives the two places with multiplicity 1",
      known_places([R1, R2pt], M) eq [<pl1, 1>, <pl2, 1>], ~nfail);
check("known_places: pairs of coordinates, places and divisors give the same places",
      known_places([[(s-1)/2, 5*(s-1)/2], [(-s-1)/2, 5*(s+1)/2]], M) eq [<pl1, 1>, <pl2, 1>]
      and known_places([* pl1, pl2 *], M) eq [<pl1, 1>, <pl2, 1>]
      and Set(known_places(Divisor(pl1) + Divisor(pl2), M)) eq {<pl1, 1>, <pl2, 1>}
      and known_places(2*Divisor(pl1), M) eq [<pl1, 2>], ~nfail);
quad := [pl : pl in Zeros(Evaluate(X^2 + 5/3*X + 1, FF!a)) | Degree(pl) eq 2][1];
E := ResidueClassField(quad);
ptE := C(E)![Evaluate(FF!a, quad), Evaluate(FF!b, quad)];
check("known_places: a point over a quadratic extension of F gives its place of degree 2",
      known_places(ptE, M) eq [<quad, 1>], ~nfail);
check("known_places: [x0, y0] off the curve, a non-effective divisor and an unknown object are errors",
      raises(func< | known_places([1, 2], M) >, "is not a point of the model")
      and raises(func< | known_places(Divisor(pl1) - Divisor(pl2), M) >, "must be effective")
      and raises(func< | known_places("a point", M) >, "a known divisor must be"), ~nfail);
check("x_polynomial: (X - x1)(X - x2) for two points, the minimal polynomial for a point of degree 2",
      x_polynomial(Divisor(pl1) + Divisor(pl2), M) eq X^2 + X - 1 and x_polynomial(Divisor(quad), M) eq X^2 + 5/3*X + 1, ~nfail);
check("x_polynomial: 0 for a divisor with a point at infinity",
      x_polynomial(Divisor(Poles(FF!a)[1]) + Divisor(pl1), M) eq 0, ~nfail);

// ---- 4. a point of degree 2 ramified at P, and verify_divisor
check("residue_field_embeddings: none for the point of degree 2 over F(sqrt -11), which is ramified at P",
      #residue_field_embeddings(quad, M, dataM) eq 0 and #point_records(M, dataM, [quad]) eq 0, ~nfail);
okk, key := place_key(quad, M, dataM);
jq := [i : i in [1..#discs] | discs[i]`home eq 1 and discs[i]`key cmpeq key];
check("place_key: the ramified point reduces to the centre of a single disc of the model, with multiplicity 2",
      okk and #jq eq 1 and frob[jq[1]] eq jq[1], ~nfail);
ok, D := verify_divisor(X^2 + 5/3*X + 1, 1, discs[jq[1]]`centre, discs[jq[1]]`centre, sweep);
check("verify_divisor: the ramified point lies in the diagonal class of that disc", ok and D eq Divisor(quad), ~nfail);
ok, D := verify_divisor(X^2 + X - 1, 1, discs[jq[1]]`centre, discs[jq[1]]`centre, sweep);
check("verify_divisor: the sum of the two F-rational points does not lie in that class", not ok, ~nfail);
_, pts := divisor_points([<pl1, 1>, <pl2, 1>], sweep, discs);
ok, D := verify_divisor(X^2 + X - 1, 1, discs[pts[1][1]]`centre, discs[pts[2][1]]`centre, sweep);
check("verify_divisor: the sum of the two F-rational points lies in the class of their discs",
      ok and D eq Divisor(pl1) + Divisor(pl2), ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
