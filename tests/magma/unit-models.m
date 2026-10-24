// tests/magma/unit-models.m   [unit test: models.m]
//
//     magma -b tests/magma/unit-models.m        (from the repository root)
//
// The plane models of curves for the library (curve_model, lc_scaling, mobius_model,
// improve_model), their good primes (good_primes: all good-reduction assumptions of the
// article, and the trial run frobenius_check), the affine patches, and the conversion of the
// points of a curve into point records (point_records), on
//   * the genus-2 curve 971.a.971.1: y^2 + y = x^5 - 2x^3 + x over Q,
//   * the plane quartics X^4 + Y^4 + XYZ^2 - Z^4 and the Klein quartic over Q,
//   * a canonical genus-4 curve in P^3 (projected to the plane),
//   * X(s3,ns5): a plane quartic over Q(sqrt 5).
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
load "models.m";
SetColumns(0);
SetLogFile("tests/magma/unit-models.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
norms := func< Ps | [ Norm(P) : P in Ps ] >;

// ---- 1. a polynomial over Q: 971.a.971.1
R<x,y> := PolynomialRing(Rationals(), 2);
M := curve_model(y^2 + y - (x^5 - 2*x^3 + x));
check("curve_model of a polynomial: the monic model itself, consistent with its functions",
      Sprint(M`Q) eq "y^2 + y - x^5 + 2*x^3 - x" and model_is_consistent(M), ~nfail);
good, bad := good_primes(M : bound := 20);
check("good_primes: [3,5,7,11,13,17,19]; 2 is bad (the leading coefficient of r is 4)",
      norms(good) eq [3,5,7,11,13,17,19] and #bad eq 1 and Norm(bad[1][1]) eq 2
      and Position(bad[1][2], "leading coefficient of r") gt 0, ~nfail);
good5 := good_primes(M : primes := [5, 7], check := true, N := 5);
check("good_primes with check (coleman_data and the zeta function of the reduction) at 5, 7",
      norms(good5) eq [5,7], ~nfail);
Mm := mobius_model(M, Matrix(Integers(), 2, 2, [1,1,1,0]));   // x = 1 + 1/x'
check("mobius_model x = 1 + 1/x': monic, of degree 2 in y and genus 2, consistent",
      LeadingCoefficient(Mm`Q) eq 1 and Degree(Mm`Q) eq 2 and Genus(FunctionField(Mm`Q)) eq 2
      and model_is_consistent(Mm), ~nfail);
ranked := improve_model(M : bound := 20, verbose := false);
check("improve_model: every candidate is a consistent model of genus 2 with good primes",
      &and[ model_is_consistent(r[1]) and Genus(FunctionField(r[1]`Q)) eq 2 : r in ranked ]
      and #ranked[1][2] ge #good, ~nfail);
check("improve_model: on equal good primes the given model is kept", ranked[1][1]`Q eq M`Q, ~nfail);

// ---- 2. lc_scaling of a model that is not monic and not integral
Lx<X> := PolynomialRing(QQ_number_field); Lxy<Y> := PolynomialRing(Lx);
Qm, c := lc_scaling(3*Y^2 + X*Y - X^5/4);
check("lc_scaling: 3y^2 + xy - x^5/4 becomes monic with integral coefficients, y' = c*y with c = 6",
      LeadingCoefficient(Qm) eq 1 and &and[ IsIntegral(a) : a in Coefficients(b), b in Coefficients(Qm) ]
      and c eq 6, ~nfail);
Qm2, c2 := lc_scaling(X*Y^2 + Y - X^3);
check("lc_scaling: a non-constant leading coefficient a(x) = x gives y' = x*y",
      LeadingCoefficient(Qm2) eq 1 and c2 eq X, ~nfail);

// ---- 3. a plane quartic over Q: patches, records, minimal model
P2<U,V,W> := ProjectiveSpace(Rationals(), 2);
C := Curve(P2, U^4 + V^4 + U*V*W^2 - W^4);
MC := curve_model(C);
goodC, badC := good_primes(MC : bound := 20);
check("plane quartic: good primes [5,11,13,17,19]; 3 and 7: r mod P is not separable",
      norms(goodC) eq [5,11,13,17,19] and Position(badC[2][2], "not separable") gt 0, ~nfail);
P17 := goodC[4];
pat := affine_patches(MC, P17 : verbose := false);
check("affine_patches at 17: the patches cover all smooth F_17-points, each patch is consistent",
      #pat`uncovered eq 0 and #pat`singular eq 0 and #pat`patches ge 2
      and &+[ #x : x in pat`points ] eq #Points(Curve(ProjectiveSpace(GF(17),2), U^4 + V^4 + U*V*W^2 - W^4))
      and &and[ model_is_consistent(Mp) : Mp in pat`patches ], ~nfail);
data := coleman_data(MC`Q, MC`L, goodC[1], 5 : verbose := false);
pts := PointSearch(C, 10);
recs := point_records(MC, data, pts);
check("point_records: one finite record for each of the 6 points of the quartic, in different discs",
      #recs eq 6 and &and[ not r`inf : r in recs ]
      and &and[ not lie_in_same_disc(recs[i], recs[j], data) : j in [i+1..#recs], i in [1..#recs] ], ~nfail);
cands := minimal_models_over_Q(MC);
check("minimal_models_over_Q: MinimizeReducePlaneQuartic gives a consistent model",
      #cands eq 1 and model_is_consistent(cands[1]), ~nfail);

// ---- 4. the Klein quartic: (0:1:0) lies on the curve, the patch Z = 1 has degree 3 in y
K4 := Curve(P2, U^3*V + V^3*W + W^3*U);
MK := curve_model(K4);
check("curve_model of the Klein quartic: the patch Z = 1, monic of degree 3 in y",
      Degree(MK`Q) eq 3 and LeadingCoefficient(MK`Q) eq 1 and model_is_consistent(MK), ~nfail);
patK := affine_patches(MK, good_primes(MK : primes := [11])[1] : verbose := false);
check("affine_patches: the 12 points of the Klein quartic mod 11 lie in good discs of the patches",
      #patK`uncovered eq 0 and &+[ #x : x in patK`points ] eq 12, ~nfail);
dataK := coleman_data(MK`Q, MK`L, 11, 4 : verbose := false);
recK := point_records(MK, dataK, [K4![1,0,0], K4![0,1,0], K4![0,0,1]]);
check("point_records: the three rational points of the Klein quartic", #recK eq 3, ~nfail);

// ---- 5. a curve in P^3: projected to the plane
P3<x0,x1,x2,x3> := ProjectiveSpace(Rationals(), 3);
E := Curve(P3, [x0*x3 - x1*x2, x0^3 + 2*x1^3 + 3*x2^3 + 5*x3^3 + x0*x1*x2]);
ME := curve_model(E);
check("curve_model of a genus-4 curve in P^3: a plane model of genus 4, consistent",
      Genus(FunctionField(ME`Q)) eq 4 and model_is_consistent(ME) and #ME`desc ge 1, ~nfail);

// ---- 6. a curve over Q(sqrt 5)
_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
Fx<x5> := PolynomialRing(F); Fxy<y5> := PolynomialRing(Fx);
Q5 := y5^4 - 2*y5^3*x5 - y5^2*x5^2 - 8*y5^3 - 2*y5^2*x5 + 2*y5*x5^2 + x5^3 + 3*y5^2 + 3*y5*x5 - 3*x5^2 - 2*y5 + 3*x5 - 1;
M5 := curve_model(Q5);
check("X(s3,ns5) over Q(sqrt 5): good primes of norm <= 40 are the primes above 19, 29, 31",
      norms(good_primes(M5 : bound := 40)) eq [19,19,29,29,31,31], ~nfail);

// ---- 7. the helpers of models.m, on the model M of 971.a.971.1 (section 1) at 7
Lq, toL := model_field(Rationals());
Lk, toLk := model_field(QuadraticField(5));
check("model_field: Q as a number field of degree 1, a quadratic field as a FldNum; from_model_field inverts the map",
      Type(Lq) eq FldNum and Degree(Lq) eq 1 and Type(Lk) eq FldNum and Degree(Lk) eq 2
      and from_model_field(toLk(QuadraticField(5).1), QuadraticField(5)) eq QuadraticField(5).1, ~nfail);
Rq<u,v> := PolynomialRing(Lq, 2);
check("map_coefficients: x^2 + 3/2*y over Q mapped into L[u,v]",
      map_coefficients(x^2 + 3/2*y, Rq, toL) eq u^2 + 3/2*v, ~nfail);
Fh := homogenization(M`Q);
check("homogenization: F(x, y, 1) = Q(x, y), homogeneous of degree 5",
      IsHomogeneous(Fh) and TotalDegree(Fh) eq 5
      and Evaluate(Fh, [Parent(M`Q)!BaseRing(Parent(M`Q)).1, Parent(M`Q).1, 1]) eq M`Q, ~nfail);
check("transform_plane_model with the identity: the same equation, a consistent model",
      transform_plane_model(M, IdentityMatrix(Integers(), 3))`Q eq M`Q
      and model_is_consistent(transform_plane_model(M, IdentityMatrix(Integers(), 3))), ~nfail);
Me := model_from_equation(M, M`Q, M`xf, M`yf, "the same equation");
check("model_from_equation: the model of the same curve from its equation and functions",
      Me`Q eq M`Q and model_is_consistent(Me), ~nfail);
check("primes_up_to_norm: the primes of Q of norm <= 20 in order",
      norms(primes_up_to_norm(M`L, 20)) eq [2,3,5,7,11,13,17,19], ~nfail);
check("model_height: the largest coefficient of y^2 + y - x^5 + 2x^3 - x is 2", model_height(M`Q) eq 2, ~nfail);
P7 := [P : P in primes_up_to_norm(M`L, 7) | Norm(P) eq 7][1];
data7 := coleman_data(M`Q, M`L, P7, 6 : verbose := false);
b0M := model_basis_functions(M, data7`W0);
check("model_basis_functions: b^0 = (1, y) for W0 = 1", b0M[1] eq 1 and b0M[2] eq M`yf, ~nfail);
FF7 := reduced_curve_function_field(M, P7);
check("reduced_curve_function_field: genus 2 and #X(F_7) = #Fq_points of coleman_data",
      Genus(FF7) eq 2 and #Places(FF7, 1) eq #Fq_points(data7), ~nfail);
forms := holomorphic_forms(M, data7);
check("holomorphic_forms: g = 2 holomorphic differentials of the function field",
      #forms eq 2 and forall{w : w in forms | IsEffective(Divisor(w))}, ~nfail);
check("holomorphic_transition: the identity matrix between a model and itself",
      holomorphic_transition(M, data7, M, data7) eq IdentityMatrix(BaseRing(M`C), 2), ~nfail);
R00 := set_point(0, 0, data7);
check("plane_reduction: the point (0,0) reduces to (0 : 0 : 1)",
      Eltseq(plane_reduction(M, data7, R00)) eq [0, 0, 1], ~nfail);
check("jacobian_rank_bounds: rank 1 for 971.a.971.1", jacobian_rank_bounds(M) eq [1, 1], ~nfail);
gs := patch_candidates(300);
check("patch_candidates: the identity first, 300 distinct coordinate changes, a shorter list is a prefix",
      IsOne(gs[1]) and #gs eq 300 and #Set(gs) eq 300 and patch_candidates(5) eq gs[1..5], ~nfail);
_, res5 := ResidueClassField(goodC[1]);
test5 := reduced_good_test(MC, IdentityMatrix(Integers(), 3), goodC[1], res5);
pts5 := Points(Curve(ProjectiveSpace(GF(5), 2), U^4 + V^4 + U*V*W^2 - W^4));
check("reduced_good_test: the points of the quartic mod 5 that it calls good are the good residue discs of the model",
      #[p : p in pts5 | test5(Eltseq(p))] eq #[R : R in Qq_points(data) | not is_bad(R, data)], ~nfail);

// ---- 8. points of degree 2 (for quadratic_points.m), on X(b3,ns5): y^2 = f(x) over Q(sqrt 5) at
//         the prime above 11: the inert quadratic extension, coleman_data over it, the records of
//         places of degree 2, a transition matrix over it
A2b<ab,bb> := AffineSpace(F, 2);
Cb := Curve(A2b, bb^2 - (9*ab^6 - 6*ab^5 - 35*ab^4 + 40*ab^2 + 12*ab - 8));
FFb := FunctionField(Cb);
Mb := curve_model(Cb);
P11 := Decomposition(MaximalOrder(Mb`L), 11)[1][1];
L2, P11b, u := inert_quadratic_extension(Mb`L, P11);
_, res11 := ResidueClassField(P11);
check("inert_quadratic_extension: u = 2, not a square mod P; P stays prime in L(sqrt 2), of norm 121",
      u eq 2 and not IsSquare(res11(u)) and Degree(L2) eq 4 and Norm(P11b) eq 121, ~nfail);
even := false;
try
  _ := inert_quadratic_extension(Mb`L, Decomposition(MaximalOrder(Mb`L), 2)[1][1]);
catch e
  even := Position(e`Object, "must be odd") gt 0;
end try;
check("inert_quadratic_extension: an error for a prime above 2", even, ~nfail);
datab := model_coleman_data(Mb, P11, 6 : aux := true, extension := <L2, P11b, u>);
datab1 := model_coleman_data(Mb, P11, 6);
// L_121(T^2) = L_11(T)*L_11(-T); the characteristic polynomial of F is T^(2g)*L_121(1/T)
L11 := LPolynomial(reduced_curve_function_field(Mb, P11));
prod := L11*Evaluate(L11, -Parent(L11).1);
L121 := Parent(L11)![Coefficient(prod, 2*i) : i in [0..4]];
cpb := Coefficients(CharacteristicPolynomial(ChangeRing(datab`F, datab`m)));
check("model_coleman_data with aux: K = Q_(11^2), the Frobenius matrix matches the zeta function of the reduction over F_121",
      #ResidueClassField(RingOfIntegers(datab`K)) eq 121 and #cpb eq 5
      and &and[Valuation(cpb[i] - Coefficient(L121, 5 - i)) ge 5 : i in [1..5]]
      and #ResidueClassField(RingOfIntegers(datab1`K)) eq 11, ~nfail);
Xb := PolynomialRing(F).1;
place2 := func< mp | [pl : pl in Zeros(Evaluate(mp, FFb!ab)) | Degree(pl) eq 2][1] >;
plsplit := place2(Xb^2 + 1/6*(3*s - 5)*Xb + 1/3*(s - 7));
plinert := place2(Xb^2 + 1/6*(3*s - 5)*Xb + 1/6*(-3*s + 1));
plram := place2(Xb^2 + 5/3*Xb + 1);
nrec := func< dat, pl | #point_records(Mb, dat, [pl]) >;
check("point_records of places of degree 2: split at P 2 records over Q_11 and Q_121, inert at P 2 only over Q_121, ramified none",
      [nrec(datab1, plsplit), nrec(datab, plsplit), nrec(datab1, plinert), nrec(datab, plinert), nrec(datab1, plram), nrec(datab, plram)]
      eq [2, 2, 0, 2, 0, 0], ~nfail);
recsb, whichb := point_records(Mb, datab, [* plsplit, 2*Divisor(plinert) *]);
OKb := RingOfIntegers(datab`K); _, redb := ResidueClassField(OKb);
xr := [redb(OKb!R`x) : R in recsb[3..4]];
check("point_records of a divisor: the points of its support with multiplicities, and the index of their origin",
      #recsb eq 6 and whichb eq [1, 1, 2, 2, 2, 2], ~nfail);
check("the two points of the inert place reduce to Frobenius-conjugate points of F_121 outside F_11",
      xr[2] eq xr[1]^11 and xr[1] ne xr[1]^11, ~nfail);
Mp, kp, cp := mobius_model(Mb, Matrix(Integers(), 2, 2, [0,1,1,0]));   // x = 1/x'
datap := model_coleman_data(Mp, P11, 6 : aux := true, extension := <L2, P11b, u>);
Tb := holomorphic_transition(Mb, datab, Mp, datap);
check("mobius_model x = 1/x': k = 3 for the sextic, constant c = 1; the data of the patch over the same field L(sqrt 2)",
      kp eq 3 and cp eq 1 and datap`L cmpeq datab`L, ~nfail);
check("holomorphic_transition over L(sqrt 2): x = 1/x' exchanges the forms dx/y and x dx/y (an antidiagonal matrix over L(sqrt 2))",
      BaseRing(Tb) cmpeq L2 and Tb[1,1] eq 0 and Tb[2,2] eq 0 and Tb[1,2]*Tb[2,1] ne 0, ~nfail);
other := false;
try
  _ := holomorphic_transition(Mb, model_coleman_data(Mb, P11, 6 : aux := true), Mp, datap);
catch e
  other := Position(e`Object, "same number field") gt 0;
end try;
check("holomorphic_transition: an error for data over two copies of L(sqrt 2)", other, ~nfail);
r2 := Roots(PolynomialRing(L2).1^2 - 2)[1][1];
outside := false;
try
  _ := to_curve_field(r2, Mb);
catch e
  outside := Position(e`Object, "does not lie in the field of the model") gt 0;
end try;
check("to_curve_field: an element of L(sqrt 2) in Q(sqrt 5) as an element of the base field; an error for sqrt 2",
      to_curve_field(L2!(Mb`L.1), Mb) eq F.1 and outside, ~nfail);
check("jacobian_rank_bounds over Q(sqrt 5): 0 <= rank <= 0 for X(b3,ns5) (RankBound); none for the plane quartic X(s3,ns5)",
      jacobian_rank_bounds(Mb) eq [0, 0] and jacobian_rank_bounds(M5) eq [], ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
