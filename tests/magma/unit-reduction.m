// tests/magma/unit-reduction.m   [unit test: the cohomology data and the reduction steps]
//
//     magma -b tests/magma/unit-reduction.m        (from the repository root)
//
// The functions of cohobasis.m and reduction.m checked directly, through identities in the
// function field FF of the curve (df/dx = Differentiation(x, f)), on y^2 = x(x-1)(x+1)(x-2)(x+3)
// over Q at 7 (b^0 = (1, y), b^inf = (1, y/x^3), z = r/lc(r) = f):
//   * the connection matrices: d(b^0)/dx = G0*b^0 and d(b^inf)/dx = Ginf*b^inf exactly;
//   * the residue matrices and their Jordan forms (jordan_0, jordan_inf), the ramification
//     indices e_0 = e_inf = 2, and the residue maps res_0, res_inf, which vanish on the basis
//     of H^1_dR(X) but not on a form of the third kind;
//   * the basis of H^1_dR(X) (2g forms) and of H^1_dR(U) (2g + 5: the six points of X - U);
//   * the matrices of the finite and the infinite reduction steps (red_lists,
//     infinite_reduction_matrices) satisfy their defining congruence and equation;
//   * the reduction omega = d(f_0 + f_inf + f_end) + sum_i c_i omega_i (reduce_with_fs) and its
//     steps coho_red_fin, change_basis_b0binf/binfb0, coho_red_inf: exactly for forms with
//     poles only at infinity, modulo p^Nmax for forms with poles along z = 0 (the finite
//     reduction reduces its coefficients modulo P^Nmax);
//   * substitute_z, val_Lxz_d, the derivatives ddx*, ord_factors, ord_r, val_Lttinv_d, and the
//     reductions modulo P^N (mod_PN_data, reduce_mod_PN_*).
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
SetColumns(0);
SetLogFile("tests/magma/unit-reduction.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
f := x*(x-1)*(x+1)*(x-2)*(x+3);
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
data := coleman_data(y^2 - f, QQ, P7, 10 : verbose := false);
dataU := coleman_data(y^2 - f, QQ, P7, 10 : verbose := false, useU := true);
g := data`g; d := 2; p := data`p;

FF, Lt := model_function_field(data);
X := FF!Lt.1;
ev := func< a | Evaluate(Numerator(a), X)/Evaluate(Denominator(a), X) >;   // a in L(x) as a function
b0 := basis_functions(FF, data`W0); binf := basis_functions(FF, data`Winf);
Z := ev(data`r/LeadingCoefficient(data`r));
// the minimum over the coefficients a of D in FF (w.r.t. 1, y) of the Gauss valuation at p
gauss := function(D)
  vs := [];
  for a in Eltseq(D) do
    if a ne 0 then
      vg := func< h | Minimum([Valuation(Rationals()!c, p) : c in Coefficients(h) | c ne 0]) >;
      Append(~vs, vg(Numerator(a)) - vg(Denominator(a)));
    end if;
  end for;
  return #vs eq 0 select Infinity() else Minimum(vs);
end function;

// ---- cohobasis.m
check("connection matrices: d(b^0)/dx = G0*b^0 and d(b^inf)/dx = Ginf*b^inf",
      [Differentiation(X, b) : b in b0] eq [&+[ev(data`G0[i,j])*b0[j] : j in [1..d]] : i in [1..d]]
      and [Differentiation(X, b) : b in binf] eq [&+[ev(data`Ginf[i,j])*binf[j] : j in [1..d]] : i in [1..d]], ~nfail);
J0, _, T0inv := jordan_0(data`r, data`G0);
Jinf, Tinf, Tinfinv := jordan_inf(data`Ginf);
t := BaseRing(data`Ginf).1;
Rinf := -Evaluate((1/t)*Evaluate(data`Ginf, 1/t), 0);
check("jordan_inf: Jinf = Tinf*Ginf_(-1)*Tinf^(-1), diagonal with entries 0 and 1/2 (e_inf = 2)",
      Jinf eq Tinf*Rinf*Tinfinv and IsDiagonal(Jinf) and {Jinf[i,i] : i in [1..d]} eq {0, 1/2}, ~nfail);
check("jordan_0: one Jordan form per irreducible factor of r (5 linear factors), entries 0 and 1/2",
      #J0 eq 5 and forall{J : J in J0 | IsDiagonal(J) and {J[i,i] : i in [1..d]} eq {0, 1/2}}, ~nfail);
e0, einf := max_ramification_indices([J : J in J0], Jinf);
check("max_ramification_indices: e_0 = e_inf = 2 (the Weierstrass points)", e0 eq 2 and einf eq 2 and e0 eq data`e0 and einf eq data`einf, ~nfail);
check("res_0 and res_inf vanish on the basis of H^1_dR(X)",
      forall{w : w in data`basis | IsZero(res_0(w, data`Q, data`r, J0, T0inv)) and IsZero(res_inf(w, data`Q, data`r, data`W0, data`Winf, data`Ginf, Jinf, Tinfinv))}, ~nfail);
check("res_0 does not vanish on the form of the third kind dx/z = (1,0)",
      not IsZero(res_0(Parent(data`basis[1])![1, 0], data`Q, data`r, J0, T0inv)), ~nfail);
check("basis_coho: 2g = 4 forms for H^1_dR(X), 2g + 5 = 9 for H^1_dR(U) (six points in X - U)",
      #data`basis eq 2*g and #dataU`basis eq 2*g + 5, ~nfail);
Lxr := RationalFunctionField(QQ); xr := Lxr.1;
check("ord_factors, ord_r: (x-1)^2/(x*(x+3)) has orders 2, -1, -1 at x-1, x, x+3",
      ord_factors((xr-1)^2/(xr*(xr+3)), [x-1]) eq 2 and ord_factors((xr-1)^2/(xr*(xr+3)), [x, x+3]) eq -1
      and ord_r((xr-1)^2/(xr*(xr+3)), f) eq -1, ~nfail);
Ltt<tt> := LaurentSeriesRing(QQ);
check("val_Lttinv_d: the minimal valuation of a vector of Laurent series",
      val_Lttinv_d(Vector([tt^-2 + 1, tt^3])) eq -2, ~nfail);
check("ddx, ddx_vec, ddx_mat: the derivative in x of y^2*x^3, of (x^2, 1/x) and of [[x, x^2]]",
      ddx(x^3*y^2) eq 3*x^2*y^2 and ddx_vec(Vector([xr^2, 1/xr])) eq Vector([2*xr, -1/xr^2])
      and ddx_mat(Matrix(Lxr, 1, 2, [xr, xr^2])) eq Matrix(Lxr, 1, 2, [1, 2*xr]), ~nfail);

// ---- reduction.m: the matrices of the steps
z := data`r/LeadingCoefficient(data`r);
M0 := z*data`G0;
check("red_lists: red_list_fin[l]*(M0 - l*z'*I) = I mod z for l = 1, 2, 3 (finite reduction)",
      forall{l : l in [1..3] | forall{e : e in Eltseq(data`red_list_fin[l]*(M0 - l*Derivative(z)*IdentityMatrix(Parent(z), d)) - IdentityMatrix(Parent(z), d)) | Numerator(e) mod Numerator(z) eq 0}}, ~nfail);
mats := infinite_reduction_matrices(data`Ginf, 30);
check("infinite_reduction_matrices: (Ginf_(-1) - m*I)^(-1) for m = 1..30, extending red_list_inf",
      #mats eq 30 and forall{m : m in [1..30] | mats[m]*(ChangeRing(Rinf, QQ) - m*IdentityMatrix(QQ, d)) eq IdentityMatrix(QQ, d)}
      and forall{m : m in [1..#data`red_list_inf] | data`red_list_inf[m] eq mats[m]}, ~nfail);

// ---- reduction.m: the reduction of forms
Qd := data`Q; Lred := BaseRing(BaseRing(Parent(Qd))); Pred := p; // the rational branch
Lxz<zz> := LaurentSeriesRing(PolynomialRing(Lred));
xz := PolynomialRing(Lred).1;
// a Laurent series in x (or a polynomial) as a function
fun_x := function(s)
  if Type(s) eq RngUPolElt then return Evaluate(s, X); end if;
  v := Valuation(s); cs := Coefficients(s);
  return &+[FF | cs[k]*X^(v+k-1) : k in [1..#cs]];
end function;
// a Laurent series in t = 1/x as a function
fun_t := function(s)
  v := Valuation(s); cs := Coefficients(s);
  return &+[FF | cs[k]*X^(-(v+k-1)) : k in [1..#cs]];
end function;
// a vector of series in z^(-1) w.r.t. b^0 as a function
fun_z := func< v | &+[FF | &+[FF | Evaluate(Coefficient(v[i], j), X)*Z^j : j in [Valuation(v[i])..-1]] * b0[i] : i in [1..d] | v[i] ne 0] >;
basisfun := [&+[FF | Evaluate(bk[i], X)*b0[i] : i in [1..d]]/Z : bk in data`basis];
redinf := infinite_reduction_matrices(data`Ginf, 40);
for spec in [<5, 0>, <8, 0>, <1, 2>, <0, 3>] do
  k, l := Explode(spec);
  w := RSpace(Lxz, d)![Lxz | 0, (Lxz!xz^k)*zz^(-l)];
  coefs, f0, finf, fend := reduce_with_fs(w, Qd, Lred, Pred, data`N, data`Nmaxred, data`r, data`W0, data`Winf,
                                          data`G0, data`Ginf, data`red_list_fin, redinf, data`basis, data`exact_primitives, data`monomial_to_basis);
  F := fun_z(f0) + &+[FF | fun_x(finf[i])*binf[i] : i in [1..d] | finf[i] ne 0] + &+[FF | Evaluate(fend[i], X)*b0[i] : i in [1..d]];
  D := X^k*Z^(-l)*b0[2]/Z - Differentiation(X, F) - &+[FF | coefs[i]*basisfun[i] : i in [1..#coefs]];
  v := gauss(D);
  check(Sprintf("reduce_with_fs: x^%o y dx/z^%o = d(f0 + finf + fend) + sum c_i omega_i %o", k, l+1,
                (l eq 0) select "exactly" else Sprintf("modulo 7^%o", data`Nmaxred)),
        (l eq 0 and v cmpeq Infinity()) or (l gt 0 and v ge data`Nmaxred), ~nfail);
end for;

// the steps separately: the finite reduction of y dx/z^3, then the infinite reduction of x^8 y dx/z
w := RSpace(Lxz, d)![Lxz | 0, zz^(-2)];
w1, f0 := coho_red_fin(w, Qd, Lred, Pred, data`Nmaxred, data`r, data`G0, data`red_list_fin);
D := Z^(-2)*b0[2]/Z - Differentiation(X, fun_z(f0)) - &+[FF | Evaluate(Coefficient(w1[i], 0), X)*b0[i] : i in [1..d]]/Z;
check("coho_red_fin: y dx/z^3 = d(f0) + w' b^0 dx/z with w' without poles along z, modulo 7^Nmax",
      forall{i : i in [1..d] | w1[i] eq 0 or Valuation(w1[i]) ge 0} and gauss(D) ge data`Nmaxred, ~nfail);
w := RSpace(Lxz, d)![Lxz | 0, Lxz!xz^8];
winf := change_basis_b0binf(w, Lred, Pred, data`Nmaxred, data`r, data`W0, data`Winf);
check("change_basis_b0binf and change_basis_binfb0: the round trip returns the form",
      Eltseq(change_basis_binfb0(winf, Lred, data`W0, data`Winf)) eq [PolynomialRing(Lred) | 0, xz^8], ~nfail);
w2, finf := coho_red_inf(winf, Qd, Lred, Pred, data`Nmaxred, data`r, data`W0, data`Winf, data`Ginf, redinf, 0);
D := X^8*b0[2]/Z - Differentiation(X, &+[FF | fun_x(finf[i])*binf[i] : i in [1..d] | finf[i] ne 0])
     - &+[FF | fun_t(w2[i])*binf[i] : i in [1..d] | w2[i] ne 0]/Z;   // finf in x, the remainder w' in t = 1/x
check("coho_red_inf: x^8 y dx/z = d(finf) + w' b^inf dx/z exactly, ord_inf(w') > ord_0(W) - deg(r) + 1 = -7",
      D eq 0 and forall{i : i in [1..d] | w2[i] eq 0 or Valuation(w2[i]) gt -7}, ~nfail);
check("substitute_z: f(g) for f = 1 + x*z + z^2 + x^3*z^5 and g = x^2 - 1",
      substitute_z(1 + xz*zz + zz^2 + xz^3*zz^5, xz^2 - 1, Lred, Pred, 5) eq 1 + xz*(xz^2-1) + (xz^2-1)^2 + xz^3*(xz^2-1)^5, ~nfail);
check("val_Lxz_d: the minimal z-adic valuation of a vector", val_Lxz_d(RSpace(Lxz, 2)![zz^-3 + 1, xz*zz]) eq -3, ~nfail);

// ---- the correction functions at a point (integrals.m), against their direct evaluation
G := connection_matrix(data`Q, data`Delta, data`s);
G0c, Ginfc := connection_matrices_0_inf(G, data`W0, data`Winf);
check("connection_matrices_0_inf: the matrices G0 and Ginf of coleman_data", G0c eq data`G0 and Ginfc eq data`Ginf, ~nfail);
Pt := set_point(3, 12, data);                         // z(3) = f(3) = 144 = 12^2
b0P := [Rationals() | 1, 12]; binfP := [Rationals() | 1, 12/27];
w := RSpace(Lxz, d)![Lxz | 0, (Lxz!xz)*zz^(-2)];      // x y dx/z^3: f_0 is not zero
coefs, f0, finf, fend := reduce_with_fs(w, Qd, Lred, Pred, data`N, data`Nmaxred, data`r, data`W0, data`Winf,
                                        data`G0, data`Ginf, data`red_list_fin, redinf, data`basis, data`exact_primitives, data`monomial_to_basis);
w := RSpace(Lxz, d)![Lxz | 0, Lxz!xz^8];              // x^8 y dx/z: f_inf is not zero
_, _, finf8, fend8 := reduce_with_fs(w, Qd, Lred, Pred, data`N, data`Nmaxred, data`r, data`W0, data`Winf,
                                     data`G0, data`Ginf, data`red_list_fin, redinf, data`basis, data`exact_primitives, data`monomial_to_basis);
pre := correction_data_K([f0, f0], [finf8, finf8], [fend8, fend8], data, data`m);
v0, N0 := evalf0(f0, Pt, data : pre := pre);
direct0 := &+[Rationals() | &+[Rationals() | Evaluate(Coefficient(f0[i], l), 3)*144^l : l in [Valuation(f0[i])..-1]]*b0P[i] : i in [1..d] | f0[i] ne 0];
check("evalf0: f_0(3,12) of x y dx/z^3 agrees with the direct evaluation to its precision",
      N0 ge 1 and Valuation(v0 - data`m(direct0)) ge N0, ~nfail);
vinf, Ninf := evalfinf(finf8, Pt, data : pre := pre`finf[1]);
evx := func< s | &+[Rationals() | Coefficients(s)[k]*3^(Valuation(s)+k-1) : k in [1..#Coefficients(s)]] >;
directinf := &+[Rationals() | evx(finf8[i])*binfP[i] : i in [1..d] | finf8[i] ne 0];
check("evalfinf: f_inf(3,12) of x^8 y dx/z agrees with the direct evaluation to its precision",
      Ninf ge 1 and Valuation(vinf - data`m(directinf)) ge Ninf, ~nfail);

// ---- reduction.m: reduction modulo P^N

g7 := x^3/49 + 50*x + 7^12;                  // P-adic valuations -2, 0, 12
r7 := reduce_mod_PN_Lx(g7, QQ, P7, 5);
check("reduce_mod_PN_Lx: a polynomial congruent coefficientwise modulo 7^5 (here also v = -2)",
      forall{c : c in Coefficients(g7 - r7) | c eq 0 or Valuation(c, P7) ge 5}, ~nfail);
cache := AssociativeArray();
r7c, cache := reduce_mod_PN_Lx_cached(g7, cache, QQ, P7, 5);
check("reduce_mod_PN_Lx_cached: the same reduction, with the data of the denominator 49 cached",
      r7c eq r7 and #Keys(cache) eq 1, ~nfail);
A7 := Matrix(QQ, 2, 2, [1/7, 8^7, 7^9, 3]);
check("reduce_mod_PN_L_mat: entrywise congruent modulo 7^4",
      forall{c : c in Eltseq(A7 - reduce_mod_PN_L_mat(A7, QQ, P7, 4)) | c eq 0 or Valuation(c, P7) ge 4}, ~nfail);
Lt7<t7> := LaurentSeriesRing(QQ);
s7 := t7^-1/49 + 1 + 7^6*t7;
check("reduce_mod_PN_Lttinv: coefficientwise congruent modulo 7^3",
      forall{c : c in Coefficients(s7 - reduce_mod_PN_Lttinv(s7, QQ, P7, 3)) | c eq 0 or Valuation(c, P7) ge 3}, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
