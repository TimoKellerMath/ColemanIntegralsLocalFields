// tests/magma/unit-internals.m   [unit test: internal functions of the library]
//
//     magma -b tests/magma/unit-internals.m        (from the repository root)
//
// Facts that the internal functions must satisfy, independently of the article's examples:
// the auxiliary polynomials and integral bases of a hyperelliptic model, the connection
// matrix, the reduction modulo P^N, the coercions to K, the roots of non-monic linear factors,
// the root finder with precisions (also over a ramified ring), the kernel of a matrix over
// Q_p, the Frobenius automorphism of a Galois field, the shared function field helpers, the
// precision helpers, and the zeros of integrals on a residue disc over a ramified K.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
SetColumns(0);
SetLogFile("tests/magma/unit-internals.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
f := x*(x-1)*(x+1)*(x-2)*(x+3);
Q := y^2 - f;

// ---- auxpolys.m, isrational.m
r, Delta, s := auxpolys(Q);
check("auxpolys(y^2 - f): r = Delta = 4f, s = 2y, s*dQ/dy = Delta mod Q",
      r eq 4*f and Delta eq 4*f and s eq 2*y and (s*Derivative(Q) - Delta) mod Q eq 0, ~nfail);
Q1, rat := coefficients_over_Q(Q);
L2<w> := NumberField(PolynomialRing(Rationals()).1^2 - 2);
L2x<x2> := PolynomialRing(L2); L2xy<y2> := PolynomialRing(L2x);
_, rat2 := coefficients_over_Q(y2^2 - x2^5 - w);
_, rat3 := coefficients_over_Q(y2^2 - x2^5 - 3);
check("coefficients_over_Q: rational for Q over Q and for y^2 - x^5 - 3 over Q(sqrt 2), not for y^2 - x^5 - sqrt 2",
      rat and rat3 and not rat2 and BaseRing(BaseRing(Parent(Q1))) eq Rationals(), ~nfail);
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
check("is_separable_mod_P: r = 4f mod 7 is separable of degree 5, x^2 + 7 is not",
      is_separable_mod_P(r, P7) and not is_separable_mod_P(x^2 + 7, P7), ~nfail);
check("genus_of_reduction: genus 2 mod 7", genus_of_reduction(Q, P7) eq 2, ~nfail);

// ---- cohobasis.m
W0 := mat_W0(Q); Winf := mat_Winf(Q);
check("mat_W0 = identity and mat_Winf = diag(1, 1/x^3) for y^2 = f of degree 5",
      W0 eq IdentityMatrix(BaseRing(W0), 2) and Winf eq DiagonalMatrix(BaseRing(Winf), [1, 1/BaseRing(Winf).1^3]), ~nfail);
check("is_integral: W0, Winf and their inverses are 7-integral, 1/7 is not",
      &and[ is_integral(A, P7) : A in [W0, W0^-1, Winf, Winf^-1] ]
      and not is_integral(Matrix(BaseRing(W0), 1, 1, [1/7]), P7), ~nfail);
G := connection_matrix(Q, Delta, s);
check("connection_matrix: d(y)/dx = f'/(2f)*y, i.e. G = diag(0, f'/(2f))",
      G[1,1] eq 0 and G[1,2] eq 0 and G[2,1] eq 0 and G[2,2] eq Derivative(f)/(2*f), ~nfail);
check("polys_to_vec: [1 + 2x, 3x^2] with degx = 2 gives (1,2,0,0,0,3)",
      Eltseq(polys_to_vec([1 + 2*x, 3*x^2], 2)) eq [1,2,0,0,0,3], ~nfail);
check("reduce_mod_Q_exact: y^3 mod Q = f*y", reduce_mod_Q_exact(PolynomialRing(FieldOfFractions(Lx))!(y^3), PolynomialRing(FieldOfFractions(Lx))!Q)
      eq PolynomialRing(FieldOfFractions(Lx))![0, f], ~nfail);

// ---- reduction.m
g := (1/3)*x^2 + (7^5/2)*x + 22;
h := reduce_mod_PN_Lx(g, QQ, P7, 4);
check("reduce_mod_PN_Lx: congruent to g modulo 7^4, with the coefficient 7^5/2 removed",
      &and[ Valuation(c, P7) ge 4 : c in Coefficients(h - g) ] and Coefficient(h, 1) eq 0, ~nfail);
check("reduce_mod_PN_L: 1/(1-7) modulo 7^3 is 1 + 7 + 49",
      reduce_mod_PN_L(1/(1-7), QQ, P7, 3) eq 57, ~nfail);
check("finite_reduction_matrix: (0 - I)^(-1)/r' = -1/(2x) = x/2 mod x^2 + 1 for M0 = 0, l = 1",
      finite_reduction_matrix(QQ, x^2 + 1, ZeroMatrix(Lx, 2, 2), 1) eq Matrix(Lx, 2, 2, [x/2, 0, 0, x/2]), ~nfail);

// ---- coercion.m
K := pAdicField(7, 10);
m := map< QQ -> K | a :-> K!Rationals()!a >;
check("coer_poly and eval_frac: f(3) = 3*2*4*1*6 = 144 in Q_7",
      Evaluate(coer_poly(f, QQ, K, m), K!3) eq 144 and eval_frac(f/(x+1), QQ, K, m, K!3) eq 36, ~nfail);
check("eval_mat: W0(3) is the identity", eval_mat(W0, QQ, K, m, K!3) eq IdentityMatrix(K, 2), ~nfail);

// ---- expansion.m
F49<w>:=GF(49); F49t<t>:=PowerSeriesRing(F49,20); F49ty<Y>:=PolynomialRing(F49t);
fac:=[<(2+t)*Y+3*t,1>,<Y^2+t,1>,<t*Y+1,1>,<(1+O(t^5))*Y-t,1>];
check("unit_linear_roots over F_49[[t]]: the roots of the linear factors with unit leading coefficient, also if it is not 1",
      #unit_linear_roots(fac) eq 2 and IsWeaklyZero(unit_linear_roots(fac)[1]+3*t/(2+t)) and IsWeaklyZero(unit_linear_roots(fac)[2]-t), ~nfail);
Z7<s>:=PolynomialRing(pAdicRing(7,10));
check("unit_linear_roots over Z_7: the root 3/8 of 8*s - 3, none for 7*s - 1",
      unit_linear_roots([<8*s-3,1>,<7*s-1,1>]) eq [pAdicRing(7,10)!3/8], ~nfail);

// ---- solver.m
Zq := pAdicRing(7, 10); Zqt<t> := PolynomialRing(Zq);
roots := roots_with_precision((t - 1)*(t - 2)*(t - 9)*t);
check("roots_with_precision: the roots 0, 1, 2, 9 of t(t-1)(t-2)(t-9) over Z_7 (2 and 9 in one residue class, 2 exact)",
      {Integers()!rt[1] : rt in roots} eq {0, 1, 2, 9} and &and[ rt[2] ge 8 : rt in roots ], ~nfail);
roots := roots_with_precision(7*(t - 3)*(t - 10));
check("roots_with_precision: the content 7 is removed; roots 3 and 10 (one residue class) with precision 8",
      {Integers()!rt[1] mod 7^8 : rt in roots} eq {3, 10} and &and[ rt[2] eq 8 : rt in roots ], ~nfail);
roots := roots_with_precision((t - 2)^2*(t - 3));
check("roots_with_precision: a double root is reported with precision <= 0",
      #roots eq 2 and exists{rt : rt in roots | Integers()!rt[1] eq 2 and rt[2] le 0}, ~nfail);
Z5 := pAdicRing(5, 10); Z5u<u> := PolynomialRing(Z5);
R := TotallyRamifiedExtension(Z5, u^2 - 5); Rt<T> := PolynomialRing(R); pi := UniformizingElement(R);
roots := roots_with_precision((T - pi)*(T - 1)*(T - 1 - pi^3));
check("roots_with_precision over Z_5[sqrt 5] (ramified): the roots pi, 1, 1 + pi^3 (the last two in one residue class)",
      #roots eq 3 and &and[ exists{ rt : rt in roots | Valuation(rt[1] - z) ge 6 and rt[2] ge 6 } : z in [pi, R!1, 1 + pi^3] ], ~nfail);
Qp := pAdicField(7, 10);
ker, Nker := basis_kernel(Matrix(Qp, 3, 1, [1, 2, 3]));
check("basis_kernel: the left kernel of (1,2,3)^T has dimension 2",
      #ker eq 2 and &and[ IsWeaklyZero(v[1] + 2*v[2] + 3*v[3]) : v in ker ], ~nfail);
ker49, Nker49 := basis_kernel(Matrix(Qp, 3, 2, [1, 0, 0, 49, 7, 0]));
check("basis_kernel: the precision of the kernel, 10 for (1,2,3)^T, 10 - 2 when the elementary divisors are 1, 49",
      Nker eq 10 and #ker49 eq 1 and Nker49 eq 8, ~nfail);

// ---- frobenius.m
L7<z> := NumberField(PolynomialRing(Rationals()).1^3 + PolynomialRing(Rationals()).1^2 - 2*PolynomialRing(Rationals()).1 - 1); // Q(zeta_7)^+
P3 := Decomposition(MaximalOrder(L7), 3)[1][1]; // inert, f = 3
tau := frobenius_aut(L7, P3);
Fq, res := ResidueClassField(P3);
check("frobenius_aut: an automorphism of Q(zeta_7)^+ with tau(a) = a^3 mod P (3 is inert)",
      Type(tau) ne RngIntElt and &and[ res(MaximalOrder(L7)!tau(L7!b)) eq res(MaximalOrder(L7)!b)^3 : b in Basis(MaximalOrder(L7)) ], ~nfail);
tauN := frobenius_aut_local(L7, P3, 6);
check("frobenius_aut_local agrees with frobenius_aut modulo P^6",
      &and[ Valuation(tauN(b) - tau(b), P3) ge 6 : b in [z, z^2 + 1/3, 5*z - 2] ], ~nfail);

// ---- integrals.m: helpers
data := coleman_data(Q, QQ, P7, 8 : verbose := false);
FF, Lt := model_function_field(data);
b0 := basis_functions(FF, data`W0);
check("model_function_field and basis_functions: b^0 = (1, y), and y^2 = f in FF",
      b0[1] eq 1 and b0[2] eq FF.1 and FF.1^2 eq FF!Evaluate(f, Lt.1), ~nfail);
FFq, mm, Fqx := reduced_function_field(data);
check("reduced_function_field: genus 2, with 8 places of degree 1 (#X(F_7) = 8)",
      Genus(FFq) eq 2 and #Places(FFq, 1) eq 8, ~nfail);
check("pow_K: x^0 is the exact 1 also for an inexact zero x", pow_K(O(data`pi^3), 0) eq 1 and AbsolutePrecision(pow_K(O(data`pi^3), 0)) gt 3, ~nfail);
check("tadicprec: at least 100, and increasing in e", tadicprec(data, 1) ge 100 and tadicprec(data, 30) ge tadicprec(data, 1), ~nfail);
check("max_prec: Nmax >= N + 1 for N = 8", data`Nmax ge 9, ~nfail);

// ---- solver.m: zeros of integrals over a ramified K
// y^2 + (x^3+1)y = x^2 + x (249.a.249.1, rank 0 over Q(sqrt 5)) over K = Q_5(sqrt 5): the
// holomorphic integrals from (0,-1) vanish on the residue disc of (0,0) exactly at (0,0)
L5<s5> := NumberField(PolynomialRing(Rationals()).1^2 - 5);
L5x<x5> := PolynomialRing(L5); L5xy<y5> := PolynomialRing(L5x);
P5 := Decomposition(MaximalOrder(L5), 5)[1][1];
data5 := coleman_data(y5^2 + (x5^3 + 1)*y5 - (x5^2 + x5), L5, P5, 12 : verbose := false);
A5 := set_point(0, -1, data5); B5 := attach_expansions(set_point(0, 0, data5), data5, 0);
v5 := [ Vector(data5`K, [1, 0]), Vector(data5`K, [0, 1]) ];
zs := zeros_on_disk(A5, B5, v5, data5);
check("zeros_on_disk over the ramified Q_5(sqrt 5): one common zero of the holomorphic integrals in the disc of (0,0), at (0,0)",
      data5`eK eq 2 and #zs eq 1 and IsWeaklyZero(zs[1]`x) and IsWeaklyZero(zs[1]`b[2]), ~nfail);

// ---- solver.m: multiple roots
// y^3 = x^4 - 3x^3 + 3x^2 + x + 3 at 7 has two points of the reduction, both bad: the point at
// infinity, where the local parameter is b^inf_3 = y^2/x^3 and 1/x vanishes to order 3 in it,
// so that the minimal polynomial of 1/x specialised there has the triple root 0, which
// Factorisation cannot separate; and (4,0). roots_with_precision on a polynomial whose
// cluster of roots ends in coefficients that are inexact zeros.
data3 := coleman_data(y^3 - (x^4 - 3*x^3 + 3*x^2 + x + 3), QQ, Decomposition(MaximalOrder(QQ), 7)[1][1], 8 : verbose := false);
pts3 := Qq_points(data3);
check("Qq_points at a point at infinity where 1/x is a triple root: the points at infinity and (4,0)",
      #pts3 eq 2 and exists{R : R in pts3 | R`inf and IsWeaklyZero(R`x)}
      and exists{R : R in pts3 | not R`inf and Valuation(R`x - 4) ge 1}, ~nfail);
// on y^2 = x^7 - 3x^6 + 3x^5 - 2x^4 + x^3 - 2x^2 + 3x - 3 at 11 the minimal polynomial used at
// the point at infinity has roots of negative valuation, which reduce to no residue
data11 := coleman_data(y^2 - (x^7 - 3*x^6 + 3*x^5 - 2*x^4 + x^3 - 2*x^2 + 3*x - 3), QQ, Decomposition(MaximalOrder(QQ), 11)[1][1], 8 : verbose := false);
pts11 := Qq_points(data11);
check("Qq_points skips the roots of negative valuation: 12 points of y^2 = x^7 - ... at 11, one at infinity",
      #pts11 eq 12 and #[R : R in pts11 | R`inf] eq 1, ~nfail);
Z7 := pAdicRing(7, 10); Z7t<T7> := PolynomialRing(Z7);
roots7 := roots_with_precision(Z7t![O(Z7!7^5), O(Z7!7^5), O(Z7!7^5), -1, 1]); // T^3*(T-1) + O(7^5)
check("roots_with_precision: the simple root 1 and the cluster at 0 of T^3*(T-1) + O(7^5)",
      exists{rt : rt in roots7 | Valuation(rt[1] - 1) ge 5} and exists{rt : rt in roots7 | Valuation(rt[1]) ge 1}, ~nfail);

// ---- solver.m: the helpers of ros_chabauty
// qp_basis and qp_coordinates on completions with e = 2 (Q(sqrt 5) at 5), f = 2 (Q(i) at 3),
// e = f = 1 (Q(i) at 5) and e = f = 2 (x^4 - 6x^2 + 4 at 5): a Z_p-basis of O_K (units and
// uniformizer times units), coordinates of the basis vectors the unit vectors, and every
// element the combination of the basis with its coordinates
Qt<t> := PolynomialRing(Rationals());
towers := [<t^2 - 5, 5>, <t^2 + 1, 3>, <t^2 + 1, 5>, <t^4 - 6*t^2 + 4, 5>];
ok := true; degrees := [];
for tw in towers do
  Lt := NumberField(tw[1]); Qp := pAdicField(tw[2], 30);
  Pt := Decomposition(MaximalOrder(Lt), tw[2])[1][1];
  Kt, mt := Completion(Lt, Pt : Precision := 20);
  Bt := qp_basis(Kt);
  Append(~degrees, #Bt);
  ok and:= #Bt eq RamificationIndex(Pt)*InertiaDegree(Pt);
  ok and:= forall{i : i in [1..#Bt] | forall{k : k in [1..#Bt] | IsWeaklyZero(qp_coordinates(Bt[i], Qp)[k] - ((k eq i) select 1 else 0))}};
  ok and:= Seqset([Valuation(b) : b in Bt]) eq Seqset([0..RamificationIndex(Pt)-1]);
  a := mt(Lt.1 + 2/7);
  ok and:= IsWeaklyZero(&+[Kt!c*Bt[k] : k -> c in qp_coordinates(a, Qp)] - a);
end for;
check("qp_basis, qp_coordinates: Z_p-bases of O_K for e = 2, f = 2, e = f = 1, e = f = 2; unit coordinate vectors; reconstruction",
      ok and degrees eq [2, 2, 1, 4], ~nfail);
// ros_left_inverse: B*A = 1 with the least denominators (delta), and false for a singular A
Q3 := pAdicField(3, 20);
okA, B, delta := ros_left_inverse(Matrix(Q3, [[3, 0], [0, 1], [1, 1]]), 20);
okA3, B3, delta3 := ros_left_inverse(Matrix(Q3, [[3, 0], [0, 3], [0, 0]]), 20);
okS := ros_left_inverse(Matrix(Q3, [[1, 2], [2, 4], [3, 6]]), 20);
is_one := func<M | forall{e : e in Eltseq(M - IdentityMatrix(Q3, 2)) | IsWeaklyZero(e)}>;
check("ros_left_inverse: B*A = 1 (delta 0 for a unimodular minor, 1 for 3*I), false for a matrix of rank 1",
      okA and is_one(B*Matrix(Q3, [[3, 0], [0, 1], [1, 1]])) and delta eq 0
      and okA3 and delta3 eq 1 and is_one(B3*Matrix(Q3, [[3, 0], [0, 3], [0, 0]])) and not okS, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
