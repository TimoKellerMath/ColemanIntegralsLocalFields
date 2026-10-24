// tests/magma/unit-input.m   [unit test: the input of the user-facing functions]
//
//     magma -b tests/magma/unit-input.m        (from the repository root)
//
// coleman_data accepts L = Q, a model in L[x,y], a model with a constant leading coefficient,
// and a rational prime with a single prime of O_L above it; the integration functions accept
// points given as pairs [x0, y0]. Invalid input raises an error that says what is wrong:
// each check below catches the error and looks for a key phrase of its message. The curve is
// y^2 = x(x-1)(x+1)(x-2)(x+3) at 7, as in unit-integrals.m.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
SetColumns(0);
SetLogFile("tests/magma/unit-input.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
// whether the call raises an error whose message contains phrase
asQ := func< M | [ Rationals()!c : c in Eltseq(M) ] >;   // the entries of a matrix over Q as a number field
raises := function(f, phrase)
  try
    _ := f();
  catch e
    return Position(e`Object, phrase) gt 0;
  end try;
  return false;
end function;

QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
f := x*(x-1)*(x+1)*(x-2)*(x+3);
Q := y^2 - f;
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
data := coleman_data(Q, QQ, P7, 8 : verbose := false);

// ---- accepted forms of the input of coleman_data
Qx<X> := PolynomialRing(Rationals()); Qxy<Y> := PolynomialRing(Qx);
dataQ := coleman_data(Y^2 - X*(X-1)*(X+1)*(X-2)*(X+3), Rationals(), 7, 8 : verbose := false);
check("coleman_data(Q over Q, Rationals(), 7, N): the same Frobenius matrix",
      Degree(dataQ`L) eq 1 and asQ(dataQ`F) eq asQ(data`F), ~nfail);
R2<u,v> := PolynomialRing(QQ, 2);
data2 := coleman_data(v^2 - u*(u-1)*(u+1)*(u-2)*(u+3), QQ, P7, 8 : verbose := false);
check("coleman_data with the model in L[x,y]: the same Frobenius matrix", asQ(data2`F) eq asQ(data`F), ~nfail);
data3 := coleman_data(3*Q, QQ, P7, 8 : verbose := false);
check("coleman_data with the constant leading coefficient 3: divided, the same Frobenius matrix",
      asQ(data3`F) eq asQ(data`F), ~nfail);

// ---- invalid input of coleman_data
check("N = 0: error", raises(func< | coleman_data(Q, QQ, P7, 0 : verbose := false) >, "positive integer"), ~nfail);
check("a model that is not monic in y: error that suggests lc_scaling",
      raises(func< | coleman_data(x*y^2 - f, QQ, P7, 8 : verbose := false) >, "lc_scaling"), ~nfail);
check("a reducible model: error", raises(func< | coleman_data(y^2 - x^2, QQ, P7, 8 : verbose := false) >, "irreducible"), ~nfail);
check("P = 4: error", raises(func< | coleman_data(Q, QQ, 4, 8 : verbose := false) >, "prime"), ~nfail);
L2<w> := NumberField(PolynomialRing(Rationals()).1^2 - 2);
L2x<x2> := PolynomialRing(L2); L2xy<y2> := PolynomialRing(L2x);
check("P = 7 with two primes of Q(sqrt 2) above it: error that lists them",
      raises(func< | coleman_data(y2^2 - x2^5 - w*x2^2 - 1, L2, 7, 8 : verbose := false) >, "primes of O_L above"), ~nfail);
check("an unknown lift: error", raises(func< | coleman_data(Q, QQ, P7, 8 : verbose := false, lift := "x") >, "lift"), ~nfail);
check("a bad prime: error that names the failing condition and good_primes",
      raises(func< | coleman_data(Q, QQ, Decomposition(MaximalOrder(QQ), 3)[1][1], 8 : verbose := false) >, "good_primes"), ~nfail);
check("coefficients not integral at P: error",
      raises(func< | coleman_data(y^2 - f/7, QQ, P7, 8 : verbose := false) >, "integral at P"), ~nfail);

// ---- points
check("set_point of a point not on the curve: error", raises(func< | set_point(3, 11, data) >, "not a point of the curve"), ~nfail);
check("set_point with x0 not integral at P: error that suggests set_bad_point",
      raises(func< | set_point(1/7, 0, data) >, "set_bad_point"), ~nfail);
check("set_bad_point with b of the wrong length: error", raises(func< | set_bad_point(0, [1], false, data) >, "values of the 2 functions"), ~nfail);
check("set_bad_point of a finite point with inf = true: error",
      raises(func< | set_bad_point(3, [1, 12], true, data) >, "divisible by P"), ~nfail);
P := set_point(3, 12, data); R := set_point(3, -12, data);
I1 := coleman_integrals_on_basis(P, R, data : verbose := false);
I2 := coleman_integrals_on_basis([3, 12], [3, -12], data : verbose := false);
check("coleman_integrals_on_basis with points given as pairs [x0,y0]", I1 eq I2, ~nfail);
check("coleman_integrals_on_basis with a negative e: error",
      raises(func< | coleman_integrals_on_basis(P, R, data : e := -1, verbose := false) >, "nonnegative"), ~nfail);
check("coleman_integral with a form of the wrong length: error",
      raises(func< | coleman_integral(P, R, [Lx!1], data) >, "sequence of 2 polynomials"), ~nfail);
check("tiny_integrals_on_basis between different residue discs: error",
      raises(func< | tiny_integrals_on_basis(P, set_point(0, 0, data), data) >, "same residue disc"), ~nfail);

// ---- the solver
check("vanishing_differentials with a single point: error", raises(func< | vanishing_differentials([P], data) >, "at least two"), ~nfail);
check("effective_chabauty without points and without a search bound: error",
      raises(func< | effective_chabauty(data) >, "bound"), ~nfail);
data11 := coleman_data(Q, QQ, Decomposition(MaximalOrder(QQ), 11)[1][1], 8 : verbose := false);
check("ros_chabauty with no data, the same prime twice, primes above different p, or one known point: errors",
      raises(func< | ros_chabauty([], [[3, 12], [3, -12]]) >, "at least one prime")
      and raises(func< | ros_chabauty([data, data], [[3, 12], [3, -12]]) >, "distinct")
      and raises(func< | ros_chabauty([data, data11], [[3, 12], [3, -12]]) >, "above the same p")
      and raises(func< | ros_chabauty([data], [[3, 12]]) >, "at least two"), ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
