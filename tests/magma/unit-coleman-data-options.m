// tests/magma/unit-coleman-data-options.m   [unit test: options of coleman_data]
//
//     magma -b tests/magma/unit-coleman-data-options.m        (from the repository root)
//
// coleman_data(Q,L,P,N : W0:=..., Winf:=...) takes the integral bases of the model as optional
// parameters (README: the article's triple (Q, W^0, W^inf)). With the integral basis
// b^0 = (1, x+y) instead of the default (1, y), i.e. W0 = [[1,0],[x,1]] (rows: the basis
// elements in terms of 1, y), the record must contain the supplied W0. Checked for a model
// with rational coefficients (the rational branch of coleman_data) and for one with
// non-rational coefficients. With full_check := true, coleman_data also tests the
// good-reduction assumptions that it does not test otherwise (good_reduction_at): the
// result at a good prime is the same, and a bad prime is rejected with the reason.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
SetColumns(0);
SetLogFile("tests/magma/unit-coleman-data-options.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

// ---- 1. y^2 = x(x-1)(x+1)(x-2)(x+3) over Q, at 7 (the rational branch)
QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - x*(x-1)*(x+1)*(x-2)*(x+3);
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];
W0 := Matrix(FieldOfFractions(Lx), 2, 2, [1, 0, x, 1]);
data := coleman_data(Q, QQ, P7, 10 : verbose := false, W0 := W0);
check("curve over Q: data`W0 is the supplied W0 (b^0 = (1, x+y))",
      [ Evaluate(c, 5) : c in Eltseq(data`W0) ] eq [ Evaluate(c, 5) : c in Eltseq(W0) ], ~nfail);

// ---- 2. y^2 = x^5 + sqrt(7)*x^2 + 1 over Q(sqrt 7), at the ramified prime above 7
X := PolynomialRing(Rationals()).1;
L3<w> := NumberField(X^2 - 7);
L3x<x3> := PolynomialRing(L3); L3xy<y3> := PolynomialRing(L3x);
Q3 := y3^2 - (x3^5 + w*x3^2 + 1);
P3 := Decomposition(MaximalOrder(L3), 7)[1][1];
W03 := Matrix(FieldOfFractions(L3x), 2, 2, [1, 0, x3, 1]);
data3 := coleman_data(Q3, L3, P3, 12 : verbose := false, W0 := W03);
check("curve over Q(sqrt 7): data`W0 is the supplied W0 (b^0 = (1, x+y))",
      [ Evaluate(c, 5) : c in Eltseq(data3`W0) ] eq [ Evaluate(c, 5) : c in Eltseq(W03) ], ~nfail);

// ---- 3. full_check
dataF := coleman_data(Q, QQ, P7, 10 : verbose := false, W0 := W0, full_check := true);
check("full_check at the good prime 7 (with the supplied W0): the same Frobenius matrix",
      dataF`F eq data`F, ~nfail);
dataF3 := coleman_data(Q3, L3, P3, 12 : verbose := false, W0 := W03, full_check := true);
check("full_check over Q(sqrt 7) at the ramified prime: the same Frobenius matrix", dataF3`F eq data3`F, ~nfail);
P3a := Decomposition(MaximalOrder(QQ), 3)[1][1];
try
  _ := coleman_data(Q, QQ, P3a, 10 : verbose := false, full_check := true);
  ok3 := false;
catch err
  ok3 := Position(err`Object, "does not have good reduction at P") gt 0;
end try;
check("full_check at the bad prime 3: rejected with the reason", ok3, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
