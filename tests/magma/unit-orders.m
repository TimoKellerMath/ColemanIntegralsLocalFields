// tests/magma/unit-orders.m   [unit test: the order functions of cohobasis.m]
//
//     magma -b tests/magma/unit-orders.m        (from the repository root)
//
// ord_0, ord_inf and ord_r of rational functions, and of matrices (the minimum over the
// entries). A zero entry must not affect the minimum, since the order of 0 is infinite. The
// matrix versions are applied to W = Winf*W0^(-1) and W^(-1) in the precision bounds, the
// truncation of E_0 and B_0, and the reduction.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m";
SetColumns(0);
SetLogFile("tests/magma/unit-orders.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
Lx<x> := RationalFunctionField(QQ);
r := PolynomialRing(QQ)!((x^2+1)*(x-2));  // squarefree, with the irreducible factors x^2+1, x-2

check("ord_0(x^2*(x+1)/(x-1)^3) = 2", ord_0(x^2*(x+1)/(x-1)^3) eq 2, ~nfail);
check("ord_inf(x^2/(x^5+1)) = 3", ord_inf(x^2/(x^5+1)) eq 3, ~nfail);
check("ord_r((x^2+1)^2*(x-2)^3/x) = 2", ord_r((x^2+1)^2*(x-2)^3/x, r) eq 2, ~nfail);
check("ord_r(1/(x-2)) = -1", ord_r(1/(x-2), r) eq -1, ~nfail);

check("ord_0(0) is infinite", ord_0(Lx!0) cmpeq Infinity(), ~nfail);
check("ord_r(0) is infinite", ord_r(Lx!0, r) cmpeq Infinity(), ~nfail);
check("ord_inf(0) is infinite", ord_inf(Lx!0) cmpeq Infinity(), ~nfail);

check("ord_0_mat(diag(x^2, x^3)) = 2", ord_0_mat(Matrix(Lx, 2, 2, [x^2, 0, 0, x^3])) eq 2, ~nfail);
check("ord_r_mat(diag(r^2, r^3)) = 2", ord_r_mat(Matrix(Lx, 2, 2, [r^2, 0, 0, r^3]), r) eq 2, ~nfail);
check("ord_inf_mat(diag(x^(-2), x^(-3))) = 2", ord_inf_mat(Matrix(Lx, 2, 2, [1/x^2, 0, 0, 1/x^3])) eq 2, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
