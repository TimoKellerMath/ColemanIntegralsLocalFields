// tests/magma/unit-package.m   [unit test: the library as a Magma package]
//
//     magma -b tests/magma/unit-package.m        (from the repository root)
//
// The package package/ColemanIntegralsLocalFields.spec (built by tools/make_package.py) is
// attached instead of loading the files: the user-facing functions are intrinsics with the
// names, signatures and defaults of the library functions, a record that is not the output
// of coleman_data is rejected by a require check, and the verbosity flag is
// ColemanIntegration. The results must agree with those of the loaded library, which is
// loaded afterwards (its functions then take precedence over the intrinsics of the same
// names). The curve and the points are those of the example in README.md.
AttachSpec("package/ColemanIntegralsLocalFields.spec");
SetColumns(0);
SetLogFile("tests/magma/unit-package.log" : Overwrite);

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
// whether the call raises an error whose message contains phrase
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
Q := y^2 - x*(x-1)*(x+1)*(x-2)*(x+3);
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];

// ---- the intrinsics
data := coleman_data(Q, QQ, P7, 10 : verbose := false);
P := set_point(3, 12, data);
W := set_bad_point(0, [1, 0], true, data);
I, N := coleman_integrals_on_basis(P, W, data : verbose := false);
printf "integrals from (3,12) to the point at infinity, through the package: %o (precision %o)\n", I, N;
check("coleman_integrals_on_basis through the package: precision 9", N eq 9, ~nfail);
I3, N3, side := coleman_integrals_on_basis(P, W, data : verbose := false, return_side := true);
check("with return_side: the same integrals and the side record as third value", I3 eq I and N3 eq N and Type(side) eq Rec, ~nfail);
R := set_point(3, -12, data);
IR, NR := coleman_integrals_on_basis(P, R, data : verbose := false);
J := coleman_integral(P, R, data`basis[1], data : IP1P2 := IR, NIP1P2 := NR);
check("coleman_integral of the first basis form from (3,12) to (3,-12): the first entry of the integrals", IsWeaklyZero(J - IR[1]), ~nfail);
check("a record that is not from coleman_data: the require check of the intrinsic",
      raises(func< | set_point(3, 12, rec<recformat<a>|a := 1>) >, "record returned by coleman_data"), ~nfail);
check("an argument of the wrong type: rejected by the signature",
      raises(func< | coleman_data(Q, QQ, P7, 10/3) >, "coleman_data"), ~nfail);
print "the verbosity flag ColemanIntegration at level 2: the Newton steps of the local expansions";
SetVerbose("ColemanIntegration", 2);
_ := tiny_integrals_on_basis(P, teichmueller_pt(P, data), data);
SetVerbose("ColemanIntegration", 0);

// ---- the loaded library gives the same results
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
dataL := coleman_data(Q, QQ, P7, 10 : verbose := false);
IL, NL := coleman_integrals_on_basis(set_point(3, 12, dataL), set_bad_point(0, [1, 0], true, dataL), dataL : verbose := false);
check("the loaded library: the same integrals (as printed) and precision", NL eq N and Sprint(IL) eq Sprint(I), ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
