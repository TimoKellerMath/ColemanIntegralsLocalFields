// tests/library/compare-bt.m   [comparison with the original code of Balakrishnan and Tuitman]
//
//     magma -b bt:=/path/to/Coleman tests/library/compare-bt.m              (seed 1)
//     magma -b bt:=/path/to/Coleman seed:=5 tests/library/compare-bt.m      (other curves)
//
// Needs the original Magma code of Balakrishnan and Tuitman (the directory with coleman.m,
// from github.com/jtuitman/Coleman), which is not part of this repository; therefore it is
// not among the tests of tests/registry.py and writes no log (run it from the repository
// root). For random curves y^2 = f(x) over Q of genus 2 and 3 at random good primes p in
// {5, 7, 11, 13}, both libraries compute coleman_data and the Coleman integrals between three
// points of good residue discs (each library's own lift of the residue, Qp_points resp.
// Qq_points: the same x, and y to each library's working precision), and they must agree: the
// same basis of H^1_dR, the Frobenius matrices modulo p^N, and the integrals to the smaller of
// the two certified precisions.
root := GetCurrentDirectory();
ChangeDirectory(bt);
load "coleman.m";
// the entry points of the original code, kept under other names before this library
// redefines them (Magma binds the identifiers of a function when it is defined)
bt_coleman_data := coleman_data; bt_integrals := coleman_integrals_on_basis;
bt_Qp_points := Qp_points; bt_is_bad := is_bad;
ChangeDirectory(root);
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
SetColumns(0);

seed0 := assigned seed select StringToInteger(seed) else 1;
SetSeed(seed0);
printf "seed %o\n", seed0;

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;

Qx<x> := PolynomialRing(Rationals()); Qxy<y> := PolynomialRing(Qx);
N := 8;
for deg in [5, 6, 7] do
  // a random curve and a prime at which both libraries accept it, with 3 good points
  repeat
    repeat
      f := Qx!([Random([-3..3]) : i in [0..deg-1]] cat [1]);
    until Discriminant(f) ne 0;
    Q := y^2 - f;
    p := Random([5, 7, 11, 13]);
    ok := true;
    try
      dbt := bt_coleman_data(Q, p, N);
      dus := coleman_data(Q, Rationals(), p, N : verbose := false, full_check := true);
      pts := [R : R in bt_Qp_points(dbt) | not R`inf and not bt_is_bad(R, dbt)];
    catch e
      ok := false;
    end try;
  until ok and #pts ge 3;
  label := Sprintf("y^2 = %o at %o", f, p);
  print "\n" cat label;
  check(label cat ": the same basis of H^1_dR", dbt`basis eq dus`basis, ~nfail);
  g := dus`g;
  check(label cat ": the Frobenius matrices agree modulo p^N",
        forall{e : e in Eltseq(ChangeRing(dbt`F, Rationals()) - ChangeRing(dus`F, Rationals())) | e eq 0 or Valuation(e, p) ge N}, ~nfail);
  // three random good points of the original code, and the points of this library in their
  // residue discs (the same residues of x and of the b_i)
  K := dus`K; Fp := GF(p);
  ourpts := [R : R in Qq_points(dus) | not R`inf and not is_bad(R, dus)];
  ours := func< R | [S : S in ourpts | Fp!(Integers()!S`x) eq Fp!(Integers()!R`x)
                                       and [Fp!(Integers()!b) : b in S`b] eq [Fp!(Integers()!b) : b in R`b]][1] >;
  P1, P2, P3 := Explode([pts[i] : i in RandomSubset({1..#pts}, 3)]);
  for pair in [<P1, P2>, <P2, P3>, <P1, P3>] do
    Ibt, Nbt := bt_integrals(pair[1], pair[2], dbt);
    Ius, Nus := coleman_integrals_on_basis(ours(pair[1]), ours(pair[2]), dus : verbose := false);
    n := Minimum(Nbt, Nus);
    // the difference, as rationals (the two libraries use different copies of Q_p)
    rat := func< c | IsWeaklyZero(c) select 0 else (Integers()!(c*p^(-v)))/p^(-v) where v := Minimum(0, Valuation(c)) >;
    check(Sprintf("%o: integrals agree to precision %o (original %o, this library %o)", label, n, Nbt, Nus),
          forall{i : i in [1..2*g] | d eq 0 or Valuation(d, p) ge n where d := rat(Ibt[i]) - rat(Ius[i])}, ~nfail);
  end for;
end for;

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
exit;
