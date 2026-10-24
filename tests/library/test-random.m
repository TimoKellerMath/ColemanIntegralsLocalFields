// tests/library/test-random.m   [library test: random curves and primes]
//
//     magma -b tests/library/test-random.m                (from the repository root; seed 1)
//     magma -b seed:=12345 tests/library/test-random.m    (other random curves and primes)
//
// Random curves -- y^2 = f(x) of genus 2 and 3 over Q and over a quadratic field, and
// y^3 = f(x) of genus 3 over Q -- with small random coefficients, each at a random prime above
// p in {5, 7, 11, 13} at which coleman_data (with full_check) finds good reduction. For each
// one the library must satisfy:
//   (1) the characteristic polynomial of the Frobenius matrix on H^1_dR is T^(2g) L(1/T),
//       L the numerator of the zeta function of the reduction (Magma's point counting);
//   (2) antisymmetry and additivity of the Coleman integrals between three random points in
//       distinct good residue discs (the points of Qq_points there);
//   (3) between a point and a second point of its residue disc (at the local parameter
//       t = p*u, u a random unit), the Coleman integrals agree with the tiny integrals;
//   (4) at an inert prime of a quadratic field: the p-power and the q-power Frobenius lift
//       give the same integrals.
// The seed is printed; a failure prints the curve and the prime. The regression uses seed 1,
// so its log is reproducible; other seeds explore further curves.
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m"; load "solver.m";
SetColumns(0);
SetLogFile("tests/library/test-random.log" : Overwrite);

seed0 := assigned seed select StringToInteger(seed) else 1;
SetSeed(seed0);
printf "seed %o\n", seed0;

nfail := 0;
check := procedure(name, ok, ~nfail)
  printf "%-4o %o\n", ok select "PASS" else "FAIL", name;
  if not ok then nfail +:= 1; end if;
end procedure;
agree := func< u, v, idx, n | forall{i : i in idx | Valuation(u[i] - v[i]) ge n} >;

Qz<z> := PolynomialRing(Rationals());

// a random squarefree polynomial of degree deg over L with small coefficients, monic
random_poly := function(L, deg)
  els := [L | a + b*L.1 : a in [-3..3], b in ((Degree(L) eq 1) select [0] else [-1..1])];
  repeat
    f := PolynomialRing(L)!([Random(els) : i in [0..deg-1]] cat [L!1]);
  until Discriminant(f) ne 0 and Coefficient(f, 0) ne 0;
  return f;
end function;

// coleman_data at a random good prime above p in {5, 7, 11, 13} (full_check), and the
// prime; inert := true asks for a prime of residue degree 2
good_data := function(Q, L, N : inert := false)
  for p in Sort([5, 7, 11, 13], func< a, b | Random([-1, 1]) >) do
    for P in [d[1] : d in Decomposition(MaximalOrder(L), p)] do
      if inert ne (InertiaDegree(P) eq 2) or RamificationIndex(P) ne 1 then
        continue;
      end if;
      try
        return true, coleman_data(Q, L, P, N : verbose := false, full_check := true), P;
      catch e
        ;
      end try;
    end for;
  end for;
  return false, 0, 0;
end function;

// (1): charpoly of F against the L-polynomial of the reduction
frobenius_ok := function(data)
  g := data`g;
  FK := ChangeRing(Submatrix(data`F, 1, 1, 2*g, 2*g), data`m);
  cp := CharacteristicPolynomial(FK);
  FFq := reduced_function_field(data);
  a := Coefficients(LPolynomial(FFq)) cat [0 : i in [1..2*g+1]];
  return forall{k : k in [0..2*g] | Valuation(Coefficient(cp, 2*g-k) - a[k+1]) ge Maximum(1, data`N div 2)};
end function;

// the points of Qq_points in the good finite residue discs
good_points := func< data | [R : R in Qq_points(data) | not R`inf and not is_bad(R, data)] >;

// (2) and (3) for the curve of data (with at least 3 good residue discs); label for the messages
integral_checks := procedure(data, label, ~nfail)
  idx := [1..#data`basis];
  pts := good_points(data);
  P, Q, R := Explode([pts[i] : i in RandomSubset({1..#pts}, 3)]);
  IPQ, N1 := coleman_integrals_on_basis(P, Q, data : verbose := false);
  IQR, N2 := coleman_integrals_on_basis(Q, R, data : verbose := false);
  IPR, N3 := coleman_integrals_on_basis(P, R, data : verbose := false);
  IQP, N4 := coleman_integrals_on_basis(Q, P, data : verbose := false);
  check(label cat ": int_P^Q = -int_Q^P", agree(IPQ, -IQP, idx, Minimum(N1, N4)), ~nfail);
  check(label cat ": int_P^Q + int_Q^R = int_P^R", agree(IPQ + IQR, IPR, idx, Minimum([N1, N2, N3])), ~nfail);
  // (3): a second point of the disc of a random good point
  P := Random(pts);
  xt, bt := local_coord(P, tadicprec(data, 1), data);
  u := data`K!Random([1..data`p-1]);
  t0 := data`p*u;
  P2 := set_bad_point(Evaluate(xt, t0), [Evaluate(b, t0) : b in bt], false, data);
  Itiny, Nt := tiny_integrals_on_basis(P, P2, data);
  Icol, Nc := coleman_integrals_on_basis(P, P2, data : verbose := false);
  check(label cat ": tiny integrals in a disc = Coleman integrals", agree(Itiny, Icol, idx, Minimum(Nt, Nc)), ~nfail);
end procedure;

N := 8;
for spec in [<1, 5, "y^2 = f(x), deg f = 5, over Q">, <1, 7, "y^2 = f(x), deg f = 7, over Q">,
             <2, 5, "y^2 = f(x), deg f = 5, over Q(sqrt d)">, <2, 6, "y^2 = f(x), deg f = 6, over Q(sqrt d)">,
             <3, 4, "y^3 = f(x), deg f = 4, over Q">] do
  kind, deg, desc := Explode(spec);
  repeat
    if kind eq 2 then
      d := Random([-7, -3, -2, -1, 2, 3, 5, 6, 7]);
      L := NumberField(z^2 - d);
    else
      L := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;
    end if;
    f := random_poly(L, deg);
    Lx<x> := PolynomialRing(L); Lxy<y> := PolynomialRing(Lx);
    Q := (kind eq 3) select y^3 - Lx!f else y^2 - Lx!f;
    ok, data, P := good_data(Q, L, N);
  until ok and #good_points(data) ge 3;
  label := Sprintf("%o, f = %o, at a prime of norm %o", desc, f, Norm(P));
  print "\n" cat label;
  check(label cat ": charpoly of Frobenius = T^(2g) L(1/T) (g = " cat Sprint(data`g) cat ")", frobenius_ok(data), ~nfail);
  integral_checks(data, label, ~nfail);
end for;

// (4): the p-power and the q-power lift at an inert prime of a quadratic field
print "";
repeat
  d := Random([-7, -3, -2, -1, 2, 3, 5, 6, 7]);
  L := NumberField(z^2 - d);
  f := random_poly(L, 5);
  Lx<x> := PolynomialRing(L); Lxy<y> := PolynomialRing(Lx);
  Q := y^2 - Lx!f;
  ok, data, P := good_data(Q, L, N : inert := true);
until ok and #good_points(data) ge 2;
dataq := coleman_data(Q, L, P, N : verbose := false, lift := "q");
pts := good_points(data); ptsq := good_points(dataq); // the same points (Qq_points is deterministic), over the two copies of K
label := Sprintf("y^2 = %o over Q(sqrt %o) at the inert prime above %o", f, d, data`p);
I, N1 := coleman_integrals_on_basis(pts[1], pts[2], data : verbose := false);
Iq, N2 := coleman_integrals_on_basis(ptsq[1], ptsq[2], dataq : verbose := false);
check(label cat ": the p-power lift (n_tau = " cat Sprint(data`ntau) cat ") and the q-power lift give the same integrals",
      data`ntau eq 2 and dataq`ntau eq 1 and forall{i : i in [1..#data`basis] | Valuation(I[i] - data`m(Iq[i] @@ dataq`m)) ge Minimum(N1, N2)}, ~nfail);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
exit;
