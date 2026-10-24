# ColemanIntegralsLocalFields

[![Checks](https://github.com/TimoKellerMath/ColemanIntegralsLocalFields/actions/workflows/checks.yml/badge.svg)](https://github.com/TimoKellerMath/ColemanIntegralsLocalFields/actions/workflows/checks.yml)
[![Magma regression tests](https://github.com/TimoKellerMath/ColemanIntegralsLocalFields/actions/workflows/magma.yml/badge.svg)](https://github.com/TimoKellerMath/ColemanIntegralsLocalFields/actions/workflows/magma.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

[Magma](http://magma.maths.usyd.edu.au/magma/) code for explicit Coleman integration on
smooth projective curves with good reduction over finite extensions `K` of `Q_p`, allowing
both ramification and nontrivial residue degree, and for (symmetric) Chabauty computations
over number fields. It accompanies the article

> Yulin Cai and Timo Keller, *Explicit Coleman integration for curves over finite extensions
> of Q_p*;

see [`CITATION.cff`](CITATION.cff) for how to cite it. The repository contains the library,
the scripts of every computation in the article together with their logs, and the tests;
the article itself is not part of it. The implementation builds on the Magma code of
Balakrishnan and Tuitman for curves over `Q_p`
([jtuitman/Coleman](https://github.com/jtuitman/Coleman)).

## Getting started

The library needs Magma (the logs were produced with V2.29-10). Run Magma from the root of the
repository, since Magma resolves `load` relative to the working directory. A curve is given by
a plane model `Q(x,y) = 0` over a number field `L`, and the integrals are computed over the
completion `K = L_P` at a prime `P`:

```magma
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";

QQ := ext< Rationals() | Polynomial([0,1]) : DoLinearExtension >;  // Q as a number field
Lx<x> := PolynomialRing(QQ); Lxy<y> := PolynomialRing(Lx);
Q := y^2 - x*(x-1)*(x+1)*(x-2)*(x+3);           // the plane model Q(x,y) = 0
P7 := Decomposition(MaximalOrder(QQ), 7)[1][1];  // K = Q_7
data := coleman_data(Q, QQ, P7, 10);             // Frobenius on H^1_dR, working precision N = 10
P := set_point(3, 12, data);                     // a point, given by its coordinates (x, y)
W := set_bad_point(0, [1, 0], true, data);       // the point at infinity: 1/x and b^inf
I, N := coleman_integrals_on_basis(P, W, data);  // the integrals of the basis forms from P to W
```

`I` contains the integrals of the forms `data``basis`, the first `2g` of which form a basis of
`H^1_dR(X)`, and `N` is the precision to which they are certified (here 9). In more detail:

* `coleman_data(Q, L, P, N)` computes the action of Frobenius on cohomology and the
  correction functions. Optional parameters: the integral bases `W0`, `Winf` of the model
  (the article's triple `(Q, W^0, W^inf)`; by default they are computed), and the Frobenius
  lift `lift := "auto"`, `"p"` or `"q"` (for unramified `P` of residue degree `f_K > 1`,
  the `p`-power lift iterated `f_K` times is usually faster than the `q`-power lift). `L` may
  also be `Rationals()` or a quadratic or cyclotomic field, `Q` an element of `L[x,y]` or a
  model with a constant leading coefficient in `y`, and `P` a rational prime with a single
  prime of `O_L` above it. Invalid input (a model that is not monic or not integral at `P`,
  a bad prime, ...) raises an error that says what is wrong and how to correct it.
* `set_point(x0, y0, data)` gives a point by its coordinates on the plane model, with `x0`
  integral at `P`. `set_bad_point(x, b, inf, data)` gives a point by the values of `x` (or of
  `1/x` if `inf` is true) and of the integral basis `b^0` (or `b^inf`); this is needed at
  points on the boundary of the affine model, where `(x, y)` does not determine the point.
* `coleman_integrals_on_basis(P1, P2, data)` returns the integrals of the basis forms from
  `P1` to `P2` and their certified precision; a good point can also be given as a pair
  `[x0, y0]`. Optional parameters: `e`, the ramification
  index of the auxiliary extension `K(pi^(1/e))` used at bad endpoints; `return_side` and
  `side1`, to reuse the part of the computation that depends only on `P1`; and
  `direct_inf`, which treats infinite endpoints without the auxiliary extension, at a cost
  in precision (with the `q`-power lift only).
* `coleman_integral(P1, P2, dif, data)` integrates an arbitrary differential of the second
  kind, given like the entries of `data``basis` (a sequence of `d` polynomials `w_i` for
  `sum_i w_i b^0_i dx/z`), between points that are not very bad, with a certified precision
  (it accounts for the loss of the reduction of the form). With `data` computed with
  `useU := true` (a basis of `H^1_dR(U)`), the form can also be of the third kind with poles at
  the points above the zeros of `r` and above `x = infinity`; the logarithms are on Iwasawa's
  branch (`log p = 0`). E.g. `dx/x = [f/x, 0]` on `y^2 = f(x)` integrates to
  `log x(R) - log x(P)`.
* `solver.m` and `symmetric_chabauty.m` contain the Chabauty-Coleman and symmetric Chabauty
  computations over number fields used in Section 8 and Appendix A of the article. The root
  finding on residue discs works over ramified `K` as well (the recognition of points by LLL
  needs `P` unramified). `quadratic_points_split` recovers the quadratic points in split and
  diagonal disc-pairs, and with `include_bad := true` also in the finite bad discs; the
  Frobenius-conjugate disc-pairs are split disc-pairs over a `K` with `f_K = 2`.
  `curve_quadratic_points` in `quadratic_points.m` does this for a curve given as a `Curve`,
  over every residue class, and reports the status of each (see "Quadratic points of a curve"
  below).
* `ros_chabauty(datas, known)` in `solver.m` is Chabauty-Coleman for the restriction of
  scalars (Siksek, "Explicit Chabauty over number fields"): it uses the completions at
  several primes above `p` at once (`datas`: the output of `coleman_data` at each of them)
  and needs only rank `<= (g-1)*sum_j [K_j:Q_p]` instead of rank `< g`. The vanishing
  functionals are `Q_p`-linear forms in the integrals at all the primes; for every residue
  polydisc (a residue disc at every prime) a contraction argument decides whether it contains
  exactly one `L`-rational point (a known one), none, or a unique common zero of the
  functionals (recognized as an `L`-rational point if possible); `res``complete` tells whether
  this determines all `L`-rational points. Polydiscs with two known points, or with a common
  zero that is not `L`-rational, remain for another argument (e.g. a Mordell-Weil sieve).
* `models.m` finds models and good primes for a curve given as a `Curve`, converts its points,
  and runs Chabauty-Coleman for it with little input (see "Curves, models and good primes"
  below).

Every function of the library begins with a comment stating its input, its output and the
algorithm or result of the article it implements. The **API reference**
[`docs/API.md`](docs/API.md) collects these comments: the user-facing functions with their
signatures, options and defaults in full, and every other function with its signature and a
one-line description (generated by `tools/make_api.py`; `make api`).

**Progress messages.** `coleman_data`, `coleman_integrals_on_basis` and the functions of
`symmetric_chabauty.m` and `models.m` print their progress if their option `verbose` is true
(the default of the first two). Further messages use Magma's verbosity mechanism with the
flag `User1` (a flag of its own, `declare verbose`, needs a package):
`SetVerbose("User1", 1)` shows the progress of the solver (`K_points`,
`vanishing_differentials`, `effective_chabauty`, `ros_chabauty`), and `SetVerbose("User1", 2)` also the
Newton steps of the local expansions (`hensel_lift`). Warnings and notes about lost precision
are always printed.

## Curves, models and good primes

`models.m` (loaded after `solver.m`) prepares a curve for the library. Its central object is a
*model*: a plane model `Q(x,y) = 0`, monic in `y` with integral coefficients, together with the
functions `x` and `y` in the function field of the curve, so that every point of the curve --
also a point at infinity or a singular point of the plane model -- can be converted into a
point record. For a curve given as a `Curve`, Chabauty-Coleman then needs a single call:

```magma
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
load "solver.m"; load "models.m";

A2<a,b> := AffineSpace(Rationals(), 2);
C := Curve(A2, b^2 + b - (a^5 - 2*a^3 + a));   // 971.a.971.1: genus 2, Mordell-Weil rank 1
pts := PointSearch(ProjectiveClosure(C), 10);  // its seven rational points
res := curve_chabauty(C, pts);
res`matched;  // for every candidate the known point it agrees with (0: none)
```

`curve_chabauty` chooses the model (`improve_model`) and a good prime of residue degree 1 that
does not divide `#J(F_p)` (here 7), runs `coleman_data` and `effective_chabauty`, and compares
the candidates with the known points: here the seven rational points and two 7-adic points in
the residue discs of `x = -1`, which are not rational. The candidates contain all rational
points if the known points generate a subgroup of finite index of a Mordell-Weil group of rank
`< g`; this is not checked. Options of `curve_chabauty`:

* new candidates whose `x` is an element of `L` of small height (`htbound`) with an
  `L`-rational point above it are reported in `res``recognized` (over number fields by LLL,
  `recognize_in_F`);
* `rank_check := true` computes bounds for the rank of the Jacobian (genus 2: over `Q`
  `RankBounds`, over a number field the upper bound `RankBound`, both by 2-descent);
* `primes := n` uses up to `n` good primes, a further one while some candidate is neither
  known nor recognized; `res``complete` tells whether at one of them every candidate is
  known or recognized, which proves that the known and recognized points are all. This helps
  for rank `<= g-2`: for rank `g-1` the integral of the vanishing differential has a zero in
  almost every residue disc, at every prime (a Mordell-Weil sieve is needed then);
* `maxN` (default `4N`): a computation that fails for lack of precision is repeated with
  twice the precision, up to `maxN`;
* `patches := true` computes the finite bad residue discs of the model in affine patches
  where they are good (`affine_patches`), with the vanishing differentials transported
  through the function field (`holomorphic_transition`).

The steps can also be run separately:

* `curve_model(C)` -- a model of a `Curve` in the affine or projective plane, or in a
  higher-dimensional space (projected birationally to the plane), or of a polynomial
  `Q(x,y)`: the affine patch `Z = 1`, made monic and integral (`lc_scaling`);
* `good_primes(M : bound := 50)` -- the primes of norm `<= bound` at which the model has good
  reduction, testing *all* good-reduction assumptions of the article (integrality, the
  reductions of `r`, of `W^0`, `W^inf` and of the integral bases, the genus and the
  étaleness of the boundary; `coleman_data` itself tests only some of them), with the reason
  for every other prime; with `check := true` also a trial run of `coleman_data` against the
  zeta function of the reduction;
* `improve_model(M : bound := 50)` -- models of the same curve ranked by their good primes:
  coordinate changes of the plane curve, changes `x = 1/x' + t` of the coordinate `x` (for a
  hyperelliptic curve: changes of the Weierstrass model), and over `Q` the reduced minimal
  Weierstrass model (`ReducedMinimalWeierstrassModel`) or the minimized and reduced plane
  quartic (`MinimizeReducePlaneQuartic`);
* `affine_patches(M, P)` -- models (affine patches of the plane curve in other coordinates)
  whose good residue discs at `P` cover all smooth `F_q`-points of the reduction, so that the
  zeros in every disc can be computed in a model in which the disc is good (bad discs need the
  more expensive auxiliary extension `K(pi^(1/e))`);
* `point_records(M, data, pts)` -- the point records of points of the curve (points of `C`,
  places, or pairs `[x0, y0]`), for data computed by `coleman_data` from the model; a place
  of degree 2, or a point over a quadratic extension, gives one record for each of its points
  over `K`, and an effective divisor the records of its points;
* `model_coleman_data(M, P, N : aux := true)` -- `coleman_data` for the model over the
  unramified quadratic extension of `L_P` (through an auxiliary field `L(sqrt u)` in which `P`
  is inert), whose residue field contains those of all points of degree 2 of the reduction.

## Quadratic points of a curve

`quadratic_points.m` (loaded after `symmetric_chabauty.m` and `models.m`) computes the
`F`-rational effective divisors of degree 2 of a curve over a number field `F` -- its points
of degree 2 and the sums of two `F`-rational points -- by symmetric Chabauty, from a few known
ones:

```magma
load "isrational.m"; load "auxpolys.m"; load "cohobasis.m"; load "frobenius.m";
load "reduction.m"; load "coercion.m"; load "expansion.m"; load "integrals.m";
load "solver.m"; load "symmetric_chabauty.m"; load "models.m"; load "quadratic_points.m";

_<T> := PolynomialRing(Rationals());
F<s> := NumberField(T^2 - 5);
A2<a,b> := AffineSpace(F, 2);
C := Curve(A2, b^2 - s*a*(a-1)*(a+1)*(a-2)*(a+3));  // genus 2 over Q(sqrt 5), rank J(F) = 0
res := curve_quadratic_points(C, [[C![0,0], C![1,0]]]);
res`complete;  // true: the divisors found and the hyperelliptic family are all
res`xpolys;    // for every divisor the polynomial prod (X - x(Q)) over its points
```

`curve_quadratic_points` chooses a good prime `P` (unramified, of residue characteristic
`p >= 5`) and works over the unramified quadratic extension `K` of `F_P`, so that the
Frobenius-conjugate residue classes of the points of degree 2 of the reduction are treated
as well. Every residue disc is computed in a model in which it is good: for a model
`y^2 + h(x) y = f(x)` the discs at infinity in two patches `x = t + 1/x'` and the Weierstrass
discs at their Weierstrass point; for other models in linear patches of the plane curve,
chosen so that the two discs of every residue class are good in one of them. The holomorphic
forms of the patches are expressed in those of the model through the function field
(`holomorphic_transition`). The differentials `V` that annihilate `J(F)` are computed from the
known divisors and from `generators` (pairs `[D1, D2]` whose differences, together with those
of the known divisors, generate a subgroup of finite index of `J(F)`); symmetric Chabauty needs
`dim V = g - rank J(F) >= 2`. Every Frobenius-stable residue class gets a status:

* `excluded`: an integral to the class is a unit (this can happen only if `p` divides
  `#J(F_q)`, `q` the norm of `P`), or another differential of `V` does not vanish at the zero
  of two of them: the class contains no `F`-rational divisor;
* `known` or `recovered`: Siksek's criterion (for a diagonal class the jet `(a_0, a_1)`) shows
  that the class contains at most one `F`-rational divisor, and it contains one: a known
  divisor, or one found by Newton's method, recognized by LLL and verified on the curve (a
  point of degree 2 ramified at `P` lies in the diagonal class of its reduction);
* `family`: a class of pullback type with a rank drop, for the hyperelliptic involution or for
  an involution `sigma` with `trace_zero := true`: its `F`-rational divisors are pullbacks;
* `unresolved`: a rank drop that is not of pullback type, or a zero that is not recognized.

`res``complete` tells whether no class is unresolved; then the known and the recovered
divisors (`res``divisors`) and the pullbacks in the classes `res``families` are all
`F`-rational effective divisors of degree 2, provided that `V` annihilates `J(F)`; for a
model `y^2 + h(x) y = f(x)` of genus 2, `rank_check := true` verifies this by an upper bound
for the rank of `J(F)` (2-descent, `res``annihilating`). For `dim V = 2` (genus 2 and rank 0,
or rank `g - 2`) a class that is neither excluded nor recovered has a `p`-adic zero,
recognized or not, so a single prime can give a complete result only if `p` divides
`#J(F_q)`; the default prime is such a prime if there is one. Otherwise the result lists the
divisors and the classes that remain, and an independent argument (e.g. the order of `J(F)`,
or a Mordell-Weil sieve through the option `reachable`) has to finish the proof. Further
options: `P`, `N`, `htbound` (the height bound of the recognition), `primes` (further primes
while the result is not complete, with the divisors found as known ones), `aux := false`
(only the classes of pairs of points over `F_q`), `include_bad`, `improve`. The curve may be
given over any number field, also with coefficients outside `Q`, as a `Curve` or a
polynomial; a known divisor as a divisor, a place, a point over a quadratic extension of `F`,
or a pair of points.

Three examples in `tests/examples/` run as tests (group `example` of the registry), each
checking its result independently:

* `quadratic-points-Xb3ns5.m`: `X(b3,ns5)` over `Q(sqrt 5)` (genus 2, rank 0) at the prime
  above 11: from one known divisor, the 79 `F`-rational effective divisors of degree 2 outside
  the hyperelliptic family (40 points of degree 2 with 20 `x`-polynomials, and 39 sums of two
  `F`-rational points); the 80 unresolved classes are empty, since `#J(F) = 80`;
* `quadratic-points-over-F.m`: two curves genuinely defined over `Q(sqrt 5)` (not base changes
  of curves over `Q`), of rank 0: the curve of the example above, complete at the prime above
  11 with `11 | #J(F_11) = 176` (160 classes excluded), and incomplete at the other prime above
  11; and a curve whose points of degree 2 are Weierstrass points over quadratic extensions;
* `quadratic-points-Xs3ns5.m`: `X(s3,ns5)` over `Q(sqrt 5)` (genus 3, rank 1) at the single
  prime 19, with the bielliptic involution: the 36 sporadic quadratic points of Appendix A
  (the 35 affine ones and the point at infinity) and the 32 sums of two `F`-rational points
  that are not pullbacks; the 370 classes that remain at 19 are what the Mordell-Weil sieve of
  Appendix A removes (about 4 minutes).

## Conventions and notation

The code uses the notation of the article; the comments in the library refer to this section.

* **Fields.** `L` is the number field of the plane model `Q(x,y) = 0`, which is monic in `y`
  of degree `d`; `P` is a prime of `O_L` and `K = L_P` the completion, with uniformizer
  `pi`, ramification index `e_K`, residue degree `f_K` and residue field of size `q`. The map
  `L -> K` is `data``m`. A model over `Q` is given over `Q` as a number field of degree 1 (as
  above); `coleman_data` then computes the Frobenius structure over `Q_p` (its *rational
  branch*) and moves only the results to `K`.
* **Precision.** `N` is the target precision and `Nmax` the working precision (`data``Nmax`),
  both absolute and in units of `v_K`, normalised by `v_K(pi) = 1`. The integrals are
  returned with the precision to which they are certified.
* **Model.** `Delta` is the discriminant of `Q` with respect to `y`, `r` the squarefree
  polynomial with the zeros of `Delta`, and `z = r/lc(r)` (the article's `r_mon`). The
  integral bases are `b^0 = W0*(1,y,...,y^(d-1))^T` over `L[x]` and
  `b^inf = Winf*(1,y,...,y^(d-1))^T` over `L[1/x]`, `W = Winf*W0^(-1)`, and `G0`, `Ginf` are
  the matrices of the differential: `d(b^0) = G0*b^0 dx`.
* **Matrices are transposed.** Coefficient vectors of functions and forms are rows, and
  `W0`, `Winf`, `W`, `G0`, `Ginf` act on them from the right: they are the transposes of the
  article's `W^0`, `W^inf`, `W`, `G^0`, `G^inf`. A form is stored as the vector `w` in
  `L[x]^d` of `sum_i w_i b^0_i dx/z`. `data``basis` holds the basis `omega_1, ..., omega_2g`
  of `H^1_dR(X)` computed by `basis_coho`, the first `g` of them holomorphic.
* **Frobenius.** The lift `F_tau^*` is `tau`-semilinear with `F_tau^*(x) = x^(q_tau)`;
  `data``qtau`, `data``tau` and `data``ntau` are `q_tau`, `tau` (a map `L -> L`, or `0` for
  the identity) and `n_tau`, so that `F_q^* = (F_tau^*)^(n_tau)`. For the `q`-power lift
  `q_tau = q` and `n_tau = 1`; for the `p`-power lift (unramified `K`) `q_tau = p` and
  `n_tau = f_K`. `data``Atau` is the matrix `A_tau` of `F_tau^*` on `data``basis`, `data``F`
  the matrix `A_q` of `F_q^*` (row `i`: `F_q^*(omega_i) = dg_i + sum_j A_q[i,j] omega_j`, as in
  the article), and `data``Clist` the matrices `C_j` of the lemma on the precision of
  semilinear composition.
* **Points.** A point is a record (see `set_bad_point` in `integrals.m`): `x` (or `1/x` at
  infinite points) and the values `b` of `b^0` (or `b^inf`), since `(x, y)` does not
  determine a point where the plane model is singular. The classification of the article
  applies: a point is *bad* if its residue disc is infinite or lies above a zero of `r`
  modulo `pi`, *very bad* if `x = infinity` or `r(x) = 0`, and *suitable bad* if it is
  finitely bad with `0 < v_K(r(x)) < 1/q`, or infinite but not very infinite.

### Library files

| file | contents | article |
| --- | --- | --- |
| `isrational.m` | recognises a model with rational coefficients (the rational branch) | |
| `auxpolys.m` | `Delta`, `r`, `s`; tests of the good-reduction assumptions | Good models |
| `cohobasis.m` | `W0`, `Winf`, `G0`, `Ginf`, residue matrices, the basis of `H^1_dR` | Good models; Computing a Frobenius lift (matrix of the differential); Computing a basis of `H^1_dR(U)` |
| `frobenius.m` | the Frobenius lift `F_tau^*` and the pullback of forms | Computing a Frobenius lift |
| `reduction.m` | the reduction procedure `omega = df_0 + df_inf + df_end + sum a_i omega_i`; reduction modulo `P^N` | Computing a basis of `H^1_dR(U)`; Precision bounds |
| `coercion.m` | maps between `L`, `K` and their polynomial and series rings | |
| `expansion.m` | expansions of functions in an integral local parameter | Computing Coleman integrals |
| `integrals.m` | `coleman_data`, points, tiny integrals, Coleman integrals, precision bookkeeping | Computing Coleman integrals; Precision bounds |
| `solver.m` | effective Chabauty (vanishing differentials, zeros on residue discs), Chabauty for the restriction of scalars | Example 8.4 |
| `symmetric_chabauty.m` | Siksek's symmetric Chabauty for quadratic points | Example 8.4; Appendix A |
| `models.m` | models of curves for the library: good primes (all good-reduction assumptions), better models, affine patches, point records, `curve_chabauty` | Good models |
| `quadratic_points.m` | symmetric Chabauty for a curve given as a `Curve`: the residue classes over the unramified quadratic extension, in patches of the model, with the status of every class (`curve_quadratic_points`) | Example 8.4; Appendix A |

The library is loaded in the order of the table (without `solver.m`, `symmetric_chabauty.m`,
`models.m` and `quadratic_points.m` if they are not needed), since Magma binds identifiers when
a function is defined.

**The library as a package.** Instead of the `load` lines,
`AttachSpec("package/ColemanIntegralsLocalFields.spec");` makes the user-facing functions
available as intrinsics with the same names, arguments and options (`coleman_data`,
`set_point`, `set_bad_point`, `coleman_integrals_on_basis`, `tiny_integrals_on_basis`,
`tiny_integrals_on_basis_to_z`, `coleman_integral`, `teichmueller_pt`,
`holomorphic_integrals_weakly_zero`, `K_points`, `Qq_points`, `vanishing_differentials`,
`zeros_on_disk`, `effective_chabauty`, `torsion_packet`, `ros_chabauty`, `symmetric_chabauty_classify`,
`quadratic_points_split`, `curve_model`, `good_primes`, `model_coleman_data`, `improve_model`,
`affine_patches`, `point_records`, `curve_chabauty`, `curve_quadratic_points`), so that scripts
run unchanged. The package needs no load
order, its other functions are local to it (they cannot clash with the user's identifiers),
`?coleman_data` shows the comment at the beginning of a function, the arguments are
type-checked (a `data` argument must be the record of `coleman_data`), and its verbosity
flag is `ColemanIntegration` instead of `User1`. A function with a varying number of return
values returns the largest number (e.g. `coleman_integrals_on_basis` always three, the third
being 0 without `return_side`). The package is generated from the library files
(`make package`; `make check` fails if it is out of date).

## Repository layout

| path | contents |
| --- | --- |
| `*.m` (top level) | the library: `isrational.m`, `auxpolys.m`, `cohobasis.m`, `frobenius.m`, `reduction.m`, `coercion.m`, `expansion.m`, `integrals.m` (Coleman integration), `solver.m`, `symmetric_chabauty.m` (Chabauty and symmetric Chabauty over number fields), `models.m` (models, good primes and Chabauty for a `Curve`), `quadratic_points.m` (the quadratic points of a `Curve`) |
| `example-*.m`, `appendix-A-*.m`, `intro-*.m` | the computations of the article, each with its `.log` (and data `.dat`) |
| `package/` | the library as a Magma package (`ColemanIntegralsLocalFields.spec`), built by `tools/make_package.py` |
| `docs/` | `API.md`, the API reference, built by `tools/make_api.py` from the comments of the library files |
| `tests/` | `regression.py`, `check_logs.py`, `registry.py`, the Python unit tests, `tests/magma/` (Magma unit tests), `tests/library/` (library tests) and `tests/examples/` (worked examples, also run as tests) |
| `tools/` | `make_package.py`, which builds the package, and `make_api.py`, which builds the API reference, from the library files |
| `.github/` | continuous integration and Dependabot |

## Tests and continuous integration

| command | what it does | needs Magma |
| --- | --- | --- |
| `make check` | `tests/check_logs.py`: every script of the registry exists together with its committed logs, results and data files, no log contains a Magma error, and every results file can be read; and the package and the API reference are built from the current library files (`tools/make_package.py --check`, `tools/make_api.py --check`) | no |
| `make package` | rebuilds the package after a change of the library files | no |
| `make api` | rebuilds the API reference `docs/API.md` after a change of the comments of the library files | no |
| `make unit` | `tests/test_tools.py`: unit tests of the test tools themselves (seconds) | no |
| `make test` | `tests/regression.py`: re-runs every script of the article, the Magma unit tests, the library tests and the examples in a scratch copy of the repository and compares what they write with the committed logs, with run times masked; about 16 minutes of CPU time | yes |
| `make test-all` | the same, including the two long Example 8.4 runs and the example `quadratic-points-Xs3ns5` (about 28 minutes of CPU time in all) | yes |
| `make update-logs` | re-runs everything and overwrites the committed logs, after an intended change | yes |

The Magma tests run in parallel, one job per core by default (`make test JOBS=2`, resp.
`tests/regression.py -j 2`, limits that), the longest tests first. `tests/regression.py`
copies the files tracked by git, so a new script has to be added with `git add` before it can
be tested.

**Numbers rather than text.** A test can record the numbers that it checks in a results file
next to its log (`NAME.results`, written by `record_result` of `tests/magma/results.m`):
integers, rationals, strings, and p-adic numbers to the precision that the computation
certifies (the option `precision`). `tests/regression.py` compares such a file numerically
(`tests/compare_results.py`): p-adic numbers agree if they agree modulo the smaller of the
two precisions, and a smaller precision than the committed one is a failure. The log of such
a test is then compared only for information, so its wording may change without a new
reference. The tests of Coleman integrals and of Chabauty record their results this way
(`unit-integrals`, `unit-coleman-integral`, `unit-infinite`, `test-precision`, `test-plift`,
`test-curve-chabauty`, `test-ros-chabauty`, and the examples); the scripts of the article keep
their logs as the reference, since the article quotes them.

The Magma **unit tests** in `tests/magma/` check the library against independent facts:

* `unit-frobenius.m` compares the characteristic polynomial of the Frobenius matrix computed
  by `coleman_data` with the zeta function of the reduction (over `Q_7`, over `Q_49` with
  the semilinear `p`-power lift, over the ramified `Q_7(sqrt 7)` with non-rational
  coefficients, and for a plane quartic over `Q_19`);
* `unit-integrals.m` checks antisymmetry, additivity through a bad endpoint, the vanishing
  of holomorphic integrals between Weierstrass points (2-torsion) and the hyperelliptic
  involution;
* `unit-infinite.m` checks integrals at infinite endpoints: the image under Frobenius near
  infinity (also when `b^inf(P_inf)^q - b^inf(P_inf)` has valuation 1), the choice of this
  image in the local parameter at infinity where the congruence mod `pi` leaves several
  roots, and the option `direct_inf` against the default computation;
* `unit-coleman-integral.m` checks `coleman_integral` on a basis form, a linear combination
  of basis forms (against `coleman_integrals_on_basis`) and the exact form `dy`
  (`int_P^R dy = y(R) - y(P)`), over `Q_7` (a model over `Q`) and over the ramified
  `Q_7(sqrt 7)`;
* `unit-orders.m` checks the orders `ord_0`, `ord_inf`, `ord_r` of functions and matrices
  (the order of `0` is infinite, so zero entries do not count);
* `unit-coleman-data-options.m` checks that `coleman_data` uses supplied integral bases `W0`,
  `Winf`, also for a model over `Q`;
* `unit-points.m` checks `is_bad`, `is_very_bad` and `lie_in_same_disc` (two points lie in
  one residue disc iff `x` and the values of `b` agree modulo `pi`);
* `unit-teichmueller.m` checks `teichmueller_pt` over `Q_7`, `Q_49` and the ramified
  `Q_7(sqrt 7)`: `x(T)^q = x(T)`, and `T` lies on the curve;
* `unit-input.m` checks the accepted input formats of `coleman_data` (`L = Q`, a model in
  `L[x,y]`, a constant leading coefficient, `P` given as a rational prime) and of the
  integration functions (points as pairs `[x0, y0]`), and that invalid input raises an error
  that says what is wrong;
* `unit-internals.m` checks internal functions against known values: the auxiliary
  polynomials and integral bases of a hyperelliptic model, the connection matrix, the
  reduction modulo `P^N`, the coercions to `K`, the root finder with precisions (also for
  two roots in one residue class whose representative is itself a root), the roots of
  linear factors whose leading coefficient is a unit other than `1`, the kernel over
  `Q_p` and its precision, the Frobenius automorphism of `Q(zeta_7)^+` at the inert prime
  `3`, the points of the reduction where a minimal polynomial has a multiple root or roots
  of negative valuation, and the `Z_p`-bases and coordinates of `ros_chabauty`;
* `unit-reduction.m` checks the cohomology data and the reduction steps through identities
  in the function field: the connection matrices (`d(b^0)/dx = G0*b^0`), the residue
  matrices, residue maps and ramification indices, the bases of `H^1_dR(X)` and
  `H^1_dR(U)`, the matrices of the reduction steps, `reduce_with_fs` and its steps
  (`omega = d(f_0 + f_inf + f_end) + sum_i c_i omega_i`, exactly for poles at infinity and
  modulo `p^N_max` for poles along `z = 0`), and the evaluation of `f_0`, `f_inf` at a point;
* `unit-helpers.m` checks helpers of `frobenius.m`, `coercion.m`, `expansion.m`,
  `integrals.m` and `solver.m` directly: the rings and reductions of the Frobenius lift
  (through the value after `z = r(x)`), coefficient twists, series over `O_K/pi^N`, Taylor
  shifts, coefficient maps between `L` and `K`, the Newton steps of the expansions, the
  precision helpers (including the bound for tiny integrals against its formula), the very
  bad point of a disc, and the maps from `L` to `K`;
* `unit-symchab.m` checks the helpers of the symmetric Chabauty recovery on systems with
  known solutions: power sums and their derivatives, the Newton solvers in `(sigma1,
  sigma2)` and in `(t1, t2)` (also with a Jacobian that is singular modulo `p`), the
  saturation of the annihilating differentials, and the reductions to `F_q`;
* `unit-models.m` checks `models.m`: models of a polynomial, of plane quartics (including
  the Klein quartic), of a canonical genus-4 curve in `P^3` and of `X(s3,ns5)` over
  `Q(sqrt 5)`; their good primes (with the reasons for the bad ones and the trial run of
  `coleman_data` against the zeta function of the reduction); `lc_scaling`,
  `mobius_model`, `improve_model`, `affine_patches` and `point_records`; and its helpers
  (`model_field`, `homogenization`, `transform_plane_model`, `model_height`,
  `holomorphic_transition`, `plane_reduction`, `jacobian_rank_bounds`, ...); for the points
  of degree 2 the inert quadratic extension, `model_coleman_data` over it (the Frobenius
  matrix against the zeta function over `F_(q^2)`), the records of places of degree 2 that
  are split, inert or ramified at `P`, and a transition matrix over the auxiliary field;
* `unit-quadratic-points.m` checks the internal functions of `quadratic_points.m` on
  `X(b3,ns5)` at 11: the models and residue discs of the sweep, the transfer of points between
  the model and its patches (also of a Weierstrass point), the hyperelliptic involution, the
  forms of the known divisors and their errors, the Frobenius-stable residue classes, the
  reduction of a point of degree 2 ramified at `P`, and the verification of divisors;
* `unit-package.m` attaches the package instead of loading the files: the intrinsics
  (also with three return values), their `require` checks and type checks, the verbosity
  flag `ColemanIntegration`, and the same integrals as the loaded library.

They are part of the fast tier; the quick variant (`magma -b quick:=1
tests/magma/unit-frobenius.m` and `unit-integrals.m`, about 3 seconds) also runs in the
pre-commit hook whenever a `.m` file changes.

All scripts are listed in `tests/registry.py`. The library tests `tests/library/test2.m` and
`tests/library/test3.m` integrate to points where a single basis function does not separate
the points of the fibre of the local parameter (the three points at infinity of a plane
quartic, the singular point of a plane sextic), and check the results: the local expansions
satisfy the curve equation, the integrals are additive and agree with `N = 15`, and (in
`test2`) do not depend on the choice of the local parameter beyond the regularization of the
forms with a pole. The library test `tests/library/test-precision.m` checks the precision
bounds of the article: the working precision `N_max` chosen by `max_prec` (the proposition on
the precision of the reduction process and the remark after it; `N_max = 14` for
`y^2 = x^5-2x^2+x+11` over `Q_5` with `N = 11`), and that the integrals agree with a run at
higher `N` to the precision they report (the proposition on the precision of `f_0`, `f_inf`,
`f_end` at a point, including the bound `T_0(P)` at finitely bad endpoints). The library test
`tests/library/test-curve-chabauty.m` runs Chabauty-Coleman for the genus-2 curve
971.a.971.1 of rank 1 from its `Curve` (`curve_chabauty`): it finds the seven rational points
and two further 7-adic points, also with a point search (`effective_chabauty` with a bound)
and for the torsion packet of the point at infinity (`torsion_packet`). The library test
`tests/library/test-ros-chabauty.m` runs `ros_chabauty` for a genus-2 curve over quadratic
fields at the primes above 3, split and inert, of rank 1 and of rank 2 = g (where no single
completion suffices), and recovers points left out of the known ones. The library test
`tests/library/test-random.m` draws random curves (`y^2 = f(x)` of genus 2 and 3 over `Q`
and over quadratic fields, `y^3 = f(x)` over `Q`) and random good primes, and checks the
Frobenius matrix against the zeta function of the reduction, antisymmetry and additivity of
the integrals, tiny against Coleman integrals within a disc, and the `p`-power against the
`q`-power lift; the regression uses the seed 1, and `magma -b seed:=n
tests/library/test-random.m` tries other curves. `tests/library/compare-bt.m` compares the
library with the original code of Balakrishnan and Tuitman over `Q_p` on random curves (the
same basis, the Frobenius matrix modulo `p^N`, the integrals to the smaller precision); it
needs that code, so it is run by hand, `magma -b bt:=/path/to/Coleman
tests/library/compare-bt.m`, and is not part of the regression. A test can be
marked as an expected failure (`xfail` in the registry); the runner then reports it as
`XFAIL`, and as `XPASS` (a failure) once it passes. The **examples** in `tests/examples/`
(group `example` of the registry, see "Quadratic points of a curve") are computations with
the user-facing functions on curves whose answer is known, each checked independently (against
the order of the Jacobian, or a published list of points); `quadratic-points-Xs3ns5` belongs
to the slow tier.

GitHub Actions (`.github/workflows/`):

* **Checks** runs `make check` and `make unit` on GitHub's runners for every push and pull
  request.
* **Magma regression tests** runs `tests/regression.py`. Magma is licensed, so this needs a
  [self-hosted runner](https://docs.github.com/en/actions/hosting-your-own-runners) on a
  machine with `magma` on its `PATH`, registered with the labels `self-hosted` and `magma`
  (runner version 2.327.1 or newer, since the actions run on Node.js 24).
  Then set the repository variable `MAGMA_RUNNER` to `true` to run the fast tier on every
  push to `main`; without it, the workflow runs only when started by hand (*Run workflow*,
  with the choice of the fast tier or all tests). It never runs for pull requests from forks,
  since a self-hosted runner executes the code it checks out.

Local git hooks: `pip install pre-commit && pre-commit install` runs `make check` and `make unit`
before every commit, and the quick Magma unit tests when a `.m` file changes;
`pre-commit run --hook-stage manual magma-regression` runs the fast Magma tier.

### Run times and memory

CPU time and peak memory as recorded on the last line of each log (one core of an AMD Ryzen 7
PRO 6850U, Magma V2.29-10). The cost of `coleman_data` grows linearly in `q_tau` (the exponent
of the Frobenius lift), and an integral with a bad endpoint by a further factor of about
`2 q e_P`, the ramification index of the auxiliary extension.

| test | where in the article | CPU time | memory |
| --- | --- | --- | --- |
| `intro-z25-fields` | Introduction (split primes of the K_i) | 0 s | 32 MB |
| `example-8.1` | Example 8.1 (prime above 109) | 32 s | 198 MB |
| `example-8.1-inert-7` | Example 8.1 (prime above 7, f_K = 3) | 0 s | 32 MB |
| `example-8.2` | Example 8.2 | 55 s | 94 MB |
| `example-8.3` | Example 8.3 | 7 s | 32 MB |
| `example-8.4-multiprime` | Example 8.4 (eight split primes) | 330 s | 339 MB |
| `example-8.4-single-prime` | Example 8.4 (the single prime 19) | 180 s | 147 MB |
| `appendix-A-rank-E` | Appendix A, step (i): E(F) | 1 s | 32 MB |
| `appendix-A-rational-points` | Appendix A, step (vii): the eight points of C(F) | 13 s | 32 MB |
| `appendix-A-covering` | Appendix A: the covering phi and D_0 = phi^*(O_E) | 1 s | 65 MB |
| `appendix-A-generators` | Appendix A, steps (i) and (iii): J(C)(F)_tors and Gamma | 221 s | 64 MB |
| `appendix-A-localdata-19` | Appendix A, steps (ii) and (v): local data at q = 19 | 4 s | 32 MB |
| `appendix-A-localdata-29` | Appendix A, steps (ii) and (v): local data at q = 29 | 31 s | 32 MB |
| `appendix-A-localdata-31` | Appendix A, steps (ii) and (v): local data at q = 31 | 5 s | 32 MB |
| `appendix-A-localdata-41` | Appendix A, steps (ii) and (v): local data at q = 41 | 15 s | 32 MB |
| `appendix-A-localdata-59` | Appendix A, steps (ii) and (v): local data at q = 59 | 27 s | 96 MB |
| `appendix-A-localdata-61` | Appendix A, steps (ii) and (v): local data at q = 61 | 33 s | 96 MB |
| `appendix-A-localdata-71` | Appendix A, steps (ii) and (v): local data at q = 71 | 31 s | 128 MB |
| `appendix-A-localdata-79` | Appendix A, steps (ii) and (v): local data at q = 79 | 52 s | 160 MB |
| `appendix-A-localdata-89` | Appendix A, steps (ii) and (v): local data at q = 89 | 71 s | 224 MB |
| `appendix-A-sieve` | Appendix A, steps (iv)-(vii): the Mordell-Weil sieve | 1 s | 32 MB |
| `unit-frobenius` | unit | 5 s | 32 MB |
| `unit-frobenius-quick` | unit | 1 s | 32 MB |
| `unit-integrals` | unit | 2 s | 32 MB |
| `unit-infinite` | unit | 5 s | 32 MB |
| `unit-coleman-integral` | unit | 2 s | 32 MB |
| `unit-orders` | unit | 0 s | 32 MB |
| `unit-coleman-data-options` | unit | 3 s | 32 MB |
| `unit-points` | unit | 0 s | 32 MB |
| `unit-teichmueller` | unit | 3 s | 32 MB |
| `unit-input` | unit | 1 s | 32 MB |
| `unit-internals` | unit | 1 s | 32 MB |
| `unit-reduction` | unit | 0 s | 32 MB |
| `unit-helpers` | unit | 1 s | 32 MB |
| `unit-symchab` | unit | 0 s | 32 MB |
| `unit-models` | unit | 4 s | 112 MB |
| `unit-quadratic-points` | unit | 2 s | 32 MB |
| `unit-package` | unit | 1 s | 32 MB |
| `test2` | library | 16 s | 32 MB |
| `test3` | library | 92 s | 94 MB |
| `test-symchab-Xb3ns5` | library | 4 s | 32 MB |
| `test-symchab-Xs3ns5` | library | 16 s | 87 MB |
| `test-plift` | library | 40 s | 32 MB |
| `test-precision` | library | 2 s | 32 MB |
| `test-curve-chabauty` | library | 19 s | 109 MB |
| `test-random` | library | 8 s | 32 MB |
| `test-ros-chabauty` | library | 12 s | 32 MB |
| `quadratic-points-Xb3ns5` | example | 45 s | 94 MB |
| `quadratic-points-over-F` | example | 75 s | 141 MB |
| `quadratic-points-Xs3ns5` | example | 219 s | 479 MB |

## Scripts for the computations in the article

The scripts are named after the place in the article where their results are used. Run each
one from the root of the repository with `magma -b <script>.m`; it writes `<script>.log`,
which contains the numbers quoted in the article.

| article | script | what it computes |
| --- | --- | --- |
| Introduction | `intro-z25-fields.m` | the smallest primes splitting completely in the five sextic fields `K_i` of `x^2+y^3=z^25` |
| Example 8.1 | `example-8.1.m` | Siksek's genus-2 curve over `Q(2^(1/3))`: integrals at the prime above `109` (totally split, so over `Q_109`) |
| Example 8.1 | `example-8.1-inert-7.m` | the same integrals at the inert prime `7`: an `f_K = 3` computation over `Q_(7^3)`, with the `7`-power Frobenius lift although `Q(2^(1/3))` is not Galois (the `343`-power lift, `lift:="q"`, takes 45 s) |
| Example 8.2 | `example-8.2.m` | `X(b3,s5)` over `Q(sqrt 5)` at the prime above `7` |
| Example 8.3 | `example-8.3.m` | a superelliptic genus-3 curve over `Q(2^(1/3))` at the ramified prime above `3` |
| Example 8.4 | `example-8.4-multiprime.m` | the 35 affine sporadic divisors of `X(s3,ns5)` over `Q(sqrt 5)`, from eight split primes |
| Example 8.4 | `example-8.4-single-prime.m` | the same 35 divisors from the single prime `19`, over `Q_(19^2)` (see below) |
| Appendix A | `appendix-A-*.m` | Proposition A.5, `C^(2)(F)` for `C = X(s3,ns5)` and `F = Q(sqrt 5)` (see below) |

## Appendix A — quadratic points on X(s3,ns5) over Q(sqrt 5) (Proposition A.5)

Steps (i)–(vii) refer to the proof of Proposition A.5. Run the scripts in this order (each
writes its own `.log`):

| script | what it does |
| --- | --- |
| `appendix-A-rational-points.m` | `C(F)`: eight points, the four points of `C(Q)` and two Galois-conjugate pairs |
| `appendix-A-covering.m` | the bielliptic covering `phi : C -> E = y^2+y=x^3+1` (225a1) in closed form, by diagonalising `sigma` on the canonical plane, and the two fibres used in the example: `phi^*(O_E) = (1,0)+(7,-3) = D_0` and `phi^*(P_E) = { x^2-(6s+34)x-18s-26 = 0, y = ((s-1)x-2s-2)/8 }` (= `fam_mp` of `appendix-A-common.m`) |
| `appendix-A-common.m` | shared setup (`load`ed by the others): curve, the involution `sigma`, the base point `p0` of the trace-zero pencil, the known divisors, `LocalData(q)`, `DegreeTwoData`, `KnownList` |
| `appendix-A-rank-E.m` | `E(F)` for `F = Q(sqrt 5)`: rank 1 |
| `appendix-A-generators.m` | `J(C)(F)_tors = <t_10, z> = Z/2 + Z/120` (order 240; `D_6` and the Steiner class are redundant) and `[J(C)(F):Gamma]` divides 2 |
| `appendix-A-localdata.m` | `magma q:=41 appendix-A-localdata.m` — caches the local data for one prime in `appendix-A-local-<q>.dat`; the log also records how many type-(c) classes lie in `H_q` and in `H_q^rob` |
| `appendix-A-sieve.m` | the Mordell–Weil sieve over the nine cached primes (needs the `.dat` files), and step (vii): every one of the 158 surviving classes is settled without a point search |

Outcome: `C^(2)(F)` consists of the known divisors and the pullbacks `phi^*(E(F))`, so
`X(s3,ns5)` has exactly 36 sporadic quadratic points over `Q(sqrt 5)`, the 35 affine ones and
the pair at infinity — unconditionally, i.e. for either possible value of `[J(C)(F):Gamma]`.

Being unconditional needs two things beyond the multiplier `I = 2` (`jmath = 2*iota_2`,
which lands in `Gamma` because `2 J(C)(F) <= Gamma`):

* the type-(c) exclusion has to be read off at a prime where no type-(c) class lies in
  `H_q^rob = { y : 2y in red_q(Gamma) } >= red_q(J(C)(F))` — true at `q = 79` and `q = 29`,
  false at the other seven primes, `q = 41` included (`appendix-A-localdata-<q>.log`);
* the local sets themselves have to be built from `H_q^rob`, not from `red_q(Gamma)`:
  for a global `D` the class `red_q(iota_2(D))` need not lie in `red_q(Gamma)` unless the
  index is 1.  `appendix-A-sieve.m` uses `Y_q = { 2c : c in R_q^rob }`.

Step (vii) — ruling out an unknown divisor above a surviving class — uses **no point
search**.  A class `x` is settled at `q` when every element of its fibre
`F_q(x) = { Dt in M_q : 2*iota_{2,q}(Dt) = rho_q(x) }` is of type (a) *and* is the
reduction of a known divisor of `K_2`: a type-(a) residue disc holds at most one
`F`-rational degree-2 divisor, and it already holds a known one.  All 158 classes are
settled this way, and each of `q = 19, 29, 61, 79` settles all 158 on its own (`q = 19, 61,
79` if the criterion is read literally, see below).  This is checked for **every** `x` in
`W`, not only for those outside the image of `K_2`: a class in that image can have further
elements in its fibre (at `q = 41`, 20 of the 158 fibres contain a class that is not the
reduction of a known divisor).  The point search `quadratic_points_split`, which found the
35 sporadic divisors, is not part of the proof: over `Q_p` it examines only pairs of
distinct *good* affine discs (no diagonal pairs, no Frobenius-conjugate pairs, none of the 6
bad discs at `q = 41`), and an unrecognised pair is not an empty one.

**Diagonal classes.** "Of type (a)" is decided on the *reduced* divisor: for a diagonal class
`2*Rt` the matrix is the jet `(a_0(Rt), a_1(Rt))`. The criterion cited in the article
(Box–Gajović–Goodman, Thm 2.6) builds its matrix from a base point `D_*` in the disc with
multiplicities collected *before* reduction, so a known divisor `R_1 + R_2` with
`R_1 != R_2` and equal reductions (a "collision", e.g. a sporadic divisor whose two points
meet mod `q`) gives `(a_0, a_0)` of rank <= 1. `appendix-A-sieve.m` therefore also runs step
(vii) with the criterion read literally — a diagonal fibre element may only be used if the
known divisor reducing to it is a double `2P`, `P in C(F)` — and it still settles all 158
classes; `q = 19, 61, 79` each do it alone (`q = 29` does not, since `Delta_20` and
`Delta_33` collide there). The jet criterion is itself valid (a formal-immersion argument in
the symmetric functions `t_1 + t_2`, `t_1*t_2`), but that argument is not in the cited
source.

## Example 8.4 — the same 35 divisors at a single prime, over K = Q_(19^2)

| script | what it does |
| --- | --- |
| `example-8.4-single-prime.m` | the uniform single-prime sweep: `coleman_data` over `K = L_P` with `L = Q(sqrt5, sqrt2)`, `P` above `19`, `(e,f) = (1,2)`, `N = 16`; `vanishing_differentials` from the three rational points `(1,0)`, `(7,-3)`, `(-1/2,-1/2)`; then `quadratic_points_split` with `basis := [1, (1+sqrt5)/2]` so that the LLL recognition targets `O_F` |

Over `K` a Frobenius-conjugate disc-pair *is* a split disc-pair, so one run sweeps both
kinds together.  Output (`example-8.4-single-prime.log`, ~11 min): 431 good residue discs
over `F_361`, the 19-power Frobenius fixing 21 of them and permuting the other 410 in 205
two-cycles, hence `C(21,2) + 205 = 415` Frobenius-stable pairs examined (out of 92665);
**all 35** affine sporadic divisors are recovered — 12 in split disc-pairs, 23 in
Frobenius-conjugate ones — and nothing outside the published list survives the recognition.
The `Q_19`-only computation returns exactly the 12 split ones (`p=19` in
`example-8.4-multiprime.log`).

Two implementation points: the irreducibility test on a recovered minimal polynomial must
be taken over `F`, not over the auxiliary field `L` (a point with `F(D) = F(sqrt u)` splits
over `L`, so a test over `L` would discard it); and the auxiliary field is otherwise
immaterial, any `L = F(sqrt u)` with `u` a non-residue mod 19 realising `K`.

## License

The code is released under the MIT License, see [`LICENSE`](LICENSE). Magma itself is
commercial software and is not covered by this license.
