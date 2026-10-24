"""The Magma scripts under test, shared by regression.py and check_logs.py.

Every script NAME.m writes NAME.log (SetLogFile(... : Overwrite)), and possibly data files.
The committed versions of these files are the reference output. A script that records its
numbers in NAME.results (tests/magma/results.m) lists it among its outputs; then the results
are compared numerically and the log only for information (tests/regression.py).

tier "fast": at most a few minutes each; together about 14 minutes on one core.
tier "slow": the two Example 8.4 runs and the example quadratic-points-Xs3ns5 (about 3, 6 and
4 minutes).

group "example": worked examples beyond the article (tests/examples/), computations with the
user-facing functions on curves whose answer is known, each of which checks its result
independently (e.g. against the order of the Jacobian or a published list of points).
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Test:
    name: str                      # test name (unique)
    script: str                    # the Magma script, relative to the repository root
    args: tuple = ()               # command-line assignments, e.g. ("q:=41",)
    tier: str = "fast"             # "fast" or "slow"
    timeout: int = 1800            # seconds
    outputs: tuple = ()            # files the script writes, compared with the committed ones
    article: str = ""              # where the result is used in the article
    group: str = "article"         # "article" (cited in the paper), "library", "unit" or "example"
    xfail: str = ""                # reason, if the script is known to fail (expected failure)

    def files(self):
        return self.outputs or (self.script[:-2] + ".log",)


# the nine split primes of the Mordell-Weil sieve (Appendix A)
SIEVE_PRIMES = (19, 29, 31, 41, 59, 61, 71, 79, 89)

TESTS = (
    Test("intro-z25-fields", "intro-z25-fields.m", article="Introduction (split primes of the K_i)"),
    Test("example-8.1", "example-8.1.m", article="Example 8.1 (prime above 109)"),
    Test("example-8.1-inert-7", "example-8.1-inert-7.m", article="Example 8.1 (prime above 7, f_K = 3)"),
    Test("example-8.2", "example-8.2.m", article="Example 8.2"),
    Test("example-8.3", "example-8.3.m", article="Example 8.3"),
    Test("example-8.4-multiprime", "example-8.4-multiprime.m", tier="slow", timeout=7200,
         article="Example 8.4 (eight split primes)"),
    Test("example-8.4-single-prime", "example-8.4-single-prime.m", tier="slow", timeout=7200,
         article="Example 8.4 (the single prime 19)"),
    Test("appendix-A-rank-E", "appendix-A-rank-E.m", article="Appendix A, step (i): E(F)"),
    Test("appendix-A-rational-points", "appendix-A-rational-points.m",
         article="Appendix A, step (vii): the eight points of C(F)"),
    Test("appendix-A-covering", "appendix-A-covering.m",
         article="Appendix A: the covering phi and D_0 = phi^*(O_E)"),
    Test("appendix-A-generators", "appendix-A-generators.m",
         article="Appendix A, steps (i) and (iii): J(C)(F)_tors and Gamma"),
) + tuple(
    Test(f"appendix-A-localdata-{q}", "appendix-A-localdata.m", args=(f"q:={q}",),
         outputs=(f"appendix-A-localdata-{q}.log", f"appendix-A-local-{q}.dat"),
         article=f"Appendix A, steps (ii) and (v): local data at q = {q}")
    for q in SIEVE_PRIMES
) + (
    Test("appendix-A-sieve", "appendix-A-sieve.m",
         article="Appendix A, steps (iv)-(vii): the Mordell-Weil sieve"),
    # unit tests of the library (tests/magma/); the quick variant runs in the pre-commit hook
    Test("unit-frobenius", "tests/magma/unit-frobenius.m", group="unit"),
    Test("unit-frobenius-quick", "tests/magma/unit-frobenius.m", args=("quick:=1",), group="unit",
         outputs=("tests/magma/unit-frobenius-quick.log",)),
    Test("unit-integrals", "tests/magma/unit-integrals.m", group="unit",
         outputs=("tests/magma/unit-integrals.log", "tests/magma/unit-integrals.results")),
    # integrals at infinite endpoints: Frobenius near infinity, the root choice in the local
    # parameter at infinity, and the option direct_inf against the default route
    Test("unit-infinite", "tests/magma/unit-infinite.m", group="unit",
         outputs=("tests/magma/unit-infinite.log", "tests/magma/unit-infinite.results")),
    # coleman_integral for forms given like data`basis (also over a model with rational
    # coefficients and over a ramified K), against coleman_integrals_on_basis and y(R) - y(P)
    Test("unit-coleman-integral", "tests/magma/unit-coleman-integral.m", group="unit",
         outputs=("tests/magma/unit-coleman-integral.log", "tests/magma/unit-coleman-integral.results")),
    # the orders ord_0, ord_inf, ord_r of functions and matrices (zero entries: infinite order)
    Test("unit-orders", "tests/magma/unit-orders.m", group="unit"),
    # the optional integral bases W0, Winf of coleman_data, also for a model over Q
    Test("unit-coleman-data-options", "tests/magma/unit-coleman-data-options.m", group="unit"),
    # is_bad, is_very_bad and lie_in_same_disc (which compares x as well as b)
    Test("unit-points", "tests/magma/unit-points.m", group="unit"),
    # teichmueller_pt over Q_7, Q_49 and the ramified Q_7(sqrt 7)
    Test("unit-teichmueller", "tests/magma/unit-teichmueller.m", group="unit"),
    # the accepted input formats of the user-facing functions, and their error messages
    Test("unit-input", "tests/magma/unit-input.m", group="unit"),
    # internal functions: auxiliary polynomials, integral bases, reduction modulo P^N,
    # coercions, the root finder with precisions, the Frobenius automorphism, helpers
    Test("unit-internals", "tests/magma/unit-internals.m", group="unit"),
    # the cohomology data and the reduction steps (cohobasis.m, reduction.m) through identities in
    # the function field: connection matrices, residues, reduce_with_fs and its steps
    Test("unit-reduction", "tests/magma/unit-reduction.m", group="unit"),
    # helpers checked directly: the rings and reductions of the Frobenius lift, series over
    # O_K/pi^N, coefficient maps, Newton steps, precisions (frobenius.m, coercion.m,
    # expansion.m, integrals.m)
    Test("unit-helpers", "tests/magma/unit-helpers.m", group="unit"),
    # the helpers of the symmetric Chabauty recovery (power sums, the Newton solvers, saturation,
    # reductions) on systems with known solutions
    Test("unit-symchab", "tests/magma/unit-symchab.m", group="unit"),
    # models.m: models of curves, good primes, better models, affine patches, point records, and
    # for points of degree 2 the inert quadratic extension, records of places of degree 2 and
    # transition matrices over it
    Test("unit-models", "tests/magma/unit-models.m", group="unit"),
    # quadratic_points.m: the sweep of models and residue discs, the transfer of points between
    # models, the known divisors in their forms, the residue classes, points ramified at P
    Test("unit-quadratic-points", "tests/magma/unit-quadratic-points.m", group="unit"),
    # the library as a Magma package (tools/make_package.py): intrinsics, require checks, the
    # verbosity flag, and the same results as the loaded library
    Test("unit-package", "tests/magma/unit-package.m", group="unit"),
    # library tests, not cited in the article
    # test2 and test3: integrals to points where a single basis function does not separate the
    # fibre of the local parameter (the points at infinity of test2, the singular point (0,0) of
    # test3), with consistency checks (expansions, additivity, another local parameter, N=15)
    Test("test2", "tests/library/test2.m", group="library"),
    Test("test3", "tests/library/test3.m", group="library"),
    Test("test-symchab-Xb3ns5", "tests/library/test-symchab-Xb3ns5.m", group="library"),
    Test("test-symchab-Xs3ns5", "tests/library/test-symchab-Xs3ns5.m", group="library"),
    # the p-power Frobenius lift over non-Galois fields (Frobenius of L_P applied through the
    # completion) against the q-power lift, and the local Frobenius map itself
    Test("test-plift", "tests/library/test-plift.m", group="library",
         outputs=("tests/library/test-plift.log", "tests/library/test-plift.results")),
    # the precision bounds: N_max (the proposition on the precision of the reduction process)
    # and the certified precision of the integrals (the proposition on the precision of f_0,
    # f_inf, f_end at a point), against runs at higher N
    Test("test-precision", "tests/library/test-precision.m", group="library",
         outputs=("tests/library/test-precision.log", "tests/library/test-precision.results")),
    # Chabauty-Coleman for a Curve (curve_chabauty in models.m, effective_chabauty with a point
    # search, torsion_packet) on the genus-2 curve 971.a.971.1 of rank 1
    Test("test-curve-chabauty", "tests/library/test-curve-chabauty.m", group="library",
         outputs=("tests/library/test-curve-chabauty.log", "tests/library/test-curve-chabauty.results")),
    # random curves and primes (seed 1; magma -b seed:=n for others): the Frobenius matrix against
    # the zeta function, antisymmetry, additivity, tiny against Coleman integrals, and the
    # p-power against the q-power Frobenius lift
    Test("test-random", "tests/library/test-random.m", group="library"),
    # Chabauty-Coleman for the restriction of scalars (ros_chabauty in solver.m): a genus-2
    # curve over quadratic fields at the primes above 3, split and inert, rank 1 and rank 2 = g
    Test("test-ros-chabauty", "tests/library/test-ros-chabauty.m", group="library",
         outputs=("tests/library/test-ros-chabauty.log", "tests/library/test-ros-chabauty.results")),
    # examples (tests/examples/): curve_quadratic_points on curves whose quadratic points are known.
    # X(b3,ns5) over Q(sqrt 5) (genus 2, rank 0) at 11: all 79 F-rational effective divisors of
    # degree 2 outside the hyperelliptic family, provably all (the order of J(F) is 80)
    Test("quadratic-points-Xb3ns5", "tests/examples/quadratic-points-Xb3ns5.m", group="example",
         outputs=("tests/examples/quadratic-points-Xb3ns5.log", "tests/examples/quadratic-points-Xb3ns5.results")),
    # a genus-2 curve genuinely defined over Q(sqrt 5) (not a base change), rank 0: at a prime P with
    # p | #J(F_P) a single prime shows that the 15 sums of Weierstrass points are all divisors
    Test("quadratic-points-over-F", "tests/examples/quadratic-points-over-F.m", group="example",
         outputs=("tests/examples/quadratic-points-over-F.log", "tests/examples/quadratic-points-over-F.results")),
    # X(s3,ns5) over Q(sqrt 5) (genus 3, rank 1) at the single prime 19: the 36 sporadic quadratic
    # points of Appendix A, also the one at infinity
    Test("quadratic-points-Xs3ns5", "tests/examples/quadratic-points-Xs3ns5.m", group="example",
         tier="slow", timeout=7200,
         outputs=("tests/examples/quadratic-points-Xs3ns5.log", "tests/examples/quadratic-points-Xs3ns5.results")),
)
