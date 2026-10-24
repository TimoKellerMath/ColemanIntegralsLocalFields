#!/usr/bin/env python3
"""Compare the numerical results of a test script with the committed ones.

    python3 tests/compare_results.py COMMITTED NEW

A results file (written by the Magma helper tests/magma/results.m) has one value per line,
"name <TAB> kind <TAB> data": kind int, rat, str or bool with the value, or padic with p, the
absolute precision N (or "exact") and a rational r, the value being r modulo p^N. Two files
agree if they have the same names with the same kinds, the exact values are equal, and the
p-adic values agree modulo p^min(N_committed, N_new), with N_new >= N_committed (a smaller
precision than the committed one is a failure). Exit status 0 if they agree, 1 otherwise.
"""
import sys
from fractions import Fraction


def parse(text):
    """The entries of a results file: name -> (kind, data fields), in the order of the file."""
    entries = {}
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) < 3:
            raise ValueError(f"line {number}: expected 'name<TAB>kind<TAB>data': {line!r}")
        name, kind, data = fields[0], fields[1], fields[2:]
        if name in entries:
            raise ValueError(f"line {number}: the name {name!r} occurs twice")
        entries[name] = (kind, data)
    return entries


def valuation(x, p):
    """The p-adic valuation of a nonzero rational x."""
    v, num, den = 0, x.numerator, x.denominator
    while num % p == 0:
        num //= p
        v += 1
    while den % p == 0:
        den //= p
        v -= 1
    return v


def precision(field):
    return float("inf") if field == "exact" else int(field)


def compare_entry(name, ref, new):
    """A description of the difference between two entries, or None if they agree."""
    (k1, d1), (k2, d2) = ref, new
    if k1 != k2:
        return f"{name}: kind {k2}, committed {k1}"
    if k1 != "padic":
        if d1 != d2:
            return f"{name}: {chr(9).join(d2)}, committed {chr(9).join(d1)}"
        return None
    p1, n1, r1 = int(d1[0]), precision(d1[1]), Fraction(d1[2])
    p2, n2, r2 = int(d2[0]), precision(d2[1]), Fraction(d2[2])
    if p1 != p2:
        return f"{name}: a {p2}-adic number, committed {p1}-adic"
    if n2 < n1:
        return f"{name}: precision {d2[1]}, less than the committed {d1[1]}"
    n = min(n1, n2)
    if r1 != r2 and valuation(r1 - r2, p1) < n:
        return f"{name}: {r2} + O({p1}^{d2[1]}) differs from the committed {r1} + O({p1}^{d1[1]})"
    return None


def compare(ref_text, new_text):
    """The list of differences between the committed results and the new ones."""
    ref, new = parse(ref_text), parse(new_text)
    problems = [f"{n}: missing" for n in ref if n not in new]
    problems += [f"{n}: not among the committed results" for n in new if n not in ref]
    for name in ref:
        if name in new:
            problem = compare_entry(name, ref[name], new[name])
            if problem:
                problems.append(problem)
    return problems


def main(argv):
    if len(argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    with open(argv[1]) as a, open(argv[2]) as b:
        problems = compare(a.read(), b.read())
    for p in problems:
        print(p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
