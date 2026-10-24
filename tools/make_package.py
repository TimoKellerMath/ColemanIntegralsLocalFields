#!/usr/bin/env python3
"""Build the Magma package of the library from the library files.

    python3 tools/make_package.py           # write package/ColemanIntegralsLocalFields.m
    python3 tools/make_package.py --check   # fail if the committed package is out of date

The library is used with `load` (README.md, "Getting started"); the package is an alternative:

    AttachSpec("package/ColemanIntegralsLocalFields.spec");

It consists of the library files concatenated in their load order (their functions become
local to the package, so they cannot clash with the user's identifiers), followed by
intrinsics with the same names, signatures and defaults for the user-facing functions
listed in USER_FUNCTIONS below. The help text of an intrinsic (`?coleman_data` in Magma) is
the comment at the beginning of the function. The verbosity flag User1 of the loaded
library becomes the flag ColemanIntegration of the package.
"""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = ["isrational.m", "auxpolys.m", "cohobasis.m", "frobenius.m", "reduction.m", "coercion.m",
           "expansion.m", "integrals.m", "solver.m", "symmetric_chabauty.m", "models.m",
           "quadratic_points.m"]
PACKAGE = ROOT / "package" / "ColemanIntegralsLocalFields.m"
SPEC = ROOT / "package" / "ColemanIntegralsLocalFields.spec"
FLAG = "ColemanIntegration"

# The user-facing functions: the types of the positional arguments ("." for any type, "data"
# for the record of coleman_data, checked by a require) and the number of return values. A
# function whose number of return values depends on an option is listed with a tuple
# (option, values with it, values without it); the intrinsic then always returns the larger
# number, the missing values being 0.
USER_FUNCTIONS = {
    # integrals.m
    "coleman_data": ([".", ".", ".", "RngIntElt"], 1),
    "set_point": ([".", ".", "data"], 1),
    "set_bad_point": ([".", "SeqEnum", "BoolElt", "data"], 1),
    "coleman_integrals_on_basis": ([".", ".", "data"], ("return_side", 3, 2)),
    "tiny_integrals_on_basis": ([".", ".", "data"], 2),
    "tiny_integrals_on_basis_to_z": ([".", "data"], 4),
    "coleman_integral": ([".", ".", ".", "data"], 2),
    "teichmueller_pt": ([".", "data"], 1),
    "holomorphic_integrals_weakly_zero": ([".", "data"], 1),
    # solver.m
    "K_points": (["data", "RngIntElt"], 1),
    "Qq_points": (["data"], 2),
    "vanishing_differentials": (["SeqEnum", "data"], 4),
    "zeros_on_disk": ([".", ".", ".", "data"], 2),
    "effective_chabauty": (["data"], 2),
    "torsion_packet": ([".", "data"], 1),
    "ros_chabauty": (["SeqEnum", "."], 1),
    # symmetric_chabauty.m
    "symmetric_chabauty_classify": (["data", "."], 1),
    "quadratic_points_split": (["data", ".", ".", "."], 3),
    # models.m
    "curve_model": (["."], 1),
    "good_primes": (["."], 2),
    "improve_model": (["."], 1),
    "affine_patches": ([".", "."], 1),
    "model_coleman_data": ([".", ".", "RngIntElt"], 2),
    "point_records": ([".", "data", "."], 2),
    "curve_chabauty": ([".", "."], 1),
    # quadratic_points.m
    "curve_quadratic_points": ([".", "."], 1),
}

DEFINITION = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*:=\s*function\s*\(", re.M)


def split_top_level(text, sep):
    """text split at the occurrences of sep outside brackets and strings."""
    parts, depth, cur, instr = [], 0, "", False
    for ch in text:
        if ch == '"':
            instr = not instr
        elif not instr and ch in "([{":
            depth += 1
        elif not instr and ch in ")]}":
            depth -= 1
        if ch == sep and depth == 0 and not instr:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return [p.strip() for p in parts if p.strip()]


def parse_function(source, name, package=True):
    """The positional arguments, the optional arguments (name, default) and the help text of
    the library function (or procedure) name in source; with package = True the help text
    is prepared for an intrinsic (braces replaced, the verbosity flag of the package)."""
    m = re.search(r"^" + re.escape(name) + r"\s*:=\s*(?:function|procedure)\s*\(", source, re.M)
    if not m:
        raise SystemExit(f"make_package: {name} not found")
    # the argument list, up to the matching parenthesis
    depth, i = 1, m.end()
    while depth:
        depth += {"(": 1, ")": -1}.get(source[i], 0)
        i += 1
    args = " ".join(source[m.end():i - 1].split())
    positional, _, optional = args.partition(":")
    positional = [a.strip() for a in positional.split(",") if a.strip()]
    options = []
    for opt in split_top_level(optional, ","):
        key, _, default = opt.partition(":=")
        options.append((key.strip(), default.strip()))
    # the help text: the comment at the beginning of the body, or else the one above the definition
    rest = source[i:].split("\n")[1:]
    body_comment = []
    for line in rest:
        s = line.strip()
        if not s and not body_comment:
            continue
        if s.startswith("//"):
            body_comment.append(s[2:].rstrip())
        else:
            break
    if not body_comment:
        above = source[:m.start()].rstrip("\n").split("\n")
        k = len(above) - 1
        while k >= 0 and above[k].strip().startswith("//"):
            k -= 1
        body_comment = [l.strip()[2:].rstrip() for l in above[k + 1:]
                        if not re.match(r"^//\s*-{5,}\s*$", l.strip())]
    lines = [l[1:] if l.startswith(" ") else l for l in body_comment]
    while lines and not lines[0].strip():
        lines.pop(0)
    help_text = "\n".join(lines)
    if package:
        help_text = help_text.replace("{", "(").replace("}", ")").replace('"User1"', f'"{FLAG}"')
    return positional, options, help_text


def intrinsic(name, source):
    types, nret = USER_FUNCTIONS[name]
    positional, options, help_text = parse_function(source, name)
    if len(types) != len(positional):
        raise SystemExit(f"make_package: {name} has {len(positional)} arguments, the table lists {len(types)}")
    sig = ", ".join(f"{a}::{'Rec' if t == 'data' else t}" for a, t in zip(positional, types))
    opts = ", ".join(f"{k}:={d}" for k, d in options)
    passed = ", ".join(f"{k}:={k}" for k, _ in options)
    call = f"{name}({', '.join(positional)}{' : ' + passed if passed else ''})"
    if isinstance(nret, tuple):
        option, with_option, without = nret
        n = with_option
    else:
        n = nret
    rets = ", ".join(["."] * n)
    head = f"intrinsic {name}({sig}{' : ' + opts if opts else ''}) -> {rets}"
    lines = [head, "{" + help_text + "}"]
    for a, t in zip(positional, types):
        if t == "data":
            lines.append(f'  require is_coleman_data({a}): "{a} must be the record returned by coleman_data";')
    vals = [f"v{k}" for k in range(1, n + 1)]
    if isinstance(nret, tuple):
        lines += [f"  if {option} then",
                  f"    {', '.join(vals)}:={call};",
                  f"    return {', '.join(vals)};",
                  "  end if;",
                  f"  {', '.join(vals[:without])}:={call};",
                  f"  return {', '.join(vals[:without] + ['0'] * (n - without))};"]
    else:
        lines += [f"  {', '.join(vals)}:={call};", f"  return {', '.join(vals)};"]
    lines.append("end intrinsic;")
    return "\n".join(lines)


def build():
    sources = {f: (ROOT / f).read_text() for f in LIBRARY}
    out = ["// ColemanIntegralsLocalFields.m -- the library as a Magma package.",
           "//",
           "// Generated by tools/make_package.py from the library files; do not edit (edit the",
           "// library files and run `python3 tools/make_package.py`, or `make package`).",
           "// Use: AttachSpec(\"package/ColemanIntegralsLocalFields.spec\"); the user-facing",
           "// functions are intrinsics with the names of the library functions (see the end).",
           "",
           f"declare verbose {FLAG}, 2;",
           ""]
    for f in LIBRARY:
        text = re.sub(r"\bvprintf User1\b", f"vprintf {FLAG}", sources[f])
        text = text.replace('SetVerbose("User1"', f'SetVerbose("{FLAG}"')
        out += [f"// {'=' * 91}", f"// {f}", f"// {'=' * 91}", "", text.rstrip("\n"), ""]
    out += [f"// {'=' * 91}", "// The intrinsics", f"// {'=' * 91}", "",
            "is_coleman_data:=function(data)",
            "  // Whether data is a record of the format of coleman_data.",
            "  return Type(data) eq Rec and &and[f in Names(Format(data)):f in [\"Q\",\"L\",\"P\",\"K\",\"m\",\"F\",\"basis\",\"f0list\"]];",
            "end function;", ""]
    allsrc = "\n".join(sources[f] for f in LIBRARY)
    for name in USER_FUNCTIONS:
        out += [intrinsic(name, allsrc), ""]
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="fail if the package is not up to date")
    args = ap.parse_args()
    text = build()
    spec = PACKAGE.name + "\n"
    if args.check:
        stale = [p for p, t in ((PACKAGE, text), (SPEC, spec)) if not p.exists() or p.read_text() != t]
        if stale:
            print("make_package: out of date: " + ", ".join(str(p.relative_to(ROOT)) for p in stale)
                  + "; run `python3 tools/make_package.py`", file=sys.stderr)
            return 1
        print("make_package: the package is up to date")
        return 0
    PACKAGE.parent.mkdir(exist_ok=True)
    PACKAGE.write_text(text)
    SPEC.write_text(spec)
    print(f"make_package: wrote {PACKAGE.relative_to(ROOT)} ({len(USER_FUNCTIONS)} intrinsics)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
