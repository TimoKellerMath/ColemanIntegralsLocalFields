// tests/magma/results.m   [helper of the test scripts: their numerical results]
//
// A test script records the numbers that it checks in a results file next to its log,
//
//     load "tests/magma/results.m";
//     RF := "tests/magma/unit-integrals.results";
//     results_start(RF);
//     record_result(RF, "int (3,12) -> inf", I : precision := N);
//
// and tests/regression.py compares that file with the committed one by
// tests/compare_results.py: integers, rationals, strings and booleans exactly, p-adic numbers
// to the smaller of the two absolute precisions, and a smaller precision than the committed
// one is a failure. The log of such a test is compared only for information, so its wording
// can change without updating the reference.
//
// Values: integers, rationals, strings, booleans, p-adic numbers (elements of p-adic fields
// and rings, also of extensions of Q_p: one entry per coordinate over Q_p w.r.t. the basis
// of the tower, name[c1], name[c2], ...), and sequences, lists, tuples, vectors and matrices
// of these (one entry per element, with the index appended to the name: name[i], name[i,j]).
// The option precision (an absolute precision in units of the valuation of the field of the
// value) caps the p-adic numbers at the precision that the computation certifies: their
// Magma precision can be larger, and the digits beyond it are not part of the result.
// A line of the file is "name <TAB> kind <TAB> data": kind int, rat, str or bool with the
// value, or padic with p, the absolute precision N (units of v_p; "exact" if infinite)
// and a rational r with x = r modulo p^N.

results_start := procedure(F)
  // Starts the results file F (overwriting it).
  Write(F, "# numerical results of a test script (tests/magma/results.m), compared by tests/compare_results.py" : Overwrite := true);
end procedure;


results_coordinates := function(x)
  // The coordinates over Q_p of an element x of a p-adic field or ring: Eltseq down the tower.
  if AbsoluteDegree(Parent(x)) eq 1 then
    return [x];
  end if;
  return &cat[$$(c) : c in Eltseq(x)];
end function;


results_padic := function(c)
  // The absolute precision N of an element c of Q_p (or Z_p), "exact" if it is infinite, and
  // a rational r with c = r modulo p^N.
  p := Prime(Parent(c));
  N := AbsolutePrecision(c);
  if Type(N) eq Infty then
    N := "exact";
  end if;
  if IsWeaklyZero(c) then
    return N, Rationals()!0;
  end if;
  v := Valuation(c);
  if v ge 0 then
    return N, Rationals()!(Integers()!c);
  end if;
  return N, (Integers()!(c*p^(-v)))/p^(-v);
end function;


record_result := procedure(F, name, x : precision := 0)
  // Appends the value x under the name to the results file F (see the head of the file).
  T := Type(x);
  if precision gt 0 and T in {FldPadElt, RngPadElt} then
    x +:= O(UniformizingElement(Parent(x))^precision);
  end if;
  if T eq RngIntElt then
    fprintf F, "%o\tint\t%o\n", name, x;
  elif T eq FldRatElt then
    fprintf F, "%o\trat\t%o\n", name, x;
  elif T eq MonStgElt then
    fprintf F, "%o\tstr\t%o\n", name, &cat[Strings() | (c in {"\t", "\n"}) select " " else c : c in Eltseq(x)];
  elif T eq BoolElt then
    fprintf F, "%o\tbool\t%o\n", name, x;
  elif T in {FldPadElt, RngPadElt} then
    cs := results_coordinates(x);
    p := Prime(Parent(x));
    for k := 1 to #cs do
      N, r := results_padic(cs[k]);
      fprintf F, "%o%o\tpadic\t%o\t%o\t%o\n", name, (#cs eq 1) select "" else Sprintf("[c%o]", k), p, N, r;
    end for;
  elif T in {SeqEnum, List, Tup} then
    for k := 1 to #x do
      $$(F, Sprintf("%o[%o]", name, k), x[k] : precision := precision);
    end for;
  elif T in {ModTupFldElt, ModTupRngElt} then
    for k := 1 to Degree(x) do
      $$(F, Sprintf("%o[%o]", name, k), x[k] : precision := precision);
    end for;
  elif ISA(T, Mtrx) then
    for i := 1 to NumberOfRows(x) do
      for j := 1 to NumberOfColumns(x) do
        $$(F, Sprintf("%o[%o,%o]", name, i, j), x[i,j] : precision := precision);
      end for;
    end for;
  else
    error Sprintf("record_result: values of type %o cannot be recorded (%o)", T, name);
  end if;
end procedure;
