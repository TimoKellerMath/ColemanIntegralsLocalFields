// isrational.m -- recognise a plane model with rational coefficients.
//
// If the model Q has coefficients in Q, coleman_data takes its "rational branch": the
// Frobenius lift and the reduction of the pullbacks are computed over Q_p, which is much
// cheaper than over the completion K = L_P, and only the results are moved to K.
//
// Notation and conventions: see "Conventions and notation" in README.md.

coefficients_over_Q:=function(Q)

  // The model Q as a polynomial over Q, if all its coefficients are rational.
  // Input:   Q in L[x][y], L a number field (possibly Q as a degree-1 number field) or Q.
  // Returns: Q as a polynomial in Q[x][y] and true, if all its coefficients lie in Q;
  //          Q unchanged and false otherwise.

  if not &and[IsCoercible(Rationals(),c):c in Coefficients(a),a in Coefficients(Q)] then
    return Q, false;
  end if;
  Qx:=PolynomialRing(Rationals());
  return PolynomialRing(Qx)![Qx![Rationals()!c:c in Coefficients(a)]:a in Coefficients(Q)], true;
end function;
