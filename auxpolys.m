// auxpolys.m -- the auxiliary polynomials of a plane model, and the good-reduction tests.
//
// For a plane model Q(x,y) = 0 of the curve X over a number field L, monic in y of degree d
// (article: section "Good models", subsection "Plane models (Q,W^0,W^inf)"):
//   Delta  the discriminant of Q with respect to y (up to a factor, see auxpolys),
//   r      the squarefree polynomial with the same zeros and leading coefficient as Delta,
//   s      a polynomial with s*dQ/dy = Delta modulo Q; it exists by the lemma that dQ/dy is
//          invertible in O_K[x,1/r,y]/(Q).
// The remaining functions test the hypotheses of the definition "Good-reduction assumptions"
// for the triple (Q,W^0,W^inf) at a prime P. P is a prime ideal of O_L, or a rational prime p
// in the rational branch of coleman_data.
//
// Notation and conventions: see "Conventions and notation" in README.md.

auxpolys:=function(Q);

  // The auxiliary polynomials r, Delta, s of the plane model Q.
  // Input:   Q in L[x][y] (or O_L[x][y]), monic and irreducible in y, defining a
  //          geometrically integral curve over L.
  // Returns: r     in L[x]: Disc_y(Q)/gcd(Disc_y(Q),Disc_y(Q)'), squarefree, with the zeros
  //                and the leading coefficient of the discriminant;
  //          Delta in L[x]: the discriminant divided by the common factor c of it and of
  //                the coefficients of the cofactor below, so that it still has only the
  //                zeros of r (hence r^m = g*Delta for some m, as froblift needs);
  //          s     in L[x][y], deg_y(s) < d: s*dQ/dy = Delta modulo Q.
  // Method:  the resultant identity a*Q + b*dQ/dy = Disc_y(Q) with deg_y(a) <= d-2 and
  //          deg_y(b) <= d-1 is a linear system with the Sylvester matrix of Q and dQ/dy;
  //          then s = b/c and Delta = Disc_y(Q)/c.

  Delta:=Discriminant(Q);
  r:=Numerator(Delta/GCD(Delta,Derivative(Delta))); // the GCD is monic, so r keeps the leading coefficient of Delta

  L:=BaseRing(Coefficients(Q)[1]);
  Lx<x>:=RationalFunctionField(L);
  d:=Degree(Q);

  // Sylvester matrix of Q and dQ/dy: rows 1..d-1 hold the shifted coefficients of Q (for a),
  // rows d..2d-1 those of dQ/dy (for b), highest powers of y first
  coefs1:=[Lx|c:c in Reverse(Coefficients(Q))];
  coefs2:=[Lx|c:c in Reverse(Coefficients(Derivative(Q)))];
  zeros:=func<n|[Lx|0:k in [1..n]]>;
  Syl:=Matrix(Lx,[zeros(i) cat coefs1 cat zeros(d-2-i):i in [0..d-2]]
                cat [zeros(i) cat coefs2 cat zeros(d-1-i):i in [0..d-1]]);

  // solve sol*Syl = (0,...,0,Disc): sol = (coefficients of a | coefficients of b), and
  // sol[2d-i] is the coefficient of y^(i-1) in b
  sol:=Solution(Syl,RModule(Lx,2*d-1)!(zeros(2*d-2) cat [Lx!Delta]));

  // divide Delta and b by their common factor
  com_fac:=Delta;
  for i:=1 to d do
    com_fac:=GCD(com_fac,Numerator(sol[2*d-i]));
  end for;
  Delta:=Numerator(Delta/com_fac);
  Lxy:=Parent(Q);
  s:=&+[Lxy|(BaseRing(Lxy)!Numerator(sol[2*d-i]/com_fac))*Lxy.1^(i-1):i in [1..d]];

  return BaseRing(Lxy)!r,BaseRing(Lxy)!Delta,s;
end function;

genus_of_reduction:=function(Q,P)

  // The genus g of X, computed from the reduction of the plane model modulo P.
  // Input:   Q in O_L[x][y], monic in y; P a prime ideal of O_L (not a place).
  // Returns: the genus of the (normalisation of the) plane curve Q mod P over the residue
  //          field. Under the good-reduction assumptions this is the genus of X, since the
  //          smooth model associated with (Q,W^0,W^inf) is flat over the valuation ring.
  // Errors:  if Q mod P is reducible (the article requires the reduction of Q to be
  //          irreducible). Smoothness is not tested here but in coleman_data.

  Fq,m:=ResidueClassField(P);
  A2:=AffineSpace(Fq,2);
  Fqxy:=CoordinateRing(A2);
  a:=Coefficients(Q); // built coefficientwise: m does not extend to polynomials
  QmodP:=&+[Fqxy|m(Coefficient(a[i],j))*Fqxy.1^j*Fqxy.2^(i-1):j in [0..Degree(a[i])],i in [1..#a]];
  if not IsIrreducible(QmodP) then
    error "genus_of_reduction: Q mod P is reducible, so P is a bad prime for this model (good_primes in models.m lists the good ones)";
  end if;
  return Genus(Curve(Scheme(A2,QmodP)));
end function;

is_separable_mod_P:=function(f,P)

  // Whether f mod P has the same degree as f and is separable, i.e. the leading coefficient
  // of f is a unit at P and the reduction of f has distinct roots. For f = r this is the
  // good-reduction assumption on the leading coefficient and the discriminant of r.
  // Input:   f in O_L[x]; P a prime ideal of O_L, or a rational prime p.

  Fq,m:=ResidueClassField(P);
  fmodP:=PolynomialRing(Fq)![m(c):c in Coefficients(f)]; // m does not extend to polynomials
  return Degree(fmodP) eq Degree(f) and IsSeparable(fmodP);
end function;

is_integral:=function(A,P)

  // Whether the matrix A over L(x) is P-integral in the sense of the good-reduction
  // assumptions, used for W^0, W^inf and their inverses: after multiplying A by the common
  // denominator of its entries (monic, hence of valuation 0 at P), every coefficient of
  // every numerator must have non-negative valuation at P.
  // Input:   A a matrix over L(x); P a prime ideal of O_L (not a place), or a rational prime p.

  return &and[c eq 0 or Valuation(c,P) ge 0:c in Coefficients(Numerator(a)),a in Eltseq(A*Denominator(A))];
end function;
