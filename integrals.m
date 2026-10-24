// integrals.m -- Coleman integrals on a curve over a finite extension K of Q_p.
//
// Article: section "Computing Coleman integrals", with the bounds of section "Precision
// bounds". The main functions:
//   coleman_data(Q,L,P,N)         the Frobenius structure: the basis of H^1_dR(X), the matrix
//                                 A_q of F_q^* on it and the correction functions (the
//                                 algorithm "Matrices of F_tau^* and F_q^* on cohomology");
//   set_point, set_bad_point      points (the point record is described at set_bad_point);
//   tiny_integrals_on_basis       integrals of the basis forms within a residue disc (the
//                                 algorithm "Tiny integrals");
//   coleman_integrals_on_basis    integrals of the basis forms between any two points (the
//                                 algorithm "Non-tiny integrals on basis");
//   coleman_integral              the integral of an arbitrary form of the second kind (the
//                                 algorithm "Integrals in general").
// A point is given by x (1/x at infinite points) and the values of the integral basis b^0
// (resp. b^inf): (x,y) does not determine a point where the plane model is singular.
//
// Conventions (see "Conventions and notation" in README.md):
//   L the number field of the model Q, P a prime ideal of O_L, K = L_P the completion (with
//   precision Nmax), m = data`m : L -> K; points and integrals live over K, or over the
//   auxiliary totally ramified extension Ke = K(pi^(1/e)) used at bad endpoints;
//   N the target precision of the integrals and Nmax the working precision, both absolute
//   and in units of v_K (v_K(pi) = 1);
//   forms are coefficient vectors w.r.t. b^0 dx/z with z = r/lc(r), and matrices act on such
//   rows from the right (the transposes of the article's matrices);
//   the Frobenius lift F_tau^* has exponent q_tau = data`qtau and coefficient automorphism
//   tau = data`tau, and F_q^* = (F_tau^*)^(n_tau) with n_tau = data`ntau.

forward minpoly; // defined below
forward update_minpolys; // defined below; coleman_data warms the basis-minpoly cache with it (Magma binds identifiers at definition time)
forward twisted_maps, correction_data_K; // defined below; coleman_data stores the correction functions over K


// ---------------------------------------------------------------------------------------------
// Helpers: the function field of the model and of its reduction

model_function_field:=function(data)

  // The function field L(x)[y]/(Q) of the model over L = data`L, and its rational function
  // field L(x) (whose generator stands for x).

  L:=data`L;
  Lt:=RationalFunctionField(L);
  f:=PolynomialRing(Lt)![Evaluate(PolynomialRing(L)!c,Lt.1):c in Coefficients(data`Q)];
  return FunctionField(f), Lt;

end function;


basis_functions:=function(FF,W)

  // The functions b_i = sum_j W[i,j]*y^(j-1), i = 1..d, in the function field FF of the
  // model (W = W0 for b^0, W = Winf for b^inf).

  d:=NumberOfRows(W);
  return [&+[FF|W[i,j]*FF.1^(j-1):j in [1..d]]:i in [1..d]];

end function;


reduced_function_field:=function(data)

  // The function field F_q(x)[y]/(Q mod P) of the reduction of the model over the residue
  // field F_q of K, the residue map mm : O_K -> F_q and F_q(x); and a function reducing an
  // element of L(x) with P-integral coefficients to F_q(x) (coefficientwise by mm o m).

  K:=data`K; m:=data`m;
  Fq,mm:=ResidueClassField(Integers(K));
  Fqx:=RationalFunctionField(Fq);
  red_poly:=func<f|Fqx!PolynomialRing(Fq)![mm(m(c)):c in Coefficients(f)]>;
  red_ratfun:=func<f|red_poly(Numerator(f))/red_poly(Denominator(f))>;
  FFq:=FunctionField(PolynomialRing(Fqx)![red_poly(a):a in Coefficients(data`Q)]);
  return FFq, mm, Fqx, red_ratfun;

end function;


pow_K:=function(x,k)

  // x^k, with the exact 1 of the parent of x for k = 0 (also for an inexact zero x).

  if k eq 0 then
    return Parent(x)!1;
  else
    return x^k;
  end if;

end function;


cached_minpoly:=function(data,k,row,col,f1,f2)

  // The minimal polynomial of f2 over L(f1) (minpoly): data`minpolys[k][row,col] if it is
  // cached (see update_minpolys), otherwise computed.

  if assigned data`minpolys and data`minpolys[k][row,col] ne 0 then
    return data`minpolys[k][row,col];
  end if;
  return minpoly(f1,f2);

end function;

final_reduction_loss:=function(monomial_to_basis,exact_primitives,P)

  // The constant c_end of the final reduction (article: the change of basis for the final
  // reduction), in units of v_P: c_end = -v_P(C_end^(-1)), where B = E*C_end expresses the
  // basis B of E_0 used by the final reduction in the monomial basis E = (x^j b^0_k dx/z).
  // In basis_coho the rows of matb are the elements of B in the basis E, i.e. matb = C_end^T,
  // so monomial_to_basis = matb^(-1) = (C_end^(-1))^T; reduce_with_fs computes the coordinates
  // v = T*monomial_to_basis of a form with monomial coordinates T, so an error of valuation
  // >= M in T gives errors of valuation >= M-c_end in v (the Frobenius matrix and f_end).
  // The article takes the primitives g_i of the exact elements dg_i of B integral. The code
  // forms f_end = sum_i v_i*g_i with the g_i = exact_primitives of basis_coho, so a g_i of
  // negative valuation (none occurs in the examples) is accounted for as well: its column of
  // monomial_to_basis then loses -min_k v_P(monomial_to_basis[k,col_i]) - v_P(g_i) digits in
  // f_end.
  // Input:   monomial_to_basis, exact_primitives from basis_coho; P a prime ideal of the field
  //          of definition of monomial_to_basis, or the rational prime p if it is over Q (the
  //          rational branch of coleman_data).
  // Returns: c_end >= 0.

  cend:=Maximum([0] cat [-Valuation(c,P):c in Eltseq(monomial_to_basis)|c ne 0]);

  ncols:=NumberOfColumns(monomial_to_basis);
  for i:=1 to #exact_primitives do
    g:=exact_primitives[i];
    vg:=Minimum([Infinity()] cat [Valuation(c,P):c in Coefficients(g[k]),k in [1..NumberOfColumns(g)]|c ne 0]); // v_P(g_i) w.r.t. b^0
    if vg lt 0 then
      col:=ncols-#exact_primitives+i; // the coordinate of dg_i, cf. reduce_with_fs
      vcol:=Minimum([Valuation(monomial_to_basis[k,col],P):k in [1..NumberOfRows(monomial_to_basis)]|monomial_to_basis[k,col] ne 0]);
      cend:=Maximum(cend,-(vcol+vg));
    end if;
  end for;

  return cend;
end function;


max_prec:=function(Q,P,N,g,W0,Winf,e0,einf,eK,eKfK:qtau:=0,cend:=0)

  // The working precision Nmax that makes the reduction of the Frobenius pullbacks provably
  // correct to precision N: the absolute precision to which F_tau^*(omega_i) is computed
  // before the reduction. It is also the relative precision of the completion K, enough to
  // hold f0, finf, fend and the Frobenius matrix to absolute precision N.
  // Input:   Q, P, N, g, W0, Winf, e0, einf as in coleman_data; eK = e_K, eKfK = v_K(q);
  //          qtau (optional): 0 for the q-power lift, p for the p-power lift (whose pole orders
  //          only scale with p); cend (optional): c_end from final_reduction_loss, in units
  //          of v_K.
  // Returns: Nmax.
  //
  // Nmax follows the proposition on the precision of the reduction process and the remark
  // after it. With N_* = N + c_end and the floor of log_p in h_0, h_1, h_2:
  //   h_0(m) = e_K*log_p((q_tau*(m-v_K(q_tau)+1)-1)*e_0)   (loss of the finite reduction of
  //            the pole orders j < q_tau*(m-v_K(q_tau)+1); by the lemma on the expansion
  //            of F_tau^*(omega) in powers of 1/r, the coefficients of the terms with
  //            j >= q_tau*(m-v_K(q_tau)) have valuation >= m),
  //   h_1    = e_K*log_p max{1, -(ord_inf(W^(-1))+1)*e_inf}   (infinite reduction of the
  //            remainder of the finite reduction),
  //   h_2    = e_K*log_p max{1, -min{q_tau*(ord_0(W)+1), ord_inf(W^(-1))+1}*e_inf}   (infinite
  //            reduction of the part without poles at the zeros of r),
  // Nmax is chosen such that
  //   m - max{h_0(m)+h_1, h_2} >= N_*   for EVERY integer m >= Nmax,   and Nmax >= v_K(q_tau)+2.
  // The levels m > Nmax are the omitted terms of the approximation of F_tau^*(omega) modulo
  // pi^Nmax with valuation m; testing only m=Nmax is not enough, since h_0 increases with m. As in the
  // remark, a candidate is found first, then an M is chosen beyond which m-h_0(m) is increasing
  // and >= N_*+h_1 (proved analytically), and the finitely many levels below M are tested.
  // Then f0, finf, fend agree with the exact ones modulo pi^N, and so does the Frobenius matrix.
  // (Under good reduction the correction term f(i) of the Kedlaya bounds vanishes, so the pole
  // order of the approximation modulo pi^m is q_tau*(m-v_K(q_tau))-1, with no f_K-growth; cf.
  // red_lists. All logarithms are taken with Ilog, which is exact.)

  W:=Winf*W0^(-1);
  p:=Characteristic(ResidueClassField(P));
  q:=#ResidueClassField(P);
  if qtau eq 0 then // q-power lift
    qtau:=q;
    vqtau:=eKfK; // v_K(q)
  else // p-power lift
    vqtau:=eK; // v_K(p)
  end if;

  ord0W:=ord_0_mat(W);
  ordinfWinv:=ord_inf_mat(W^(-1));
  h0:=func<m | eK*Ilog(p,(qtau*(m-vqtau+1)-1)*e0)>;
  h1:=eK*Ilog(p,Maximum(1,-(ordinfWinv+1)*einf));
  h2:=eK*Ilog(p,Maximum(1,-Minimum(qtau*(ord0W+1),ordinfWinv+1)*einf));
  Nstar:=N+cend;

  // a candidate: the smallest Nmax >= max{v_K(q_tau)+2, N_*+h_2} with Nmax-h_0(Nmax) >= N_*+h_1
  Nmax:=Maximum(vqtau+2,Nstar+h2);
  while Nmax-h0(Nmax) lt Nstar+h1 do
    Nmax:=Nmax+1;
  end while;

  // the levels m >= M: x - e_K*log_p((q_tau*(x-v_K(q_tau)+1)-1)*e_0) is increasing for x >= M if
  // (M-v_K(q_tau)+1-1/q_tau)*ln(p) >= e_K, which holds if M-v_K(q_tau)+1-1/q_tau >= 3/2*e_K
  // (as 1/ln(p) <= 1/ln(2) < 3/2), and its value at M is >= N_*+h_1 if
  // ((q_tau*(M-v_K(q_tau)+1)-1)*e_0)^e_K <= p^(M-N_*-h_1); flooring the logarithm only
  // increases it, so then m-h_0(m) >= N_*+h_1 for every integer m >= M.
  M:=Maximum(Nmax,Nstar+h1);
  while (M-vqtau+1-1/qtau lt 3/2*eK) or (((qtau*(M-vqtau+1)-1)*e0)^eK gt p^(M-Nstar-h1)) do
    M:=M+1;
  end while;

  // the levels Nmax <= m < M: if a test fails, Nmax becomes one plus the largest failing level
  for m:=M-1 to Nmax by -1 do
    if m-h0(m) lt Nstar+h1 then
      Nmax:=m+1;
      break;
    end if;
  end for;

  return Nmax; // precision to be used in the computations
end function;


frobenius_matrix:=function(Q,L,P,qtau,N,Nmax,g,r,W0,Winf,G0,Ginf,frobmatb0r,red_list_fin,red_list_inf,basis,exact_primitives,monomial_to_basis,verbose:tau:=0)

  // The matrix A_tau of the Frobenius lift F_tau^* on H^1_dR w.r.t. basis, and the one-step
  // correction functions (steps (1) and (2) of the algorithm "Matrices of F_tau^* and F_q^* on
  // cohomology"): F_tau^*(omega_i) = d(f_(tau,i)) + sum_j A_tau[i,j]*omega_j with
  // f_(tau,i) = f0_i + finf_i + fend_i.
  // Input:   Q, L, P; qtau the exponent of the lift and tau its coefficient automorphism (0 for
  //          the q-power lift, cf. froblift); N, Nmax the target and working precisions; g,
  //          r, W0, Winf, G0, Ginf, basis, exact_primitives, monomial_to_basis from coleman_data;
  //          frobmatb0r from froblift; red_list_fin, red_list_inf from red_lists; verbose:
  //          print a dot per basis form.
  // Returns: F (= A_tau, over L; row i: the class of F_tau^*(omega_i)), and the lists f0list,
  //          finflist, fendlist of the correction functions (cf. reduce_with_fs).
  // The expensive per-level ingredients of the reduction, the matrices (M0/r'-l*I)^(-1)/r'
  // mod r and (Ginf_(-1)-m*I)^(-1), are precomputed once in red_lists and shared by all basis
  // forms.

  rows:=[]; f0list:=[]; finflist:=[]; fendlist:=[];
  for w in basis do
    dif:=frobenius_pullback(w,Q,P,qtau,Nmax,r,frobmatb0r:tau:=tau); // F_tau^*(omega_i) modulo P^Nmax, in ((O_L/P^Nmax)[x]((z)))^d
    dif:=convert_to_Lxzzinvd(dif,L); // lifted to (L[x]((z)))^d
    coefs,f0,finf,fend:=reduce_with_fs(dif,Q,L,P,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,exact_primitives,monomial_to_basis:qtau:=qtau); // dif is a Frobenius pullback with lift exponent qtau
    Append(~rows,coefs);
    Append(~f0list,f0); Append(~finflist,finf); Append(~fendlist,fend);
    if verbose then
      printf ".";
    end if;
  end for;

  return Matrix(L,rows),f0list,finflist,fendlist;

end function;


matrix_over_Q:=function(W,F)

  // The matrix W over L(x) as a matrix over the rational function field F = Q(x), if the
  // numerators and denominators of all its entries have rational coefficients.
  // Output: true and the matrix over F, or false and W.

  R:=RingOfIntegers(F);
  to_R:=function(f)
    cs:=Coefficients(f);
    if not &and[IsCoercible(Rationals(),c):c in cs] then
      return false, R!0;
    end if;
    return true, R![Rationals()!c:c in cs];
  end function;
  entries:=[F|];
  for a in Eltseq(W) do
    ok1,num:=to_R(Numerator(a));
    ok2,den:=to_R(Denominator(a));
    if not (ok1 and ok2) then
      return false, W;
    end if;
    Append(~entries,num/den);
  end for;
  return true, Matrix(F,NumberOfRows(W),NumberOfColumns(W),entries);

end function;


coleman_data_input:=function(Q,L,P,N,lift,verbose)

  // The input of coleman_data, checked and brought into the form the computation needs.
  // Accepted: L the rationals or a number field (absolute, relative, quadratic or cyclotomic);
  //           Q in L[x][y] or L[x,y] (x the first variable), or with coefficients in a
  //           subfield of L (e.g. Z or Q), monic in y up to a nonzero constant factor;
  //           P a prime ideal of O_L, or a rational prime with exactly one prime of O_L above it;
  //           N a positive integer; lift one of "auto", "p", "q", "plocal".
  // Returns:  Q in L[x][y], monic in y, irreducible, with P-integral coefficients; L an
  //           absolute number field of type FldNum (Q as a number field of degree 1 for L = Q);
  //           P a prime ideal of O_L.
  // Errors:   with the reason and how to correct the input.

  if not (Type(N) eq RngIntElt and N ge 1) then
    error "coleman_data: the precision N must be a positive integer (in units of v_K)";
  end if;
  if not (Type(lift) eq MonStgElt and lift in {"auto","p","q","plocal"}) then
    error "coleman_data: the option lift must be \"auto\", \"p\", \"q\" or \"plocal\"";
  end if;

  // the number field: absolute, of type FldNum
  case Type(L):
    when FldRat:
      Lnew:=ext<Rationals()|Polynomial([0,1]):DoLinearExtension>; // Q as a number field
      toL:=func<c|Lnew!c>;
    when FldQuad, FldCyc:
      Lnew:=NumberField(DefiningPolynomial(L));
      toL:=func<c|Lnew!Eltseq(L!c)>;
    when FldNum:
      Lnew:=IsAbsoluteField(L) select L else AbsoluteField(L); // L may be given as a relative extension
      toL:=func<c|Lnew!c>;
    else
      error Sprintf("coleman_data: L must be Q or a number field, not %o",Type(L));
  end case;

  // the model, in L[x][y]
  Lx<x>:=PolynomialRing(Lnew); Lxy<y>:=PolynomialRing(Lx);
  try
    if Type(Q) eq RngMPolElt then
      if Rank(Parent(Q)) ne 2 then
        error "";
      end if;
      Q:=&+[Lxy|toL(Coefficients(Q)[i])*x^e[1]*y^e[2] where e:=Exponents(Monomials(Q)[i]):i in [1..#Monomials(Q)]];
    else
      Q:=Lxy![Lx![toL(c):c in Coefficients(a)]:a in Coefficients(Q)];
    end if;
  catch e
    error "coleman_data: Q must be a polynomial in x and y over L (an element of L[x][y] or of L[x,y]), or over a subfield of L";
  end try;
  if Degree(Q) lt 1 then
    error "coleman_data: Q must have positive degree in y";
  end if;
  lc:=LeadingCoefficient(Q);
  if Degree(lc) gt 0 then
    error Sprintf("coleman_data: Q must be monic in y, but its leading coefficient is %o. Replace y by y/a(x) and multiply by a(x)^(d-1) (lc_scaling or curve_model in models.m do this)",lc);
  end if;
  if lc ne 1 then
    Q:=Q/LeadingCoefficient(lc);
    if verbose then
      print "coleman_data: Q is divided by the leading coefficient",LeadingCoefficient(lc),"to make it monic in y.";
    end if;
  end if;
  if not IsIrreducible(Q) then
    error "coleman_data: Q must be irreducible over L (it must define an integral curve)";
  end if;

  // the prime
  OL:=MaximalOrder(Lnew);
  if Type(P) eq RngIntElt then
    if not IsPrime(P) then
      error Sprintf("coleman_data: P must be a prime ideal of O_L or a rational prime, not %o",P);
    end if;
    dec:=Decomposition(OL,P);
    if #dec gt 1 then
      error Sprintf("coleman_data: there are %o primes of O_L above %o, of norms %o; pass one of them, e.g. Decomposition(MaximalOrder(L),%o)[1][1]",#dec,P,[Norm(Pp[1]):Pp in dec],P);
    end if;
    P:=dec[1][1];
  else
    try
      P:=OL!!P;
    catch e
      error "coleman_data: P must be a prime ideal of the maximal order of L, or a rational prime";
    end try;
    if not IsPrime(P) then
      error "coleman_data: P is not a prime ideal";
    end if;
  end if;
  if not &and[c eq 0 or Valuation(c,P) ge 0:c in Coefficients(a),a in Coefficients(Q)] then
    error "coleman_data: the coefficients of Q must be integral at P. Scale y (and x) to make them integral (lc_scaling in models.m), or choose another prime (good_primes in models.m)";
  end if;
  return Q, Lnew, P;

end function;


reduce_poly_mod_P:=function(f,res,Fqx)

  // The reduction of f in L[x] (P-integral coefficients) in Fqx = F_q[x], by res : O_L -> F_q.

  return Fqx![res(c):c in Coefficients(f)];
end function;


reduce_ratfun_mod_P:=function(f,res,Fqx)

  // The reduction of f in L(x) in F_q(x), for f = n/d with d monic (as Magma normalises it)
  // and n, d P-integral.

  return reduce_poly_mod_P(Numerator(f),res,Fqx)/reduce_poly_mod_P(Denominator(f),res,Fqx);
end function;


is_P_integral_poly:=function(f,P)

  // Whether all coefficients of the polynomial f over L are P-integral.

  return &and[c eq 0 or Valuation(c,P) ge 0:c in Coefficients(f)];
end function;


reduction_test_data:=function(Q:W0:=0,Winf:=0)

  // The data of the model Q in L[x][y] that the test at a single prime needs, computed once:
  // a record with r, Delta (auxpolys), W0, Winf and their inverses (mat_W0, mat_Winf unless
  // given), the genus g, and the numbers nr, ninf of geometric points of X above the zeros
  // of r and above x = infinity.

  r,Delta:=auxpolys(Q);
  if Type(W0) eq RngIntElt then
    W0:=mat_W0(Q);
  end if;
  if Type(Winf) eq RngIntElt then
    Winf:=mat_Winf(Q);
  end if;
  FL:=FunctionField(Q);
  geometric_points:=func<pls|&+[Integers()|Degree(pl):pl in pls]>;
  fmt:=recformat<Q,r,Delta,W0,W0inv,Winf,Winfinv,g,nr,ninf>;
  return rec<fmt|Q:=Q,r:=r,Delta:=Delta,W0:=W0,W0inv:=W0^(-1),Winf:=Winf,Winfinv:=Winf^(-1),
                 g:=Genus(FL),nr:=geometric_points(Zeros(FL!r)),
                 ninf:=geometric_points(Poles(FL!BaseRing(Parent(Q)).1))>;
end function;


good_reduction_at:=function(T,P)

  // Whether the triple (Q, W^0, W^inf) of the model passes the good-reduction assumptions at
  // the prime P, and if not, why.
  // Input:  T = reduction_test_data(Q); P a prime ideal of O_L.
  // Output: true and "", or false and the reason.
  //
  // The tests, cheapest first: Q has P-integral coefficients; the leading coefficient of r
  // is a unit and r mod P is separable of the same degree (assumption (1)); W0, Winf and their
  // inverses are P-integral (assumption (3)); Q mod P is geometrically irreducible of genus g;
  // the reductions of b^0 and b^inf are integral bases of the reduction over F_q[x] and
  // F_q[1/x] (assumption (2)): the matrices W0~ * W0max^(-1), Winf~ * Winfmax^(-1) relating
  // them to the integral bases of the reduction (mat_W0, mat_Winf over F_q) are invertible
  // over F_q[x], F_q[1/x]; and the points of X above the zeros of r and above infinity stay
  // distinct modulo P (assumption (4): the reduced boundary is etale, i.e. it has as many
  // geometric points as the generic fibre).

  Q:=T`Q; d:=Degree(Q);
  if not &and[is_P_integral_poly(Coefficient(Q,i),P):i in [0..d]] then
    return false, "the coefficients of Q are not integral at P";
  end if;
  if not is_P_integral_poly(T`r,P) or Valuation(LeadingCoefficient(T`r),P) gt 0 then
    return false, "the leading coefficient of r is not a unit at P (a zero of r meets x = infinity)";
  end if;
  if not is_separable_mod_P(T`r,P) then
    return false, "r mod P is not separable (two zeros of r meet modulo P)";
  end if;
  for W in [<T`W0,"W0">,<T`W0inv,"W0^(-1)">,<T`Winf,"Winf">,<T`Winfinv,"Winf^(-1)">] do
    if not is_integral(W[1],P) then
      return false, Sprintf("%o is not integral at P",W[2]);
    end if;
  end for;
  Fq,res:=ResidueClassField(P);
  Fqx<x>:=PolynomialRing(Fq); Fqxy<y>:=PolynomialRing(Fqx);
  Qt:=&+[Fqxy|reduce_poly_mod_P(Coefficient(Q,i),res,Fqx)*y^i:i in [0..d]];
  R2<X,Y>:=PolynomialRing(Fq,2);
  if not IsIrreducible(&+[R2|Evaluate(Coefficient(Qt,i),X)*Y^i:i in [0..d]]) then
    return false, "Q mod P is reducible";
  end if;
  FFq:=FunctionField(Qt);
  if Degree(ExactConstantField(FFq),Fq) gt 1 then
    return false, "Q mod P is not geometrically irreducible";
  end if;
  if Genus(FFq) ne T`g then
    return false, Sprintf("the reduction has genus %o, not %o",Genus(FFq),T`g);
  end if;
  // assumption (2): the reductions of the integral bases are integral bases
  W0t:=Matrix(d,d,[reduce_ratfun_mod_P(a,res,Fqx):a in Eltseq(T`W0)]);
  Winft:=Matrix(d,d,[reduce_ratfun_mod_P(a,res,Fqx):a in Eltseq(T`Winf)]);
  T0:=W0t*mat_W0(Qt)^(-1);
  if not (&and[Degree(Denominator(a)) eq 0:a in Eltseq(T0)] and Degree(Numerator(Determinant(T0))) eq 0) then
    return false, "the reduction of b^0 is not an integral basis of the reduction over F_q[x]";
  end if;
  Tinf:=Winft*mat_Winf(Qt)^(-1);
  Fqt:=FieldOfFractions(Fqx);
  inv:=func<a|Evaluate(a,1/Fqt.1)>; // a(1/t): in F_q[t] iff a in F_q[1/x]
  if not (&and[Degree(Denominator(inv(a))) eq 0:a in Eltseq(Tinf)] and Degree(Numerator(inv(Determinant(Tinf)))) eq 0) then
    return false, "the reduction of b^inf is not an integral basis of the reduction over F_q[1/x]";
  end if;
  // assumption (4)
  geometric_points:=func<pls|&+[Integers()|Degree(pl):pl in pls]>;
  if geometric_points(Zeros(FFq!reduce_poly_mod_P(T`r,res,Fqx))) ne T`nr then
    return false, "points of X above the zeros of r meet modulo P";
  end if;
  if geometric_points(Poles(FFq!x)) ne T`ninf then
    return false, "points of X above x = infinity meet modulo P";
  end if;
  return true, "";
end function;


good_reduction_failure:=function(Delta,r,W0,Winf,P)

  // The first tested good-reduction condition that fails at P, as a sentence, or "": the
  // leading coefficient of Delta (and r) is a unit and r mod P is separable of the same degree
  // (assumption (1) of the definition "Good-reduction assumptions"), and W0, Winf and their
  // inverses are P-integral (assumption (3)). P is a prime ideal, or p in the rational branch.

  if Degree(r) lt 1 then
    return "r is constant";
  end if;
  if Valuation(LeadingCoefficient(Delta),P) gt 0 then
    return "the leading coefficient of r is not a unit (a zero of r meets x = infinity modulo P)";
  end if;
  if not is_separable_mod_P(r,P) then
    return "r mod P is not separable (two zeros of r meet modulo P)";
  end if;
  for W in [<W0,"W0">,<W0^(-1),"W0^(-1)">,<Winf,"Winf">,<Winf^(-1),"Winf^(-1)">] do
    if not is_integral(W[1],P) then
      return Sprintf("%o is not integral at P (the integral basis does not reduce well)",W[2]);
    end if;
  end for;
  return "";

end function;


reduction_model:=function(Q,W0,Winf,verbose)

  // The model over the field of the reduction: in the rational branch of coleman_data (Q
  // has rational coefficients, and so do W0 and Winf if they are supplied) the model and the
  // integral bases over Q, where the Frobenius structure is computed over Q_p; otherwise Q
  // itself, over L.
  // Returns: the model, whether it is rational, and W0, Winf (0 if not supplied).

  QL:=Q; // the model over L
  Q, isrational:=coefficients_over_Q(Q);
  if isrational then
    Qx:=FieldOfFractions(BaseRing(Q));
    if Type(W0) ne RngIntElt then
      isrational,W0Q:=matrix_over_Q(W0,Qx);
      W0:=isrational select W0Q else W0;
    end if;
    if isrational and Type(Winf) ne RngIntElt then
      isrational,WinfQ:=matrix_over_Q(Winf,Qx);
      Winf:=isrational select WinfQ else Winf;
    end if;
    if not isrational then
      Q:=QL;
      if verbose then
        print "coleman_data: the supplied integral bases have non-rational coefficients; the model is treated over L.";
      end if;
    end if;
  end if;
  return Q, isrational, W0, Winf;

end function;


semilinear_composition:=function(Atau,tau,ntau)

  // The matrix A_q = tau^(n_tau-1)(A_tau)*...*tau(A_tau)*A_tau of F_q from the matrix A_tau of
  // the (tau-semilinear if n_tau > 1) lift (step (3) of the algorithm "Matrices of F_tau^* and
  // F_q^* on cohomology"), and the suffix products Clist[k+1] = C_k =
  // tau^(n_tau-1)(A_tau)*...*tau^(k+1)(A_tau), k = 0..n_tau-1 (C_(n_tau-1) = I; the C_j of the
  // proof of the lemma on the precision of the semilinear composition).
  // Input:   Atau a square matrix over L; tau the coefficient automorphism (0 for the identity,
  //          cf. twist_mat); ntau = n_tau.

  L:=BaseRing(Atau);
  Atau_conj:=[Atau];
  for k:=1 to ntau-1 do
    Atau_conj[k+1]:=twist_mat(Atau_conj[k],tau); // tau^k(A_tau)
  end for;
  Clist:=[IdentityMatrix(L,NumberOfRows(Atau)):k in [1..ntau]];
  for k:=ntau-2 to 0 by -1 do
    Clist[k+1]:=Clist[k+2]*Atau_conj[k+2];
  end for;
  return Clist[1]*Atau_conj[1], Clist;

end function;


frobenius_sanity_checks:=procedure(F,Atau,m,g,q,eKfK,N,ntau,verbose)

  // Cheap sanity checks on the matrix F = A_q of F_q on a basis of H^1_dR(X) (over L, mapped
  // to K by m): its characteristic polynomial is the numerator of the zeta function of the
  // reduction, so it must have coefficients in Z, satisfy the Weil functional equation, and
  // have det = +-q^g; for the p-power lift (n_tau > 1) also n_tau*v_K(det A_tau) = v_K(q^g).
  // This catches most implementation and precision errors (in particular in the semilinear
  // composition of the p-power lift) at negligible cost. A failure is printed as a warning;
  // with verbose, success is reported.
  // The Frobenius matrix itself need not be integral with respect to the
  // Balakrishnan-Tuitman basis of H^1_dR (single entries with v_K = -1 occur routinely,
  // especially for small p), so non-integrality is not flagged as an error; correctness
  // is certified by the determinant, rationality and functional-equation checks.

  FK:=ChangeRing(F,m);
  thresh:=Maximum(1,N div 2); // genuine errors show up at valuation ~0, precision noise at ~N
  sane:=true;
  vminF:=Minimum([Valuation(c):c in Eltseq(FK)]);
  vdetF:=Valuation(Determinant(FK));
  if vdetF ne g*eKfK then
    sane:=false;
    print "WARNING (sanity): v_K(det F) =",vdetF,"but det F = +-q^g requires",g*eKfK;
  end if;
  if ntau gt 1 then
    vdetAtau:=Valuation(Determinant(ChangeRing(Atau,m)));
    if ntau*vdetAtau ne g*eKfK then
      sane:=false;
      print "WARNING (sanity): v_K(det A) =",vdetAtau,"for the p-power lift matrix A, but n_tau*v_K(det A) should be",g*eKfK;
    end if;
  end if;
  acp:=Coefficients(CharacteristicPolynomial(FK)); // P(T)=sum acp[i+1]T^i, deg 2g, monic
  // coordinates over Q_p: rational coefficients have all higher coordinates ~0
  rational:=forall{a:a in acp|forall{c:c in Eltseq(a)[2..#Eltseq(a)]|Valuation(c) ge thresh}};
  if not rational then
    sane:=false;
    print "WARNING (sanity): the characteristic polynomial of Frobenius does not have coefficients in Z_p";
  end if;
  eps:=(Valuation(acp[1]-q^g) ge Valuation(acp[1]+q^g)) select 1 else -1; // det F = eps*q^g
  funceq:=forall{i:i in [0..2*g]|Valuation(q^i*acp[i+1]-eps*q^g*acp[2*g-i+1]) ge thresh}; // q^i a_i = eps q^g a_{2g-i}
  if not funceq then
    sane:=false;
    print "WARNING (sanity): the characteristic polynomial of Frobenius does not satisfy the Weil functional equation";
  end if;
  if verbose and sane then
    print "coleman_data: sanity checks on the Frobenius matrix passed (determinant, rationality, functional equation).";
    if vminF lt 0 then
      print "coleman_data: (the Frobenius matrix has minimal entry valuation",vminF,"< 0; this is normal for the H^1_dR basis and not an error).";
    end if;
  end if;

end procedure;


coleman_data:=function(Q,L,P,N:useU:=false,basis0:=[],basis1:=[],basis2:=[],verbose:=true,W0:=0,Winf:=0,lift:="auto",full_check:=false)

  // The data for Coleman integration on the smooth projective curve X with plane model Q at
  // the completion K = L_P, to P-adic precision N (article: sections "Good models" to
  // "Computing Coleman integrals"; the steps are marked below).
  // Input:   Q in O_L[x][y], monic and irreducible in y, with good reduction at P in the sense
  //          of the definition "Good-reduction assumptions" (the cheap ones are tested, all of
  //          them with full_check); L a number field (or Q);
  //          P a prime ideal of O_L; N >= 1 the target precision, in units of v_K. Other
  //          forms of the input are accepted as described at coleman_data_input.
  //          Optional: useU (a basis of H^1_dR(U) instead of H^1_dR(X)); basis0, basis1, basis2
  //          (prescribed bases, see basis_coho); verbose (progress, timings and the sanity
  //          checks below); W0, Winf (the integral bases, as in mat_W0, mat_Winf; computed if
  //          0; for a model with rational coefficients they must have rational coefficients
  //          too, otherwise the model is treated over L);
  //          lift = "auto"/"p"/"q"/"plocal": the Frobenius lift. For f_K >= 2 the p-power
  //          lift (q_tau = p, n_tau = f_K) is used when possible ("auto"), which shrinks all
  //          series lengths by a factor of about q/p compared to the q-power lift; "q" forces
  //          the q-power lift, "p" fails if the p-power lift is not available. It is
  //          available if the model has rational coefficients, and otherwise whenever P is
  //          unramified: tau is then a global automorphism of L if there is one (e.g. L/Q
  //          Galois), and else the Frobenius of L_P applied through the completion, modulo
  //          P^Nmax (frobenius_aut_local). "plocal" is "p" with the latter forced (for tests);
  //          full_check: also test the other good-reduction assumptions (good_reduction_at:
  //          Q mod P geometrically irreducible of genus g, the reductions of b^0 and b^inf
  //          integral bases of the reduction, an etale reduced boundary), at the cost of
  //          function field computations over F_q.
  // Returns: the record data described before its definition at the end of this function.
  // Errors:  if the input is invalid (coleman_data_input), or P fails one of the tested
  //          good-reduction conditions; the message says which.
  // A model with rational coefficients takes the rational branch: the Frobenius lift and the
  // reduction are computed over Q_p (cheaper than over K), and the results are moved to K.

  Q,L,P:=coleman_data_input(Q,L,P,N,lift,verbose);

  ResetMaximumMemoryUsage();
  t0:=Cputime();
  if verbose then
    print "Computing Delta,r,s,W^0,W^inf,G:";
  end if;
  print_resources:=procedure(t)
    if verbose then
      print "Time (s) :    ", Cputime(t);
      print "Memory (Mb) : ", GetMaximumMemoryUsage() div (1024^2), "\n";
    end if;
  end procedure;

 // Preparation: the residue field and the invariants of K

  Fq:=ResidueClassField(P);
  p:=Characteristic(Fq);
  q:=#Fq;
  eK:=Valuation(p,Place(P));   // e_K
  eKfK:=Valuation(q,Place(P)); // e_K*f_K = v_K(q)
  fK:=eKfK div eK;             // residue degree, q = p^fK
  g:=genus_of_reduction(Q,P);

  tau:=0;     // the coefficient automorphism tau of the lift (0 = identity)
  tauprec:=0; // 0, or the precision of its approximation tau_N if tau is not a global automorphism
  qtau:=q;    // q_tau, the exponent of the Frobenius lift (q or p)
  ntau:=1;    // n_tau, the number of lift steps composing to F_q (1 or f_K)

  // the rational branch: a model with rational coefficients (and supplied integral bases with
  // rational coefficients) is reduced over Q_p
  QL:=Q; // the model over L
  Q,isrational,W0,Winf:=reduction_model(Q,W0,Winf,verbose);

  // the field, prime and invariants over which the Frobenius structure is computed: Q_p in the
  // rational branch (e = 1, v_p(q) = f_K), K otherwise
  if isrational then
    Lred:=Rationals(); Pred:=p; eKred:=1;
    Nred:=Ceiling(N/eK); // the target precision over Q_p, in units of v_p
  else
    Lred:=L; Pred:=P; eKred:=eK;
    Nred:=N;
  end if;

  // the Frobenius lift: for f_K >= 2 the p-power Frobenius instead of the q-power one, which
  // shrinks all series lengths and pole orders by a factor of about q/p; the matrix of F_q is
  // recovered as tau^(f_K-1)(A_tau)*...*tau(A_tau)*A_tau in (8). Over Q, tau acts trivially on
  // the coefficients. Over L it needs P unramified: tau is a global automorphism of L if one
  // induces the Frobenius of K (e.g. when L/Q is Galois); otherwise (or with lift="plocal")
  // the map tau_N of frobenius_aut_local, which induces it modulo P^Nmax -- all that the
  // computation needs. (The message is printed where it always appeared in the two branches.)
  plift:=(lift ne "q") and (fK gt 1) and (isrational or eK eq 1);
  if (lift in {"p","plocal"}) and (fK gt 1) and not plift then
    error "coleman_data: the p-power Frobenius lift requires P to be unramified over p (or a model with rational coefficients); use lift:=\"q\"";
  end if;
  if plift then
    qtau:=p;
    ntau:=fK;
    if not isrational and lift ne "plocal" then
      tau:=frobenius_aut(L,P);
    end if;
  end if;
  liftmessage:=procedure()
    if verbose and plift then
      print "Using the p-power Frobenius lift (p =",p,", f_K =",fK,").";
    end if;
  end procedure;
  if isrational then
    liftmessage();
  end if;

 // (1) the model: r, Delta, s and the integral bases (unless supplied)
  r,Delta,s:=auxpolys(Q);
  if Type(W0) eq RngIntElt then
    W0:=mat_W0(Q);
  end if;
  if Type(Winf) eq RngIntElt then
    Winf:=mat_Winf(Q);
  end if;

 // (2) the tested good-reduction conditions at P (genus_of_reduction checked that Q mod P is
 //     irreducible)
  failure:=good_reduction_failure(Delta,r,W0,Winf,Pred);
  if failure eq "" and full_check then // all assumptions, for the model and the integral bases over L
    Lpol:=PolynomialRing(L);
    overL:=func<W|Matrix(FieldOfFractions(Lpol),NumberOfRows(W),NumberOfColumns(W),
                         [(Lpol!Numerator(a))/(Lpol!Denominator(a)):a in Eltseq(W)])>;
    _,failure:=good_reduction_at(reduction_test_data(QL:W0:=overL(W0),Winf:=overL(Winf)),P);
  end if;
  if failure ne "" then
    error Sprintf("coleman_data: the model does not have good reduction at P: %o. good_primes in models.m lists the good primes of the model, and improve_model searches for a model with more good primes",failure);
  end if;

 // (3) the connection matrices, their residue matrices and the maximal ramification indices
 //     e_0, e_inf of x (these do not change under base change)
  G:=connection_matrix(Q,Delta,s);
  G0,Ginf:=connection_matrices_0_inf(G,W0,Winf);
  Jinf,Tinf,Tinfinv:=jordan_inf(Ginf);
  J0,T0,T0inv:=jordan_0(r,G0);
  e0,einf:=max_ramification_indices(J0,Jinf);
  print_resources(t0);

 // (4) the cohomology basis (algorithm "Computing cohomology basis")
  ResetMaximumMemoryUsage();
  t:=Cputime();
  if verbose then
    print isrational select "Computing basis H^1(X) over the rational field:" else "Computing basis H^1(X):";
  end if;
  basis,exact_primitives,monomial_to_basis:=basis_coho(Q,Pred,r,W0,Winf,G0,Ginf,J0,Jinf,T0inv,Tinfinv,useU,basis0,basis1,basis2);
  print_resources(t);

 // (5) the working precision Nmax and the Frobenius lift on functions (algorithm "Compute
 //     matrix of Frobenius on functions")
  ResetMaximumMemoryUsage();
  t:=Cputime();
  if not isrational then
    liftmessage();
  end if;
  if verbose then
    print "Computing Frobenius lift:";
  end if;
  qtauarg:=plift select p else 0; // max_prec and red_lists: 0 for the q-power lift
  if isrational then
    cend:=eK*final_reduction_loss(monomial_to_basis,exact_primitives,p); // c_end in units of v_K (the final reduction runs over Q_p)
    Nmax:=max_prec(Q,P,N,g,W0,Winf,e0,einf,eK,eKfK:qtau:=qtauarg,cend:=cend); // the working precision over K
    // the working precision over Q_p, in units of v_p: for precision p^Nred, i.e. at least
    // pi^N; it satisfies the condition of max_prec over Q_p (target Nred, c_end/e_K), since h_0
    // over Q_p at the level m is at most h_0 over K at the level e_K*m, divided by e_K
    NmaxQ:=max_prec(Q,P,Nred*eK,g,W0,Winf,e0,einf,eK,eKfK:qtau:=qtauarg,cend:=cend);
    Nmaxred:=Maximum(Ceiling(NmaxQ/eK),Valuation(qtau,p)+2);
  else
    cend:=final_reduction_loss(monomial_to_basis,exact_primitives,P); // c_end in units of v_K
    Nmax:=max_prec(Q,P,N,g,W0,Winf,e0,einf,eK,eKfK:qtau:=qtauarg,cend:=cend); // the working precision
    Nmaxred:=Nmax;
    if plift and Type(tau) eq RngIntElt then // no global automorphism of L induces the Frobenius of K (or lift="plocal")
      tauprec:=Nmax+1; // >= Nmax suffices (cf. frobenius_aut_local); one digit of margin
      tau:=frobenius_aut_local(L,P,tauprec);
      if verbose then
        printf "%o: the Frobenius of L_P is applied through the completion, modulo P^%o.\n",
          (lift eq "plocal") select "lift=\"plocal\"" else "No global Frobenius automorphism of L at P", tauprec;
      end if;
    end if;
  end if;
  // modulo P^(Nmax - v(q_tau)) over the field of the reduction: the pullback of dx contributes
  // the factor q_tau
  frobmatb0r:=froblift(Q,Pred,qtau,Nmaxred-eKred*Valuation(qtau,p),r,Delta,s,W0:tau:=tau);
  print_resources(t);

 // (6) the reduction matrices, for the pole orders up to q_tau*(Nmax - v(q_tau)) - 1 that
 //     the pullbacks computed in (5) can have (cf. red_lists)
  if verbose then
    print "Computing reduction matrices:";
  end if;
  red_list_fin,red_list_inf:=red_lists(Q,Lred,Pred,q,Nmaxred,r,W0,Winf,G0,Ginf,e0,einf,J0,Jinf,T0,Tinf,T0inv,Tinfinv,eKred,eKred*fK:qtau:=qtauarg);
  print_resources(t);

 // (7) the matrix A_tau and the correction functions (frobenius_matrix), correct modulo
 //     pi^Nred over the field of the reduction
  ResetMaximumMemoryUsage();
  t:=Cputime();
  if verbose then
    print "Computing Frobenius matrix:";
  end if;
  F,f0list,finflist,fendlist:=frobenius_matrix(Q,Lred,Pred,qtau,Nred,Nmaxred,g,r,W0,Winf,G0,Ginf,frobmatb0r,red_list_fin,red_list_inf,basis,exact_primitives,monomial_to_basis,verbose:tau:=tau);
  if verbose then
    print "";
  end if;
  print_resources(t);


 // (8) the matrix of F_q (step (3) of the algorithm "Matrices of F_tau^* and F_q^* on
 //     cohomology"): with A_tau the matrix of the (tau-semilinear if n_tau > 1) lift,
 //     F_tau^*(omega_i) = d(f_i) + sum_j A_tau[i,j]*omega_j, the matrix of F_q is
 //     A_q = tau^(n_tau-1)(A_tau)*...*tau(A_tau)*A_tau. The suffix products
 //     Clist[k+1] = C_k = tau^(n_tau-1)(A_tau)*...*tau^(k+1)(A_tau) (C_(n_tau-1) = I; the C_j of the
 //     proof of the lemma on the precision of the semilinear composition) are the
 //     coefficients of g_q = sum_k C_k*(F_tau^*)^k(f_tau), needed in coleman_integrals_on_basis.
 //     For n_tau = 1 all of this is trivial.

  Atau:=ChangeRing(F,L); // A_tau, over L
  F,Clist:=semilinear_composition(Atau,tau,ntau); // A_q, the matrix of F_q on H^1_dR(X), and the C_k


 // (9) the record

  K1,m1:=Completion(L,P:Precision:=Nmax); // K1 has infinite precision (it is free), m1 has relative precision Nmax
  K:=ChangePrecision(K1,Nmax); // K has precision Nmax: relative precision N would not hold all coefficients correct to absolute precision N
  m:=m1*Coercion(K1,K); // the completion map L -> K
  pi:=m(UniformizingElement(P));

 // cheap sanity checks on the Frobenius matrix (only meaningful for the H^1(X) basis)
  if #basis eq 2*g then
    frobenius_sanity_checks(F,Atau,m,g,q,eKfK,N,ntau,verbose);
  end if;

  // The record data (the transposes of the article's matrices, see the file header):
  //   Q, L, P, p          the model (rational coefficients in the rational branch), the number
  //                       field (absolute), the prime ideal, the residue characteristic;
  //   eK, N, Nmax         e_K, the target precision and the working precision (units of v_K);
  //   K, m, pi            the completion with precision Nmax, the map m : L -> K, m(uniformizer);
  //   g                   the genus;
  //   W0, Winf            the integral bases b^0, b^inf (mat_W0, mat_Winf);
  //   r, Delta, s         from auxpolys; forms are w.r.t. b^0 dx/z, z = r/lc(r);
  //   G0, Ginf            the connection matrices (connection_matrices_0_inf);
  //   e0, einf            the maximal ramification indices above the zeros of r, resp. infinity;
  //   basis               omega_1, ..., omega_2g (or a basis of H^1_dR(U)), vectors in L[x]^d;
  //   exact_primitives,   from basis_coho, for the final reduction;
  //   monomial_to_basis
  //   F                   A_q, the matrix of F_q^* on the basis (over L, correct modulo pi^N);
  //   f0list, finflist,   the one-step correction functions f_(tau,i) = f0 + finf + fend of the
  //   fendlist            basis forms (reduce_with_fs);
  //   red_list_fin,       the matrices of the reduction steps (red_lists);
  //   red_list_inf
  //   corrK               the correction functions with their coefficients in K, at every
  //                       Frobenius level k = 0..n_tau-1 (correction_data_K with the coefficient
  //                       map twisted_maps(data)[k+1]);
  //   minpolys            cache of minimal polynomials of the basis functions (update_minpolys);
  //   Atau, Clist         A_tau and the C_k (see (8));
  //   tau, tauprec        the coefficient automorphism (0 for tau = id) and, if it is the local
  //                       approximation tau_N, its precision (0 otherwise);
  //   ntau, qtau          n_tau and q_tau;
  //   cend                the loss c_end of the final reduction (units of v_K), which entered Nmax;
  //   Nmaxred, eKred      N_max and e_K of the field over which the Frobenius matrix was reduced
  //                       (Q_p in the rational branch, K otherwise), which bound the pole orders
  //                       and coefficients of the f0list (cf. evalf0_list).
  format:=recformat<Q,L,P,p,eK,N,K,m,pi,g,W0,Winf,r,Delta,s,G0,Ginf,e0,einf,basis,monomial_to_basis,exact_primitives,F,f0list,finflist,fendlist,corrK,Nmax,red_list_fin,red_list_inf,minpolys,Atau,Clist,tau,tauprec,ntau,qtau,cend,Nmaxred,eKred>;
  out:=rec<format|>;
  out`Q:=Q; out`L:=L; out`P:=P; out`p:=p; out`eK:=eK; out`N:=N; out`K:=K; out`m:=m; out`pi:=pi; out`g:=g; out`W0:=W0; out`Winf:=Winf; out`r:=r; out`Delta:=Delta; out`s:=s; out`G0:=G0; out`Ginf:=Ginf;
  out`e0:=e0; out`einf:=einf; out`basis:=basis; out`monomial_to_basis:=monomial_to_basis; out`exact_primitives:=exact_primitives; out`F:=F; out`f0list:=f0list;
  out`finflist:=finflist; out`fendlist:=fendlist; out`Nmax:=Nmax; out`red_list_fin:=red_list_fin; out`red_list_inf:=red_list_inf;
  out`Atau:=Atau; out`Clist:=Clist; out`tau:=tau; out`tauprec:=tauprec; out`ntau:=ntau; out`qtau:=qtau;
  out`cend:=cend; out`Nmaxred:=Nmaxred; out`eKred:=eKred;

  // The correction functions with their coefficients in K at every Frobenius level: they
  // depend only on the curve, so every evaluation at an endpoint reuses them.
  mks:=twisted_maps(out);
  out`corrK:=[correction_data_K(f0list,finflist,fendlist,out,mks[k+1]):k in [0..ntau-1]];

  // Warm the basis-minpoly cache (the index=0 row: the minimal polynomial of each b_i over L(x),
  // resp. over L(1/x)). These depend only on the curve (Q,W0,Winf), not on the integration
  // endpoints, so computing them once here lets every later integral reuse them (coleman_side
  // only updates a local copy of data, and over a number field the minpoly/NullSpace work would
  // dominate the per-integral runtime). The per-point index>0 rows (ramified-uniformizer
  // minpolys) stay lazy.
  out:=update_minpolys(out,false,0);
  out:=update_minpolys(out,true,0);

  if verbose then
    print "coleman_data: Nmax =",Nmax;
    print "coleman_data: total time (s):",Cputime(t0);
  end if;

  return out;

end function;

known_digits:=function(x0)

  // The number of known digits of an element x0 of a p-adic field: its relative precision if
  // x0 is not weakly zero, and its absolute precision if it is (an inexact zero O(pi^a)).

  if RelativePrecision(x0) eq 0 then
    return AbsolutePrecision(x0);
  else
    return RelativePrecision(x0);
  end if;
end function;

set_point:=function(x0,y0,data)

  // The point with affine coordinates (x0,y0) on the plane model, as a point record over K
  // (see set_bad_point).
  // Input:   x0, y0 in L (or in Q, Z) with x0 P-integral; data from coleman_data.
  // Requires: (x0,y0) on the curve (if only approximately, a warning reports to which
  //          precision); if W0 is not the identity, the point must be good: at a bad point
  //          (x0,y0) need not determine the point, so set_bad_point is needed there.
  // Returns: the record with inf = false, x = m(x0), b = the values of b^0 at the point
  //          (b^0 = W0*(1,y,...,y^(d-1))^T), r = z(x0) with z = r/lc(r).

  Q:=data`Q; L:=data`L; m:=data`m; W0:=data`W0; d:=Degree(Q);
  ok1,x0:=IsCoercible(L,x0); ok2,y0:=IsCoercible(L,y0);
  if not (ok1 and ok2) then
    error "set_point: x0 and y0 must be elements of the number field data`L (or of Q); for points over K use set_bad_point";
  end if;
  if Valuation(m(x0)) lt 0 then
    error "set_point: x0 is not integral at P, so the point lies in an infinite residue disc; give it by set_bad_point(1/x0, [values of b^inf], true, data), or convert it with point_records (models.m)";
  end if;

  // sanity: check that (x0,y0) satisfies the curve equation (to precision N)
  Qval:=&+[Evaluate(Coefficient(Q,i),x0)*y0^i:i in [0..d]];
  if Qval ne 0 then
    vQpt:=Valuation(m(Qval));
    if vQpt lt 1 then
      error Sprintf("set_point: (%o, %o) is not a point of the curve, not even modulo P (Q(x0,y0) = %o)",x0,y0,Qval);
    end if;
    if vQpt lt data`N then
      print "WARNING: the point (x0,y0) only satisfies the curve equation up to precision",vQpt,"- results involving it are at most that accurate";
    end if;
  end if;

  rx0:=Evaluate(data`r/LeadingCoefficient(data`r),x0);
  if W0 ne IdentityMatrix(BaseRing(W0),d) and Valuation(m(rx0)) gt 0 then // a finitely bad point
    error "set_point: (x0,y0) lies in a bad residue disc (r(x0) = 0 mod P), where (x,y) need not determine the point; give it by set_bad_point(x0, [values of b^0], false, data), or convert it with point_records (models.m)";
  end if;

  // the values of b^0 at the point, computed in L; the point record over K (the relative
  // precision of the entries matters for evaluating the correction functions f0, finf, fend)
  b:=Vector(L,[y0^i:i in [0..d-1]])*Transpose(ChangeRing(Evaluate(W0,x0),L));
  format:=recformat<x,b,r,inf,xt,bt,index>;
  return rec<format|inf:=false,x:=m(x0),b:=Eltseq(ChangeRing(b,m)),r:=m(rx0)>;

end function;


is_bad:=function(Pt,data)

  // Whether the point Pt is bad, i.e. lies in a bad residue disc: an infinite disc (Pt`inf),
  // or a finitely bad one (v_K(z(x(Pt))) > 0; article: the definition of bad and good points).

  return Pt`inf or Valuation(Pt`r) gt 0;

end function;


is_very_bad:=function(Pt,data)

  // Whether the point Pt is very bad: x(Pt) = infinity (Pt`x = 1/x(Pt) = 0) or z(x(Pt)) = 0,
  // decided to the precision NK of K (an inexact zero counts as zero).

  NK:=Precision(data`K);
  return Pt`inf select Valuation(data`K!Pt`x) ge NK else Valuation(Pt`r) ge NK;

end function;


lie_in_same_disc:=function(Pt1,Pt2,data)

  // Whether the points Pt1, Pt2 lie in the same residue disc: both are finite or both are
  // infinite, and x (resp. 1/x) and the values of b^0 (resp. b^inf) agree modulo pi. These
  // are the coordinates of the affine charts of the smooth model, so they determine the
  // reduction of a point.

  return Pt1`inf eq Pt2`inf and Valuation(Pt1`x-Pt2`x) ge 1
         and &and[Valuation(Pt1`b[i]-Pt2`b[i]) ge 1:i in [1..#Pt1`b]];

end function;


minpoly:=function(f1,f2)

  // The minimal polynomial of f2 over L(f1), as a polynomial in L[x][y] with x standing for
  // f1 and y for f2 (article: the algorithm "Minimal polynomial of a function in a function
  // field").
  // Input:   f1, f2 in a function field L(x)[y]/(Q) of a curve over L, f1 nonconstant.
  // Method:  for f1 = x or 1/x, L(f1) = L(x), and the minimal polynomial of f2 in the function
  //          field over L(x) gives the relation (after x = 1/f1 for f1 = 1/x). Otherwise find
  //          a nontrivial L-linear relation among the f1^j*f2^i, 0 <= j <= deg(f2),
  //          0 <= i <= deg(f1) (deg the degree of the divisor of poles; the minimal polynomial
  //          has degree at most deg(f1) = [L(x,y):L(f1)] in y and at most deg(f2) in f1), after
  //          clearing denominators. In both cases the result is the irreducible factor of the
  //          relation that vanishes at (f1,f2), normalised by the factorisation.

  FF:=Parent(f1);
  Lt:=BaseRing(FF); // L(x)
  L:=BaseRing(Lt);
  Lx:=PolynomialRing(L);
  Lxy:=PolynomialRing(Lx);

  if f1 eq FF!Lt.1 or f1 eq FF!(1/Lt.1) then
    C:=Coefficients(MinimalPolynomial(f2)); // over L(x)
    if f1 ne FF!Lt.1 then
      C:=[Evaluate(c,1/Lt.1):c in C]; // over L(1/x): x = 1/f1
    end if;
    denom:=LCM([Denominator(c):c in C]);
    poly:=Lxy![Lx!Numerator(denom*c):c in C];
  else
    dy:=Degree(PoleDivisor(Divisor(f1)));
    dx:=Degree(PoleDivisor(Divisor(f2)));
    // 1, f1, ..., f1^dx, f2, f1*f2, ...: wanted w in L^((dx+1)*(dy+1)) with w*S^T = 0
    S:=[f1^j*f2^i:j in [0..dx],i in [0..dy]];
    // a common denominator of the coordinates a_k in L(x) of the S[i] = a_0 + a_1*y + ...
    denom:=LCM([Denominator(a):a in Eltseq(s),s in S]);
    maxdeg:=Maximum([0] cat [Degree(Numerator(denom*a)):a in Eltseq(s),s in S]);
    // denom*S[i] = T[i]*(1,x,...,x^maxdeg,y,x*y,...)^T
    T:=[[Coefficient(Numerator(denom*a),k):k in [0..maxdeg],a in Eltseq(s)]:s in S];
    R:=Basis(NullSpace(Matrix(T)))[1];
    poly:=&+[Lxy|R[i*(dx+1)+j+1]*Lx.1^j*Lxy.1^i:j in [0..dx],i in [0..dy]];
  end if;

  vanishing:=[fac[1]:fac in Factorisation(poly)|&+[FF|Evaluate(Coefficient(fac[1],j),f1)*f2^j:j in [0..Degree(fac[1])]] eq 0];
  return vanishing[#vanishing];

end function;


set_bad_point:=function(x,b,inf,data:check:=true)

  // A point given by x and the values of the integral basis, as a point record; needed at
  // bad points, where (x,y) need not determine the point.
  // Input:   x: x(P), or 1/x(P) if inf; b: the values of b^0 (resp. b^inf if inf) at P; x and
  //          b in L (or Q; they are mapped to K by m) or in a p-adic field (K or an extension,
  //          as produced by find_bad_point_in_disc); inf: whether P is infinite;
  //          check (optional): test that x and b are integral at P and that every b_i
  //          satisfies its minimal polynomial over L(x) (resp. L(1/x)) at x, with a warning if
  //          not; internal callers whose points are correct by construction pass false.
  // Returns: the point record, used for all points of the library:
  //            inf     true iff P lies in an infinite residue disc (x is then 1/x(P));
  //            x, b    x(P) (or 1/x(P)) and the values of b^0 (or b^inf), over K or an
  //                    extension of K;
  //            r       z(x(P)), z = r/lc(r) (finite points only);
  //            xt, bt, index (optional, filled in by local_coord or find_suitable_point_in_disc):
  //                    the expansions of x (or 1/x) and b in the integral local parameter
  //                    t at P, and the index of that parameter (0: t = x - x(P), resp.
  //                    1/x - 1/x(P); i > 0: t = b_i - b_i(P), see local_data).

  Q:=data`Q; L:=data`L; K:=data`K; m:=data`m; d:=Degree(Q);
  if Type(inf) ne BoolElt then
    error "set_bad_point: inf must be true (an infinite point, given by 1/x and b^inf) or false";
  end if;
  if #b ne d then
    error Sprintf("set_bad_point: b must contain the values of the %o functions of the integral basis b^0 (resp. b^inf)",d);
  end if;

  format:=recformat<x,b,r,inf,xt,bt,index>;
  Pt:=rec<format|inf:=inf>;
  z:=data`r/LeadingCoefficient(data`r);
  if Type(Parent(x)) eq FldPad then // x (and b) in a p-adic field
    Pt`x:=x;
    Pt`b:=b;
    if not inf then
      Pt`r:=Evaluate(PolynomialRing(Parent(x))!coer_poly(z,L,K,m),x);
    end if;
  else // x and b in L
    ok,x:=IsCoercible(L,x);
    if not (ok and &and[IsCoercible(L,c):c in b]) then
      error "set_bad_point: x and b must be elements of the number field data`L (or of Q), or of a p-adic field over K";
    end if;
    Pt`x:=m(x);
    Pt`b:=[m(L!c):c in b];
    if not inf then
      Pt`r:=m(Evaluate(z,x));
    end if;
  end if;

  if check then
    if inf and Valuation(Pt`x) le 0 then
      error "set_bad_point: for an infinite point (inf = true) x must be 1/x(P), which is divisible by P; this point is finite: use inf = false and the values of b^0";
    end if;
    if not inf and Valuation(Pt`x) lt 0 then
      error "set_bad_point: x(P) is not integral at P, so the point is infinite: use inf = true with 1/x(P) and the values of b^inf";
    end if;
    if exists{c:c in Pt`b|Valuation(c) lt 0} then
      error "set_bad_point: the values of the integral basis must be integral at P; check that b holds the values of b^0 (resp. b^inf if inf), not of 1, y, y^2, ...";
    end if;
    // every coordinate b_i must satisfy its minimal polynomial over L[x] (resp. L[1/x] if
    // inf; note that Pt`x stores 1/x(P) then), which holds at every point of the curve. This
    // catches wrongly entered bad/infinite points at full precision. (Mutual consistency of
    // the b_i, i.e. that they all belong to the same point of the fibre, is checked mod P
    // later by the place matching in local_data.)
    FF,Lt:=model_function_field(data);
    xfun:=inf select FF!(1/Lt.1) else FF!Lt.1;
    bfun:=basis_functions(FF,inf select data`Winf else data`W0);
    k:=inf select 2 else 1;
    NN:=data`N*Degree(Parent(Pt`x),K); // precision N in units of the uniformizer of Parent(Pt`x)
    for i:=1 to d do
      C:=Coefficients(cached_minpoly(data,k,1,i+1,xfun,bfun[i]));
      val:=&+[Parent(Pt`x)|eval_frac(C[j],L,K,m,Pt`x)*Pt`b[i]^(j-1):j in [1..#C]];
      if RelativePrecision(val) ne 0 and Valuation(val) lt NN then
        print "WARNING: coordinate b_(",i-1,") of the point only satisfies its minimal polynomial up to precision",Valuation(val),"of",NN,"- the point may not lie on the curve";
      end if;
    end for;
  end if;

  return Pt;

end function;



update_minpolys:=function(data,inf,index)

  // Fill the cache data`minpolys of the minimal polynomials used for the local expansions
  // (local_coord): two (d+2) x (d+2) matrices over L[x][y], minpolys[1] for finite points
  // (b = b^0, s = x) and minpolys[2] for infinite points (b = b^inf, s = 1/x). Row 1 holds in
  // column i+1 the minimal polynomial of b_(i-1) over L(s); for index >= 1, row index+1 holds
  // in column 1 the minimal polynomial of s over L(b_(index-1)) and in column i+1 that of
  // b_(i-1) over L(b_(index-1)) -- for the local parameter b_(index-1) - b_(index-1)(P) (cf.
  // local_data). Zero entries are not computed yet.
  // Input:   data; inf: which of the two matrices; index: which row (0 for the local
  //          parameter s - s(P)).
  // Returns: data with the entries of that row filled in (immediately if they are cached).

  d:=Degree(data`Q);
  Lxy:=PolynomialRing(PolynomialRing(data`L));
  if not assigned data`minpolys then
    data`minpolys:=[ZeroMatrix(Lxy,d+2,d+2),ZeroMatrix(Lxy,d+2,d+2)];
  end if;
  minpolys:=data`minpolys;
  k:=inf select 2 else 1;

  // Fast exit: if the minpolys needed for this (inf,index) are already cached, skip the
  // (expensive) function-field and minimal-polynomial construction below. After coleman_data
  // warms the index=0 rows this makes update_minpolys a no-op on the common good-point path.
  if &and[minpolys[k][index+1,i+1] ne 0:i in [1..d]] and (index eq 0 or minpolys[k][index+1,1] ne 0) then
    return data;
  end if;

  FF,Lt:=model_function_field(data);
  sfun:=inf select FF!(1/Lt.1) else FF!Lt.1;               // s = 1/x (infinite) or x (finite)
  bfun:=basis_functions(FF,inf select data`Winf else data`W0); // b^inf or b^0 as functions
  // the parameter of the row: s for index = 0, b_(index-1) otherwise
  par:=(index eq 0) select sfun else bfun[index];
  if index gt 0 and minpolys[k][index+1,1] eq 0 then
    minpolys[k][index+1,1]:=minpoly(par,sfun);
  end if;
  for i:=1 to d do
    if minpolys[k][index+1,i+1] eq 0 then
      minpolys[k][index+1,i+1]:=minpoly(par,bfun[i]);
    end if;
  end for;
  data`minpolys:=minpolys;
  return data;

end function;


frobenius_pt_inf:=function(Pt,Pinf,data)

  // The image F_q(Pt) of a point Pt of an infinite residue disc under the q-power Frobenius
  // lift, computed in the integral local parameter t at the very infinite point Pinf of the
  // disc (article: the algorithm "q-power Frobenius of a point and correction values", at
  // infinity). F_q^*(t) = t^q*U(t) with U = 1 mod pi, so T = t(F_q(Pt)) is the root of
  // 1/x(T) = (1/x(Pt))^q with v_K(T - t(Pt)^q) > q*v_K(t(Pt)), and b^inf(F_q(Pt)) = b^inf(T).
  // Unlike the congruence b(F_q(Pt)) = b(Pt)^q mod pi used in frobenius_pt, this determines
  // the branch at every depth of the disc.
  // Input:   Pt an infinite point, not very infinite, over K or a totally ramified extension
  //          K(pi^(1/e)); Pinf the very infinite point of its disc, with the expansions
  //          Pinf`xt, Pinf`bt, Pinf`index of 1/x and b^inf in t (local_coord), to a t-adic
  //          precision prec with prec*q*v_K(t(Pt)) at least the precision of K.
  // Requires: p does not divide the ramification index of x at Pinf (then the root is
  //          unique); the callers check this.
  // Returns: the point record of F_q(Pt) (without expansions).

  K:=data`K; d:=Degree(data`Q); q:=#ResidueClassField(data`P);
  Ke:=Parent(Pt`x); e:=Degree(Ke,K); NK:=Precision(K);

  if not Pt`inf then
    error "frobenius_pt_inf: the point is not infinite";
  end if;
  index:=Pinf`index;
  if index eq 0 then
    t0:=Pt`x-Ke!Pinf`x; // the local parameter is 1/x (Pt`x stores 1/x(Pt))
  else
    t0:=Pt`b[index]-Ke!Pinf`b[index];
  end if;
  if IsWeaklyZero(t0) then
    error "frobenius_pt_inf: the point is very infinite";
  end if;
  if Valuation(t0) le 0 then
    error "frobenius_pt_inf: the point does not lie in the residue disc of Pinf";
  end if;

  ut:=Pinf`xt; dut:=Derivative(ut); // 1/x as a power series in t, and its derivative
  c:=Pt`x^q;                        // 1/x(F_q(Pt))
  T0:=t0^q;
  T:=T0;
  for k:=1 to Ceiling(Log(2,e*NK+2))+2 do // Newton's method; the relative error squares
    T:=T-(eval_series_Ke(ut,T,K)-c)/eval_series_Ke(dut,T,K);
  end for;
  if Valuation(T-T0) le q*Valuation(t0) then
    error "frobenius_pt_inf: Newton's method did not find the root T = t^q (mod pi*t^q)";
  end if;

  FPt:=Pt;
  FPt`x:=c;
  FPt`b:=[eval_series_Ke(Pinf`bt[i],T,K):i in [1..d]];
  delete FPt`xt;
  delete FPt`bt;
  delete FPt`index;

  return FPt;

end function;


frobenius_pt:=function(Pt,data:qtau:=0,msrc:=0,mtgt:=0,center:=0)

  // The image of Pt under one step G_k of the Frobenius lift, P_(k+1) = G_k(P_k) (article: the
  // algorithm "q-power Frobenius of a point and correction values"; for the q-power lift
  // this is F_q(Pt)): x -> x^(q_tau), and the values of b are the roots of their minimal
  // polynomials (resp. of the target curve at a good point, by Hensel's lemma) at the new x
  // that are congruent to b(Pt)^(q_tau).
  // Input:   Pt a suitable point (good; finitely bad with v_K(z(x(Pt))) < 1/q; or infinite
  //          and not very infinite) over K or a totally ramified extension of K; data;
  //          qtau (optional): the exponent of the step (default q; p for one step of the
  //          p-power lift); msrc, mtgt (optional): the twisted coefficient maps m*tau^k and
  //          m*tau^(k+1) of the source and the target curve X_k, X_(k+1) of the step (default
  //          data`m for both, the q-power case); center (optional, q-power lift only): the
  //          very infinite point of the disc of an infinite Pt, with its expansions
  //          (local_coord), used by frobenius_pt_inf if the congruence modulo pi leaves
  //          several roots.
  // Returns: the point record of the image (without expansions).
  // Errors:  if no root is congruent to b(Pt)^(q_tau).

  x0:=Pt`x; Q:=data`Q; P:=data`P; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); L:=data`L; K:=data`K; m:=data`m;
  q:=#ResidueClassField(P);
  if qtau eq 0 then
    qtau:=q;
  end if;
  if Type(msrc) eq RngIntElt then
    msrc:=m;
  end if;
  if Type(mtgt) eq RngIntElt then
    mtgt:=m;
  end if;

  Ke:=Parent(x0); Key:=PolynomialRing(Ke); e:=Degree(Ke,K);
  x0q:=x0^qtau;
  b:=Pt`b;

  // the roots, at the new x (resp. 1/x), of the twist to the target curve of the minimal
  // polynomial C_0(s) + C_1(s)*b + ... of a basis function b over L(s); Roots returns the roots
  // with the precision they actually have
  target_roots:=func<poly|Roots(Key![eval_frac(c,L,K,mtgt,x0q):c in Coefficients(poly)])>;
  if is_bad(Pt,data) then // the function field is only needed in the infinite/bad branches below
    FF,Lt:=model_function_field(data);
  end if;

  if not is_bad(Pt,data) then // finite good point

    y0:=(Vector(b)*Transpose(eval_mat(W0^(-1),L,K,msrc,x0)))[2]; // in Ke; source-level basis change to read off y0
    // the target curve X_(k+1): Q^(tau^(k+1))(x0^q_tau, Y), and its root congruent to y0^q_tau
    fy:=Key![Evaluate(coer_poly(c,L,K,mtgt),x0q):c in Coefficients(Q)];
    y0q:=HenselLift(fy,y0^qtau);
    // the b^0-values of the image point: W0^(tau^(k+1)) at x0^q_tau
    b:=Eltseq(Vector(Ke,[pow_K(y0q,i):i in [0..d-1]])*Transpose(eval_mat(W0,L,K,mtgt,x0q)));

  elif Pt`inf then // infinite point

    bfun:=basis_functions(FF,Winf);
    for i:=1 to d do
      roots:=target_roots(cached_minpoly(data,2,1,i+1,FF!(1/Lt.1),bfun[i])); // b^inf_i over L(1/x)

      // The image satisfies b_i(F(P)) = b_i(P)^q mod pi on the whole infinite disc
      // (since F_q^*(t)=t^q*U(t) with U=1 mod pi), so v_K(root-b_i(P)^q) >= 1, with equality if
      // b_i(P_inf)^q-b_i(P_inf) has valuation 1. Near
      // the boundary of the disc no other root passes; deeper in a ramified disc, or if b_i
      // does not separate the points at infinity, several can, and then the local parameter
      // at the very infinite point decides (frobenius_pt_inf).
      vals:=[Valuation(rt[1]-b[i]^qtau):rt in roots];
      cand:=[j:j in [1..#roots]|vals[j] ge e];
      if #cand ne 1 then
        if Type(center) eq Rec and qtau eq q then
          return frobenius_pt_inf(Pt,center,data);
        end if;
        if #cand eq 0 then
          error "frobenius_pt: no root of the minimal polynomial of a basis function at the image of an infinite point is congruent to its value at the point; the point is not suitable or the precision is too low";
        end if;
        print "NOTE: frobenius_pt: the congruence mod pi leaves",#cand,"roots for b_(",i-1,") of the image of an infinite point; taking the closest one";
      end if;
      _,jbest:=Maximum([vals[j]:j in cand]);
      b[i]:=roots[cand[jbest]][1];
    end for;

  else // finite bad point

    bfun:=basis_functions(FF,W0);
    for i:=1 to d do
      roots:=target_roots(cached_minpoly(data,1,1,i+1,FF!Lt.1,bfun[i])); // b^0_i over L(x)
      // The roots of the other points of the fibre in the disc differ from b_i(P)^q at
      // v_K about q/e if b_i is a local parameter; a coordinate that is no local parameter
      // can leave several roots beyond this threshold (e.g. in Example 8.3), so take the
      // closest one.
      vals:=[Valuation(rt[1]-b[i]^qtau):rt in roots];
      cand:=[j:j in [1..#roots]|vals[j] gt qtau];
      if #cand eq 0 then
        error "frobenius_pt: no root of the minimal polynomial of a basis function at the image point is congruent to its value at the point to the power q; the point is too close to the very bad point of its disc (increase e) or the precision is too low";
      end if;
      _,jbest:=Maximum([vals[j]:j in cand]);
      b[i]:=roots[cand[jbest]][1];
    end for;

  end if;

  Pt`x:=x0q;
  Pt`b:=b;
  rKe:=Key!coer_poly(data`r/LeadingCoefficient(data`r),L,K,mtgt); // z of the target curve
  Pt`r:=Evaluate(rKe,Pt`x);
  delete Pt`xt;
  delete Pt`bt;
  delete Pt`index;

  return Pt;
end function;


teichmueller_pt:=function(Pt,data)

  // The Teichmueller point of the residue disc of a good point Pt: the point T of the disc
  // whose x-coordinate is the Teichmueller representative of x(Pt) mod pi, i.e. the root of
  // X^q = X congruent to x(Pt), q = #k(P). (Not used by the library.)
  // Input:   Pt a good point over K (then x - x(Pt) is a local parameter on its disc); data.
  // Returns: the point record of T (without expansions).
  // Method:  x(T) is the Newton lift of x(Pt) as a root of X^q - X, whose derivative
  //          q*X^(q-1) - 1 is a unit; y(T) is the Hensel lift of y(Pt) as a root of Q(x(T),Y),
  //          whose derivative is a unit at a good point; b(T) = W0(x(T))*(1,y,...,y^(d-1)).
  //          This works for every K (unramified or not).

  if Pt`inf or is_bad(Pt,data) then
    error "teichmueller_pt: the point must be good (the Teichmueller point is defined here only in good residue discs)";
  end if;
  K:=data`K; L:=data`L; m:=data`m; NK:=Precision(K); d:=Degree(data`Q);
  q:=#ResidueClassField(data`P);
  x0:=K!Pt`x;

  // x(T): Newton's method for X^q - X, to the full precision of K
  xT:=ChangePrecision(x0,NK);
  repeat
    step:=(xT^q-xT)/(q*xT^(q-1)-1);
    xT:=xT-step;
  until IsWeaklyZero(step);

  // y(T): the root of Q(x(T),Y) congruent to y(Pt) = (W0(x(Pt))^(-1)*b(Pt))_2
  y0:=(Vector(K,Pt`b)*Transpose(eval_mat(data`W0^(-1),L,K,m,x0)))[2];
  fy:=PolynomialRing(K)![eval_frac(c,L,K,m,xT):c in Coefficients(data`Q)];
  yT:=HenselLift(fy,ChangePrecision(y0,NK));
  bT:=Eltseq(Vector(K,[pow_K(yT,i):i in [0..d-1]])*Transpose(eval_mat(data`W0,L,K,m,xT)));

  return set_bad_point(xT,bT,false,data:check:=false);

end function;


local_data:=function(Pt,data)

  // The local data at a point Pt over K for the expansions: the ramification index of the
  // reduced map x at the reduction of Pt, and the choice of the integral local parameter
  // (article: the proposition on the uniformizer at a point).
  // Input:   Pt a point over K; data.
  // Returns: eP, index for a good point (eP = 1, index = 0: t = x - x(Pt)); and for a bad
  //          point eP, index, place, bmodP: eP = e_P~ the ramification index of x mod P at the
  //          reduction of Pt (= e_P at a very bad point); index = 0 if eP = 1 (t = x - x(Pt),
  //          resp. 1/x - 1/x(Pt) at an infinite point), otherwise the smallest i such that
  //          b_(i-1) - b_(i-1)(Pt) is a uniformizer at the reduction; place: the place of the
  //          reduced function field at the reduction of Pt; bmodP: the reduced basis
  //          functions b mod P (b = b^0, resp. b^inf).
  // Errors:  if no place above x(Pt) mod P has the reduced b-values of Pt.


  if not is_bad(Pt,data) then
    return 1,0;
  end if;

  d:=Degree(data`Q);
  FFq,mm,Fqx,red_ratfun:=reduced_function_field(data); // the function field of the curve mod P
  if Pt`inf then
    places:=InfinitePlaces(FFq);
    W:=data`Winf;
  else
    places:=Decomposition(FFq,Zeros(Fqx.1-Parent(Fqx.1)!mm(Pt`x))[1]); // the places above x(Pt) mod P
    W:=data`W0;
  end if;
  // the reduction of b, where b is b^0 or b^inf
  bmodP:=[&+[FFq|red_ratfun(W[i,j])*FFq.1^(j-1):j in [1..d]]:i in [1..d]];

  // the place with the reduced b-values of Pt (both sides lie in the residue field of O_K)
  matching:=[pl:pl in places|forall{j:j in [1..d]|Evaluate(bmodP[j],pl) eq mm(Pt`b[j])}];
  if #matching eq 0 then
    error "local_data: the point does not lie on the curve: no point of the reduction has its values of x and b mod P (check the values of the integral basis given to set_bad_point)";
  end if;
  place:=matching[#matching];

  eP:=RamificationIndex(place);
  index:=0;
  if eP gt 1 then
    uniformizers:=[i:i in [1..d]|Valuation(bmodP[i]-Evaluate(bmodP[i],place),place) eq 1];
    if #uniformizers eq 0 then
      error "local_data: no basis function b_i - b_i(P) is a uniformizer at the reduction of the point (the integral basis does not satisfy the good-reduction assumptions at P)";
    end if;
    index:=uniformizers[1];
  end if;
  return eP,index,place,bmodP;

end function;




expansion_at_point:=function(poly,c,y0,hmodP,place,tmodP,Kt,Sq,OK,L,K,m:approx:=0)

  // The expansion h(t) in Kt = K[[t]] of a function h at a (very) bad point P in the integral
  // local parameter t = s - c at P, where s is x, 1/x or a basis function b_index and c = s(P)
  // (article: the proposition on the uniformizer at a point and the algorithm "Expansion of a
  // function in an integral local parameter").
  // Input:   poly the minimal polynomial of h over L(s) (from data`minpolys); c = s(P);
  //          y0 = h(P); hmodP the reduction of h; place the place of the reduced curve at the
  //          reduction of P; tmodP the reduction of t; Kt the power series ring (its precision
  //          is the t-adic precision prec); Sq the Laurent series ring over O_K/pi^NK of the
  //          same precision; OK, L, K, m; approx (optional): an expansion of h at P in the
  //          same local parameter computed before.
  // Returns: h(t) in Kt.
  // Method:  the branch of poly through P is selected by the expansion of hmodP in tmodP
  //          (approx_root), or by approx if its precision suffices, and then Hensel lifted.
  // If h does not separate the points of the fibre of s through P, i.e. h(P) is a multiple
  // root of poly(c,z) (e.g. two points at infinity with the same value of a b_i^infinity, or
  // further zeros of the local parameter where h=h(P)), then the derivative of poly(c+t,z) at
  // the branch has t-adic valuation v2>0, and the Newton iteration determines h(t) only mod
  // t^(prec-v2) from poly(c+t,z) mod t^prec (cf. hensel_lift); poly(c+t,z) is then evaluated
  // to v2 more terms, so that h(t) is still correct to the t-adic precision prec.

  prec:=Precision(Kt);
  C:=Coefficients(poly);
  fy:=PolynomialRing(Kt)![eval_frac_shift(C[j],L,K,m,c,Kt,Sq,OK):j in [1..#C]]; // poly(c+t,z), evaluated via Taylor shifts

  modPprec:=mod_P_prec(fy,L,K,m);

  if Type(approx) ne RngIntElt and Precision(Parent(approx)) ge modPprec then
    approxroot:=approx;
  else
    expamodP:=mod_P_expansion(hmodP,place,tmodP,modPprec);
    approxroot:=approx_root(fy,y0,L,K,m,modPprec,expamodP);
  end if;

  derroot:=Evaluate(Derivative(fy),approxroot);
  if not IsWeaklyZero(derroot) and WeakValuation(derroot) gt 0 then // (a vanishing derivative is reported by hensel_lift)
    v2:=WeakValuation(derroot);
    Ktv:=PowerSeriesRing(K,prec+v2);
    Sqv:=LaurentSeriesRing(CoefficientRing(Sq),prec+v2);
    fy:=PolynomialRing(Ktv)![eval_frac_shift(C[j],L,K,m,c,Ktv,Sqv,OK):j in [1..#C]];
  end if;

  return Kt!hensel_lift(fy,approxroot,L,K,m);

end function;


local_coord:=function(Pt,prec,data:index:=-1)

  // The expansions of x and b^0 (resp. 1/x and b^inf if Pt is infinite) at Pt in the integral
  // local parameter t chosen by local_data (article: the algorithm "Expansion of a function in
  // an integral local parameter", applied in the algorithm "Tiny integrals").
  // Input:   Pt a good or very bad point over K (or, if good, over an unramified extension of
  //          K); prec the t-adic precision; data; index (optional, >= 0): force the integral
  //          local parameter b_index - b_index(P) (index = 0: x - x(P), resp. 1/x, which
  //          needs e_P = 1), provided that its reduction is a uniformizer at the reduction of
  //          P; for consistency checks, since the expansions are then computed from
  //          different minimal polynomials.
  // Returns: xt, bt, index: xt in K[[t]] the expansion of x (resp. 1/x), bt the list of
  //          those of the b_i, and the index of the local parameter (see local_data). If Pt
  //          carries expansions of at least this precision (in the same parameter), they are
  //          returned.
  // Method:  at a good point t = x - x(P), y(t) is the Hensel lift of y(P) in Q(x(t),y) = 0,
  //          and b(t) = W0(x(t))*(1,y(t),...)^T. At a very bad point each of the functions u
  //          (x or 1/x) and b_i is expanded from its own minimal polynomial (expansion_at_point);
  //          the parameter is u - u(P) if e_P = 1 and b_index - b_index(P) if e_P >= 2.
  // Errors:  at a bad point that is not very bad (use find_bad_point_in_disc first).

  forced:=index;
  if assigned Pt`xt and Precision(Parent(Pt`xt)) ge prec and (forced lt 0 or Pt`index eq forced) then
    xt:=Pt`xt;
    bt:=Pt`bt;
    index:=Pt`index;
    return xt,bt,index;
  end if;

  if is_bad(Pt,data) and not is_very_bad(Pt,data) then
    error "local_coord: the point is bad but not very bad; expansions are computed at good points and at the very bad point of a bad disc (find_bad_point_in_disc)";
  end if;

  if forced gt 0 and not is_bad(Pt,data) then
    error "local_coord: at a good point the local parameter is x-x(P); a basis function cannot be forced";
  end if;

  x0:=Pt`x; Q:=data`Q; W0:=data`W0; Winf:=data`Winf; d:=Degree(Q); b:=Pt`b; m:=data`m;
  L:=data`L; K:=data`K;
  // Allow endpoints over an unramified extension Ke of K (e.g. a Frobenius-conjugate
  // disc centre over Q_{q^2}). The whole good-point branch is built over the field where
  // the point lives; Ke=K (the usual case) leaves everything unchanged. The coefficient
  // map L->K is post-composed with K->Ke. (Only the good finite branch supports Ke>K.)
  if AbsoluteDegree(Parent(x0)) gt AbsoluteDegree(K) then
    mK:=m; K:=Parent(x0); m:=map< L -> K | a :-> K!mK(a) >;
  end if;
  NK:=Precision(K); Kt<t>:=PowerSeriesRing(K,prec); Kty:=PolynomialRing(Kt);
  OK:=RingOfIntegers(K);
  Sq:=LaurentSeriesRing(quo<OK|UniformizingElement(K)^NK>,prec); // for the fast series divisions in eval_frac_shift
  Fq:=ResidueClassField(Integers(K));
  FF,Lt:=model_function_field(data);

  if not is_bad(Pt,data) then // finite good point

    xt:=t+Parent(t)!x0; // the local parameter is t = x - x(P)
    y0:=(Vector(b)*Transpose(eval_mat(W0^(-1),L,K,m,x0)))[2];
    fy:=Kty![Evaluate(coer_poly(c,L,K,m),xt):c in Coefficients(Q)]; // Q(x(t),y)
    yt:=hensel_lift(fy,Kt!y0,L,K,m);

    // b_i = sum_j W0[i,j]*y^(j-1), as in set_point, computed in the fraction field of Kt
    FracKt:=FieldOfFractions(Kt);
    ypowerst:=[FracKt!1,yt];
    for i:=3 to d do
      Append(~ypowerst,ypowerst[i-1]*yt);
    end for;
    W0xt:=Matrix(FracKt,NumberOfRows(W0),NumberOfColumns(W0),[eval_frac(a,L,K,m,FracKt!xt):a in Eltseq(W0)]);
    bt:=[Kt!c:c in Eltseq(Vector(ypowerst[1..d])*Transpose(W0xt))];

    index:=0;

  else // (very) bad point: expansions of u=x (resp. u=1/x if Pt is infinite; then x0=1/x(P)) and of the integral basis b=b^0 (resp. b=b^infinity)

    eP,index,place,bmodP:=local_data(Pt,data);
    FFq:=Parent(bmodP[1]); // Fq(X)
    Fqx:=BaseRing(FFq);  // Fq(x)

    if forced ge 0 then // the forced local parameter must be an integral local parameter (cf. local_data)
      if (forced eq 0 and eP ne 1) or (forced gt 0 and Valuation(bmodP[forced]-Evaluate(bmodP[forced],place),place) ne 1) then
        error "local_coord: the forced local parameter is not an integral local parameter at this point";
      end if;
      index:=forced;
    end if;
    if assigned Pt`index and Pt`index ne index then // expansions in another local parameter are no approximate roots
      if assigned Pt`xt then
        delete Pt`xt;
      end if;
      if assigned Pt`bt then
        delete Pt`bt;
      end if;
    end if;

    if Pt`inf then
      W:=Winf; k:=2; ufun:=FF!(1/Lt.1); umodP:=1/Fqx.1;
    else
      W:=W0; k:=1; ufun:=FF!Lt.1; umodP:=Fqx.1;
    end if;

    bfun:=basis_functions(FF,W); // the basis b in L(X)

    // Each of the functions u and b_i is expanded from its minimal polynomial over L(s), where
    // t=s-s(P), on the branch through P selected by the expansion of the reduction of the
    // function (expansion_at_point). This does not use the plane model, which may be singular at
    // P or, if P is infinite, not contain P: the b_i together separate the points of the fibre
    // (they are an integral basis), even if a single b_i does not.

    if index eq 0 then // e_P=1: the local parameter is t=u-u(P)

      xt:=t+x0; // in K[[t]]
      tmodP:=umodP-Fq!x0;
      bt:=[expansion_at_point(cached_minpoly(data,k,1,i+1,ufun,bfun[i]),x0,b[i],bmodP[i],place,tmodP,Kt,Sq,OK,L,K,m
                              :approx:=(assigned Pt`bt) select Pt`bt[i] else 0):i in [1..d]];

    else // e_P>=2 (or a forced index): the local parameter is t=b_index-b_index(P)

      tmodP:=bmodP[index]-Fq!b[index];
      xt:=expansion_at_point(cached_minpoly(data,k,index+1,1,bfun[index],ufun),b[index],x0,FFq!umodP,place,tmodP,Kt,Sq,OK,L,K,m
                             :approx:=(assigned Pt`xt) select Pt`xt else 0);
      bt:=[(i eq index) select t+b[i]
           else expansion_at_point(cached_minpoly(data,k,index+1,i+1,bfun[index],bfun[i]),b[index],b[i],bmodP[i],place,tmodP,Kt,Sq,OK,L,K,m
                                   :approx:=(assigned Pt`bt) select Pt`bt[i] else 0):i in [1..d]];

    end if;

  end if;

  return xt,bt,index;

end function;


point_to_K:=function(Pt,K)

  // The point record Pt with its coordinates coerced from a different-precision copy of K
  // (e.g. produced by Qq_points in the solver, which works at increased precision) into K
  // itself; points over genuine extensions K(pi^(1/e)) are left untouched. Mixing copies of K
  // would make the vector arithmetic combining tiny integrals fail with "Arguments are not
  // compatible".

  if (Parent(Pt`x) cmpne K) and IsCoercible(K,Pt`x) and &and[IsCoercible(K,c):c in Pt`b] then
    Pt`x:=K!Pt`x;
    Pt`b:=[K!c:c in Pt`b];
    if assigned Pt`r and IsCoercible(K,Pt`r) then
      Pt`r:=K!Pt`r;
    end if;
  end if;
  return Pt;
end function;


tiny_integral_prec:=function(prec,e,maxpoleorder,maxdegree,mindegree,val,NPP,data)

  // The precision (in units of v_K) to which the tiny integrals computed by
  // tiny_integrals_on_basis are correct (article: the proposition on the precision of tiny
  // integrals, with the bounds nu_1, nu_2, nu_3 for the omitted tail, the terms of positive
  // order and the terms of negative order). The computation is in units of v_Ke = e*v_K.
  // Input:   prec (not used); e: the far endpoint lies in K(pi^(1/e)); maxpoleorder: the
  //          maximal pole order k of the integrands at the expansion point; maxdegree,
  //          mindegree: the maximal and minimal degree of the integrand series (the last
  //          known term; the truncation index l of the proposition is mindegree+1);
  //          val = v_Ke(t(P2)) >= 1, the valuation of the local parameter at the far endpoint;
  //          NPP <= NK, the precision of the local parameter at the endpoints; data.
  // Returns: min(m1, m2, m3)/e, where m1 = e*nu_1, and m2, m3 are e*nu_2 and the bound for
  //          the negative-order terms lowered further: both contain an additional -val, and
  //          m2 uses i instead of i*val (val >= 1). Both changes only lower the bound.

  eK:=data`eK; p:=data`p;
  NtP:=Minimum(NPP,data`Nmax); // the precision N of the proposition: that of the local parameter, at most Nmax (that of the coefficients)

  // the omitted tail (nu_1): the omitted term t^(i+1)/(i+1) has valuation
  // >= (i+1)*val - e*eK*log_p(i+1) (worst case val = 1, i.e. v_K(t(P2)) = 1/e)

  // (x*val - e*eK*log_p(x) is minimal at x = e*eK/(val*ln(p)) and increases beyond)
  imax:=Maximum(mindegree+1,Ceiling(e*eK/(val*Log(p))));
  m1:=Minimum([(i+1)*val-e*eK*Ilog(p,i+1):i in [mindegree+1..imax]]);

  // the computed terms of positive order (nu_2, lowered: see above)

  m2:=Minimum([NtP*e-val] cat [NtP*e+i-e*eK*Ilog(p,i+1):i in [1..maxdegree]]);

  // the terms of negative order (nu_3 with v_K(t(P2)) in place of the maximum, lowered by -val)

  m3:=NtP*e-val;
  if maxpoleorder ge 2 then
    m3:=NtP*e-val-maxpoleorder*val-e*eK*Ilog(p,maxpoleorder-1);
  end if;

  m:=Minimum([m1,m2,m3]);

  return m/e;

end function;


find_bad_point_in_disc:=function(Pt,data)

  // The very bad point of the residue disc of a bad point Pt (it is unique and defined over
  // K: the remark on the unique very bad point in a bad residue disc).
  // Input:   Pt a bad point over K; data.
  // Returns: the point record of the very bad point: x = the root of r congruent to x(Pt)
  //          (Hensel lift), resp. 1/x = 0 for an infinite disc; the b-values are the roots of
  //          the minimal polynomials of the b_i over L(x) (resp. over L(b_index) if the local
  //          parameter is b_index - b_index(P), see local_data) that are congruent to the
  //          b-values of Pt modulo pi.
  // Errors:  if no such root exists (increase N).

  b:=Pt`b; d:=Degree(data`Q); L:=data`L; K:=data`K; m:=data`m; Ky:=PolynomialRing(K);
  if not is_bad(Pt,data) then
    error "find_bad_point_in_disc: the residue disc of the point is good, it contains no bad point";
  end if;

  if Pt`inf then
    x0:=K!0;
  else
    x0:=HenselLift(Ky!coer_poly(data`r,L,K,m),Pt`x); // the zero of r in the disc (r mod P is separable)
  end if;

  FF,Lt:=model_function_field(data);
  _,index:=local_data(Pt,data);
  k:=Pt`inf select 2 else 1;
  bfun:=basis_functions(FF,Pt`inf select data`Winf else data`W0);
  xfun:=Pt`inf select FF!(1/Lt.1) else FF!(Lt.1);

  // the first root of poly(s0,Y) congruent to c modulo pi (poly the minimal polynomial of a
  // basis function over L(s), s0 in K)
  root_near:=function(poly,s0,c)
    roots:=[rt[1]:rt in Roots(Ky![eval_frac(a,L,K,m,s0):a in Coefficients(poly)])|Valuation(rt[1]-c) gt 0];
    if #roots eq 0 then
      error "find_bad_point_in_disc: no root of the minimal polynomial of a basis function reduces into the residue disc of the point (increase N)";
    end if;
    return roots[1];
  end function;

  if index eq 0 then // x - x0 (resp. 1/x) is the local parameter
    for i:=1 to d do
      b[i]:=root_near(cached_minpoly(data,k,1,i+1,xfun,bfun[i]),x0,b[i]);
    end for;
  else // b_index - b_index(P) is the local parameter: the other b_i over L(b_index), not over
       // L(x), since b_index separates the points of the disc and x(P), b(P) have the same precision
    b[index]:=root_near(cached_minpoly(data,k,1,index+1,xfun,bfun[index]),x0,b[index]);
    for i in [i:i in [1..d]|i ne index] do
      b[i]:=root_near(cached_minpoly(data,k,index+1,i+1,bfun[index],bfun[i]),b[index],b[i]);
    end for;
  end if;

  return set_bad_point(x0,b,Pt`inf,data); // x0 and b are in K

end function;


tadicprec:=function(data,e:vmin:=0)

  // The t-adic precision l of the series in the tiny integrals (article: the remark after
  // the proposition on the precision of tiny integrals; the article cites this function).
  // Input:   data; e: the far endpoint lies in K(pi^(1/e)); vmin (optional): v_K of the
  //          local parameter at the far endpoint (default 1/e, the worst case; the actual
  //          value, if known, gives shorter series).
  // Returns: the least l >= 100 with floor((1+l)*vmin) - e_K*floor(log_p(l+1)) >= Nmax: the
  //          omitted terms have valuation at least Nmax (not the optimal l; larger e needs
  //          larger l).

  eK:=data`eK; Nmax:=data`Nmax;
  p:=data`p;

  if vmin eq 0 then
    vmin:=1/e;
  end if;

  prec:=1;
  while Floor((1+prec)*vmin)-eK*Ilog(p,prec+1) lt Nmax do // Nmax is the precision of K
    prec+:=1;
  end while;
  return Maximum(prec,100); // at least 100 (an arbitrary bound against problems with short series)

end function;

find_suitable_point_in_disc:=function(Pt,data,Ke)

  // A suitable bad point S close to the boundary of the residue disc of a very bad point Pt
  // (article: the algorithm "Find a suitable bad point close to the boundary", step (3)): S is
  // the point of the disc with t(S) = u = pi^(1/e), the uniformizer of Ke = K(pi^(1/e)), for the
  // integral local parameter t at Pt; S is suitable bad if e > q*e_P (lemma on the criterion
  // for suitable bad points; checked by the caller, coleman_integrals_on_basis).
  // Input:   Pt a very bad or a good point over K; data; Ke = K(pi^(1/e)) (not used for a
  //          good point).
  // Returns: Pt with its expansions xt, bt, index attached (to the t-adic precision
  //          tadicprec(data,e), resp. tadicprec(data,1) at a good point), and S (S = Pt at a
  //          good point).

  Q:=data`Q; d:=Degree(Q); K:=data`K; e:=Degree(Ke,K); L:=data`L; m:=data`m;
  u:=UniformizingElement(Ke);
  
  if is_bad(Pt,data) then
    xt,bt,index:=local_coord(Pt,tadicprec(data,e),data); // (reuses expansions stored in Pt)
    Pt`xt:=xt;       
    Pt`bt:=bt;       
    Pt`index:=index; 
    // the point with t = u; evaluation at the uniformizer costs only O(length) K-operations
    format:=recformat<x,b,r,inf,xt,bt,index>;
    S:=rec<format|inf:=Pt`inf,x:=eval_series_Ke(xt,u,K),b:=[eval_series_Ke(bt[i],u,K):i in [1..d]]>;
    S`r:=Evaluate(PolynomialRing(Ke)!coer_poly(data`r/LeadingCoefficient(data`r),L,K,m),S`x);
  else
    xt,bt,index:=local_coord(Pt,tadicprec(data,1),data);
    Pt`xt:=xt;       
    Pt`bt:=bt;       
    Pt`index:=index; 
    S:=Pt;
  end if;
  
  return Pt, S;
  
end function;


log_iwasawa:=function(t)

  // The p-adic logarithm of t != 0 in a finite extension F of Q_p, on Iwasawa's branch
  // log(p) = 0: with w the uniformizer of F, e = v_w(p) and t = w^v*u (u a unit),
  // log(t) = (v/e)*log(w^e/p) + log(u), w^e/p and u being units (Log).

  F:=Parent(t);
  p:=Prime(F);
  w:=UniformizingElement(F);
  e:=Valuation(F!p);
  v:=Valuation(t);
  return (v/e)*Log(w^e/p)+Log(t/w^v);

end function;


integrand_series:=function(P1,xt,bt,data,St,OK)

  // The integrands omega_i/dt of the basis forms in the integral local parameter t at a
  // centre P1 over K (good or very bad), as Laurent series over Oq = O_K/pi^NK (the
  // coefficient ring of St), from the expansions xt, bt of x (resp. 1/x) and b at P1
  // (local_coord): omega_i/dt = (sum_j w_j(x(t))*b^0_j(t))*x'(t)/z(x(t)), without their
  // t^(-1) terms, and as second value these residues res_i at P1 (in K). Forms of the second
  // kind have none; a form of the third kind (e.g. of the basis of H^1_dR(U), option useU of
  // coleman_data) can have one at a centre that is a point of X - U, and its primitive has
  // the logarithmic term res_i*log(t) (tiny_integrals_on_basis).
  //
  // All series multiplications and inversions are carried out over the exact quotient ring
  // Oq, where Magma uses fast polynomial multiplication: over the inexact field K (or, worse,
  // over the number field L) series arithmetic is quadratic in the length with large
  // constants -- a single multiplication of length ~4000 over L can take minutes. The
  // expansions and the model data r, basis, W are integral, so nothing is lost modulo pi^NK.

  d:=Degree(data`Q); L:=data`L; K:=data`K; m:=data`m; r:=data`r; lc_r:=LeadingCoefficient(r);
  Oq:=CoefficientRing(St); tq:=St.1;
  xtS:=series_K_to_Oq(xt,St,OK);
  btS:=[series_K_to_Oq(bt[i],St,OK):i in [1..d]];

  if P1`inf then
    xtS:=series_inverse(xtS); // the expansion of x = 1/(1/x); invertible over St since the leading coefficient is a unit (t reduces to a uniformizer)
    Winv:=data`W0*data`Winf^(-1);
    btS:=[&+[btS[j]*fracL_eval_Oq(Winv[i,j],m,OK,xtS):j in [1..d]]:i in [1..d]]; // the values of b^0 = W0*Winf^(-1)*b^inf
  end if;

  if P1`inf or not is_bad(P1,data) then // P1 infinite or good: z(x(t)) is invertible
    denomS:=series_inverse(polL_eval_Oq(PolynomialRing(L)!(r/lc_r),m,OK,xtS)); // 1/z(x(t))
  else // P1 finitely (very) bad: z(x(t)) has a zero at t = 0
    Kx:=PolynomialRing(K);
    rK:=Kx!coer_poly(r/lc_r,L,K,m);
    zero:=HenselLift(rK,P1`x);
    Cs:=Coefficients(rK div (Kx.1-zero)); // z = s*(x - x(P1))
    sS:=St!0;
    for j:=#Cs to 1 by -1 do
      sS:=sS*xtS+(Oq!OK!Cs[j]);
    end for;
    denomS:=series_inverse((xtS-(Oq!OK!zero))*sS); // 1/z(x(t)) = 1/((x(t)-x(P1))*s(x(t))); x(t)-x(P1) has a unit leading coefficient
  end if;

  derxtS:=Derivative(xtS);
  diffsS:=[]; residues:=[K|];
  for i:=1 to #data`basis do
    di:=&+[polL_eval_Oq(data`basis[i][j],m,OK,xtS)*btS[j]:j in [1..d]]*derxtS*denomS;
    res:=Coefficient(di,-1);
    if res ne 0 then
      di:=di-res*tq^(-1);
    end if;
    Append(~diffsS,di);
    Append(~residues,(res eq 0) select K!0 else K!(OK!res)); // the exact 0 of K if there is none
  end for;
  return diffsS, residues;

end function;


tiny_integrals_on_basis:=function(P1,P2,data:prec:=0,Pt:=0)

  // The tiny integrals int_P1^P2 omega_i of the basis forms, for P1, P2 in the same residue
  // disc (article: the algorithm "Tiny integrals").
  // Input:   P1, P2 points in the same residue disc, P2 over K or over a totally ramified
  //          extension Ke = K(pi^(1/e)); data; prec (optional): the t-adic precision (default:
  //          tadicprec, with the actual valuation of the local parameter at P2);
  //          Pt (optional): a point over K in the disc, needed if P1 is not defined over K.
  // Returns: the vector of the integrals (over the field of P2) and the precision to which
  //          they are correct, in units of v_K (tiny_integral_prec).
  // Method:  the integrals are reduced to integrals from a K-rational centre: from P1 itself
  //          if P1 is over K and good or very bad, otherwise from Pt, resp. from the very bad
  //          point of the disc (int_P1^P2 = int_C^P2 - int_C^P1). From the centre, the
  //          expansions x(t), b(t) in the integral local parameter t (local_coord) give each
  //          integrand as a Laurent series in t, which is integrated termwise and evaluated at
  //          t(P2); the series arithmetic runs over O_K/pi^NK.
  // Errors:  if the points do not lie in the same residue disc (lie_in_same_disc).

  P1:=point_to_K(P1,data`K); // guard against points over different-precision copies of K
  P2:=point_to_K(P2,data`K);
  if Type(Pt) eq Rec then
    Pt:=point_to_K(Pt,data`K);
  end if;
  x1:=P1`x; x2:=P2`x; b1:=P1`b; b2:=P2`b; N:=data`N; basis:=data`basis;
  d:=Degree(data`Q); K:=data`K;
  Ke:=Parent(x1); NK:=Precision(K);

  if not lie_in_same_disc(P1,P2,data) then
    error "tiny_integrals_on_basis: the points do not lie in the same residue disc (their x and b differ modulo pi); use coleman_integrals_on_basis";
  end if;
  
  // If P1 and P2 agree to the full precision to which they are given, the integrals
  // vanish to (at least) that precision. (The agreement is compared with the precision of
  // the points, not with the precision NK of K: points of slightly lower absolute precision,
  // e.g. produced by Qq_points, whose roots are computed at precision N < NK, never reach NK,
  // and the precision estimate of the series evaluation below would degenerate to 0.)
  if IsWeaklyZero(x1-x2) and &and[IsWeaklyZero(b1[i]-b2[i]):i in [1..d]] then
    eloc:=Degree(Parent(x1-x2),K);
    valeq:=Minimum([Valuation(x1-x2)] cat [Valuation(b1[i]-b2[i]):i in [1..d]]); // = the absolute precisions of the differences
    return RSpace(Ke,#basis)!0, Minimum(N,valeq/eloc); // precision in units of v_K, as for the generic return below
  end if;

  if Degree(Ke,K) gt 1 then // P1 needs to be defined over K
    tinyPtoP2,NtinyPtoP2:=$$(Pt,P2,data);
    tinyPtoP1,NtinyPtoP1:=$$(Pt,P1,data);
    return tinyPtoP2-tinyPtoP1,Minimum(NtinyPtoP2,NtinyPtoP1);
  end if;
  
  if not Type(Pt) eq Rec then // no centre given: P1 is over K and serves as the centre
    Pt:=P1;
  end if;

  if is_bad(Pt,data) and not is_very_bad(Pt,data) then // in a bad disc, expand around the very bad point
    Pt:=find_bad_point_in_disc(Pt,data);
    tinyPttoP2,NtinyPttoP2:=$$(Pt,P2,data);
    tinyPttoP1,NtinyPttoP1:=$$(Pt,P1,data);
    return tinyPttoP2-tinyPttoP1,Minimum(NtinyPttoP2,NtinyPttoP1);
  end if;

  // from here on P1 is over K and good or very bad: the expansions are taken at P1

  e:=Degree(Parent(x2),K);

  if prec eq 0 then // no t-adic precision specified
    // Sharper truncation: instead of the worst case v_K(t(P2))>=1/e, use the actual
    // valuation of the local parameter at P2; only tiny integrals to a point produced
    // by find_suitable_point_in_disc genuinely need series of length about e*Nmax.
    _,index0:=local_data(P1,data);
    if index0 eq 0 then
      val0:=Valuation(x2-x1);
    else
      val0:=Valuation(b2[index0]-b1[index0]);
    end if;
    if val0 ge 1 then // val0 is in units of the uniformizer of Parent(x2), so v_K(t(P2))=val0/e
      prec:=tadicprec(data,e:vmin:=val0/e);
    else
      prec:=tadicprec(data,e);
    end if;
  end if;

  // The integrands are expanded over the exact quotient ring Oq = OK/pi^NK
  // (integrand_series); only the final integration (division by the exponents) is done back
  // over K, whose precision loss is accounted for in tiny_integral_prec.

  Kt:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  St:=LaurentSeriesRing(quo<OK|UniformizingElement(K)^NK>,prec);
  xt,bt,index:=local_coord(P1,prec,data); // xt, bt in O_K[[t]]
  diffsS,residues:=integrand_series(P1,xt,bt,data,St,OK);

  maxpoleorder:=-Minimum([Valuation(di):di in diffsS]); // the maximal pole order k of the integrands at P1
  maxdegree:=Maximum([Degree(di):di in diffsS]); // the degree of a series is that of its last known coefficient
  mindegree:=Minimum([Degree(di):di in diffsS]);
  indefints:=[Integral(series_Oq_to_K(di,Kt,OK)):di in diffsS]; // integrate over K

  if index eq 0 then // the local parameter is x - x(P1) (resp. 1/x - 1/x(P1))
    t0:=x2-x1;
    NPP:=Minimum(AbsolutePrecision(x1),1/e*AbsolutePrecision(x2));
  else // the local parameter is b_index - b_index(P1)
    t0:=b2[index]-b1[index]; // t(P2)
    NPP:=Minimum(AbsolutePrecision(b1[index]),1/e*AbsolutePrecision(b2[index]));
  end if;
  val:=Valuation(t0);

  tinyP1toP2:=[eval_series_Ke(f,t0,K):f in indefints]; // in Ke; fast path when t0 is a power of the uniformizer

  NtinyP1toP2:=tiny_integral_prec(prec,e,maxpoleorder,maxdegree,mindegree,val,NPP,data);

  // the logarithmic terms res_i*log(t(P2)) of forms of the third kind with a residue res_i at
  // the centre P1: the primitive of res_i/t is res_i*log(t), normalised by Iwasawa's branch
  // log(p) = 0 (log_iwasawa) and by the value 0 of the regular part at the centre, as for
  // the other terms (so that differences of such integrals from the centre are the integrals)
  if exists{c:c in residues|not IsWeaklyZero(c)} then
    logt0:=log_iwasawa(t0);
    for i in [i:i in [1..#residues]|not IsWeaklyZero(residues[i])] do
      term:=residues[i]*logt0;
      tinyP1toP2[i]+:=term;
      NtinyP1toP2:=Minimum(NtinyP1toP2,AbsolutePrecision(term)/e);
    end for;
  end if;

  if NtinyP1toP2 le 0 then
    print "WARNING: tiny integral has no correct digits (estimated precision",NtinyP1toP2,"); increase N (or e)";
  end if;

  return Vector(tinyP1toP2),NtinyP1toP2;

end function;


tiny_integrals_on_basis_to_z:=function(Pt,data:prec:=0)

  // The tiny integrals of the basis forms from Pt to a variable point of its residue disc,
  // as Laurent series in the integral local parameter t of the disc: the indefinite
  // integrals int_Pt^(P(t)) omega_i (used by the solver and symmetric Chabauty to find the
  // zeros of integrals in a disc).
  // Input:   Pt a point over K; data; prec (optional): the t-adic precision (default
  //          tadicprec(data,1)).
  // Returns: the vector of these series over K (the constant terms make them vanish at Pt),
  //          the expansions xt and bt (a vector) of x (resp. 1/x) and b at the centre of the
  //          disc in t (at Pt if it is good or very bad, else at the very bad point of its
  //          disc), and the precision of the tiny integral from Pt to the centre, which is
  //          added to the series (the precision of the series coefficients themselves is
  //          that of K).

  Pt:=point_to_K(Pt,data`K); // guard against points over different-precision copies of K
  K:=data`K; NK:=Precision(K);

  if is_bad(Pt,data) and not is_very_bad(Pt,data) then // in a bad disc the centre is the very bad point
    P1:=find_bad_point_in_disc(Pt,data);
  else
    P1:=Pt;
  end if;
  x1:=P1`x;

  IPtP1,NIPtP1:=tiny_integrals_on_basis(Pt,P1,data:prec:=prec); // int_Pt^P1, in K

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,1);
  end if;

  // the integrands over the exact quotient ring Oq = OK/pi^NK (integrand_series); only the
  // final integration returns to K
  Kt<t>:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  St:=LaurentSeriesRing(quo<OK|UniformizingElement(K)^NK>,prec);
  xt,bt,index:=local_coord(P1,prec,data);
  diffsS,residues:=integrand_series(P1,xt,bt,data,St,OK);
  if exists{c:c in residues|not IsWeaklyZero(c)} then
    print "WARNING: tiny_integrals_on_basis_to_z: a basis form has a residue at the centre of the disc (a form of the third kind); its logarithmic term is not part of the series";
  end if;
  indefints:=[Integral(series_Oq_to_K(di,Kt,OK)):di in diffsS];

  return Vector(indefints)+ChangeRing(IPtP1,K),xt,Vector(bt),NIPtP1; // bt as a vector, so that Evaluate maps over its entries

end function;





powtab:=function(x,lo,hi);

  // Returns T, lo with T[k-lo+1] = x^k for lo <= k <= hi (lo may be negative: the f_i are
  // Laurent series). One table per point and exponent range, a single exponentiation plus
  // hi-lo multiplications, replaces computing x^k anew for every coefficient of every basis
  // element when the f_i are evaluated at a point.

  if hi lt lo then return [Parent(x)|], lo; end if;
  T:=[Parent(x)| pow_K(x,lo) ];
  for k:=lo+1 to hi do T[k-lo+1]:=T[k-lo]*x; end for;
  return T, lo;

end function;


twisted_maps:=function(data)

  // The twisted coefficient maps mks[k+1] = m o tau_L^k, k = 0..n_tau, where tau_L is the
  // automorphism of L with m o tau_L = tau o m (mks[n_tau+1] = m since tau^n_tau = id; for the
  // local approximation of frobenius_aut_local these identities hold to the precision Nmax of
  // K, which is all that is used). mks[k+1] maps the coefficients of the functions of the
  // Frobenius level k (the curve X_k of the p-power lift); for the q-power lift n_tau = 1.

  m:=data`m;
  ntau:=(assigned data`ntau) select data`ntau else 1;
  tau:=(assigned data`tau) select data`tau else 0;
  mks:=[* m *];
  if Type(tau) ne RngIntElt then
    tauk:=tau;
    for k:=1 to ntau do
      mks[k+1]:=tauk*m; // apply tau_L^k first, then the completion map
      tauk:=tauk*tau;
    end for;
    mks[ntau+1]:=m;
  else
    for k:=1 to ntau do
      mks[k+1]:=m;
    end for;
  end if;
  return mks;

end function;


map_coefficients_K:=function(C,Mb)

  // The elements of the sequence C (in L, or in Q) mapped to K by the coefficient map mLK with
  // the images Mb = [mLK(L.1^(i-1)) : i in [1..Degree(L)]] of the power basis: since mLK is
  // Q-linear, mLK(c) = sum_i Eltseq(c)[i]*Mb[i], summed over the nonzero coordinates (0 maps
  // to the exact 0). Evaluating these rational linear combinations is far cheaper than
  // applying the Magma map: the completion map reconstructs from the embedding on every call,
  // and for the p-power lift mLK = m o tau_L^k is more expensive still.

  K:=Universe(Mb);
  if #Mb eq 1 or Type(Universe(C)) in {FldRat,RngInt} then // c rational: Eltseq(c) = [c,0,...,0]
    return [K|(c eq 0) select K!0 else (Rationals()!c)*Mb[1]:c in C];
  end if;
  return [K|&+[K|E[i]*Mb[i]:i in [1..#Mb]|E[i] ne 0] where E:=Eltseq(c):c in C];

end function;


// The correction functions of one Frobenius level, with their coefficients in K
// (correction_data_K); they depend on the functions and on the level, not on the point:
//   Oq     the quotient ring O_K/pi^NK, NK = Precision(K), of the fast evaluation in evalf0_list,
//   f0     for each f_0 a record of format f0_K_format:
//            pole   its pole order in z (0 if it has none),
//            vmin   the minimal valuation v_0 of its nonzero coefficients in K (Infinity if
//                   there are none),
//            terms  for each entry i, 0 if f_0[i] = 0, and otherwise <val, CK, NZ>: the series
//                   f_0[i] in z has valuation val, CK[j] are the coefficients in K of its j-th
//                   coefficient (a polynomial in x) and NZ[j] the indices of the nonzero ones,
//            fast   0 if a coefficient is not integral; otherwise for each entry i (0 if
//                   f_0[i] = 0) the polynomials A_k(w) = sum_j CK[j][k]*w^(1-j-val) over Oq,
//                   k = 1..deg(r), so that A_k(1/z(P)) is the coefficient of x(P)^(k-1),
//   finf   for each f_inf a record of format finf_K_format: the exponent range lo..hi of its
//          entries (Laurent series in x) and C[i] = <val, the coefficients in K> of its entry i
//          (w.r.t. b^inf, used at infinite points); lofin, hifin, Cfin the same for the entries
//          of f_inf*W (w.r.t. b^0, used at finite points),
//   fend   for each f_end, for each entry i the coefficients in K of the polynomial f_end[i].
correction_K_format:=recformat<Oq,f0,finf,fend>;
f0_K_format:=recformat<pole,vmin,terms,fast>;
finf_K_format:=recformat<lo,hi,C,lofin,hifin,Cfin>;

correction_data_K:=function(f0s,finfs,fends,data,mLK)

  // The correction functions f0s, finfs, fends (lists of vectors, as data`f0list,
  // data`finflist, data`fendlist) with their coefficients mapped to K by the coefficient map
  // mLK (data`m, or m o tau_L^k for the twisted functions of the Frobenius level k), in the
  // form used by evalf0_list, evalfinf and evalfend (correction_K_format). coleman_data
  // computes them for the basis forms at every level once (data`corrK), and every evaluation
  // at a point reuses them.
  // Errors:  if an f_0 has terms with positive powers of z (they are series in 1/z).

  K:=data`K; L:=data`L; d:=Degree(data`Q); degr:=Degree(data`r);
  Mb:=[mLK(L.1^(i-1)):i in [1..Degree(L)]];
  OK:=RingOfIntegers(K);
  Oq:=quo<OK|UniformizingElement(K)^Precision(K)>; Ow:=PolynomialRing(Oq);

  f0data:=[];
  for f0 in f0s do
    terms:=[* *]; vmin:=Infinity();
    for i:=1 to d do
      if f0[i] eq 0 then
        terms[i]:=0;
        continue;
      end if;
      C:=Coefficients(f0[i]); val:=Valuation(f0[i]);
      if val+#C-1 gt 0 then
        error "correction_data_K: f_0 has terms with positive powers of z";
      end if;
      CK:=[map_coefficients_K(Coefficients(c),Mb):c in C];
      NZ:=[[k:k in [1..#D]|D[k] ne 0] where D:=Coefficients(C[j]):j in [1..#C]];
      vmin:=Minimum([vmin] cat [Valuation(CK[j][k]):k in NZ[j],j in [1..#C]]);
      terms[i]:=<val,CK,NZ>;
    end for;
    fast:=0;
    if Type(vmin) eq Infty or vmin ge 0 then
      // the coefficient of w^ex in A_k is that of the series term j = 1-val-ex
      fast:=[* (Type(t) eq RngIntElt) select 0 else
               [Ow![(j le #t[2] and k le #t[2][j]) select Oq!OK!t[2][j][k] else Oq!0 where j:=1-t[1]-ex:ex in [0..-t[1]]]:k in [1..degr]]
             : t in terms *];
    end if;
    Append(~f0data,rec<f0_K_format|pole:=Maximum([0] cat [-Valuation(f0[i]):i in [1..d]|f0[i] ne 0]),vmin:=vmin,terms:=terms,fast:=fast>);
  end for;

  // the exponent range and the coefficients of the entries of a vector v of Laurent series
  series_K:=function(v)
    nz:=[i:i in [1..d]|v[i] ne 0];
    lo:=(#nz eq 0) select 0 else Minimum([Valuation(v[i]):i in nz]);
    hi:=(#nz eq 0) select 0 else Maximum([Valuation(v[i])+#Coefficients(v[i])-1:i in nz]);
    return lo,hi,[<(v[i] eq 0) select 0 else Valuation(v[i]),map_coefficients_K(Coefficients(v[i]),Mb)>:i in [1..d]];
  end function;
  finfdata:=[];
  if #finfs gt 0 then
    W:=data`Winf*data`W0^(-1);
    for finf in finfs do
      lo,hi,C:=series_K(finf);
      lofin,hifin,Cfin:=series_K(finf*ChangeRing(W,BaseRing(finf)));
      Append(~finfdata,rec<finf_K_format|lo:=lo,hi:=hi,C:=C,lofin:=lofin,hifin:=hifin,Cfin:=Cfin>);
    end for;
  end if;

  fenddata:=[[map_coefficients_K(Coefficients(fend[i]),Mb):i in [1..d]]:fend in fends];

  return rec<correction_K_format|Oq:=Oq,f0:=f0data,finf:=finfdata,fend:=fenddata>;

end function;


correction_level:=function(data,k,mk)

  // The correction functions of the basis forms at the Frobenius level k with the coefficient
  // map mk = twisted_maps(data)[k+1] (correction_data_K): data`corrK[k+1], computed by
  // coleman_data; computed here for a record without it.

  if "corrK" in Names(Format(data)) and assigned data`corrK then
    return data`corrK[k+1];
  end if;
  return correction_data_K(data`f0list,data`finflist,data`fendlist,data,mk);

end function;


f0_pole_bound:=function(data)

  // j_0 = q_tau*(N_max - v(q_tau)) of part (1) of the proposition on the precision of f_0,
  // f_inf, f_end at a point: the reduction computes the terms c_jk/r^j b^0_k of f_0 with
  // j < j_0 (the approximation of F_tau^*(omega) modulo pi^N_max has pole order j_0 - 1 in r),
  // and the terms with j >= j_0 are omitted. N_max and v are those of the field over which
  // the reduction ran (Q_p in the rational branch of coleman_data, K otherwise; cf.
  // data`Nmaxred, data`eKred).

  q:=#ResidueClassField(data`P);
  qtau:=(assigned data`qtau) select data`qtau else q;
  eKred:=(assigned data`eKred) select data`eKred else data`eK;
  Nmaxred:=(assigned data`Nmaxred) select data`Nmaxred else data`Nmax;
  return qtau*(Nmaxred-eKred*Valuation(qtau,data`p));

end function;


f0_tail_prec:=function(data,vr)

  // T_0(P) of part (1) of the proposition on the precision of f_0, f_inf, f_end at a point,
  // in units of v_K: a lower bound
  // for the valuations of the omitted terms c_jk(P)/r(P)^j b^0_k(P), j >= j_0, of f_0(P) at a
  // good or finitely bad point P with v_K(r(P)) = vr (rational, 0 <= vr < 1/q_tau):
  //   T_0(P) = min_{a >= j_0} { floor(a/q_tau) + v_K(q_tau) - e_K*floor(log_p(a*e_0)) - a*vr },
  // with j_0 = f0_pole_bound(data). (In the rational branch of coleman_data the reduction runs
  // over Q_p, so the bound for the coefficients is e_K times the one over Q_p, i.e. the first
  // term is s*floor(a/q_tau) with s = e_K; in general s = e_K/data`eKred.)
  // As in the remark after the proposition, finitely many tests suffice. With C the value at
  // a = j_0, choose M > j_0 with
  //   M*(s/q_tau-vr) > 2*e_K   and   M*(s/q_tau-vr) + v_K(q_tau) - s - e_K*(floor(log_p(M*e_0))+1) >= C;
  // then every a >= M gives a value >= C. Moreover, on each block q_tau*k <= a < q_tau*(k+1)
  // (j_0 is a multiple of q_tau) the value does not increase with a, so it suffices to test the
  // last element of each block in [j_0,M) and a = M-1.

  p:=data`p; eK:=data`eK; e0:=data`e0;
  q:=#ResidueClassField(data`P);
  qtau:=(assigned data`qtau) select data`qtau else q;
  eKred:=(assigned data`eKred) select data`eKred else eK;
  s:=eK div eKred;
  vq:=eK*Valuation(qtau,p); // v_K(q_tau)
  j0:=f0_pole_bound(data);

  slope:=s/qtau-vr;
  if slope le 0 then
    error Sprintf("f0_tail_prec: v_K(r(P)) = %o, but the series f_0(P) only converges for v_K(r(P)) < %o; the point is not suitable (increase e)",vr,s/qtau);
  end if;
  value:=func<a | s*(a div qtau)+vq-eK*Ilog(p,a*e0)-a*vr>;

  C:=value(j0);
  M:=j0+1;
  while (M*slope le 2*eK) or (M*slope+vq-s-eK*(Ilog(p,M*e0)+1) lt C) do
    M:=M+qtau; // any M with both properties will do
  end while;

  T0:=C;
  a:=j0+qtau-1;
  while a lt M-1 do
    T0:=Minimum(T0,value(a));
    a:=a+qtau;
  end while;
  T0:=Minimum(T0,value(M-1));

  return T0;

end function;


f0_values_Oq:=function(pre,z0,x0,b,K)

  // The values of the f_0 of pre (correction_data_K) at a good finite point over K with
  // z(P) = z0, x(P) = x0 and b^0(P) = b, all integral (z0 a unit): computed over the exact
  // quotient ring Oq=OK/pi^NK of pre instead of the inexact p-adic field K, by Horner's rule
  // for the polynomials A_k(1/z(P)) and then in x(P). Magma's FldPad arithmetic is slow (it
  // carries a precision with every element); over Oq it uses fast integer/polynomial
  // arithmetic. Since Oq is exact, the result is the sum of f0_values_Ke reduced modulo
  // pi^NK.

  OK:=RingOfIntegers(K); Oq:=pre`Oq; Oqx:=PolynomialRing(Oq);
  w0:=Oq!(OK!(K!(1/z0))); // 1/r(P), a unit
  xq:=Oq!(OK!(K!x0));
  bq:=[Oq!(OK!(K!c)):c in b];
  value:=func<f|&+[Oq|Evaluate(Oqx![Evaluate(A,w0):A in f`fast[i]],xq)*bq[i]:i in [1..#bq]|Type(f`fast[i]) ne RngIntElt]>;
  return [K|K!(OK!value(f)):f in pre`f0]; // lifted back to K once at the end

end function;


f0_values_Ke:=function(pre,z0,x0,b,d,maxpole,degr)

  // The values of the f_0 of pre (correction_data_K) at a point over Ke = Parent(x0) with
  // z(P) = z0, x(P) = x0 and b^0(P) = b (d values, a sequence or a vector); maxpole bounds
  // their pole orders in z. The power
  // tables of 1/z(P) and x(P) (the dominant cost, ~maxpole multiplications in the ramified
  // extension Ke) are shared among all entries, and the inner sums are regrouped so that the
  // long loops only contain (K-scalar)*(Ke-element) products instead of full
  // Ke-multiplications.

  Ke:=Parent(x0);
  invz0:=1/z0;
  invz0pow:=[Ke!1];
  for i:=1 to maxpole do
    invz0pow[i+1]:=invz0pow[i]*invz0; // 1/r(P)^i, i=0,...,maxpole
  end for;
  xpow:=[Ke!1];
  for i:=1 to degr-1 do
    xpow[i+1]:=xpow[i]*x0; // powers of x(P)
  end for;

  vals:=[Ke|];
  for f in pre`f0 do
    f0P:=Ke!0;
    for i:=1 to d do
      if Type(f`terms[i]) ne RngIntElt then
        val,CK,NZ:=Explode(f`terms[i]);
        acc:=[Ke!0:k in [1..degr]]; // accumulator for the coefficient of x(P)^(k-1)
        for j:=1 to #CK do
          zj:=invz0pow[2-j-val];
          for k in NZ[j] do
            acc[k]:=acc[k]+CK[j][k]*zj; // scalar times Ke-element, no Ke-multiplication
          end for;
        end for;
        s:=Ke!0;
        for k:=1 to degr do
          if acc[k] ne 0 then
            s:=s+acc[k]*xpow[k];
          end if;
        end for;
        f0P:=f0P+s*b[i];
      end if;
    end for;
    Append(~vals,f0P);
  end for;
  return vals;

end function;


evalf0_list:=function(f0s,Pt,data:mLK:=0,pre:=0)

  // The values at the point Pt of the functions f0 = sum_k f0_k b^0_k in the list f0s (the
  // f_0 parts of the correction functions, f0_k in L[x]((z)) with z = r), with certified
  // precisions (article: part (1) of the proposition on the precision of f_0, f_inf, f_end at
  // a point; the algorithm "q-power Frobenius of a point and correction values").
  // Input:   f0s a list of vectors in (L[x]((z)))^d (data`f0list); Pt a suitable point over K
  //          or K(pi^(1/e)); data; mLK (optional): the coefficient map L -> K to use instead
  //          of data`m: passing m*tau^k evaluates the twisted functions f0^(tau^k) on the
  //          curve X_k (p-power lift); pre (optional): correction_data_K(f0s,[],[],data,mLK),
  //          the coefficients mapped to K (for the f0list at the Frobenius level k this is
  //          data`corrK[k+1]); computed if not given.
  // Returns: the list of the values (in the field of Pt) and the list of their precisions
  //          (units of v_K).
  // At a good finite point over K the f0 are evaluated over the exact quotient ring O_K/pi^NK
  // by the polynomials A_k of correction_data_K. Otherwise the power tables of 1/z(P) and
  // x(P) (the dominant cost, ~maxpole multiplications in the ramified extension Ke) are
  // shared among all entries, and the inner sums are regrouped so that the long loops only
  // contain (K-scalar)*(Ke-element) products instead of full Ke-multiplications.

  x0:=Pt`x; b:=Pt`b; Q:=data`Q; r:=data`r; W0:=data`W0; Winf:=data`Winf; N:=data`N;
  d:=Degree(Q); L:=data`L; K:=data`K; m:=data`m;
  if Type(mLK) ne RngIntElt then
    m:=mLK;
  end if;
  if Type(pre) eq RngIntElt then
    pre:=correction_data_K(f0s,[],[],data,m);
  end if;
  Ke:=Parent(x0);
  e:=Degree(Ke,K);
  Kex:=PolynomialRing(Ke);
  degr:=Degree(r);

  // The power table only needs the largest actual pole order of the f0 in z = r. The precision
  // estimate is that of part (1) of the proposition on the precision of f_0, f_inf, f_end at
  // a point: at a good or finitely bad point it is
  //   min{ T_0(P), N - (j_0-1)*v_K(r(P)) + min{v_0-v_K(r(P)),0} },
  // with the a priori pole order j_0-1 = q_tau*(Nmax-v(q_tau))-1 of the computed f0 (not its
  // actual pole order: coefficients that vanish there are only known modulo pi^N), v_0 the
  // minimal valuation of its coefficients, and T_0(P) the bound for the omitted terms j >= j_0
  // (f0_tail_prec); at an infinite point it is
  //   N + (ord_inf(W^(-1))+1)*v_K(1/x(P)) + min{v_0-v_K(1/x(P)),0}.
  // (The f0 of a Frobenius pullback has pole order <= j_0-1; the maximum with the actual pole
  // order below only matters for the f0 of an arbitrary form in coleman_integral.)
  j0:=f0_pole_bound(data);
  poles:=[f`pole:f in pre`f0]; // the actual pole orders in z
  maxpole:=Maximum([0] cat poles);

  rKe:=Kex!coer_poly(r,L,K,m);
  lcr:=LeadingCoefficient(rKe);

  if Pt`inf then
    Winv:=W0*Winf^(-1);
    Lt:=BaseRing(Winv);
    b:=Vector(b)*Transpose(eval_mat(Evaluate(Winv,1/Lt.1),L,K,m,x0)); // values of the b_i^0 at Pt
    z0:=Evaluate(rKe,1/x0)/lcr; // z(x(Pt))
    xx:=1/x0; // x(Pt)
  else
    z0:=Pt`r;
    xx:=x0;
  end if;

  NN:=Minimum([e*N,known_digits(z0),known_digits(Pt`x),Minimum([known_digits(Pt`b[i]):i in [1..d]])]); // the N of the proposition (the precision of the point), in units of v_Ke

  // Fast path for e=1 (Ke=K, i.e. a good finite endpoint, which covers the bulk of the
  // calls): the f0 are evaluated over the exact quotient ring Oq=OK/pi^NK (f0_values_Oq).
  // All inputs are integral there: z0=r(P) is a unit at a good point, x0 and the b_i are
  // integral, and the f0 coefficients are integral (the cohomology reduction reduces them
  // mod P^Nmax; otherwise the sum over Ke is used).
  if e eq 1 and not Pt`inf and Valuation(z0) eq 0 and Valuation(xx) ge 0 and &and[Valuation(c) ge 0:c in b]
     and &and[Type(f`fast) ne RngIntElt:f in pre`f0] then
    vals:=f0_values_Oq(pre,z0,xx,b,K);
    vz0:=Valuation(z0);
    T0:=f0_tail_prec(data,vz0); // >= N here, by the choice of Nmax (z0 is a unit)
    precs:=[];
    for n:=1 to #f0s do
      f:=pre`f0[n];
      corr:=(Type(f`vmin) eq Infty) select 0 else Minimum(f`vmin-vz0,0); // min{v_0-v_K(r(P)),0}
      precs[n]:=Minimum(T0,NN-Maximum(j0-1,poles[n])*vz0+corr); // e=1, finite point
    end for;
    return vals,precs;
  end if;

  vals:=f0_values_Ke(pre,z0,xx,b,d,maxpole,degr);
  if not Pt`inf then
    T0:=f0_tail_prec(data,Valuation(z0)/e); // in units of v_K
  end if;
  precs:=[];
  for n:=1 to #f0s do
    f:=pre`f0[n];
    // (units of v_Ke = e*v_K)
    valf0:=(Type(f`vmin) eq Infty) select f`vmin else e*f`vmin; // e*v_0
    if Pt`inf then
      corr:=(Type(valf0) eq Infty) select 0 else Minimum(valf0-Valuation(x0),0); // e*min{v_0-v_K(1/x(P)),0}
      Nf0P:=NN+(ord_inf_mat(Winv)+1)*Valuation(x0)+corr;
      precs[n]:=Nf0P/e;
    else
      corr:=(Type(valf0) eq Infty) select 0 else Minimum(valf0-Valuation(z0),0); // e*min{v_0-v_K(r(P)),0}
      Nf0P:=NN-Maximum(j0-1,poles[n])*Valuation(z0)+corr; // the a priori pole order j_0-1, not the actual one
      precs[n]:=Minimum(T0,Nf0P/e);
    end if;
  end for;

  return vals,precs;

end function;


evalf0:=function(f0,Pt,data:mLK:=0,pre:=0)

  // Evaluate a single vector of functions f0 in L[x][[z,1/z]]^d at Pt, cf. evalf0_list (pre:
  // correction_data_K for a list containing f0, or for [f0] alone).

  vals,precs:=evalf0_list([f0],Pt,data:mLK:=mLK,pre:=pre);
  return vals[1],precs[1];

end function;


evalfinf:=function(finf,Pt,data:mLK:=0,pre:=0,Wpre:=0,Winvpre:=0)

  // Evaluate a vector of functions finf in L[x,1/x][z,1/z]^d, given w.r.t. b^inf (the
  // primitive f_inf of the infinite reduction), at the point Pt over Ke = K(pi^(1/e)).
  //
  // Input:  finf  sequence of d Laurent series (coefficients in L[x,1/x]); the function is
  //               sum_i finf[i]*b^inf_i,
  //         Pt    a point record (set_point, set_bad_point) over Ke; any point of U or an
  //               infinite point.
  // Output: f_inf(Pt) in Ke and its absolute precision in units of v_Ke, following part (2)
  //         of the proposition on the precision of f_0, f_inf, f_end at a point.
  //
  // mLK (optional): coefficient map L->K to use instead of data`m (cf. evalf0).
  // pre (optional): the entry of correction_data_K for finf (its coefficients mapped to K);
  // computed if not given.
  // Wpre/Winvpre (optional): the constant matrices W = Winf*W0^(-1) and W^(-1), which
  // depend on neither finf nor Pt. Computing them costs a d x d inversion over a Laurent
  // polynomial ring, and evalfinf is called 2*(2g)*n_tau times per Coleman integral, so
  // the caller computes them once.
  //
  // At an infinite point the values of b^inf are Pt`b and the series is evaluated at 1/x(Pt);
  // at a finite point the values of b^inf are W*b^0(Pt), i.e. the entries of finf*W are
  // evaluated with the values of b^0.

  x0:=Pt`x; b:=Pt`b; Q:=data`Q; W0:=data`W0; Winf:=data`Winf; N:=data`N; P:=data`P;
  d:=Degree(Q); L:=data`L; K:=data`K; m:=data`m;
  if Type(mLK) ne RngIntElt then
    m:=mLK;
  end if;
  if Type(pre) eq RngIntElt then
    pre:=correction_data_K([],[finf],[],data,m)`finf[1];
  end if;
  q:=#ResidueClassField(P);
  Ke:=Parent(x0);
  e:=Degree(Ke,K);

  NN:= Minimum([e*N,known_digits(Pt`x),Minimum([known_digits(Pt`b[i]):i in [1..d]])]); // the N of the proposition (the precision of the point); no r here

  if Type(Wpre) eq RngIntElt then W:=Winf*W0^(-1); else W:=Wpre; end if;
  if Type(Winvpre) eq RngIntElt then Winv:=W^(-1); else Winv:=Winvpre; end if;

  // sum_i sum_j C[i][2][j]*s^(val_i+j-1)*b[i], with the powers of s = 1/x(Pt) resp. x(Pt)
  // from one table; valfinf: the minimal valuation of the coefficients (in units of v_Ke)
  evaluate:=function(lo,hi,C,s)
    sP:=Ke!0;
    valfinf:=Infinity();
    T,off:=powtab(s,lo,hi);
    for i:=1 to d do
      val,CK:=Explode(C[i]);
      for j:=1 to #CK do
        cK:=Ke!CK[j];
        sP:=sP+cK*T[val+j-1-off+1]*b[i];
        valfinf:=Minimum(valfinf,Valuation(cK));
      end for;
    end for;
    return sP, valfinf;
  end function;

  if Pt`inf then
    finfP,valfinf:=evaluate(pre`lo,pre`hi,pre`C,1/x0);
    // Part (2) of the proposition on the precision of f_0, f_inf, f_end at a point (units
    // of v_Ke = e*v_K): the exact f_inf has
    // degree kappa_3 <= -min{q_tau*(ord_0(W)+1), ord_inf(W^(-1))+1} in x, and its coefficients
    // agree with those of finf modulo pi^N, also beyond the degree of finf, so at an infinite point
    // the precision is N + min{q_tau*(ord_0(W)+1), ord_inf(W^(-1))+1}*v_K(1/x(P)) + min{v_inf-v_K(1/x(P)),0}.
    // (The maximum with the actual degree hi only matters for the f_inf of an arbitrary form in
    // coleman_integral, which need not satisfy this bound.)
    qtau:=(assigned data`qtau) select data`qtau else q;
    kappa3:=Maximum(-Minimum(qtau*(ord_0_mat(W)+1),ord_inf_mat(Winv)+1),pre`hi);
    corr:=(Type(valfinf) eq Infty) select 0 else Minimum(valfinf-Valuation(x0),0); // e*min{v_inf-v_K(1/x(P)),0}
    NfinfP:=NN-kappa3*Valuation(x0)+corr;
  else
    finfP,valfinf:=evaluate(pre`lofin,pre`hifin,pre`Cfin,x0);
    NfinfP:=NN+Minimum(valfinf,0);
  end if;

  return finfP, NfinfP/e;

end function;


evalfend:=function(fend,Pt,data:mLK:=0,pre:=0,Wpre:=0,Winvpre:=0)

  // Evaluate a vector of polynomials fend in L[x]^d, given w.r.t. b^0 (the primitive f_end
  // of the final reduction, an element of B_0 meet B_inf), at the point Pt over
  // Ke = K(pi^(1/e)).
  //
  // Input:  fend  sequence of d polynomials in x; the function is sum_i fend[i]*b^0_i,
  //         Pt    a point record over Ke; any point of U or an infinite point.
  // Output: f_end(Pt) in Ke and its absolute precision in units of v_Ke, following part (3)
  //         of the proposition on the precision of f_0, f_inf, f_end at a point.
  //
  // mLK, pre, Wpre, Winvpre (optional): as in evalfinf.
  //
  // At an infinite point the values of b^0 are W^(-1)*b^inf(Pt) and the polynomials are
  // evaluated at x(Pt) (written as a power of 1/x(Pt)); the precision can then be negative
  // (ord_0(W)+1 < 0), and the caller has to choose a suitable point closer to the boundary.

  x0:=Pt`x; b:=Pt`b; Q:=data`Q; W0:=data`W0; Winf:=data`Winf; N:=data`N;
  d:=Degree(Q); K:=data`K; m:=data`m; L:=data`L;
  if Type(mLK) ne RngIntElt then
    m:=mLK;
  end if;
  if Type(pre) eq RngIntElt then
    pre:=correction_data_K([],[],[fend],data,m)`fend[1];
  end if;
  Ke:=Parent(x0);
  e:=Degree(Ke,K);

  NN:= Minimum([e*N,known_digits(Pt`x),Minimum([known_digits(Pt`b[i]):i in [1..d]])]); // the N of the proposition (the precision of the point); no r here

  if Pt`inf then
    if Type(Wpre) eq RngIntElt then W:=Winf*W0^(-1); else W:=Wpre; end if;
    if Type(Winvpre) eq RngIntElt then Winv:=W^(-1); else Winv:=Winvpre; end if;
    Lt:=BaseRing(Winv);
    b:=Vector(b)*Transpose(eval_mat(Evaluate(Winv,1/Lt.1),L,K,m,x0)); // values of the b_i^0 at Pt
    s:=1/x0; // the polynomials in x are evaluated as polynomials in 1/(1/x(Pt))
  else
    s:=x0;
  end if;
  fendP:=Ke!0;
  valfend:=0;
  T:=powtab(s,0,Maximum([#pre[i]-1:i in [1..d]] cat [0]));
  for i:=1 to d do
    for j:=1 to #pre[i] do
      cK:=Ke!pre[i][j];
      fendP:=fendP+cK*T[j]*b[i];
      valfend:=Minimum(valfend,Valuation(cK));
    end for;
  end for;
  if Pt`inf then
    NfendP:=NN+(ord_0_mat(W)+1)*Valuation(x0)+Minimum(valfend-Valuation(x0),0); // may be negative, see above
  else
    NfendP:=NN+Minimum(valfend,0);
  end if;

  return fendP, NfendP/e;

end function;

round_to_K:=function(V,K)

  // Round a vector V over a totally ramified extension Ke = K(u), u = pi^(1/e), to K.
  //
  // Input:  V  vector over Ke (Coleman integrals between K-rational endpoints, computed over
  //            the auxiliary field Ke of find_suitable_point_in_disc),
  //         K  the completion.
  // Output: the vector of the u^0-components (over K), and remval, the v_K-valuation of the
  //         remaining components (the coefficients of u^1,...,u^(e-1)); Infinity() if these
  //         vanish to the full precision or if Ke = K.
  //
  // The integrals lie in K, so the remaining components must vanish. For very bad or ramified
  // endpoints they cancel only to a v_K-precision that is bounded independently of N and e
  // (it is limited by the auxiliary data at the boundary, e.g. the Frobenius image of the
  // point near the boundary computed with Roots in frobenius_pt), so they are not required to
  // vanish to the full precision. The caller caps the reported precision at remval: a
  // non-positive remval signals an error (a warning is printed), a positive one limits the
  // precision (e.g. in Example 8.3).

  Ke:=CoefficientRing(V);

  if Degree(Ke,K) eq 1 then

    return V, Infinity(); // Ke = K (its base field need not be K); nothing to cancel

  else

  e:=Degree(Ke,K);
  v:=[];
  remvals:=[];
  for i:=1 to #Eltseq(V) do
    v[i]:=Eltseq(V[i])[1];
    nk:=V[i]-v[i];
    if not IsWeaklyZero(nk) then
      Append(~remvals,Valuation(nk)/e); // v_K of the uncancelled ramified part
    end if;
  end for;
  remval:=Infinity(); // default: ramified part cancelled fully => no extra constraint on the precision
  if #remvals gt 0 then
    remval:=Minimum(remvals);
    if remval le 0 then
      print "WARNING: round_to_K: the integral has a spurious ramified component of non-positive valuation",remval,"- the result is likely wrong (increase N, or use a larger e / a prime with better endpoints)";
    else
      print "NOTE: round_to_K: the auxiliary ramified part did not fully cancel (v_K =",remval,"); the K-result is returned, but the reported precision is capped at this value, since it does not improve with N or e.";
    end if;
  end if;

  return Vector(v), remval;

  end if;

end function;

change_abs_precision:=function(x,k)

  // Set the absolute precision of the p-adic number x to k.
  //
  // Output: x with absolute precision min(k, AbsolutePrecision(x)), and that precision. If x
  //         carries fewer than k digits, it is returned unchanged with its own precision:
  //         digits cannot be manufactured.
  //
  // A shortfall is not an error: an entry of the Frobenius matrix or of an assembled integral
  // can carry fewer digits after a loss of precision upstream. The precision reported by
  // coleman_integrals_on_basis is computed from the actual precision of the assembled values,
  // so a shortfall propagates into a smaller reported precision, and the callers print a note
  // when the achieved precision is below the requested one.

  a:=AbsolutePrecision(x);
  if a lt k then
    return x, a;
  end if;
  return ChangePrecision(x,Maximum(0,k-a+RelativePrecision(x))), k;
end function;

change_abs_precision_vec:=function(V,k)

  // change_abs_precision for every entry of the vector V; the second value is the minimal
  // achieved precision.

  kk:=k;
  for i:=1 to #Eltseq(V) do
    V[i],ai:=change_abs_precision(V[i],k);
    kk:=Minimum(kk,ai);
  end for;
  return V, kk;
end function;

change_abs_precision_mat:=function(M,k)

  // change_abs_precision for every entry of the matrix M; the second value is the minimal
  // achieved precision.

  kk:=k;
  for i:=1 to NumberOfRows(M) do
    for j:=1 to NumberOfColumns(M) do
      M[i,j],aij:=change_abs_precision(M[i,j],k);
      kk:=Minimum(kk,aij);
    end for;
  end for;
  return M, kk;
end function;

// The record of one endpoint of a Coleman integral, as computed by coleman_side:
//   Pt         the endpoint (a point record, set_point/set_bad_point),
//   S          the point used for the Frobenius equation: Pt itself if Pt is good, otherwise
//              a suitable point in the residue disc of Pt (find_suitable_point_in_disc),
//   tinyPtoS   the tiny integrals from Pt to S on the basis, NPtoS their precision,
//   tinyStoFS  the sum of the tiny integrals between the Frobenius images of S (the
//              right-hand side of the Frobenius equation), NStoFS its precision,
//   Itot       the assembled contribution of the endpoint, Ndk the precisions of its parts,
//   e, Ke      the ramification index and field of the auxiliary extension of S,
//   bad        whether Pt is bad, direct whether the endpoint was handled by
//              coleman_side_direct (option direct_inf).
coleman_side_format:=recformat<Pt,S,tinyPtoS,NPtoS,tinyStoFS,NStoFS,Itot,Ndk,e,Ke,bad,direct>;

coleman_side:=function(Pt,data,e,Ke,mks,qtau,ntau,Clist:verbose:=true)

  // The part of the Frobenius equation of coleman_integrals_on_basis that depends on one
  // endpoint Pt only (algorithm "Non-tiny integrals on basis").
  //
  // Input:  Pt     an endpoint over K (good, bad or infinite),
  //         e, Ke  the ramification index and the field K(pi^(1/e)) of the auxiliary point
  //                near the boundary (used if Pt is bad),
  //         mks    the twisted coefficient maps m o tau^k, k = 0..ntau,
  //         qtau, ntau, Clist  the Frobenius data (data`qtau, data`ntau, data`Clist).
  // Output: a coleman_side_format record: the point S (Pt itself if Pt is good, otherwise a
  //         suitable point near the boundary of the disc of Pt over Ke), the tiny integrals
  //         Pt -> S and S -> F_q(S), and the accumulated evaluations
  //         sum_k C_k*(f_{tau,i}(F_tau^k(S)))_i with their precisions.
  //
  // The record is independent of the other endpoint and can be reused (option side1 of
  // coleman_integrals_on_basis): in the solver many integrals share the same base point.

  K:=data`K; m:=data`m; basis:=data`basis; L:=data`L;
  f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist;

  eP,index:=local_data(Pt,data);
  data:=update_minpolys(data,Pt`inf,index);

  t:=Cputime();
  Pt,S:=find_suitable_point_in_disc(Pt,data,Ke);
  if verbose then
    printf "coleman_integrals_on_basis: suitable point/local expansions: %o s\n", Cputime(t);
  end if;

  Fside:=Parent(S`x); // Ke if P is bad, K if P is good (then S=P)

  t:=Cputime();
  tinyPtoS,NPtoS:=tiny_integrals_on_basis(Pt,S,data);
  tinyPtoS,NtinyAch:=change_abs_precision_vec(tinyPtoS,Integers()!(Degree(Parent(tinyPtoS[1]),K)*NPtoS));
  if NtinyAch lt Integers()!(Degree(Parent(tinyPtoS[1]),K)*NPtoS) then
    NPtoS:=NtinyAch/Degree(Parent(tinyPtoS[1]),K); // the tiny integral was less precise than predicted: track it
  end if;
  if verbose then
    printf "coleman_integrals_on_basis: tiny integral P -> S: %o s\n", Cputime(t);
  end if;

  // The chain of Frobenius images S -> F_tau(S) -> ... -> F_tau^ntau(S) = F_q(S); for the
  // q-power lift (ntau = 1) this is the single step S -> F_q(S).

  // For the q-power lift at an infinite P, frobenius_pt falls back to the local parameter at
  // the very infinite point P if the congruence mod pi leaves the root ambiguous.
  t:=Cputime();
  center:=0;
  if Pt`inf and ntau eq 1 and eP mod data`p ne 0 then
    center:=Pt;
  end if;
  Spts:=[* S *];
  for k:=1 to ntau do
    Spts[k+1]:=frobenius_pt(Spts[k],data:qtau:=qtau,msrc:=mks[k],mtgt:=mks[k+1],center:=center);
  end for;
  if verbose then
    printf "coleman_integrals_on_basis: Frobenius of the point (%o step(s)): %o s\n", ntau, Cputime(t);
  end if;

  t:=Cputime();
  tinyStoFS,NStoFS:=tiny_integrals_on_basis(S,Spts[ntau+1],data:Pt:=Pt); // F_q(S) lies in the same residue disc as S
  if verbose then
    printf "coleman_integrals_on_basis: tiny integral S -> F_q(S): %o s\n", Cputime(t);
  end if;

  // Evaluations of the f_{tau,i} along the chain, accumulated with the matrices C_k of the
  // lemma on the precision of semilinear composition (C_0 = I for the q-power lift).

  t:=Cputime();
  V:=RSpace(Fside,#basis);
  Itot:=V!0;
  Ndk:=[];
  Wconst:=data`Winf*data`W0^(-1); Winvconst:=Wconst^(-1); // constant: hoisted out of evalfinf/evalfend
  for k:=0 to ntau-1 do
    dk:=[];
    pre:=correction_level(data,k,mks[k+1]); // the coefficients of the f_i of the level, in K
    f0vals,Nf0s:=evalf0_list(f0list,Spts[k+1],data:mLK:=mks[k+1],pre:=pre); // all basis elements at once, sharing the power tables
    for i:=1 to #basis do
      finfi,Nfinfi:=evalfinf(finflist[i],Spts[k+1],data:mLK:=mks[k+1],pre:=pre`finf[i],Wpre:=Wconst,Winvpre:=Winvconst);
      fendi,Nfendi:=evalfend(fendlist[i],Spts[k+1],data:mLK:=mks[k+1],pre:=pre`fend[i],Wpre:=Wconst,Winvpre:=Winvconst);
      ndki:=Minimum([Nf0s[i],Nfinfi,Nfendi]);
      Ndk[i]:=(k eq 0) select ndki else Minimum(Ndk[i],ndki);
      dk[i]:=(Fside!f0vals[i])+(Fside!finfi)+(Fside!fendi);
    end for;
    if ntau eq 1 then // C_0 = I: precisions stay per entry
      Itot:=Itot+V!Vector(dk);
    else // multiplication by C_k mixes the entries
      CkF:=ChangeRing(ChangeRing(Clist[k+1],m),Fside);
      Itot:=Itot+Vector(dk)*Transpose(CkF);
    end if;
  end for;
  if ntau gt 1 then // the entries were mixed by the C_k
    nmin:=Minimum(Ndk);
    Ndk:=[nmin:i in [1..#basis]];
  end if;
  if verbose then
    printf "coleman_integrals_on_basis: evaluation of f_i at the %o level(s): %o s\n", ntau, Cputime(t);
  end if;

  side:=rec<coleman_side_format|>;
  side`Pt:=Pt; side`S:=S; side`tinyPtoS:=tinyPtoS; side`NPtoS:=NPtoS;
  side`tinyStoFS:=tinyStoFS; side`NStoFS:=NStoFS; side`Itot:=Itot; side`Ndk:=Ndk;
  side`e:=e; side`Ke:=Ke; side`bad:=is_bad(Pt,data); side`direct:=false;

  return side;

end function;


coleman_side_direct:=function(Pt,data:verbose:=true)

  // The part of the Frobenius equation for an infinite endpoint Pt over K, computed without
  // the auxiliary extension K(pi^(1/e)) (option direct_inf of coleman_integrals_on_basis).
  //
  // Input:  Pt  an infinite point over K; the q-power lift (data`ntau = 1).
  // Output: a coleman_side_format record as in coleman_side, with Ke = K.
  //
  // An infinite point that is not very infinite is suitable (definition of bad and good
  // points), so the side is computed at Pt itself if v_K(t(Pt)) = 1, and otherwise (Pt very
  // infinite, or deeper in its disc) at the K-rational point S with t(S) = pi, where t is the
  // integral local parameter at the very infinite point Pinf of the disc. F_q(S) is computed
  // by frobenius_pt_inf. Compared with the point near the boundary over K(pi^(1/e)), this
  // costs about q*(m-1)*v_K(t(S)) digits if the basis forms have poles of order m at Pinf.

  K:=data`K; m:=data`m; L:=data`L; basis:=data`basis; NK:=Precision(K);

  if not Pt`inf then
    error "coleman_side_direct: the endpoint is not infinite";
  end if;

  t:=Cputime();
  if is_very_bad(Pt,data) then
    Pinf:=Pt;
  else
    Pinf:=find_bad_point_in_disc(Pt,data);
  end if;
  eP,index:=local_data(Pinf,data);
  if eP mod data`p eq 0 then
    error "coleman_side_direct: p divides the ramification index",eP,"of x at the very infinite point";
  end if;
  data:=update_minpolys(data,true,index);
  xt,bt,index:=local_coord(Pinf,NK+2,data); // NK terms for the point t=pi, NK/q for F_q(S)
  Pinf`xt:=xt; Pinf`bt:=bt; Pinf`index:=index;

  if index eq 0 then
    tP:=Pt`x-Pinf`x;
  else
    tP:=Pt`b[index]-Pinf`b[index];
  end if;
  if not IsWeaklyZero(tP) and Valuation(tP) le 1 then
    S:=Pt;
    tinyPtoS:=RSpace(K,#basis)!0; NPtoS:=NK;
  else // P very infinite, or deeper in its disc: the K-rational point with t=pi
    pi:=K!data`pi;
    S:=set_bad_point(eval_series_Ke(xt,pi,K),[eval_series_Ke(bt[i],pi,K):i in [1..#bt]],true,data:check:=false);
    tinyPtoS,NPtoS:=tiny_integrals_on_basis(Pt,S,data);
    tinyPtoS,NtinyAch:=change_abs_precision_vec(tinyPtoS,Floor(NPtoS));
    NPtoS:=Minimum(NPtoS,NtinyAch);
  end if;
  if verbose then
    printf "coleman_integrals_on_basis: direct route at an infinite endpoint, point S with v_K(t(S)) = 1: %o s\n", Cputime(t);
  end if;

  t:=Cputime();
  FS:=frobenius_pt_inf(S,Pinf,data);
  tinyStoFS,NStoFS:=tiny_integrals_on_basis(S,FS,data);
  if verbose then
    printf "coleman_integrals_on_basis: Frobenius of the point and tiny integral S -> F_q(S): %o s\n", Cputime(t);
  end if;

  t:=Cputime();
  Wconst:=data`Winf*data`W0^(-1); Winvconst:=Wconst^(-1);
  pre:=correction_level(data,0,m);
  f0vals,Nf0s:=evalf0_list(data`f0list,S,data:mLK:=m,pre:=pre);
  dk:=[]; Ndk:=[];
  for i:=1 to #basis do
    finfi,Nfinfi:=evalfinf(data`finflist[i],S,data:mLK:=m,pre:=pre`finf[i],Wpre:=Wconst,Winvpre:=Winvconst);
    fendi,Nfendi:=evalfend(data`fendlist[i],S,data:mLK:=m,pre:=pre`fend[i],Wpre:=Wconst,Winvpre:=Winvconst);
    Ndk[i]:=Minimum([Nf0s[i],Nfinfi,Nfendi]);
    dk[i]:=(K!f0vals[i])+(K!finfi)+(K!fendi);
  end for;
  if verbose then
    printf "coleman_integrals_on_basis: evaluation of f_i at S: %o s\n", Cputime(t);
  end if;

  side:=rec<coleman_side_format|>;
  side`Pt:=Pt; side`S:=S; side`tinyPtoS:=tinyPtoS; side`NPtoS:=NPtoS;
  side`tinyStoFS:=tinyStoFS; side`NStoFS:=NStoFS; side`Itot:=RSpace(K,#basis)!Vector(dk); side`Ndk:=Ndk;
  side`e:=1; side`Ke:=K; side`bad:=true; side`direct:=true;

  return side;

end function;


auxiliary_e:=function(e,P1,P2,bad1,bad2,data,verbose)

  // The ramification index e of the auxiliary totally ramified extension K(pi^(1/e)) of the
  // points near the boundary for the endpoints P1, P2 of coleman_integrals_on_basis (bad1,
  // bad2: whether they need such a point): the given e if e > q*e_P, where e_P is the
  // ramification index of x at the very bad point of the disc (the maximum over the two
  // endpoints), and otherwise 2*q*e_P+1 (run-time optimal; with a warning if e was given);
  // e = 1 if neither endpoint needs it. Prints a note on the expected loss of digits.

  q:=#ResidueClassField(data`P); N:=data`N;
  if bad1 or bad2 then
    eP1:=1; eP2:=1; // ramification index of x at (the very bad point of) the disc; =1 for good points
    if bad1 then
      eP1:=local_data(P1,data);
    end if;
    if bad2 then
      eP2:=local_data(P2,data);
    end if;
    ePmax:=Maximum(eP1,eP2);
    if e eq 0 then
      e:=2*q*ePmax+1;
      if verbose then
        printf "coleman_integrals_on_basis: autocomputed e = %o.\n", e;
      end if;
    elif e le q*ePmax then
      print "WARNING: supplied e =",e,"is unsuitable (need e >",q*ePmax,"strictly); using e =",2*q*ePmax+1,"instead";
      e:=2*q*ePmax+1;
    end if;
    // Predict the precision loss at the near-boundary points: the f-lists are stored
    // to precision N only, and evaluating the 1/r-powers at S with v_K(r(S))=eP/e
    // amplifies the coefficient error by maxpole*eP/e digits, where maxpole=j_0-1 is the
    // a priori pole order of the f_{i,0} in z=r that the certified precision of
    // evalf0_list uses. The run-time optimal e=2*q*eP+1 thus trades
    // about half the digits for tiny integrals that are shorter by a factor ~maxpole/(2*q);
    // for (almost) all N digits one needs e about maxpole*eP, or a larger N in coleman_data.
    maxpole:=f0_pole_bound(data)-1;
    eloss:=Ceiling(maxpole*ePmax/e);
    if eloss gt 1 then
      print "NOTE: with e =",e,"expect about",Maximum(N-eloss,0),"correct digits (evaluation loss about",eloss,"digits); for about",N-1,"digits use e =",maxpole*ePmax,"(slower tiny integrals) or increase N";
    end if;
  elif e eq 0 then
    e:=1;
  end if;
  return e;

end function;


very_bad_point_with_expansions:=function(Pt,e,data)

  // The very bad point S of the residue disc of the bad point Pt (find_bad_point_in_disc),
  // with its local expansions attached to the t-adic precision tadicprec(data,e), and data
  // with the minimal polynomials of S cached (update_minpolys).

  S:=find_bad_point_in_disc(Pt,data);
  _,index:=local_data(S,data);
  data:=update_minpolys(data,S`inf,index);
  S`xt,S`bt,S`index:=local_coord(S,tadicprec(data,e),data);
  return S, data;

end function;


solve_frobenius_equation:=function(side1,side2,Ke,data,verbose,ttotal:warn:=true)

  // The Coleman integrals of the basis forms between the endpoints of the two sides (records
  // of coleman_side or coleman_side_direct): the solution J of the Frobenius equation
  //   (Phi - I) J = sum_k C_k (d_k(S1)-d_k(S2)) - tiny(S1 -> F_q S1) + tiny(S2 -> F_q S2)
  // plus tiny(P1 -> S1) - tiny(P2 -> S2), rounded from Ke to K (round_to_K), and the
  // precision Nout to which it is correct (algorithm "Non-tiny integrals on basis").
  // Input:   Ke the auxiliary field of the sides; verbose, ttotal for the timings; warn: print
  //          the warning on the precision loss if p divides #J of the reduction.

  F:=data`F; basis:=data`basis; N:=data`N; K:=data`K; m:=data`m; L:=data`L;

  KeC:=((side1`bad and not side1`direct) or (side2`bad and not side2`direct)) select Ke else K; // the field the combined vectors live in

  // Combine the two sides: I = sum_k C_k (d_k(S1)-d_k(S2)) - tiny(S1->F_q S1) + tiny(S2->F_q S2)

  I:=[];
  for i:=1 to #basis do
    Ni:=Minimum([side1`Ndk[i],side2`Ndk[i],side1`NStoFS,side2`NStoFS]);
    I[i]:=(KeC!side1`Itot[i])-(KeC!side2`Itot[i])-(KeC!side1`tinyStoFS[i])+(KeC!side2`tinyStoFS[i]);
    I[i]:=change_abs_precision(I[i],Integers()!(Degree(KeC,K)*Ni)); // change to the absolute precision Ni for entry i (kept per entry, so that high-valuation entries of (F-I)^(-1) can be exploited in the solve)
  end for;


  t:=Cputime();
  mat:=(F-IdentityMatrix(L,#basis)); // notice that absolute precision of F is N
  mat:=ChangeRing(mat,m); // the relative precision may be more than N (the working precision is Nmax>N)
  mat,Nmat:=change_abs_precision_mat(mat,N); // change to absolute precision N for matrix
  if Nmat lt N then
    print "NOTE: the Frobenius matrix carries only",Nmat,"digits of absolute precision (N =",N,
          "); the precision reported for the integral is reduced accordingly";
  end if;
  vdet:=Valuation(Determinant(mat));
  if vdet gt 0 and warn then
    // det(F-I)=+-P(1)=+-#Jac_X(F_q) (P = characteristic polynomial of Frobenius on H^1),
    // so vdet=e_K*v_p(#Jac_X(F_q)) is known in advance from the zeta function of the
    // reduction; inverting F-I then loses 2*vdet digits of precision. If possible,
    // choose a prime with p not dividing #Jac_X(F_q), or increase N by 2*vdet.
    print "WARNING: det(F-I) has positive valuation",vdet,"(p divides #Jac of the reduction); expect a precision loss of",2*vdet,"digits in the final linear solve";
  end if;
  matinv:=mat^-1;

  IS1S2:=Vector(I)*Transpose(ChangeRing(matinv,KeC));    // Solve the linear system.

  // cheap sanity check: the solution must satisfy the linear system (F-I)*J = I to the
  // working precision. This is a single matrix-vector product (negligible next to the
  // inversion) and catches errors in the assembly of the right-hand side I or in the
  // inversion/precision of F-I; a correct solve leaves only the precision-truncation,
  // which is weakly zero.
  residual:=IS1S2*Transpose(ChangeRing(mat,KeC))-Vector(I);
  if not &and[IsWeaklyZero(c):c in Eltseq(residual)] then
    vres:=Minimum([Valuation(c):c in Eltseq(residual)]);
    print "WARNING (sanity): the Coleman integral does not satisfy the Frobenius linear system (F-I)*J = I to precision (residual valuation",vres,"); the result may be wrong";
  end if;

  IP1P2:=IS1S2+ChangeRing(side1`tinyPtoS,KeC)-ChangeRing(side2`tinyPtoS,KeC);  // value in Ke, should be in K (all values are correct, magma will choose the best precision)

  IP1P2,remval:=round_to_K(IP1P2,K); // value in K; remval = v_K to which the auxiliary ramified part cancelled (Infinity if fully)

  if verbose then
    printf "coleman_integrals_on_basis: linear solve: %o s\n", Cputime(t);
    printf "coleman_integrals_on_basis: total time: %o s\n", Cputime(ttotal);
  end if;

  Nout:=Minimum([AbsolutePrecision(a):a in Eltseq(IP1P2)]);
  // Never report more correct digits than the auxiliary ramified data delivered.
  // The answer is assembled over Ke=K(pi^(1/e)); its u^0 component carries a per-entry
  // AbsolutePrecision ~ N, but the u^1..u^(e-1) directions (which must vanish) only
  // cancel to v_K=remval, a fixed quantity independent of N and e. Cap there.
  if Type(remval) ne Infty and remval lt Nout then
    Nout:=Floor(remval);
  end if;
  if Nout le 0 then
    print "WARNING: no correct digits remain in the Coleman integrals (precision",Nout,"); increase N";
  end if;

  return IP1P2, Nout;

end function;


as_point:=function(Pt,data,fname)

  // A point argument of a user-facing function fname: a point record (set_point,
  // set_bad_point), or a pair [x0,y0] of coordinates of a good point of the plane model,
  // converted by set_point.

  if Type(Pt) eq Rec then
    return Pt;
  end if;
  if Type(Pt) in {SeqEnum,Tup,List} and #Pt eq 2 then
    return set_point(Pt[1],Pt[2],data);
  end if;
  error Sprintf("%o: a point must be a point record (set_point, set_bad_point) or a pair [x0, y0] of coordinates of a good point of the plane model",fname);

end function;


coleman_integrals_on_basis:=function(P1,P2,data:e:=0,verbose:=true,side1:=0,return_side:=false,direct_inf:=false,target:=0,warn:=true)

  // The Coleman integrals of the basis forms from P1 to P2 (algorithm "Non-tiny integrals on
  // basis").
  //
  // Input:  P1, P2  points over K (set_point, set_bad_point): points of U, bad points or
  //                 infinite points; a pair [x0,y0] stands for set_point(x0,y0,data),
  //         data    the output of coleman_data.
  // Output: the vector (int_P1^P2 omega_i)_i over K, i = 1..2g (the basis data`basis), and
  //         its absolute precision Nout (an integer, a lower bound for the number of correct
  //         digits of every entry).
  //
  // Options:
  //   e          the ramification index of the auxiliary totally ramified extension
  //              K(pi^(1/e)) of the points near the boundary. For an endpoint in a bad
  //              residue disc with ramification index eP (of x at the very bad point of the
  //              disc) the point S near the boundary has v_K(r(S)) = eP/e, and correctness
  //              requires e > q*eP. Default (e = 0): e = 2*q*eP+1, which is run-time optimal
  //              (it keeps Nmax about 2*N instead of about (q*eP+1)*N for e = q*eP+1).
  //   verbose    print progress and the timings of the individual steps.
  //   return_side, side1
  //              with return_side := true the part of the computation that depends on P1
  //              only is returned as a third value; passed back as side1 it is reused for
  //              further integrals from the same base point P1 (as in the solver), which
  //              roughly halves their cost. The cached side fixes e and Ke.
  //   direct_inf use infinite endpoints without the extension K(pi^(1/e))
  //              (coleman_side_direct): an infinite point that is not very infinite is
  //              suitable, a very infinite one is replaced by the K-rational point t = pi of
  //              its disc. This saves the auxiliary extension but loses about q*(m-1) digits,
  //              m the pole order of the basis forms at the point at infinity; q-power lift
  //              only.
  //   target     the precision wanted (default 0: none): if the result is less precise and
  //              an endpoint uses a point near the boundary over K(pi^(1/e)), whose
  //              evaluation loses about j_0*e_P/e digits (see the note printed for e), the
  //              integrals are recomputed with e = 2e+1, up to e = (j_0-1)*e_P+1, beyond which
  //              a larger e gains nothing; otherwise a larger N in coleman_data is needed.
  //   warn       print the warning that p divides #J of the reduction, so that the linear
  //              solve loses digits (det(F-I) has positive valuation); false for a caller
  //              that computes many integrals with the same data and warns once itself.
  //
  // Method: a bad endpoint that is not very bad is first replaced by the very bad point of
  // its disc (plus a tiny integral). Each endpoint P_j gives a point S_j (P_j itself if good,
  // a suitable point near the boundary otherwise; coleman_side), and the integrals J from S1
  // to S2 solve the Frobenius equation (matrices of F_tau^* and F_q^* on cohomology)
  //   (Phi - I) J = sum_k C_k (d_k(S1) - d_k(S2)) - tiny(S1 -> F_q S1) + tiny(S2 -> F_q S2),
  // where Phi = data`F, C_k = data`Clist[k+1] and d_k are the values of the twisted primitives
  // f_{tau,i} at F_tau^k(S_j), k = 0..ntau-1 (for the q-power lift: ntau = 1 and C_0 = I).
  // Finally int_P1^P2 = tiny(P1 -> S1) + J - tiny(P2 -> S2), rounded from Ke to K.

  if not (Type(e) eq RngIntElt and e ge 0) then
    error "coleman_integrals_on_basis: the option e must be a nonnegative integer (0: chosen automatically)";
  end if;
  P1:=point_to_K(as_point(P1,data,"coleman_integrals_on_basis"),data`K); // guard against points over different-precision copies of K (e.g. from Qq_points)
  P2:=point_to_K(as_point(P2,data,"coleman_integrals_on_basis"),data`K);
  F:=data`F; basis:=data`basis; N:=data`N;
  K:=data`K; m:=data`m; pi:=data`pi; L:=data`L;
  q:=#ResidueClassField(data`P);
  ttotal:=Cputime();

  // Frobenius lift data (q-power lift if the record predates the p-power lift)
  qtau:=(assigned data`qtau) select data`qtau else q;
  ntau:=(assigned data`ntau) select data`ntau else 1;
  Clist:=(assigned data`Clist) select data`Clist else [IdentityMatrix(L,#basis)];
  mks:=twisted_maps(data); // the twisted coefficient maps m o tau_L^k, k = 0..ntau

  // Endpoints handled by the direct route (option direct_inf, or a cached direct side)
  direct1:=false; direct2:=false;
  if direct_inf and (P1`inf or P2`inf) then
    if ntau eq 1 then
      direct1:=P1`inf; direct2:=P2`inf;
    else
      print "NOTE: direct_inf needs the q-power Frobenius lift (coleman_data(...:lift:=\"q\")); using near-boundary points instead";
    end if;
  end if;
  if Type(side1) eq Rec then
    direct1:=assigned side1`direct and side1`direct;
  end if;
  bad1:=is_bad(P1,data) and not direct1; // endpoints that need a near-boundary point over Ke
  bad2:=is_bad(P2,data) and not direct2;

  // A cached side fixes e (and Ke); check that it is still suitable for P2: e > q*e_P2 for
  // correctness, and, if e is chosen automatically (e = 0), at least the value 2*q*e_P2+1 that
  // the choice for P2 gives (a smaller e is correct but loses more digits, about
  // j_0*e_P2/e; cf. auxiliary_e)
  if Type(side1) eq Rec and not direct1 then
    eP2:=bad2 select local_data(P2,data) else 1;
    if bad2 and (side1`e le q*eP2 or (e eq 0 and side1`e lt 2*q*eP2+1)) then
      if verbose then
        print "coleman_integrals_on_basis: the cached base point data has a smaller e than P2 needs; recomputing without the cache.";
      end if;
      side1:=0;
    else
      e:=side1`e;
    end if;
  end if;

  // Determine a suitable e
  if Type(side1) ne Rec or direct1 then
    e:=auxiliary_e(e,P1,P2,bad1,bad2,data,verbose);
  end if;

  // First make sure that if P1 or P2 is bad (and not on the direct route), then it is very bad

  if bad1 and not is_very_bad(P1,data) then
    if verbose then
      print "coleman_integrals_on_basis: P1 is bad but not very bad, replacing it by the very bad point of its disc.";
    end if;
    S1,data:=very_bad_point_with_expansions(P1,e,data);
    IS1P1,NIS1P1:=tiny_integrals_on_basis(S1,P1,data); // value in K; t-adic precision chosen automatically
    IS1P2,NIS1P2:=$$(S1,P2,data:e:=e,verbose:=verbose,direct_inf:=direct_inf,target:=target);
    IP1P2:=IS1P2-IS1P1;
    NIP1P2:=Ceiling(Minimum([NIS1P1,NIS1P2]));
    if return_side then
      return IP1P2,NIP1P2,0; // the basepoint was replaced, so no reusable side data for P1
    end if;
    return IP1P2,NIP1P2;
  end if;

  if bad2 and not is_very_bad(P2,data) then
    if verbose then
      print "coleman_integrals_on_basis: P2 is bad but not very bad, replacing it by the very bad point of its disc.";
    end if;
    S2,data:=very_bad_point_with_expansions(P2,e,data);
    IP1S2,NIP1S2,side1:=$$(P1,S2,data:e:=e,verbose:=verbose,side1:=side1,return_side:=true,direct_inf:=direct_inf,target:=target);
    IP2S2,NIP2S2:=tiny_integrals_on_basis(P2,S2,data); // t-adic precision chosen automatically
    IP1P2:=IP1S2-IP2S2;
    NIP1P2:=Ceiling(Minimum([NIP1S2,NIP2S2]));
    if return_side then
      return IP1P2,NIP1P2,side1;
    end if;
    return IP1P2,NIP1P2;
  end if;

  // If P1,P2 is bad (hence very bad) or good, use a near boundary point over Ke; infinite
  // endpoints on the direct route are handled over K by coleman_side_direct.
  // (the minimal polynomials for each endpoint are updated inside coleman_side)

  if Type(side1) eq Rec and not direct1 then
    Ke:=side1`Ke; // the cached side fixes the auxiliary field
  else
    Ka<u>:=PolynomialRing(K);
    Ke<u>:=TotallyRamifiedExtension(K,u^e-pi);
  end if;
  if Type(side1) ne Rec then
    if direct1 then
      side1:=coleman_side_direct(P1,data:verbose:=verbose);
    else
      side1:=coleman_side(P1,data,e,Ke,mks,qtau,ntau,Clist:verbose:=verbose);
    end if;
  end if;
  if direct2 then
    side2:=coleman_side_direct(P2,data:verbose:=verbose);
  else
    side2:=coleman_side(P2,data,e,Ke,mks,qtau,ntau,Clist:verbose:=verbose);
  end if;

  IP1P2,Nout:=solve_frobenius_equation(side1,side2,Ke,data,verbose,ttotal:warn:=warn);

  // the option target: a larger e for the points near the boundary
  if target gt 0 and Nout lt target and ((side1`bad and not side1`direct) or (side2`bad and not side2`direct)) then
    ePmax:=Maximum([1] cat [local_data(Pt,data):Pt in [P1,P2]|is_bad(Pt,data)]);
    ecap:=(f0_pole_bound(data)-1)*ePmax+1;
    if e lt ecap then
      enew:=Minimum(2*e+1,ecap);
      if verbose then
        printf "coleman_integrals_on_basis: precision %o < target %o; recomputing with e = %o.\n", Nout, target, enew;
      end if;
      return $$(P1,P2,data:e:=enew,verbose:=verbose,return_side:=return_side,direct_inf:=direct_inf,target:=target,warn:=warn);
    end if;
  end if;

  if return_side then
    return IP1P2, Nout, side1;
  end if;
  return IP1P2, Nout;
end function;


holomorphic_integrals_weakly_zero:=function(IP1P2,data)

  // Diagnostic for torsion endpoints.
  //
  // Input:  IP1P2  a vector of integrals int_P1^P2 omega_i returned by
  //                coleman_integrals_on_basis.
  // Output: true iff its first g entries are weakly zero.
  //
  // The first g basis forms are holomorphic (basis_coho), and their integrals are the
  // coordinates of the p-adic logarithm of the class of P2 - P1 in the Jacobian. They vanish
  // iff the class is torsion, so for torsion classes the result must be true.

  g:=data`g;
  return &and[IsWeaklyZero(IP1P2[i]):i in [1..g]];
end function;


local_expansions_consistent:=function(Pt,prec,data:index:=-1)

  // Diagnostic for the local expansions at a point Pt (local_coord; index as there).
  //
  // Input:  Pt a point record, prec the t-adic precision of the expansions.
  // Output: whether the expansions satisfy the equations of the model modulo pi^NK
  //         (NK = Precision(K)), and the smallest t-adic absolute precision to which these
  //         equations are known (the poles of x and y at an infinite point cost t-adic
  //         precision).
  //
  // The expansions x(t) (resp. 1/x(t) if Pt is infinite) and b(t) (b = b^0, resp. b^inf) are
  // computed independently, each from its own minimal polynomial (at a good point from the
  // plane model). They belong to Pt iff Y = W^(-1)(x(t))*b(t) satisfies Y = (1,y,...,y^(d-1))
  // and Q(x(t),y) = 0 for y = Y[2] (W = W0, resp. Winf); these are the d+1 series checked. The
  // series arithmetic is done over OK/pi^NK, as in tiny_integrals_on_basis: over K the inexact
  // zero 1/x(P) = O(pi^NK) of an infinite point would make 1/(1/x(P)+t) meaningless.

  Q:=data`Q; K:=data`K; m:=data`m; d:=Degree(Q);
  xt,bt:=local_coord(Pt,prec,data:index:=index);
  OK:=RingOfIntegers(K);
  Oq:=quo<OK|UniformizingElement(K)^Precision(K)>;
  St:=LaurentSeriesRing(Oq,prec);
  xS:=series_K_to_Oq(xt,St,OK);
  bS:=[series_K_to_Oq(bt[i],St,OK):i in [1..d]];
  if Pt`inf then
    xS:=1/xS;
    Winv:=data`Winf^(-1);
  else
    Winv:=data`W0^(-1);
  end if;
  Y:=[&+[fracL_eval_Oq(Winv[i,j],m,OK,xS)*bS[j]:j in [1..d]]:i in [1..d]];
  res:=[Y[1]-1] cat [Y[k]-Y[2]^(k-1):k in [3..d]] cat [&+[polL_eval_Oq(Coefficient(Q,i),m,OK,xS)*Y[2]^i:i in [0..d]]];
  return &and[IsWeaklyZero(s):s in res], Minimum([AbsolutePrecision(s):s in res]);

end function;



coleman_integral:=function(P1,P2,dif,data:IP1P2:=0,NIP1P2:=0,direct_inf:=false)

  // The Coleman integral of a 1-form from P1 to P2 (algorithm "Integrals in general"): of the
  // second kind, or, with data for a basis of H^1_dR(U) (coleman_data(...: useU := true)), of
  // the third kind with poles at points of X - U (the points above the zeros of r and above
  // x = infinity); the logarithms are on Iwasawa's branch log(p) = 0 (log_iwasawa).
  //
  // Input:  P1, P2  points over K that are not very bad (the primitives f_0, f_inf, f_end of
  //                 dif can have poles at the very bad points); a pair [x0,y0] stands for
  //                 set_point(x0,y0,data),
  //         dif     the form sum_i dif[i]*b^0_i dx/z, z = r/lc(r): a sequence or vector of d
  //                 polynomials in x over L (or over Q), like the entries of data`basis (of
  //                 the second kind on U, or of the third kind as above),
  //         data    the output of coleman_data.
  // Output: int_P1^P2 dif in K and its absolute precision.
  //
  // Options: IP1P2, NIP1P2  the integrals of the basis forms from P1 to P2 and their
  //          precision (coleman_integrals_on_basis), if already known; direct_inf as there.
  //
  // Method: reduce_with_fs writes dif = d(f_0) + d(f_inf) + d(f_end) + sum_i c_i omega_i, so
  //   int_P1^P2 dif = f(P2) - f(P1) + sum_i c_i int_P1^P2 omega_i,  f = f_0 + f_inf + f_end.
  // The reduction runs over the field of the reduction data: L, or Q in the rational branch
  // of coleman_data, where a form with coefficients in L is split into its rational
  // coordinates w.r.t. the power basis of L.
  // Precision: dif has at most simple poles above the zeros of r, so the finite reduction
  // does nothing (f_0 = 0). The reduction runs modulo pi^Nmax; by the propositions on the
  // infinite and on the final reduction it loses e_K*floor(log_p(mu*e_inf)) + c_end digits,
  // mu = -ord_inf(w) - deg(r) + 1 for the coefficients w of dif w.r.t. b^inf (and for
  // coefficients of valuation v < 0 the form pi^(-v)*dif is the integral one). So c_i,
  // f_inf and f_end are correct to the precision Ncoef = Nmax + min(v,0) - loss, and their
  // values at the points are evaluated with Ncoef in place of N if it is smaller.

  Q:=data`Q; L:=data`L; K:=data`K; m:=data`m; d:=Degree(Q);
  P1:=as_point(P1,data,"coleman_integral"); P2:=as_point(P2,data,"coleman_integral");
  if not (Type(dif) in {SeqEnum,ModTupRngElt,ModTupFldElt} and #Eltseq(dif) eq d) then
    error Sprintf("coleman_integral: dif must be a sequence of %o polynomials in x (the coefficients of the form w.r.t. b^0 dx/z), like the entries of data`basis",d);
  end if;
  for Pt in [P1,P2] do
    if is_very_bad(Pt,data) then
      error "coleman_integral: an endpoint is very bad (x = infinity or r(x) = 0), where the primitive of the form can have a pole; integrate to another point of its residue disc";
    end if;
  end for;

  // the field, prime and working precision of the reduction data
  Lred:=BaseRing(BaseRing(Parent(Q))); // Q in the rational branch, L otherwise
  rational:=Type(Lred) eq FldRat;
  Pred:=rational select data`p else data`P;
  Lx:=PolynomialRing(L);
  difL:=[Lx!dif[i]:i in [1..d]];

  // the components to reduce: dif itself, or its rational coordinates (rational branch)
  if rational then
    n:=Degree(L);
    coord:=func<c,k|Eltseq(L!c)[k]>;
    theta:=[L!1] cat [L.1^(k-1):k in [2..n]]; // the power basis of L
    components:=[<m(theta[k]),[PolynomialRing(Rationals())![coord(c,k):c in Coefficients(w)]:w in difL]>:k in [1..n]];
  else
    components:=[<K!1,difL>];
  end if;

  if NIP1P2 eq 0 then
    IP1P2,NIP1P2:=coleman_integrals_on_basis(P1,P2,data:direct_inf:=direct_inf);
  end if;

  Ired:=K!0; Nred:=Infinity();
  Nwork:=data`Nmaxred*(data`eK div data`eKred); // the working precision of the reduction, in units of v_K
  for comp in components do
    Lxz:=LaurentSeriesRing(PolynomialRing(Lred));
    w:=RSpace(Lxz,d)![Lxz!PolynomialRing(Lred)!c:c in comp[2]]; // polynomials in x as series in z
    if w eq 0 then
      continue;
    end if;
    // the precision Ncoef of the reduction (see the comment at the beginning)
    winf:=change_basis_b0binf(w,Lred,Pred,data`Nmaxred,data`r,data`W0,data`Winf);
    nz:=[i:i in [1..d]|winf[i] ne 0];
    mu:=(#nz eq 0) select 0 else -Minimum([Valuation(winf[i]):i in nz])-Degree(data`r)+1;
    loss:=data`eK*Ilog(data`p,Maximum(1,mu*data`einf))+data`cend;
    vdif:=Minimum([0] cat [Valuation(m(L!c)):c in Coefficients(a),a in comp[2]|c ne 0]);
    Ncoef:=Nwork+vdif-loss;
    dataE:=data;
    dataE`N:=Minimum(data`N,Ncoef); // the precision of the coefficients, for the evaluations
    // the matrices of the infinite reduction up to the level mu (red_lists computes them for
    // the levels of the Frobenius pullbacks)
    redinf:=(mu gt #data`red_list_inf) select infinite_reduction_matrices(data`Ginf,mu) else data`red_list_inf;
    coefs,f0,finf,fend:=reduce_with_fs(w,Q,Lred,Pred,data`N,data`Nmaxred,data`r,data`W0,data`Winf,data`G0,data`Ginf,
                                      data`red_list_fin,redinf,data`basis,data`exact_primitives,data`monomial_to_basis);
    vals:=[]; precs:=[];
    pre:=correction_data_K([f0],[finf],[fend],data,m); // the coefficients in K, for both endpoints
    for Pt in [P1,P2] do
      finfP,NfinfP:=evalfinf(finf,Pt,dataE:pre:=pre`finf[1]);
      fendP,NfendP:=evalfend(fend,Pt,dataE:pre:=pre`fend[1]);
      if forall{i:i in [1..d]|f0[i] eq 0} then // f_0 = 0 (see above): exact
        Append(~vals,finfP+fendP);
        precs cat:=[NfinfP,NfendP];
      else
        f0P,Nf0P:=evalf0(f0,Pt,dataE:pre:=pre);
        Append(~vals,f0P+finfP+fendP);
        precs cat:=[Nf0P,NfinfP,NfendP];
      end if;
    end for;
    Icomp:=vals[2]-vals[1]+&+[m(L!coefs[i])*IP1P2[i]:i in [1..#coefs]];
    // the errors of the c_i (precision Ncoef) times the integrals, and the c_i times the errors
    // of the integrals (precision NIP1P2)
    Ncomp:=Minimum(precs cat [NIP1P2+Valuation(m(L!c)):c in coefs|c ne 0]
                   cat [Ncoef+Minimum([Valuation(IP1P2[i]):i in [1..#coefs]])]);
    Ired+:=comp[1]*Icomp;
    Nred:=Minimum(Nred,Ncomp+Valuation(comp[1]));
  end for;

  if Nred cmpeq Infinity() then // dif = 0
    return K!0, data`N;
  end if;
  Nout:=Ceiling(Nred);
  return Ired+O(Parent(Ired)!data`pi^Nout), Nout;

end function;