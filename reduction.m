// reduction.m -- reduction of differential forms in cohomology, and reduction modulo P^N.
//
// Article: section "Computing a basis of H^1_dR(U)": the proposition on the reduction of a
// cohomology class and the algorithm "Reduction procedure", which writes a form as
//     omega = d(f_0) + d(f_inf) + d(f_end) + sum_i a_i*omega_i
// with omega_i the basis of basis_coho: the finite reduction (coho_red_fin) lowers the pole
// order along the zeros of r, the infinite reduction (coho_red_inf) the pole order at the
// points above infinity, and the final reduction (in reduce_with_fs) expresses the remainder
// in E_0 cap E_inf in the basis. red_lists precomputes the matrices of the reduction steps;
// the precision bounds are in the subsection "Precision bounds for reduction" and in the
// proposition on the precision of the reduction process (section "Precision bounds").
//
// Forms are coefficient vectors w of sum_i w_i b^0_i dx/z (resp. b^inf_i), z = r/lc(r); the
// matrices act on coefficient rows from the right (the transposes of the article's).
// The functions reduce_mod_PN_* replace an element of L (or of a polynomial ring, a series
// ring or a matrix ring over L) by a simpler element congruent to it modulo P^N; this keeps
// the coefficients of the exact arithmetic over L small.
//
// Notation and conventions: see "Conventions and notation" in README.md.

finite_reduction_matrix:=function(L, r, M0, l)

    // The matrix of one finite reduction step at pole order l (article: the matrix M~ of
    // step (1.1) of the algorithm "Reduction procedure").
    // Input:   L a number field; r in L[x] monic and squarefree; M0 = r*G0 in M_d(L[x]);
    //          l an integer that is not an eigenvalue of M0/r' at any zero of r (the
    //          eigenvalues lie in [0,1), so any l >= 1 qualifies).
    // Returns: M' in M_d(L[x]) with entries of degree < deg(r) and
    //          M' = (M0/r' - l*I)^(-1)/r' modulo r.

    d:=NumberOfRows(M0);
    Lx<x>:=PolynomialRing(L);
    assert IsMonic(r);

    R:=quo<Lx|r>;                                     // L[x]/(r)
    r_prime_inv_R:=R!Derivative(r)^-1;                // r' is invertible modulo r: gcd(r,r') = 1
    A:=Matrix(R,d,d,[(R!a)*r_prime_inv_R:a in Eltseq(M0)])-l*IdentityMatrix(R,d); // M0/r' - l*I
    if not IsInvertible(A) then
      error Sprintf("finite_reduction_matrix: M0/r' - %o*I is not invertible modulo r (%o is an eigenvalue of a residue matrix)",l,l);
    end if;
    MPrime:=A^-1*r_prime_inv_R;                       // M' = (M0/r' - l*I)^(-1)/r'
    return Matrix(Lx,d,d,[Lx!a:a in Eltseq(MPrime)]); // lifted to L[x], entries of degree < deg(r)

end function;

reduce_mod_PN_L:=function(f,L,P,N);

  // A simple element of L congruent to f modulo P^N (absolute precision N), i.e. f as an
  // element of L_P modulo P^N.
  // Input:   f in L; P a prime ideal of O_L (or a rational prime p); N an integer.
  // Returns: 0 if v_P(f) >= N; otherwise pi^v times a representative in O_L of the P-unit
  //          u = f/pi^v (v = v_P(f), pi = UniformizingElement(P)) modulo P^(N-v), computed
  //          as the quotient Numerator(u)/Denominator(u) in O_L/P^(N-v).

  OL:=MaximalOrder(L);
  f:=L!f;
  if Type(P) eq RngOrdIdl then
    pi:=UniformizingElement(P); 
  else
    pi:=P;
  end if; 
  
  if f ne 0 then
    ord:=Valuation(f,P);
    if ord ge N then
      f:=0;
    else
      m:=P^(N-ord);
      OLmodm:=quo<OL|m>;
      unit:=f/(pi^ord);  // a P-unit
      f:=OL!((OLmodm!Numerator(unit))/(OLmodm!Denominator(unit))); // the quotient in O_L/P^(N-v)
      f:=pi^ord*(L!f);
    end if;
  end if;
  return f;
end function;


mod_PN_data:=function(denom,L,P,N)

  // For an integer denom with v = v_P(denom) and pi = UniformizingElement(P) (pi = p for a
  // rational prime P = p): the ring O = O_L/P^(N+v), the inverse in O of the P-unit
  // denom/pi^v, and pi^v. Then denom*f modulo P^(N+v), times the inverse, divided by pi^v, is
  // congruent to f modulo P^N (the reduce_mod_PN_* functions below).

  OL:=MaximalOrder(L);
  pi:=(Type(P) eq RngOrdIdl) select UniformizingElement(P) else P;
  ord:=Valuation(L!denom,P);
  O:=quo<OL|P^(N+ord)>;
  return O, (O!(denom/pi^ord))^-1, pi^ord;

end function;


reduce_mod_PN_Lx_cached:=function(f,cache,L,P,N)

  // A simple polynomial in L[x] congruent to f in L[x] coefficientwise modulo P^N, and the
  // associative array cache of the data of mod_PN_data (indexed by the denominator) with the
  // entry used for f added. A loop over many polynomials with few distinct denominators (the
  // reduction steps of coho_red_fin) thus builds each quotient ring and inverse only once:
  // they cost more than the reduction of a polynomial itself.
  // Method:  with D the common integer denominator of the coefficients, v = v_P(D) and
  //          pi = UniformizingElement(P), reduce D*f modulo P^(N+v), multiply by the inverse
  //          of the P-unit D/pi^v modulo P^(N+v), and divide by pi^v.

  if f eq 0 then
    return f, cache;
  end if;
  Lx:=PolynomialRing(L);
  f:=Lx!f;
  denom:=LCM([Denominator(c):c in Coefficients(f)]); // an integer with denom*f in O_L[x]
  if not IsDefined(cache,denom) then
    O,unitinv,ppow:=mod_PN_data(denom,L,P,N);
    cache[denom]:=<O,unitinv,ppow>;
  end if;
  O,unitinv,ppow:=Explode(cache[denom]);
  return Lx!PolynomialRing(MaximalOrder(L))!(unitinv*(PolynomialRing(O)!(f*denom)))/ppow, cache;

end function;


reduce_mod_PN_Lx:=function(f,L,P,N)

  // A simple polynomial in L[x] congruent to f in L[x] coefficientwise modulo P^N
  // (reduce_mod_PN_Lx_cached without a cache).

  g:=reduce_mod_PN_Lx_cached(f,AssociativeArray(Integers()),L,P,N);
  return g;

end function;


reduce_mod_PN_L_mat:=function(A,L,P,N)

  // A simple matrix over L congruent to A entrywise modulo P^N (as reduce_mod_PN_Lx).

  if A eq 0 then
    return A;
  end if;
  A:=ChangeRing(A,L);
  denom:=LCM([Denominator(a):a in Eltseq(A)]);
  O,unitinv,ppow:=mod_PN_data(denom,L,P,N);
  A:=unitinv*ChangeRing(ChangeRing(A*denom,MaximalOrder(L)),O);
  return ChangeRing(ChangeRing(A,MaximalOrder(L)),L)/ppow;

end function;


reduce_mod_PN_Lttinv:=function(f,L,P,N)

  // A simple Laurent series over L congruent to f coefficientwise modulo P^N (as
  // reduce_mod_PN_Lx, applied to the coefficients of f in L((t))).

  if f eq 0 then
    return f;
  end if;
  Lttinv:=Parent(f);
  denom:=LCM([Denominator(c):c in Coefficients(f)]);
  f:=f*denom;
  O,unitinv,ppow:=mod_PN_data(denom,L,P,N);
  OL:=MaximalOrder(L);
  C:=Coefficients(unitinv*Polynomial(ChangeUniverse(ChangeUniverse(Coefficients(f),OL),O)));
  return (Lttinv.1)^Valuation(f)*(Lttinv!ChangeUniverse(ChangeUniverse(C,OL),L))/ppow;

end function;


forward infinite_reduction_matrices; // defined below

red_lists:=function(Q,L,P,q,N,r,W0,Winf,G0,Ginf,e0,einf,J0,Jinf,T0,Tinf,T0inv,Tinfinv,eK,eKfK:qtau:=0)

  // The matrices of all steps of the finite and the infinite reduction of the Frobenius
  // pullbacks F_tau^*(omega_i), computed once and shared by the 2g basis forms (article: the
  // remark after the algorithm "Reduction procedure").
  // Input:   Q, L, P; q = #k(P); N = Nmax, the working precision; r, W0, Winf, G0, Ginf from
  //          coleman_data; eK = e_K and eKfK = e_K*f_K = v_K(q); qtau (optional): the
  //          exponent q_tau of the lift, 0 for the q-power lift (q_tau = q).
  //          (e0, einf, J0, Jinf, T0, Tinf, T0inv, Tinfinv are not used.)
  // Returns: red_list_fin: red_list_fin[l] = (M0/r' - l*I)^(-1)/r' mod r (finite_reduction_matrix)
  //            for the pole orders l = 1, ..., q_tau*(Nmax - v_K(q_tau)) - 1 along r that the
  //            approximation of F_tau^*(omega) modulo pi^Nmax can have (the lemma on the
  //            expansion of F_tau^*(omega) in powers of 1/r);
  //          red_list_inf: red_list_inf[m] = (Ginf_(-1) - m*I)^(-1) for the levels
  //            m = 1, ..., -q_tau*(ord_0(W)+ord_inf(W)+1) - ord_inf(W^(-1)) of the infinite
  //            reduction.

  Lx:=PolynomialRing(L);
  d:=Degree(Q);
  W:=Winf*W0^(-1);
  if qtau eq 0 then // q-power lift (tau=id)
    qtau:=q;
    vqtau:=eKfK; // v_K(q)
    corr:=0;
    // No correction term: with f(i) as in the theorem of section "Effective convergence
    // bounds" (the maximum of the two bounds of Kedlaya, p-adic Differential Equations,
    // Thm 18.3.3 and Rmk 18.3.4), the Thm 18.3.3 term gives f(i) >= 0 whenever
    // v_K(Phi) = v_K(Phi^(-1)) = 0, and f(i) = 0 once v_K(N) >= 0 too (both hold under good
    // reduction). Hence the pole order of the approximation of F_tau^*(omega) modulo pi^N is
    // q*(N-v_K(q))-1, exactly as over Q_p: there is no growth depending on f_K. (The bound of
    // Rmk 18.3.4 alone, which is negative, would suggest an extra term q*eK*(d-1)*(fK-1).)
  else // p-power lift (tau-semilinear, x -> x^p): no correction term either
    vqtau:=eK; // v_K(p)
    corr:=0;
  end if;
  zprec_omega:=qtau*(N-vqtau)-1+corr; // the maximal pole order along r of the approximation of F_tau^*(omega) modulo pi^N (N = Nmax)

  rL:=Lx!r;
  rL:=Numerator(rL/LeadingCoefficient(rL)); // the monic r (= z)

  // finite reduction matrices (M0/r'-l*I)^(-1)/r' mod r, M0 = z*G0, for the pole orders
  // l = 1, ..., zprec_omega

  redlistfin:=[finite_reduction_matrix(L,rL,rL*G0,l):l in [1..zprec_omega]];

  // infinite reduction matrices (Ginf_(-1) - m*I)^(-1), for the levels m (mu in the article)
  // that the reduction of the pullbacks can reach; they scale with q_tau

  redlistinf:=infinite_reduction_matrices(Ginf,-qtau*(ord_0_mat(W)+ord_inf_mat(W)+1)-ord_inf_mat(W^(-1)));

  return redlistfin,redlistinf;

end function;


infinite_reduction_matrices:=function(Ginf,mmax)

  // The matrices (Ginf_(-1) - m*I)^(-1), m = 1, ..., mmax, of the steps of the infinite
  // reduction (red_list_inf of red_lists), Ginf_(-1) the residue matrix of Ginf at infinity.
  // A form whose infinite reduction starts at a level mu needs them up to mmax = mu.

  L:=BaseRing(BaseRing(Ginf)); X:=BaseRing(Ginf).1; d:=NumberOfRows(Ginf);
  D:=-Evaluate((1/X)*Evaluate(Ginf,1/X),0); // Ginf_(-1)
  matrices:=[];
  for m:=1 to mmax do
    D:=D-IdentityMatrix(L,d);
    Append(~matrices,D^(-1));
  end for;
  return matrices;

end function;


convert_to_Lxzzinvd:=function(w,L); 

  // The vector w in S^d, S = (O_L/P^N)[x]((z)) (as returned by frobenius_pullback), lifted
  // to (L[x]((z)))^d: every coefficient in O_L/P^N is replaced by a representative in O_L.

  d:=NumberOfColumns(w);
  OL:=MaximalOrder(L);
  OLx:=PolynomialRing(OL);
  OLxz:=LaurentSeriesRing(OLx);
  OLxzd:=RSpace(OLxz,d);
  Lx<x>:=PolynomialRing(L);
  Lxz<z>:=LaurentSeriesRing(Lx);
  Lxzd:=RSpace(Lxz,d);
  
  return Lxzd!(OLxzd!w);
end function;



val_Lxz_d:=function(v)

  // The z-adic valuation of a vector v in (R[x]((z)))^d: the minimal valuation of its entries.

  val:=Minimum([Valuation(a):a in Eltseq(v)]);
  return val;
end function;


coho_red_fin:=function(w,Q,L,P,N,r,G0,red_list_fin); 

  // Finite reduction: step (1) of the algorithm "Reduction procedure", using part (1) of the
  // proposition on the reduction of a cohomology class.
  // Input:    w in (L[x]((z)))^d, the form omega = sum_i w_i b^0_i dx/z with z = r/lc(r) (the
  //           coefficient of z^(-l) is the article's w_l); Q, L, P; N = Nmax (all coefficients
  //           are reduced modulo P^N on the way); r, G0 from coleman_data (d(b^0) = G0*b^0 dx);
  //           red_list_fin from red_lists.
  // Requires: the pole order l0 of omega along z = 0 is at most #red_list_fin.
  // Returns:  w', f0 with omega = d(sum_i f0_i b^0_i) + sum_i w'_i b^0_i dx/z, where
  //           f0 = sum_{l=1..l0} v_l z^(-l) (the article's f_0) and w' has no negative powers
  //           of z, i.e. at most simple poles above the zeros of r (omega' in E_0).
  // Method:   for l = l0, ..., 1: v_l = w_l*red_list_fin[l] mod z, and
  //           u_l = (w_l - v_l*(M0 - l*z'*I))/z - v_l' with M0 = z*G0 is added to w_(l-1).

  Lx<x>:=PolynomialRing(L);
  Lxz<z>:=LaurentSeriesRing(Lx);
  
  d:=Degree(Q);
  V:=RSpace(Lx,d);
  Lxzd:=RSpace(Lxz,d);

  M:=r*G0; // lc(r)*M0, with r as given

  r:=Lx!r;
  lc_r:=LeadingCoefficient(r);
  r:=Numerator(r/lc_r); // from now on r is the monic z

  f0:=Lxzd!0;
  if forall{i:i in [1..d]|w[i] eq 0} then // w = 0
    return w,f0;
  end if;
  l0:=-val_Lxz_d(w);
  if l0 le 0 then // no negative powers of z: at most simple poles above the zeros of r
    return w,f0;
  end if;

  wcoefs:=[[Lx|Coefficient(w[i],j):j in [-l0..0]]:i in [1..d]]; // the coefficients of z^j, j <= 0

  // Precompute the constant part mat0 = M0 = z*G0 and z' once; the matrix of a reduction
  // step is mat0 - l*z'*I (only the diagonal depends on l), so
  // vvec*(mat0 - l*z'*I) = vvec*mat0 - l*z'*vvec. Reducing the coefficients modulo P^N in
  // every step (reduce_mod_PN_Lx) keeps them small: without it they grow over the ~l0
  // iterations and the number-field arithmetic in this loop dominates the cost of the
  // whole Frobenius matrix. The quotient rings of the reduction are cached (cache).
  cache:=AssociativeArray(Integers());
  reduce_seq:=function(S,cache) // the reductions of the polynomials in S, and the cache
    for k:=1 to #S do
      S[k],cache:=reduce_mod_PN_Lx_cached(S[k],cache,L,P,N);
    end for;
    return S, cache;
  end function;
  mat0,cache:=reduce_seq([Lx!Numerator(a):a in Eltseq(M)],cache);
  mat0,cache:=reduce_seq(Eltseq(Matrix(Lx,d,d,mat0)/lc_r),cache);
  mat0:=Matrix(Lx,d,d,mat0);
  rprime:=Lx!Coefficients(Derivative(r)); // r'
  r,cache:=reduce_mod_PN_Lx_cached(r,cache,L,P,N);

  for l:=l0 to 1 by -1 do
    wvec:=V![wcoefs[i][-l+l0+1]:i in [1..d]]; // w_l, the coefficient vector of z^(-l)
    vvec:=wvec*red_list_fin[l]; // v_l = w_l*M' mod z
    vvec,cache:=reduce_seq([a mod r:a in Eltseq(vvec)],cache);
    vvec:=V!vvec;
    f0+:=Lxzd![(Lxz!vvec[i])*z^(-l):i in [1..d]]; // f_0 += v_l*z^(-l)
    vmat0:=vvec*mat0; // v_l*M0
    // u_l = (w_l - v_l*(M0 - l*z'*I))/z - v_l' (the numerator is divisible by z)
    uvec,cache:=reduce_seq([((wvec[i]-vmat0[i]+l*rprime*vvec[i]) div r)-Derivative(vvec[i]):i in [1..d]],cache);
    for i:=1 to d do
      wcoefs[i][-l+l0+1]:=0; // the term z^(-l) is removed
      wcoefs[i][-l+l0+2]+:=uvec[i]; // and u_l is added to the coefficient of z^(-(l-1))
    end for;
  end for;

  // w': the new coefficient of z^0 and the unchanged positive powers of z
  for i:=1 to d do
    C:=[wcoefs[i][l0+1]];
    if w[i] ne 0 then
      C cat:=[Coefficient(w[i],j):j in [1..Degree(w[i])]];
    end if;
    w[i]:=Lxz!C;
  end for;

  return w,f0;
end function;


substitute_z:=function(f,g,L,P,N);  

  // f(g): the substitution z -> g in f in L[x]((z)) without negative powers of z, exactly
  // over L (the arguments L, P, N are not used).
  // Method:  f is cut into blocks of 4 coefficients, each block evaluated by Horner's rule,
  //          and the blocks are combined pairwise with g^4, g^8, ... (fewer multiplications
  //          of long polynomials than Horner's rule on all of f).

  if f eq 0 then
    return CoefficientRing(Parent(f))!0;
  end if;

  k:=Ceiling((Degree(f)+1)/4);
  h:=[];
  for i:=0 to k-1 do
    h[i+1]:=CoefficientRing(Parent(f))!Coefficient(f,4*i+3); 
    for j:=1 to 3 do
      h[i+1]:=h[i+1]*g+Coefficient(f,4*i+3-j);
    end for;
  end for;
  h[k+1]:=0; // f(g) = (a0+a1*g+a2*g^2+a3*g^3) + g^4*(a4+...+a7*g^3) + ... ; h[i+1] is the i-th block

  gpow:= g^4;

  while k gt 1 do // combine the blocks pairwise: h_new[i] = h[2i] + g^(4*2^s)*h[2i+1]
    h_old:=h;
    h:=[];
    k:=Ceiling(k/2);
    for i:=0 to k-1 do
      h[i+1]:=h_old[2*i+1]+h_old[2*i+2]*gpow;
    end for;
    h[k+1]:=0;
    if k gt 1 then
      gpow:= gpow^2;
    end if;
  end while;
 
  return h[1];
end function;


change_basis_b0binf:=function(w,L,P,N,r,W0,Winf);

  // The change of basis from b^0 to b^inf for the infinite reduction (step (2.1) of the
  // algorithm "Reduction procedure": w~ = W^(-1)*u~ in the article's convention).
  // Input:   w in (L[x]((z)))^d without negative powers of z, the form sum_i w_i b^0_i dx/z;
  //          L, P, N (passed on to substitute_z, unused there); r, W0, Winf.
  // Returns: w' in (L((t)))^d, t = 1/x, with sum_i w_i b^0_i dx/z = sum_i w'_i(t) b^inf_i dx/z:
  //          substitute z = r, write the polynomials in x as Laurent polynomials in t, and
  //          multiply by W^(-1), W = Winf*W0^(-1).

  d:=NumberOfRows(Winf);
  
  Lx:=PolynomialRing(L);
  r:=Lx!r;
  lc_r:=LeadingCoefficient(r);
  r:=Numerator(r/lc_r); 

  Lttinv<t>:=LaurentSeriesRing(L);
  Lttinvd:=RSpace(Lttinv,d);
  
  W:=Winf*W0^(-1);
  Winv:=W^(-1);
  // z = r: a polynomial in x, written as a Laurent polynomial in t = 1/x
  in_t:=func<f|(f eq 0) select Lttinv!0 else t^(-Degree(f))*(Lttinv!Reverse(Coefficients(f)))>;
  return (Lttinvd![in_t(substitute_z(w[i],r,L,P,N)):i in [1..d]])*Evaluate(Winv,t^(-1));
end function;


coho_red_inf:=function(w,Q,L,P,N,r,W0,Winf,Ginf,red_list_inf,qtau);

  // Infinite reduction: step (2) of the algorithm "Reduction procedure", using part (2) of
  // the proposition on the reduction of a cohomology class.
  // Input:    w in (L((t)))^d, t = 1/x, the form omega = sum_i w_i b^inf_i dx/z (from
  //           change_basis_b0binf); Q, L, P; N = Nmax; r, W0, Winf, Ginf from coleman_data;
  //           red_list_inf from red_lists; qtau: the exponent q_tau of the Frobenius lift if
  //           w comes from the approximation modulo P^Nmax of a Frobenius pullback, and 0 for
  //           an arbitrary form.
  // Requires: the levels mu reached are at most #red_list_inf; for qtau > 0 this is checked
  //           through the order bound below.
  // Returns:  w', finf with omega = d(sum_i finf_i b^inf_i) + sum_i w'_i b^inf_i dx/z, where
  //           finf = sum_mu vbar_mu*x^mu (a vector of Laurent series in x; the article's
  //           f_inf) and ord_inf(w') > ord_0(W) - deg(r) + 1, so that the remainder lies in
  //           E_0 cap E_inf.
  // Method:   while mu = -ord_inf(w) - deg(r) + 1 > -(ord_0(W)+1): with c the leading
  //           coefficient vector of w, vbar = -c*(Ginf_(-1) - mu*I)^(-1) (red_list_inf[mu]),
  //           v = vbar*x^mu, and w is replaced by w - z*(v*Ginf + v').
  //           For qtau > 0 the coefficients of w are first reduced modulo P^Nmax, and the order
  //           condition of the proposition on the precision of the reduction process (the
  //           lower bound for ord_inf(u_k^ + u'_k^) in the remark after it) is checked.

  d:=Degree(Q);
  degr:=Degree(r);
  
  Lx:=PolynomialRing(L);
  Lttinv<t>:=LaurentSeriesRing(L);
  Lttinvd:=RSpace(Lttinv,d);
  Ld:=RSpace(L,d);
  Lxxinv<x>:=LaurentSeriesRing(L);
  Lxxinvd:=RSpace(Lxxinv,d);
  
  finf:=Lxxinvd!0;

  // Reduce the b^inf-coefficients modulo P^N (N = Nmax) before the infinite reduction, so that
  // w is the approximation omega^ of F_tau^*(omega) whose coefficients are reduced modulo
  // pi^Nmax (the remark after the proposition on the precision of the reduction process). The
  // pullback is only known modulo pi^Nmax, and the lifts of its residues to L do not preserve
  // the exact cancellations (e.g. after the multiplication by W^(-1) in change_basis_b0binf,
  // or in the last step of the finite reduction, which is truncated modulo pi^Nmax as well):
  // terms of too negative order at infinity survive with coefficients that are nonzero
  // multiples of pi^Nmax, and the infinite reduction would start above the levels covered by
  // h_1 and h_2 in max_prec. E.g. in test2 (p = q = 5, ord_0(W) = -3, ord_inf(W^(-1)) = -4,
  // deg(r) = 9, bound -18, Nmax = 13) the 4th and 5th basis forms would have a t^(-19) term
  // whose coefficient has 5-adic valuation 13 = Nmax, while the genuine leading coefficients
  // have valuation 1 = v(q); and the finite remainder in test3 would be one order worse than
  // the valuation bound for the finite reduction (-15 instead of -14).
  // The exact pullback satisfies the order bound, and the computed w is congruent to it plus
  // the exact remainder of the finite reduction (which satisfies the bound) modulo pi^Nmax,
  // so after the reduction modulo pi^Nmax the bound holds.
  if qtau gt 0 then
    for i:=1 to d do
      w[i]:=reduce_mod_PN_Lttinv(w[i],L,P,N);
    end for;
  end if;

  nonzero:=[i:i in [1..d]|w[i] ne 0];
  if #nonzero eq 0 then
    return w,finf;
  end if;

  Minf:=r*Ginf;

  W:=Winf*W0^(-1);
  ord0W:=ord_0_mat(W);

  r:=Lx!r;
  lc_r:=LeadingCoefficient(r);
  r:=Numerator(r/lc_r); // the monic z
  Minf:=Minf/lc_r;      // z*Ginf

  Minftinv:=Evaluate(Minf,t^(-1)); // z*Ginf as a function of t = 1/x
  rtinv:=Evaluate(r,1/t); // z(1/t)


  valw:=Minimum([Valuation(w[i]):i in nonzero]); // ord_inf(w), the t-adic valuation
  degw:=Maximum([0] cat [Degree(w[i]):i in nonzero]);

  // The order condition of the proposition on the precision of the reduction process for the
  // form entering the infinite reduction (after the reduction modulo P^Nmax above): it
  // guarantees that the infinite reduction starts at a level m <= -min{q_tau*(ord_0(W)+1),
  // ord_inf(W^(-1))+1}, so that it loses at most h_2 digits (max_prec). qtau must be the
  // exponent of the Frobenius lift, not #ResidueClassField(P): in the rational branch the
  // reduction runs over Q_p, where #ResidueClassField(p) = p is too small for the q-power lift
  // with f_K > 1 (e.g. y^2 = x(x-1)(x-2) over Q(sqrt 6), P | 7, f_K = 2 gives ord_inf = -27,
  // which is >= the correct bound -51 for q = 49 but < the bound -9 for q = 7).
  if qtau gt 0 then
    bound:=Minimum(qtau*(ord0W+1),ord_inf_mat(W^(-1))+1)-degr+1;
    if valw lt bound then
      error Sprintf("coho_red_inf: the approximation of the Frobenius pullback has order %o at infinity after the reduction modulo P^Nmax, but the proposition on the precision of the reduction process requires at least %o",valw,bound);
    end if;
  end if;

  wcoefs:=[[L|Coefficient(w[i],j):j in [valw..degw]]:i in [1..d]];

  m0:=-valw-degr+1; // the first level mu

  m:=m0;

  while m gt -(ord0W+1) do // i.e. while ord_inf(w) <= ord_0(W) - deg(r) + 1
    wvec:=Ld![-wcoefs[i][-m+m0+1]:i in [1..d]]; // minus the coefficient of t^(-(m+deg(r)-1)) = x^(m+deg(r)-1)
    vvec:=wvec*red_list_inf[m]; // vbar = -c*(Ginf_(-1) - m*I)^(-1)
    finf+:=Lxxinvd![vvec[i]*x^m:i in [1..d]]; // f_inf += vbar*x^m
    dif:=((Lttinvd!vvec)*t^(-m)*Minftinv)+rtinv*m*t^(1-m)*(Lttinvd!vvec); // z*(v*Ginf + v') with v = vbar*x^m, x = 1/t
    for i:=1 to d do
      C,val:=Coefficients(dif[i]);
      for j:=1 to #C do
        wcoefs[i][j+val-1+m0+degr]-:=C[j]; // w -= z*(v*Ginf + v')
      end for;
      wcoefs[i][-m+m0+1]:=0; // the leading coefficient cancels by construction
    end for;
    m:=m-1;
  end while;

  for i:=1 to d do
    w[i]:=t^(-m0-degr+1)*(Lttinv!wcoefs[i]);
  end for;

  return w,finf;

end function;


change_basis_binfb0:=function(w,L,W0,Winf);

  // The change of basis from b^inf back to b^0, for the remainder of the infinite reduction.
  // Input:   w in (L((t)))^d, t = 1/x, the form sum_i w_i(t) b^inf_i dx/z; L, W0, Winf.
  // Returns: the coefficient vector (a 1 x d matrix over L[x]) of the same form w.r.t.
  //          b^0 dx/z: w*W(1/t), written in x, with the terms of negative degree in x
  //          dropped. For the remainder of the infinite reduction, which lies in
  //          E_0 cap E_inf, the exact coefficients are polynomials in x, so these terms vanish.


  t:=Parent(w[1]).1;
  Lx:=PolynomialRing(L);
  
  W:=Winf*W0^(-1);
  w:=w*Evaluate(W,t^(-1)); // the coordinates w.r.t. b^0, as Laurent series in t
  w:=Evaluate(w,t^(-1));   // t -> 1/t: from now on the series variable stands for x
  for i:=1 to NumberOfColumns(w) do
    temp:=w[1,i];
    if temp ne 0 then
      for j:=Valuation(temp) to -1 do // drop the negative powers of x
        temp:=temp-Coefficient(temp,j)*t^j;
      end for;
    end if;
    w[1,i]:=temp;
  end for;
  w:=Evaluate(w,Lx.1);
  return w;
end function;


reduce_with_fs:=function(dif,Q,L,P,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,exact_primitives,monomial_to_basis:qtau:=0)

    // The algorithm "Reduction procedure": omega = d(f0) + d(finf) + d(fend) + sum_i coefs[i]*omega_i
    // with omega_i the forms of basis.
    // Input:    dif in (L[x]((z)))^d, the form omega = sum_i dif_i b^0_i dx/z (as produced by
    //           frobenius_pullback and convert_to_Lxzzinvd; the reduction steps expect
    //           series in z); Q, L, P; N the target precision and Nmax the working precision;
    //           r, W0, Winf, G0, Ginf, red_list_fin, red_list_inf, basis, exact_primitives,
    //           monomial_to_basis from coleman_data;
    //           qtau (optional): the exponent of the Frobenius lift if dif is the approximation
    //           modulo P^Nmax of a Frobenius pullback (as in frobenius_matrix); then the
    //           b^inf-coefficients are reduced modulo P^Nmax before the infinite reduction and
    //           the order condition is checked (see coho_red_inf). qtau = 0 (default): dif is
    //           reduced as it is.
    // Returns:  coefs: the coordinates of the class of omega w.r.t. basis;
    //           f0 (w.r.t. b^0, a series in z^(-1)), finf (w.r.t. b^inf, a Laurent series in
    //           x), fend (w.r.t. b^0, a polynomial vector): the functions f_0, f_inf, f_end.
    //           For a Frobenius pullback the article's precision bounds apply (f0, finf, fend
    //           and coefs correct modulo pi^N); for other forms the precision is not tracked.
    // Method:   coho_red_fin, change to b^inf, coho_red_inf, change back to b^0, then the final
    //           reduction: the remainder lies in E_0 cap E_inf; its monomial coordinates times
    //           monomial_to_basis give its coordinates in the full basis of E_0, whose first
    //           #basis entries are coefs and whose last #exact_primitives entries are the
    //           coefficients a_j of the exact forms dg_j, so fend = sum_j a_j*g_j.

    d:=Degree(Q); 
    degr:=Degree(r);

    dif,f0:=coho_red_fin(dif,Q,L,P,Nmax,r,G0,red_list_fin); // the reduction runs at Nmax; f0 is correct to precision N
    dif:=change_basis_b0binf(dif,L,P,Nmax,r,W0,Winf);
    dif,finf:=coho_red_inf(dif,Q,L,P,Nmax,r,W0,Winf,Ginf,red_list_inf,qtau);
    dif:=change_basis_binfb0(dif,L,W0,Winf); // now in E_0 cap E_inf

    // final reduction: write the remainder in the basis of E_0

    W:=Winf*W0^(-1);
    ord0W:=ord_0_mat(W);
    ordinfW:=ord_inf_mat(W);

    T:=[Coefficient(dif[1,k],j):j in [0..degr-ord0W-ordinfW-2],k in [1..d]]; // the monomial coordinates (x^j b^0_k dx/z)
    v:=Vector(T)*monomial_to_basis; // the coordinates in the full basis of E_0
    coefs:=[v[j]:j in [1..#basis]];
    // fend = sum_j a_j*g_j w.r.t. b^0, a_j the coordinate of dg_j, at the end of the basis
    n:=NumberOfColumns(monomial_to_basis)-#exact_primitives;
    fend:=&+[Universe(exact_primitives)|v[n+j]*exact_primitives[j]:j in [1..#exact_primitives]];

    return coefs,f0,finf,fend; 

end function;