// frobenius.m -- the Frobenius lift on functions and its pullback of differential forms.
//
// Article: section "Computing a Frobenius lift": the tau-semilinear lift F_tau^* with
// F_tau^*(x) = x^(q_tau), F_tau^*(1/r) = 1/r^tau(x^(q_tau)) and F_tau^*(y) = beta, the root of
// Q^tau(x^(q_tau),beta) = 0 congruent to y^(q_tau) (the proposition on the expression of the
// Frobenius lift), computed by the algorithm "Compute matrix of Frobenius on functions"
// (froblift), and the pullback F_tau^*(omega) of a form (frobenius_pullback, the formula after
// that algorithm). Two cases occur:
//   - the q-power lift: tau = id, q_tau = q = #k(P), n_tau = 1 (also used for ramified K);
//   - the p-power lift: tau the Frobenius automorphism of the unramified K = L_P, q_tau = p,
//     n_tau = f_K; F_q^* = (F_tau^*)^(n_tau). tau is given by a map L -> L: a global
//     automorphism of L (frobenius_aut) or its approximation modulo P^prec (frobenius_aut_local).
//
// The computations take place in R = (O_L/P^N)[x]((z))[y] with z standing for r(x): elements
// of O_L[x,1/r,y]/(Q) are kept "radix reduced", i.e. every coefficient of a power of z has
// x-degree < deg(r) and y-degree < d. Here r is normalised to be monic (r/lc(r) = z of the
// other files, the article's r_mon).
//
// Notation and conventions: see "Conventions and notation" in README.md.

getrings:=function(OL,P,N)

  // The coefficient rings for the Frobenius lift at precision N.
  // Input:   OL = O_L; P a prime ideal of O_L (or a rational prime p); N >= 1.
  // Returns: O = O_L/P^N (= O_K/pi^N), Ox = O[x], S = Ox((z)) (Laurent series in z = r(x)),
  //          R = S[y].

    O:=quo<OL|P^N>;
    Ox<x>:=PolynomialRing(O);
    S<z>:=LaurentSeriesRing(Ox); 
    R<y>:=PolynomialRing(S);
    return O,Ox,S,R;

end function;

radix_reduce:=function(f,r); 

  // The radix-r normal form of f: every coefficient polynomial a(x) of a power z^k with
  // deg(a) >= deg(r) is divided by r, a = c*r + b, and the quotient c is moved to z^(k+1).
  // Input:   f in O[x]((z))[y]; r in O[x] monic (a unit leading coefficient suffices).
  // Returns: f' with the same value as f after substituting z = r(x), and all coefficients
  //          of x-degree < deg(r).

  C:=Coefficients(f); // the coefficients of f, in O[x]((z))
  for i:=1 to #C do
    if C[i] ne 0 then
      v:=Valuation(C[i]);
      D:=Coefficients(C[i]);
      j:=1;
      while j le #D do 
        if Degree(D[j]) ge Degree(r) then
          a,b:=Quotrem(D[j],BaseRing(BaseRing(Parent(f)))!r); 
          D[j]:= b;
          if #D lt j+1 then
            D[j+1]:=a;
          else
            D[j+1]:=D[j+1]+a;
          end if;      
        end if;
        j:=j+1;
      end while;
      C[i]:=(BaseRing(Parent(f)).1)^v*(BaseRing(Parent(f))!D);
    end if;  
  end for;
  return Parent(f)!C; 
end function;


reduce_mod_Q:=function(f,Q,r); 

  // The remainder of f modulo Q (y-degree < deg_y(Q)), in radix-r normal form.
  // Input:   f, Q in O[x]((z))[y], Q monic in y; r in O[x] monic.


  f:=radix_reduce(f,r);
  Q:=radix_reduce(Q,r);

  while Degree(f) ge Degree(Q) do
    f:=f-Coefficient(f,Degree(f))*(Parent(f).1)^(Degree(f)-Degree(Q))*(Parent(f)!Q);
    f:=radix_reduce(f,r);
  end while;
  
  return f;  
end function;


substitute_xq:=function(f,xq,r) 

  // f(x^(q_tau),y): the substitution x -> x^(q_tau) in an element f of R without powers of z.
  // Input:   f in O[x]((z))[y] whose coefficients are polynomials in x (no z); xq the element
  //          x^(q_tau) of R in radix-r normal form (pow_mod_Q(x,q_tau,Q,r)); r monic.
  // Returns: f(xq,y) in radix-r normal form.

  // 1) the degree degxf of f in x

  C:=Coefficients(f);
  degxf:=Maximum([0] cat [Degree(Coefficient(c,0)):c in C|c ne 0]); // f has no z: its coefficients are the z^0 terms

  // 2) the powers xq^k, k <= degxf, in radix-r normal form

  xqpow:=[Parent(f)!1,xq];
  for i:=2 to degxf do
    Append(~xqpow,radix_reduce(xqpow[i]*xq,r));
  end for;

  // 3) substitute them into f

  y:=Parent(f).1;
  out:=Parent(f)!0;
  for i:=1 to #C do
    D:=Coefficients(Coefficient(C[i],0));
    out+:=&+[Parent(f)|D[j]*xqpow[j]:j in [1..#D]]*y^(i-1);
  end for;
  return out;
end function;


pow_mod_Q:=function(f,n,Q,r);

  // f^n in R/(z-r,Q), by binary exponentiation with reductions modulo Q (radix-r normal form).
  // Input:   f in R = O[x]((z))[y]; n >= 0; Q monic in y; r monic.

  if n eq 0 then
    return Parent(f)!1;
  end if;

  digits:=Intseq(n,2);
  f2i:=f;
  
  if digits[1] eq 1 then 
    fpow:=f;
  else
    fpow:=Parent(f)!1;
  end if;

  for i:=2 to #digits do
    f2i:=reduce_mod_Q(f2i*f2i,Q,r);
    if digits[i] eq 1 then
      fpow:=reduce_mod_Q(fpow*f2i,Q,r);
    end if;
  end for;

  return fpow;
  
end function;


twist_pol:=function(f,tau)

  // The coefficient twist f^tau of a polynomial f over O_L or L (article: r^tau, Delta^tau).
  // Input:   tau a field automorphism of L (frobenius_aut) or its approximation tau_N
  //          modulo P^prec (frobenius_aut_local, which maps O_L to O_L); tau = 0 (an
  //          integer) means the identity, and f is returned unchanged.

  if Type(tau) eq RngIntElt then
    return f;
  end if;
  L:=Domain(tau);
  return Parent(f)![tau(L!c):c in Coefficients(f)];
end function;


twist_polxy:=function(f,tau)

  // The coefficient twist f^tau of f in (O_)L[x][y] (article: Q^tau, s^tau); tau as in twist_pol.

  if Type(tau) eq RngIntElt then
    return f;
  end if;
  return Parent(f)![twist_pol(c,tau):c in Coefficients(f)];
end function;


twist_mat:=function(A,tau)

  // The entrywise twist tau(A) of a matrix A over L (article: tau^k(A_tau)); tau as in twist_pol.

  if Type(tau) eq RngIntElt then
    return A;
  end if;
  return Matrix(BaseRing(A),NumberOfRows(A),NumberOfColumns(A),[tau(c):c in Eltseq(A)]);
end function;


frobenius_aut:=function(L,P)

  // A global automorphism of L inducing the Frobenius automorphism tau of K = L_P, for the
  // p-power lift.
  // Input:   L a number field; P an unramified prime ideal of O_L, of residue degree f_K.
  // Returns: an automorphism tau of L with tau(x) = x^p mod P for all x in O_L (so tau(P) = P)
  //          and tau^(f_K) = id, i.e. a generator of the decomposition group at P that
  //          induces the Frobenius on the residue field; such a tau exists e.g. when L/Q is
  //          Galois. Returns 0 if there is none; coleman_data then uses frobenius_aut_local.

  OL:=MaximalOrder(L);
  Fq,mm:=ResidueClassField(P);
  p:=Characteristic(Fq);
  fK:=Degree(Fq);

  for tau in Automorphisms(L) do
    // x -> x^p and x -> tau(x) mod P are both additive (char p), so checking on a Z-basis suffices
    if forall{b:b in Basis(OL)|mm(OL!tau(L!b)) eq mm(OL!b)^p} then
      // require tau^fK = id, so that tau generates the decomposition group at P
      c:=L.1;
      for k:=1 to fK do
        c:=tau(c);
      end for;
      if c eq L.1 then
        return tau;
      end if;
    end if;
  end for;

  return 0;

end function;


frobenius_aut_local:=function(L,P,prec)

  // The Frobenius automorphism tau of K = L_P, as a map L -> L modulo P^prec; used instead of
  // frobenius_aut when no global automorphism of L induces it (e.g. L = Q(2^(1/3)) at an
  // inert prime). A global automorphism is not needed: the p-power lift is computed modulo
  // P^Nmax, O_L/P^N = O_K/p^N for the completion m : L -> K, and tau acts on it.
  // Input:   L a number field; P an unramified prime ideal of O_L; prec >= 1.
  // Returns: a map tau_N : L -> L with
  //              m(tau_N(c)) = tau(m(c)) + O(p^(prec+min(0,v_P(c)))),
  //          computed as c -> m(c) -> tau(m(c)) (FrobeniusImage) -> lift back to L. On
  //          P-integral elements tau_N induces the ring homomorphism O_(P) -> O_L/P^prec
  //          lifting x -> x^p, and the lift is reduced to a representative in O_L, so that
  //          polynomials over O_L stay over O_L. An element with v_P(c) = -j < 0 is scaled
  //          by p^j first; its image then has absolute precision prec-j, which is all that
  //          m(c) carries.
  // Caveats: tau_N is additive and multiplicative, and tau_N^(f_K) is the identity, only
  //          modulo P^prec. Hence (i) prec must be at least the working precision Nmax of
  //          coleman_data, where every use of tau ends up modulo P^Nmax or in K to precision
  //          Nmax, and (ii) tau must not be applied to numerator and denominator of a
  //          rational function separately and the quotient formed in L(x): the approximate
  //          images need no longer cancel. froblift therefore twists the polynomials
  //          r^(-ord_r(W0))*W0[i,j], not W0.

  OL:=MaximalOrder(L);
  p:=Characteristic(ResidueClassField(P));
  K1,m1:=Completion(L,P:Precision:=prec);
  K:=ChangePrecision(K1,prec);
  mK:=m1*Coercion(K1,K);
  O:=quo<OL|P^prec>;

  tauN:=function(c)
    c:=L!c;
    if c eq 0 then
      return L!0;
    end if;
    y:=mK(c);
    j:=Maximum(0,-Valuation(y)); // v_P(c) = v_K(m(c)), since P is unramified
    z:=FrobeniusImage(y*p^j);    // tau(p^j c), integral
    l:=z@@mK;                    // a P-integral element of L
    l:=L!(OL!(O!l));             // its representative in O_L modulo P^prec
    return l/p^j;
  end function;

  return map<L->L|c:->tauN(c)>;

end function;


froblift:=function(Q,P,qtau,N,r,Delta,s,W0:tau:=0);

  // The matrix of the Frobenius lift F_tau^* on functions, w.r.t. the basis b^0/r, modulo P^N
  // (article: the algorithm "Compute matrix of Frobenius on functions").
  // Input:   Q in O_L[x][y], monic in y; P a prime ideal of O_L (or p in the rational branch);
  //          qtau the exponent q_tau of the lift; N the precision; r, Delta, s from auxpolys
  //          (s*dQ/dy = Delta mod Q, r^m = g*Delta for some m); W0 from mat_W0;
  //          tau (optional): the coefficient automorphism, 0 for tau = id (the q-power lift,
  //          qtau = #k(P)); for the p-power lift (qtau = p) frobenius_aut(L,P), or
  //          frobenius_aut_local(L,P,prec) with prec >= N.
  // Returns: mat, a d x d matrix over S = (O_L/P^N)[x]((z)) with
  //            F_tau^*(b^0_i/r) = (b^0_i/r)^tau(x^(q_tau),beta) = sum_j mat[i,j]*b^0_j/r
  //          modulo P^N (row i: the image of the i-th basis function; the transpose of the
  //          article's M). Here r means the monic z = r/lc(r). For the p-power lift all pole
  //          orders are about p*N instead of q*N, the main run-time gain for f_K >= 2.
  // In coleman_data, N = Nmax - v_K(q_tau): the pullback of dx brings the factor q_tau.
  // Method:  (1) Newton iteration for alpha = F_tau^*(1/r) = 1/r^tau(x^(q_tau)) and
  //          beta = F_tau^*(y) (the proposition on the expression of the Frobenius lift; the
  //          precision doubles in every step); (2) the matrix w.r.t. 1/r, y/r, ...,
  //          y^(d-1)/r, from F_tau^*(y^i/r) = beta*F_tau^*(y^(i-1)/r); (3) the change to b^0/r:
  //          mat = F_tau^*(W0)*mat_y*W0^(-1), the transpose of (W^0)^(-1)*M~*(W^0)^tau(x^(q_tau)).

  // 1) the images of 1/r and y under the lift, in R

  L:=BaseRing(Coefficients(Q)[1]);
  OL:=MaximalOrder(L);
  OLx<x>:=PolynomialRing(OL);
  OLxy<y>:=PolynomialRing(OLx);
  Q:=OLxy!Q;
  s:=OLxy!s;
  r:=OLx!r;
  Delta:=OLx!Delta;

  // the tau-twists of the defining data, which enter the images under F_tau^*; the
  // reduction ring O[x]((z))/(z-r,Q) always uses the untwisted r and Q. W0 is twisted in
  // step 3) below, through the polynomials r^(-ord_r(W0))*W0[i,j].
  Qtau:=twist_polxy(Q,tau);
  stau:=twist_polxy(s,tau);
  rtau:=twist_pol(r,tau);
  Deltatau:=twist_pol(Delta,tau);

  O,Ox,S,R:=getrings(OL,P,N);
  x:=Ox.1; y:=R.1; z:=S.1;

  d:=Degree(Q);

  over_R:=func<f|R![Ox!c:c in Coefficients(f)]>; // a polynomial over O_L[x] in y, as an element of R
  Q:=over_R(Q);
  QtauR:=over_R(Qtau);

  rLx:=Parent(Numerator(W0[1,1]))!r;
  rLx:=rLx/LeadingCoefficient(rLx); // the monic r in L[x], for ord_r of W0 and W0^(-1)

  r:=(Ox!Coefficients(r));
  Delta:=(Ox!Coefficients(Delta));
  rtau:=(Ox!Coefficients(rtau));
  Deltatau:=(Ox!Coefficients(Deltatau));

  s:=over_R(s);
  stauR:=over_R(stau);
  lc:=LeadingCoefficient(r);
  r:=r/lc; // make r monic (and keep s*dQ/dy = Delta)
  s:=s/lc;
  Delta:=Delta/lc;
  lctau:=LeadingCoefficient(rtau);
  rtau:=rtau/lctau;
  stauR:=stauR/lctau;
  Deltatau:=Deltatau/lctau;

  cnt:=1; // m in the article: the least m with r^m = g*Delta
  while (r^cnt mod Delta ne 0) do
    cnt:=cnt+1;
  end while;
  g:=r^cnt div Delta;
  gtau:=rtau^cnt div Deltatau; // the tau-twist of g

  // Newton iteration (article: the proof of the proposition on the expression of the
  // Frobenius lift): alpha_n = alpha_(n-1)*(2 - r^tau(x^q)*alpha_(n-1)) and
  // beta_n = beta_(n-1) - Q^tau(x^q,beta)*s^tau(x^q,beta)*g^tau(x^q)*alpha^m, starting from
  // alpha_0 = 1/r^q, beta_0 = y^q (q = q_tau). Each step doubles the P-adic precision, so the
  // steps are run at the precisions ..., ceil(N/4), ceil(N/2), N.

  prec:=[];
  k:=N;
  while k gt 1 do
    Append(~prec,k);
    k:=Ceiling(k/2);
  end while;
  prec:=Reverse(prec);

  alpha:=R!(z^(-qtau));
  beta:=pow_mod_Q(y,qtau,Q,r);
  xq:=pow_mod_Q(R!x,qtau,Q,r);

  // the most expensive part of the Frobenius lift over a number field
  for i:=1 to #prec do
    Oi,Oxi,Si,Ri:=getrings(OL,P,prec[i]);
    xqi:=Ri!xq;
    rxq:=substitute_xq(Ri!(Oxi!rtau),xqi,r);
    alpha:=(Ri!alpha);
    alpha:=radix_reduce(alpha*radix_reduce(2-alpha*rxq,r),r); // alpha -> F_tau^*(1/r) = 1/r^tau(x^q)

    alpha_power:=alpha;
    for j:=2 to cnt do
      alpha_power:=radix_reduce(alpha_power*alpha,r);
    end for;
    gxq:=substitute_xq(Ri!(Oxi!gtau),xqi,r);
    alpha1:=radix_reduce(gxq*alpha_power,r); // F_tau^*(1/Delta) = g^tau(x^q)*alpha^m

    powers:=[Ri!1]; // beta^(j-1)
    for j:=2 to d+1 do
      Append(~powers,reduce_mod_Q((Ri!beta)*powers[j-1],Q,r));
    end for;

    Qxq:=substitute_xq(Ri!QtauR,xqi,r);
    sxq:=substitute_xq(Ri!stauR,xqi,r);
    evalQxq:=radix_reduce(&+[Ri|Coefficient(Qxq,j)*powers[j+1]:j in [0..d]],r); // Q^tau(x^q,beta)
    evalsxq:=radix_reduce(&+[Ri|Coefficient(sxq,j)*powers[j+1]:j in [0..Degree(stauR)]],r); // s^tau(x^q,beta)

    beta:=(Ri!beta);
    beta:=radix_reduce(beta-reduce_mod_Q(radix_reduce(evalQxq*evalsxq,r),Q,r)*(Ri!alpha1),r); // beta -> F_tau^*(y), the root of Q^tau(x^q,.)

  end for;

  // At this point alpha*r^tau(x^q) = 1, alpha1*Delta^tau(x^q) = 1 and Q^tau(x^q,beta) = 0
  // modulo P^N; these identities are not tested here (it would be slow).

  alpha:=(R!alpha);
  beta:=(R!beta);

  // 2) the matrix mat_y with F_tau^*(y^(i-1)/r) = sum_j mat_y[i,j]*y^(j-1)/r (rows)

  rows:=[z*alpha]; // r*F_tau^*(1/r)
  for i:=2 to d do
    Append(~rows,reduce_mod_Q(beta*rows[i-1],Q,r)); // r*F_tau^*(y^(i-1)/r) = beta*(r*F_tau^*(y^(i-2)/r))
  end for;
  mat:=Matrix(S,d,d,[Coefficient(rows[i],j-1):j in [1..d],i in [1..d]]);

  // 3) the matrix w.r.t. b^0/r: F_tau^*(W0)*mat_y*W0^(-1), with W0 and its inverse written
  //    over S (a power of r in their denominators becomes a power of z)

  over_S:=func<a|Coefficient(radix_reduce(R!a,r),0)>; // an element of R without y, in radix-r normal form in S
  normal_form:=func<M|Matrix(S,d,d,[over_S(a):a in Eltseq(M)])>;
  rW:=BaseRing(W0)!rLx;

  W0inv:=W0^(-1);
  ordrW0inv:=ord_r_mat(W0inv,rLx);
  W0invS:=Matrix(S,d,d,[over_S(z^ordrW0inv*(Ox!Numerator(rW^(-ordrW0inv)*a))):a in Eltseq(W0inv)]); // W0^(-1) over S: r^ord * (polynomial)
  mat:=normal_form(mat*W0invS); // mat_y*W0^(-1)

  // W0[i,j] = r^ord_r(W0) * W0num with the POLYNOMIAL W0num, so
  // F_tau^*(W0[i,j]) = alpha^(-ord_r(W0)) * W0num^tau(x^q): tau is applied to the polynomial
  // only. Twisting numerator and denominator of W0[i,j] separately is exact only for a
  // global automorphism (for frobenius_aut_local the twisted denominator would no longer
  // divide). The power of 1/r in W0 becomes a power of alpha.
  ordrW0:=ord_r_mat(W0,rLx);
  alphapow:=pow_mod_Q(alpha,-ordrW0,Q,r);
  FqW0S:=Matrix(S,d,d,[over_S(alphapow*substitute_xq(R!(Ox!twist_pol(Numerator(rW^(-ordrW0)*a),tau)),xq,r)):a in Eltseq(W0)]);
  mat:=normal_form(FqW0S*mat); // F_tau^*(W0)*mat_y*W0^(-1)

  return mat; // F_tau^*(b^0_i/r) = sum_j mat[i,j]*b^0_j/r modulo P^N

end function;


frobenius_pullback:=function(w,Q,P,qtau,N,r,frobmatb0r:tau:=0)

  // The pullback F_tau^*(omega) of omega = sum_i w_i b^0_i dx/r modulo P^N (article: the formula
  // for the q_tau-power Frobenius of a differential form, after the algorithm "Compute matrix
  // of Frobenius on functions"):
  //   F_tau^*(omega) = sum_j ( sum_i q_tau*x^(q_tau-1)*w_i^tau(x^(q_tau))*mat[i,j] ) b^0_j dx/r.
  // Input:   w in L[x]^d; Q, r as in froblift (r is made monic here: r means z = r/lc(r));
  //          P, qtau, tau as in froblift; frobmatb0r the matrix mat of froblift, known modulo
  //          P^(N - v_K(q_tau)) (in coleman_data N = Nmax).
  // Returns: the coefficient vector f in (O_L/P^N)[x]((z))^d of F_tau^*(omega) w.r.t.
  //          b^0 dx/r, modulo P^N. The products are formed modulo P^(N - v_K(q_tau)); the
  //          final factor q_tau (from d(x^q_tau) = q_tau*x^(q_tau-1)*dx) restores precision N.

  L:=BaseRing(Coefficients(Q)[1]);
  OL:=MaximalOrder(L);
  OLx<x>:=PolynomialRing(OL);
  OLxy<y>:=PolynomialRing(OLx);
  Q:=OLxy!Q;
  r:=OLx!r;
  if Type(P) eq RngOrdIdl then
    vq:=Valuation(qtau,Place(P)); // v_K(q_tau): e_K*f_K for the q-power lift, e_K for the p-power lift
  else
    vq:=Valuation(qtau,P);  // P = p, a rational prime (rational branch)
  end if;

  O,Ox,S,R:=getrings(OL,P,N-vq); // precision N - v_K(q_tau) suffices before the factor q_tau
  x:=Ox.1;

  d:=Degree(Q);
  Q:=R!Q;

  frobmatb0r:=Matrix(S,d,d,[S!a:a in Eltseq(frobmatb0r)]); // over S
  Sd:=RSpace(S,d);

  r:=(Ox!Coefficients(r));
  lc:=LeadingCoefficient(r);
  r:=r/lc;

  xq_minus_one:=pow_mod_Q(R!(Ox!x),qtau-1,Q,r);
  xq:=radix_reduce(xq_minus_one*(R!(Ox!x)),r);

  frob:=Sd!0;
  for i:=1 to d do
    if Type(tau) eq RngIntElt then
      Cw:=Coefficients(w[i]);
    else
      Cw:=[tau(c):c in Coefficients(w[i])]; // the coefficient twist w_i^tau (F_tau^* is tau-semilinear)
    end if;
    temp:=radix_reduce((xq_minus_one)*substitute_xq(R!(Ox!Cw),xq,r),r); // x^(q-1)*w_i^tau(x^q)
    for j:=1 to d do
      frob[j]:=Coefficient(radix_reduce(frob[j]+frobmatb0r[i,j]*temp,r),0); // += x^(q-1)*w_i^tau(x^q)*mat[i,j]
    end for;
  end for;

  O,Ox,S,R:=getrings(OL,P,N);
  Sd:=RSpace(S,d);
  frob:=qtau*(Sd!frob); // the factor q_tau of d(x^q_tau) = q_tau*x^(q_tau-1)*dx

  return frob;
end function;