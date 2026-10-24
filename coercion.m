// coercion.m -- moving polynomials, series and matrices between L and its completion K.
//
// The curve and the cohomological data live over the number field L; points, local
// expansions and integrals live over the completion K = L_P (precision NK = Nmax) or over a
// finite extension of K (the auxiliary totally ramified K(pi^(1/e)), or an unramified
// extension). m : L -> K is the completion map (data`m), possibly composed with a power of the
// Frobenius tau (the coefficient twist of the p-power lift).
//
// The second half implements fast series arithmetic over the exact quotient ring
// Oq = O_K/pi^NK (series_K_to_Oq etc.), used by the tiny integrals and the local expansions.
//
// Notation and conventions: see "Conventions and notation" in README.md.

coer_poly:=function(f,L,K,m)

  // The image of f in L[x] in K[x] under the coefficient map m : L -> K.

  C:=Coefficients(f);
  Kx:=PolynomialRing(K);
  return &+[Kx|m(C[i])*Kx.1^(i-1):i in [1..#C]|C[i] ne 0];

end function;

coer_plseries:=function(f,L,K,m)

  // The image of a power series f in L[[t]] (or a Laurent series in L((t))) in K[[t]]
  // (resp. K((t))) under m, with the same t-adic precision.

  Kt:=ChangeRing(Parent(f),K);
  if f eq 0 then
    return Kt!0;
  end if;
  n:=Valuation(f);
  // the known coefficients of f (its relative precision may be below that of the ring)
  return Kt!&+[Kt|m(Coefficient(f,i))*Kt.1^i:i in [n..n+RelativePrecision(f)-1]|Coefficient(f,i) ne 0];

end function;

eval_frac:=function(f,L,K,m,x0)

  // f(x0) for f in L(x) and x0 in a finite extension K' of K (numerator and denominator are
  // mapped to K[x] by m and evaluated at x0).

  return Evaluate(coer_poly(Numerator(f),L,K,m),x0)/Evaluate(coer_poly(Denominator(f),L,K,m),x0);

end function;


eval_mat:=function(W,L,K,m,x0)

  // W(x0) for a matrix W over L(x) and x0 in a finite extension K' of K (entrywise eval_frac);
  // the result is a matrix over Parent(x0).

  return Matrix(Parent(x0),NumberOfRows(W),NumberOfColumns(W),[eval_frac(a,L,K,m,x0):a in Eltseq(W)]);

end function;



// approximations of elements over K by elements over L

approx_inL:=function(c,K,L,m)

  // An element cL of L with m(cL) = c to the precision of c: the preimage of c under the
  // inverse of the completion map m : L -> K, so c = m(cL) + O(pi^(NK + v(cL))) (relative
  // precision NK).

  return Inverse(m)(c); // a section of m

end function;

approx_plseriesinL:=function(f,K,L,m)

  // An approximation in L((t)) of f in K((t)) (its known coefficients, by approx_inL).

  Lt:=ChangeRing(Parent(f),L);
  if f eq 0 then
    return Lt!0;
  end if;
  n:=Valuation(f);
  return Lt!&+[Lt|approx_inL(Coefficient(f,i),K,L,m)*Lt.1^i:i in [n..n+RelativePrecision(f)-1]];

end function;

approx_polypseriesinL:=function(fy,K,L,m)

  // An approximation in L[[t]][y] of fy in K[[t]][y], coefficientwise by approx_plseriesinL.

  Lt:=PowerSeriesRing(L,Precision(BaseRing(Parent(fy)))); // the same t-adic precision
  Lty:=PolynomialRing(Lt);
  C:=Coefficients(fy);
  return &+[Lty|approx_plseriesinL(C[i],K,L,m)*Lty.1^(i-1):i in [1..#C]];

end function;

// ---------------------------------------------------------------------------------
// Fast series arithmetic via the exact quotient ring Oq = OK/pi^NK.
// Magma's (Laurent) series arithmetic over the inexact p-adic field K is quadratic in
// the length with large constants, and over the number field L it is far worse (a
// single multiplication of length ~4000 over L can take many minutes), while over the
// finite quotient ring it uses fast polynomial multiplication and takes milliseconds.
// All series appearing in the tiny integrals are integral (they are expansions w.r.t.
// a uniformizer on the good-reduction model), so nothing is lost modulo pi^NK.

series_K_to_Oq:=function(f,S,OK)

  // Convert a (Laurent or power) series f over K with integral coefficients to the
  // Laurent series ring S over Oq=OK/pi^NK.

  if IsWeaklyZero(f) then
    return S!0;
  end if;
  Oq:=CoefficientRing(S);
  v:=Valuation(f);
  s:=(S.1)^v*(S![Oq|OK!c:c in Coefficients(f)]);
  ap:=AbsolutePrecision(f);
  if Type(ap) eq Infty then
    return s;
  end if;
  return s+O(S.1^(Integers()!ap));
end function;


series_Oq_to_K:=function(f,Kt,OK)

  // Convert a Laurent series over Oq=OK/pi^NK back to the Laurent series ring Kt over K.

  K:=CoefficientRing(Kt);
  if IsWeaklyZero(f) then
    return Kt!0;
  end if;
  v:=Valuation(f);
  s:=(Kt.1)^v*(Kt![K|K!(OK!c):c in Coefficients(f)]);
  ap:=AbsolutePrecision(f);
  if Type(ap) eq Infty then
    return s;
  end if;
  return s+O(Kt.1^(Integers()!ap));
end function;


series_inverse:=function(f)

  // 1/f for a power or Laurent series f over Oq=OK/pi^NK whose leading coefficient is a
  // unit, by Newton's iteration g -> g*(2-u*g) for the unit part u = f/t^v (every step
  // doubles the number of correct terms), with the precision of 1/f. The inverse is unique
  // to that precision, so the result is that of the division 1/f, which takes time quadratic
  // in the length over Oq (5 s for length 5000), while a multiplication takes 0.04 s.

  S:=Parent(f);
  v:=Valuation(f);
  u:=(v eq 0) select f else f*S.1^(-v); // a power series with a unit constant term
  n:=RelativePrecision(f);
  if Type(n) eq Infty then
    n:=Precision(S);
  end if;
  g:=S!(Coefficient(u,0)^-1);
  k:=1;
  while k lt n do
    k:=Minimum(2*k,n);
    g:=ChangePrecision(g,k); // correct modulo t^(k/2); the Newton step doubles that
    g:=g*(2-ChangePrecision(u,k)*g);
  end while;
  g:=ChangePrecision(g,n);
  return (v eq 0) select g else g*S.1^(-v);

end function;


polL_eval_Oq:=function(g,m,OK,xS)

  // Evaluate a polynomial g over L (with P-integral coefficients) at the Laurent series
  // xS over Oq=OK/pi^NK, mapping the coefficients through m: L -> K (Horner).

  S:=Parent(xS);
  Oq:=CoefficientRing(S);
  C:=Coefficients(g);
  s:=S!0;
  for i:=#C to 1 by -1 do
    s:=s*xS+(Oq!OK!m(C[i]));
  end for;
  return s;
end function;


fracL_eval_Oq:=function(f,m,OK,xS)

  // Evaluate f in L(x) at the Laurent series xS over Oq; the evaluated denominator must
  // have a unit leading coefficient (true for the W-matrices of a good model evaluated
  // at the expansion of x, whose leading coefficient is a unit).

  return polL_eval_Oq(Numerator(f),m,OK,xS)*series_inverse(polL_eval_Oq(Denominator(f),m,OK,xS));
end function;


eval_series_Ke:=function(f,t0,K)

  // f(t0) for a Laurent series f over K and t0 with v(t0) > 0 in a totally ramified
  // extension Ke = K(pi^(1/e)) of K. If t0 is exactly a power u^v of the uniformizer
  // (the case for the near-boundary points of find_suitable_point_in_disc, where the
  // local parameter takes the value u), the sum is just a regrouping of the
  // coefficients (using u^e=pi), costing O(length) K-operations instead of O(length)
  // Ke-multiplications; otherwise fall back to Horner.

  Ke:=Parent(t0);
  e:=Degree(Ke,K);
  C,vf:=Coefficients(f);
  if #C eq 0 then
    return Ke!0;
  end if;
  vt:=Valuation(t0);
  if (e gt 1) and (vt ge 1) and IsWeaklyZero(t0-Ke.1^vt) then // t0=u^vt exactly
    piK:=UniformizingElement(K);
    acc:=[K!0:j in [1..e]];
    idx:=vf*vt;
    j:=((idx mod e)+e) mod e;
    curk:=(idx-j) div e;
    pik:=piK^curk;
    for i:=0 to #C-1 do
      idx:=(vf+i)*vt;
      j:=((idx mod e)+e) mod e;
      k:=(idx-j) div e;
      while curk lt k do
        pik:=pik*piK;
        curk:=curk+1;
      end while;
      if C[i+1] ne 0 then
        acc[j+1]:=acc[j+1]+C[i+1]*pik;
      end if;
    end for;
    s:=Ke!0;
    upow:=Ke!1;
    for j:=1 to e do
      if acc[j] ne 0 then
        s:=s+(Ke!acc[j])*upow;
      end if;
      if j lt e then
        upow:=upow*Ke.1;
      end if;
    end for;
    return s;
  end if;
  // generic Horner
  s:=Ke!0;
  for i:=#C to 1 by -1 do
    s:=s*t0+C[i];
  end for;
  return s*t0^vf;
end function;


taylor_shift_K:=function(g,c)

  // For a polynomial g over K, return the coefficient sequence [g(c),g'(c)/1!,...] of
  // g(c+t), computed by repeated synthetic division (O(deg^2) operations in K).

  S:=Coefficients(g);
  out:=[];
  while #S gt 0 do
    b:=[Universe(S)|];
    r:=S[#S];
    for i:=#S-1 to 1 by -1 do
      b[i]:=r;
      r:=S[i]+r*c;
    end for;
    Append(~out,r);
    S:=b;
  end while;
  return out;
end function;


eval_frac_shift:=function(f,L,K,m,c,Kt,St,OK)

  // Evaluate f in L(x) at the linear series c+t as an element of the series ring Kt
  // over K. The numerator and denominator are Taylor-shifted to c (cheap), and the one
  // series inversion is done over the exact quotient ring Oq=OK/pi^NK whenever
  // possible — over the inexact K it would cost a full-length quadratic division.

  num:=coer_poly(Numerator(f),L,K,m);
  den:=coer_poly(Denominator(f),L,K,m);
  cnum:=taylor_shift_K(num,c);
  cden:=taylor_shift_K(den,c);
  if #cnum eq 0 then
    return Kt!0;
  end if;
  if #cden eq 1 then // constant denominator
    return (Kt!cnum)/cden[1];
  end if;
  // scale numerator and denominator by the same power of pi to make them integral
  minval:=Minimum([Valuation(x):x in cnum cat cden|not IsWeaklyZero(x)] cat [0]);
  if minval lt 0 then
    sc:=UniformizingElement(K)^(-minval);
    cnum:=[x*sc:x in cnum];
    cden:=[x*sc:x in cden];
  end if;
  // the lowest-order non-(weakly-)zero denominator coefficient must be a unit for the
  // division over Oq; otherwise fall back to the (slow) division over K
  vd:=0;
  while vd lt #cden and IsWeaklyZero(cden[vd+1]) do
    vd:=vd+1;
  end while;
  if vd lt #cden and Valuation(cden[vd+1]) eq 0 then
    Oq:=CoefficientRing(St);
    nS:=St![Oq|OK!x:x in cnum];
    dS:=St![Oq|OK!x:x in cden];
    return series_Oq_to_K(nS*series_inverse(dS),Kt,OK);
  end if;
  return (Kt!cnum)/(Kt!cden);
end function;
