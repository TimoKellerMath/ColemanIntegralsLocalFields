// expansion.m -- power series expansions of functions in an integral local parameter.
//
// Article: section "Computing Coleman integrals", the algorithm "Expansion of a function in an
// integral local parameter": to expand a function h at a point P in an integral local
// parameter t (the proposition on the uniformizer at a point), take a polynomial relation
// fy(t,h) = 0 (the minimal polynomial of h over L(t), see minpoly in integrals.m), select the
// branch through P by the expansion of the reduction of h modulo P (mod_P_expansion,
// mod_P_prec, approx_root), and Hensel lift it in K[[t]] (hensel_lift).
//
// Notation and conventions: see "Conventions and notation" in README.md.

divide_by_tpower:=function(f,v)

  // f/t^v for a power series f (over K or over OK/pi^NK) whose coefficients below t^v
  // vanish to the working precision: they are dropped. (Over the quotient ring OK/pi^NK a
  // series with zero constant term is not invertible, and over K such coefficients may be
  // inexact zeros O(pi^NK), which the series arithmetic treats as nonzero.)

  if v eq 0 then
    return f;
  end if;
  R:=Parent(f);
  ap:=AbsolutePrecision(f);
  return R![Coefficient(f,k):k in [v..ap-1]]+O(R.1^(ap-v));

end function;

unit_linear_roots:=function(fac)

  // The roots -b/a of the linear factors a*y + b with a unit a in the factorisation fac (of a
  // polynomial over O_K or over F_q[[t]]); the other factors have no root in the coefficient
  // ring. The factors need not be monic: over a power series ring the leading coefficient of
  // a factor can be 1 only to a lower precision, and its comparison with 1 can then fail.

  return [-Coefficient(f[1],0)/Coefficient(f[1],1):f in fac|Degree(f[1]) eq 1 and Valuation(Coefficient(f[1],1)) eq 0];

end function;


hensel_newton_Oq:=function(fy,root,prec_seq,v2)

  // The Newton iteration of hensel_lift over the exact quotient ring OK/pi^NK, for fy in
  // K[[t]][y] and root in K[[t]] with integral coefficients: the root at the t-adic precisions
  // prec_seq (each step divides by t^v2, v2 = v_t(fy'(root))), returned over K with t-adic
  // precision tprec - v2. Magma's power series arithmetic over the finite quotient ring uses
  // fast polynomial multiplication and is orders of magnitude faster (1000x at length ~3000)
  // than over K, where it is quadratic in the length with large constants. The result agrees
  // with the computation over K modulo pi^NK, which is all the precision K carries anyway.

  Kt:=BaseRing(Parent(fy));
  K:=BaseRing(Kt);
  tprec:=Precision(Kt);
  NK:=Precision(K);
  OK:=Integers(K);
  piK:=UniformizingElement(K);


  Oq:=quo<OK|piK^NK>;
  S:=PowerSeriesRing(Oq,tprec);
  Sy:=PolynomialRing(S);

  toS:=function(co) // convert a power series over K with integral coefficients to S
    if IsWeaklyZero(co) then
      return S!0;
    end if;
    vco:=Valuation(co);
    s:=(S.1)^vco*(S![Oq|OK!c:c in Coefficients(co)]);
    apco:=AbsolutePrecision(co);
    if Type(apco) eq RngIntElt and apco lt tprec then
      s:=ChangePrecision(s,apco);
    end if;
    return s;
  end function;

  fyS:=Sy![toS(co):co in Coefficients(fy)];
  derfyS:=Derivative(fyS);
  rootS:=toS(root);

  if v2 eq 0 then
    vprintf User1, 2: "hensel_lift: #prec_seq = %o (over OK/pi^N)\n", #prec_seq;
  else
    vprintf User1, 2: "hensel_lift: #prec_seq = %o (over OK/pi^N; multiple root, v_t(fy') = %o)\n", #prec_seq, v2;
  end if;
  for j:=1 to #prec_seq do
    rootS:=ChangePrecision(rootS,prec_seq[j]);
    num:=Evaluate(fyS,rootS);
    if not IsWeaklyZero(num) then
      rootS:=rootS-divide_by_tpower(num,v2)*series_inverse(divide_by_tpower(Evaluate(derfyS,rootS),v2));
    end if;
    rootS:=ChangePrecision(rootS,prec_seq[j]-v2); // fy mod t^prec_seq[j] determines the root mod t^(prec_seq[j]-v2)
  end for;

  assert IsWeaklyZero(Evaluate(fyS,rootS)); // cheap over the quotient ring

  // convert back to K[[t]] (coefficients correct mod pi^NK)
  Ktfull:=PowerSeriesRing(K,tprec);
  if IsWeaklyZero(rootS) then
    root:=Ktfull!0;
  else
    vro:=Valuation(rootS);
    root:=(Ktfull.1)^vro*(Ktfull![K!OK!c:c in Coefficients(rootS)]);
  end if;
  if v2 gt 0 then
    root:=ChangePrecision(root,tprec-v2);
  end if;

  return root;

end function;


hensel_newton_K:=function(fy,root,prec_seq,v2)

  // The Newton iteration of hensel_lift over the inexact field K (for fy or root with
  // non-integral coefficients), at the t-adic precisions prec_seq as in hensel_newton_Oq;
  // the result is checked at the previous precision.

  Kt:=BaseRing(Parent(fy));
  K:=BaseRing(Kt);
  tprec:=Precision(Kt);
  derfy:=Derivative(fy);


  vprintf User1, 2: "hensel_lift: #prec_seq = %o\n", #prec_seq;
  for j:=1 to #prec_seq do
    vprintf User1, 2: "%o (prec = %o): ", j, prec_seq[j];
    root:=ChangePrecision(root,prec_seq[j]);
    t0:=Cputime();
    num:=Evaluate(fy,root);
    if IsWeaklyZero(num) then // already a root to this precision
      root:=PowerSeriesRing(K,prec_seq[j])!root;
      if v2 gt 0 then
        root:=ChangePrecision(root,prec_seq[j]-v2);
      end if;
      vprintf User1, 2: "Time: %o\n", Cputime(t0);
      continue;
    end if;
    if v2 eq 0 then
      v:=Valuation(num);
      // The Newton correction num/derfy(root) has t-valuation v (about half of prec_seq[j]),
      // so the derivative is only needed mod t^(prec_seq[j]-v+2*v2): truncating root before
      // evaluating derfy does not change the result mod t^prec_seq[j], but the division by
      // the short series is about 4 times cheaper (series arithmetic over K is quadratic
      // in the length), which makes up most of the cost of a Newton step.
      dtrunc:=Evaluate(derfy,ChangePrecision(root,Maximum(prec_seq[j]-v+2*v2,2*v2+1)));
      root:=root-num/dtrunc;
      root:=PowerSeriesRing(K,prec_seq[j])!root;
    else // divide by t^v2 explicitly; fy mod t^prec_seq[j] determines the root mod t^(prec_seq[j]-v2)
      root:=root-divide_by_tpower(num,v2)/divide_by_tpower(Evaluate(derfy,root),v2);
      root:=PowerSeriesRing(K,prec_seq[j])!ChangePrecision(root,prec_seq[j]-v2);
    end if;
    vprintf User1, 2: "Time: %o\n", Cputime(t0);
  end for;

  // check the result at the previous precision: a full-precision evaluation would cost
  // as much as the entire last Newton step, and that step already guarantees the
  // remaining digits (any wrong root fails far below this precision)
  checkprec:=#prec_seq le 1 select tprec-v2 else prec_seq[#prec_seq-1]-v2;
  assert IsWeaklyZero(Evaluate(fy,ChangePrecision(root,checkprec)));

  return root;

end function;


hensel_lift:=function(fy,root,L,K,m);

  // The root of fy in K[[t]] near the approximate root root, by Newton iteration (step (2) of
  // the algorithm "Expansion of a function in an integral local parameter").
  // Input:    fy in K[[t]][y]; root in K[[t]], an approximate root (e.g. from approx_root);
  //           L, K, m as in coercion.m. The t-adic precision tprec is that of the series ring.
  // Requires: the Hensel criterion below; otherwise an error is raised.
  // Returns:  the root, to t-adic precision tprec - v2, and v2.
  // Prints:   "hensel_lift: #prec_seq = ..." (the number of Newton steps) at verbosity level 2
  //           of the flag User1 (SetVerbose("User1", 2); see "Progress messages" in README.md).
  // Inexact zeros O(pi^NK) of K count as nonzero in the series arithmetic over K, so the
  // valuations below are weak ones, and the iteration runs over O_K/pi^NK when possible.
  //
  // The criterion (the algorithm "Expansion of a function in an integral local parameter"):
  // v2 = v_t(fy'(root)) is finite, the coefficient of t^v2 in
  // fy'(root) is a unit of OK, and v1=v_t(fy(root))>2*v2. Usually v2=0. v2>0 means that
  // root(0) is a multiple root of fy(0,y): the function does not separate the points of the
  // fibre of the local parameter through the point (e.g. two points at infinity with the same
  // value of a b_i^infinity), and the branches of fy only separate at the order t^v2. The
  // Newton step then divides by t^v2; and fy mod t^tprec determines the root only mod
  // t^(tprec-v2), so the root is returned with t-adic precision tprec-v2
  // (expansion_at_point evaluates fy to v2 more terms).

  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  tprec:=Precision(Kt); // t-adic precision

  derfy:=Derivative(fy);

  // The valuations are weak ones: coefficients that vanish to the precision of K do not
  // count. For a multiple root, the constant term of fy'(root) is such an inexact zero
  // O(pi^NK), which LeadingCoefficient would return as the leading coefficient.
  derroot:=Evaluate(derfy,root);
  if IsWeaklyZero(derroot) or WeakValuation(Coefficient(derroot,WeakValuation(derroot))) ne 0 then
    // fy'(root) vanishes to the available t-adic precision, or its leading coefficient is
    // divisible by P: the branches of fy through root(0) are not separated (to this
    // precision, resp. modulo P), so the root is not determined by Hensel's lemma
    error "Cannot compute the local expansion: fy'(root) vanishes to the available t-adic precision or has a leading coefficient divisible by P (the branches through the point are not separated); Hensel lift does not apply";
  end if;

  v2:=WeakValuation(derroot);
  fyroot:=Evaluate(fy,root);
  if IsWeaklyZero(fyroot) and (#Coefficients(fyroot) eq 0 or WeakValuation(fyroot) le 2*v2) then
    // fy(root) vanishes to its t-adic precision: WeakValuation only counts its stored
    // coefficients (and fails if there are none), its absolute precision is the sharper bound
    v1:=AbsolutePrecision(fyroot);
  else
    v1:=WeakValuation(fyroot);
  end if;

  if not v1 gt 2*v2 then
    error Sprintf("hensel_lift: the Hensel criterion v_t(fy(root)) = %o > 2*v_t(fy'(root)) = %o fails; the approximate root is not precise enough",v1,2*v2);
  end if;

  prec_seq:=[];
  k:=tprec;

  while k gt v1 do
    Append(~prec_seq,k);
    k:=Ceiling(k/2+v2);
  end while;
  prec_seq:=Reverse(prec_seq);

  // If fy and root have integral coefficients (the generic case: they come from integral
  // minimal polynomials and integral point coordinates), the Newton iteration runs over the
  // exact quotient ring OK/pi^NK (hensel_newton_Oq), otherwise over K (hensel_newton_K).

  integral:=&and[IsWeaklyZero(co) or &and[Valuation(c) ge 0:c in Coefficients(co)]:co in Coefficients(fy) cat [root]];
  if integral then
    return hensel_newton_Oq(fy,root,prec_seq,v2), v2;
  end if;
  return hensel_newton_K(fy,root,prec_seq,v2), v2;

end function;

mod_P_prec:=function(fy,L,K,m);

  // The t-adic precision needed to separate the roots of fy modulo P and to start the Hensel
  // lift: the roots of fy mod P in F_q[[t]] (from the linear factors of the factorisation;
  // Roots is avoided because of problems with it) must be distinct to this precision, and
  // each must satisfy the Hensel criterion v_t(fy(z)) > 2*v_t(fy'(z)) at it.
  // Input:   fy in K[[t]][y] with coefficients in O_K[[t]]; L, K, m (unused).
  // Returns: modPprec >= 1.
  // Errors:  if fy mod P has a repeated factor.

  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  tprec:=Precision(Kt);
  K:=BaseRing(Kt);
  OK:=Integers(K);
  Fq:=ResidueClassField(OK);
  Fqt:=PowerSeriesRing(Fq,tprec);
  Fqty:=PolynomialRing(Fqt);

  fymodP:=Fqty!fy;
  derfymodP:=Derivative(fymodP);

  fac:=Factorisation(fymodP); // can be slow...
  if exists{f:f in fac|f[2] gt 1} then
    error "mod_P_prec: the reduction of the polynomial relation has a repeated factor, so its roots modulo P are not separated (the t-adic precision is not high enough)";
  end if;
  zeros:=unit_linear_roots(fac); // in Fq[[t]]

  modPprec:=1;
  for i:=1 to #zeros do
    done:=false;
    prec:=1;
    while not done do
      v1:=Valuation(Evaluate(fymodP,ChangePrecision(zeros[i],prec)));
      v2:=Valuation(Evaluate(derfymodP,ChangePrecision(zeros[i],prec)));
      if Minimum(prec,v1) gt 2*v2 then
        done:=true;
      end if;
      prec:=prec+1;
    end while;
    modPprec:=Maximum(modPprec,prec); // every root satisfies the Hensel criterion at this precision
  end for;

  // the roots are distinct at this precision
  modPprec:=Maximum([modPprec] cat [Valuation(zeros[i]-zeros[j]):j in [i+1..#zeros],i in [1..#zeros]]);
 
  return modPprec;
 
end function;


approx_root:=function(fy,y0,L,K,m,modPprec,expamodP)

  // An approximate root of fy in K[[t]], to t-adic precision modPprec, on the branch through
  // the point: the root that is congruent to y0 modulo t and to expamodP modulo P (step (2)
  // of the algorithm "Expansion of a function in an integral local parameter"). It is the
  // starting value of hensel_lift.
  // Input:   fy in K[[t]][y] with coefficients in O_K[[t]]; y0 in K, the value at the point;
  //          L, K, m; modPprec from mod_P_prec; expamodP in F_q[[t]], the expansion of the
  //          reduction of the function (mod_P_expansion).
  // Method:  digit by digit: with root known modulo t^Nroot, the lowest t-coefficient of
  //          fy(t, root + z*t^Nroot) is a polynomial in z, and its roots in O_K that reduce to
  //          the digit of expamodP give the next digit; if fy(t, root) vanishes to the
  //          available precision, the digit of expamodP is lifted directly.
  // Errors:  if not exactly one approximate root remains, or if it does not satisfy the
  //          Hensel criterion.

  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  tprec:=Precision(Kt); // t-adic precision

  // the root is only needed mod t^modPprec, so truncate fy and all the work below to
  // that precision: at the full precision of Kt (~e*Nmax for boundary points) the
  // series operations and the coefficientwise L-approximations here dominated the
  // entire run time of the local expansions
  if modPprec lt tprec then
    tprec:=modPprec;
    Kt:=PowerSeriesRing(K,tprec);
    Kty:=PolynomialRing(Kt);
    fy:=Kty![Kt!c:c in Coefficients(fy)];
  end if;

  OK:=Integers(K);
  Fq,redmap:=ResidueClassField(OK);
  OKz:=PolynomialRing(OK);
  Lz:=PolynomialRing(L);
  Lzt:=PowerSeriesRing(Lz,tprec);
  
  roots:=[[*Kt!y0,1*]];
  i:=1;
  while i le #roots do // roots: the candidates [* root modulo t^Nroot, Nroot *]
    root:=roots[i][1];
    Nroot:=roots[i][2];
    if Nroot lt modPprec then
      roots:=Remove(roots,i);
      newroot:=root+Kty.1*Kt.1^Nroot;
      // fy(t,root+y*t^Nroot) = fy(t,root) + fy'(t,root)*y*t^Nroot + ..., with fy(t,root) = O(t^Nroot);
      // wanted: y with fy(t,root+y*t^Nroot) = O(t^(Nroot+1)); y is called z below
      C:=Coefficients(fy);
      fynewroot:=&+[Kty|(Kt!C[j])*newroot^(j-1):j in [1..#C]];
      fynewroot:=approx_polypseriesinL(Kty!fynewroot,K,L,m); // in Lty
      // fy(t,root+z*t^Nroot) = sum_i a_i(z)*t^i in L[z][[t]]
      fznewroot:=&+[Lzt|Coefficient(Coefficient(fynewroot,j),k)*(Lz.1)^j*(Lzt.1)^k:k in [0..tprec-1],j in [0..Degree(fynewroot)]];
      // If fy(t,root) vanishes to the available t-precision (fznewroot=0, valuation>=tprec),
      // the digit at t^Nroot is not determined by fy: the residue y0 is a multiple root of
      // fy mod (P,t) (a ramified/degenerate point, so the linear z-term derfy_0*z is absent).
      // The correct digit is then read off from the known mod-P expansion expamodP of the
      // point, which selects the right branch in the residue disc. (Here
      // Coefficient(fznewroot,Valuation(fznewroot)) cannot be used: the valuation is Infinity.)
      if (fznewroot eq 0) or (Valuation(fznewroot) ge tprec) then
        soldigit:=Coefficient(expamodP,Nroot) @@ redmap; // lift the Fq-digit to OK
        roots:=Insert(roots,i,[*root+(Kt!soldigit)*(Kt.1)^Nroot,Nroot+1*]);
      else
        fac:=Factorisation(OKz!coer_poly(Coefficient(fznewroot,Valuation(fznewroot)),L,K,m)); // the lowest t-coefficient (of t^Nroot), a polynomial in z over O_K
        for sol in unit_linear_roots(fac) do // its linear factors give the candidate digits (it is linear if the digit is a simple root modulo P)
          if Fq!sol eq Coefficient(expamodP,Nroot) then
            roots:=Insert(roots,i,[*Evaluate(newroot,sol),Nroot+1*]);
          end if;
        end for;
      end if;
    else
      i:=i+1;
    end if;
  end while;

  if #roots ne 1 then
    error Sprintf("approx_root: %o approximate roots of the polynomial relation reduce to the expansion of the point modulo P (expected exactly one); the local parameter does not separate the branches through the point",#roots);
  end if;

  root:=roots[1][1];
  root:=coer_plseries(approx_plseriesinL(root,K,L,m),L,K,m);

  v1:=Valuation(approx_plseriesinL(Evaluate(fy,root),K,L,m));
  v2:=Valuation(approx_plseriesinL(Evaluate(Derivative(fy),root),K,L,m));

  if v1 le 2*v2 then
    error Sprintf("approx_root: the approximate root does not satisfy the Hensel criterion v_t(fy(root)) = %o > 2*v_t(fy'(root)) = %o; increase the t-adic precision",v1,2*v2);
  end if;

  return root;

end function;

mod_P_expansion:=function(f,place,tmodP,modPprec);

  // The expansion of a function f on the reduced curve in the uniformizer tmodP at a place,
  // to t-adic precision modPprec (step (2) of the algorithm "Expansion of a function in an
  // integral local parameter": the expansion of the reduction of h).
  // Input:   f in F_q(X); place a place of F_q(X) of degree 1 (the reduction of the point);
  //          tmodP a uniformizer at that place; modPprec >= 1.
  // Returns: expamodP in F_q[[t]], computed by the recursion a_i = ((f - a_0 - ... )/t^i)(place).

  FFq:=Parent(f);
  Fqx:=BaseRing(FFq); // Fq(x)
  Fq:=BaseRing(Fqx);
  Fqt:=PowerSeriesRing(Fq,modPprec);

  expamodP:=Fqt!0;
  for i:=0 to modPprec-1 do
    val:=Evaluate(f,place); // the value at the place, in its residue field F_q
    expamodP:=expamodP+val*Fqt.1^i; // f = a0 + a1*tmodP + ...: f(place) = a0, ((f-a0)/tmodP)(place) = a1, ...
    f:=(f-val)/tmodP;
  end for;
  
  return expamodP;
  
end function;