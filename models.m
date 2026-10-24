// models.m -- plane models of a curve for the Coleman integration code: the good primes of a
// model, better models, the affine patches of a curve, its points as point records, and
// Chabauty-Coleman for a curve given as a Curve.
//
// The library needs a plane model Q(x,y) = 0, monic in y with integral coefficients, and a
// prime P at which the triple (Q, W^0, W^inf) has good reduction (article: the definition
// "Good-reduction assumptions"; README: "Conventions and notation"). The functions below
// produce such models from a polynomial or from a Curve, find their good primes, and convert
// the points of the curve into point records:
//
//   curve_model(C)               a model of C: a Curve in affine or projective space (projected
//                                to a plane curve if necessary), or a polynomial Q(x,y);
//   good_primes(M)               the primes of small norm at which the model M has good
//                                reduction, and the reason for every other prime;
//   improve_model(M)             models obtained from M by transformations that preserve the
//                                curve, ranked by their good primes;
//   model_coleman_data(M, P, N)  coleman_data for the model M, also (aux) over the unramified
//                                quadratic extension of L_P, for the points of degree 2;
//   affine_patches(M, P)         plane models (affine patches of the plane curve) whose good
//                                residue discs at P cover all smooth points of the reduction;
//   point_records(M, data, pts)  the point records of points of the curve (also of places of
//                                degree 2 and of divisors), for data computed by coleman_data
//                                from the model;
//   curve_chabauty(C, pts)       Chabauty-Coleman for a curve given as a Curve or a polynomial:
//                                model, prime, coleman_data, effective_chabauty, and the
//                                identification of the candidates.
//
// A model is a record with the fields
//   Q       the plane model in L[x][y], monic in y with integral coefficients,
//   L       the number field of the model (Q as a number field of degree 1 for a curve over Q),
//   C       the curve, FF its function field (over the base field K of C),
//   xf, yf  the functions x and y of the model, elements of FF with Q(xf,yf) = 0,
//   F       the homogeneous equation over L of a plane curve birational to C, in the
//           coordinates (u_1 : u_2 : u_3) = base,
//   base    functions u_1, u_2, u_3 in FF with F(u_1,u_2,u_3) = 0,
//   c       the polynomial c(x) over L with yf = c(xf)*u_2/u_3 (and xf = u_1/u_3),
//   desc    the transformations that led to the model (a sequence of strings).
// Every point of the smooth projective curve -- also a point at infinity of the plane model
// or a singular point of it -- is a place of FF, so point_records converts all points of C,
// whatever model is used. quadratic_points.m builds on these functions for the points of
// degree 2 (curve_quadratic_points).
//
// Load after integrals.m (which contains the tests of the good-reduction assumptions,
// good_reduction_at) and, for curve_chabauty, after solver.m.

model_format:=recformat<Q,L,C,FF,xf,yf,F,base,c,desc>;

// Q as a number field of degree 1, the field of the models of curves over Q
QQ_number_field:=ext<Rationals()|Polynomial([0,1]):DoLinearExtension>;


// ---------------------------------------------------------------------------------------------
// Fields and polynomials

model_field:=function(K)

  // The number field L over which the library works for a curve over K, and the map K -> L.
  // Input:  K the rationals or a number field (absolute, relative, quadratic or cyclotomic).
  // Output: L = Q as a number field of degree 1 for K = Q; the absolute field of K for a
  //         relative extension; an isomorphic field of type FldNum for a quadratic or
  //         cyclotomic field; K itself otherwise.

  case Type(K):
    when FldRat:
      L:=QQ_number_field;
      return L, map<K->L|a:->L!a>;
    when FldQuad, FldCyc:
      L:=NumberField(DefiningPolynomial(K));
      return L, map<K->L|a:->L!Eltseq(a)>;
    when FldNum:
      if IsAbsoluteField(K) then
        return K, map<K->K|a:->a>;
      end if;
      L:=AbsoluteField(K);
      return L, map<K->L|a:->L!a>;
  end case;
  error Sprintf("model_field: the base field of the curve must be Q or a number field, not %o",Type(K));
end function;


from_model_field:=function(c,K)

  // An element c of the field model_field(K) as an element of K.

  case Type(K):
    when FldRat:
      return Rationals()!c;
    when FldQuad, FldCyc:
      return K!Eltseq(c);
  end case;
  return K!c;
end function;


to_curve_field:=function(c,M)

  // An element c of M`L, or of a number field containing M`L (the field data`L of
  // model_coleman_data with aux := true), that lies in M`L, as an element of the base field
  // of the curve of M.

  ok,c:=IsCoercible(M`L,c);
  if not ok then
    error "to_curve_field: a coefficient does not lie in the field of the model; compute the data with model_coleman_data";
  end if;
  return from_model_field(c,BaseRing(M`C));
end function;


inert_quadratic_extension:=function(L,P)

  // A quadratic extension of the number field L in which the prime P is inert: its completion
  // at the prime above P is the unramified quadratic extension of L_P, whose residue field
  // F_(q^2) contains the residue fields of all points of degree 2 of the reduction (the
  // Frobenius-conjugate residue classes of symmetric Chabauty).
  // Input:  L an absolute number field (model_field), P a prime ideal of O_L of odd residue
  //         characteristic.
  // Output: L2 = L(sqrt u), an absolute number field into which L coerces; the prime ideal
  //         P2 = P*O_L2 of O_L2 (prime, since P is inert); and u, an element of O_L that is a
  //         unit and not a square modulo P: the first such element among 2, 3, ..., 100, then
  //         among a + w (w in the integral basis of O_L, a = 0, 1, ..., 20), otherwise the
  //         lift of a generator of the multiplicative group of the residue field.

  OL:=MaximalOrder(L); P:=OL!!P;
  Fq,res:=ResidueClassField(P);
  if IsEven(#Fq) then
    error "inert_quadratic_extension: the residue characteristic of P must be odd";
  end if;
  cands:=[OL|a:a in [2..100]] cat [OL|a+w:a in [0..20],w in Basis(OL)];
  us:=[u:u in cands|res(u) ne 0 and not IsSquare(res(u))];
  u:=(#us gt 0) select us[1] else PrimitiveElement(Fq)@@res;
  L2:=AbsoluteField(ext<L|PolynomialRing(L).1^2-L!u>);
  P2:=ideal<MaximalOrder(L2)|[L2!(L!g):g in Generators(P)]>;
  if not IsPrime(P2) then
    error "inert_quadratic_extension: P is not inert in L(sqrt u)";
  end if;
  return L2,P2,u;
end function;


map_coefficients:=function(f,R,h)

  // The multivariate polynomial f with every coefficient mapped by h, as an element of the
  // polynomial ring R with the same number of variables.

  C:=Coefficients(f); M:=Monomials(f);
  return &+[R|h(C[i])*Monomial(R,Exponents(M[i])):i in [1..#M]];
end function;


homogenization:=function(Q)

  // The homogenization F(X,Y,Z) in L[X,Y,Z] of Q in L[x][y]: F(x,y,1) = Q(x,y).

  L:=BaseRing(BaseRing(Parent(Q)));
  R<X,Y,Z>:=PolynomialRing(L,3);
  terms:=[<Coefficient(Coefficient(Q,i),j),j,i>:j in [0..Degree(Coefficient(Q,i))],i in [0..Degree(Q)]];
  terms:=[t:t in terms|t[1] ne 0];
  n:=Maximum([t[2]+t[3]:t in terms]);
  return &+[R|t[1]*X^t[2]*Y^t[3]*Z^(n-t[2]-t[3]):t in terms];
end function;


lc_scaling:=function(Q)

  // A model of the curve Q(x,y) = 0 that is monic in y with coefficients in O_L[x].
  // Input:  Q in L[x][y] of degree d >= 1 in y, a_d = LeadingCoefficient(Q).
  // Output: Qm in O_L[x][y], monic in y, and c in L[x] such that the function y of Qm is
  //         c(x)*y, i.e. Qm(x, c(x)*y) is a multiple of Q(x,y).
  //
  // With u = a_d if a_d is not constant and u = 1 otherwise, and c = u*D for an integer D,
  //   Qm = sum_i a_i*u^(d-i)*D^(d-i)/a_d * y^i
  // is monic with polynomial coefficients; D is the smallest positive integer that makes them
  // integral. A non-constant a_d makes its zeros bad x-coordinates of Qm.

  L:=BaseRing(BaseRing(Parent(Q)));
  OL:=MaximalOrder(L);
  d:=Degree(Q);
  ad:=LeadingCoefficient(Q);
  if Degree(ad) gt 0 then // b_i = a_i*a_d^(d-i-1)
    u:=ad;
    b:=[Coefficient(Q,i)*ad^(d-i-1):i in [0..d-1]] cat [Parent(ad)!1];
  else
    u:=Parent(ad)!1;
    b:=[Coefficient(Q,i)/LeadingCoefficient(ad):i in [0..d]];
  end if;
  // D: for every rational prime p below a denominator the least k such that p^(k*(d-i))
  // times every coefficient of b_i is integral at every prime above p
  den:=LCM([Integers()|Denominator(c):c in Coefficients(b[i+1]),i in [0..d-1]] cat [1]);
  D:=1;
  for p in PrimeDivisors(den) do
    vs:=[<Valuation(c,Pp[1])/RamificationIndex(Pp[1]),i>:Pp in Decomposition(OL,p),c in Coefficients(b[i+1]),i in [0..d-1]|c ne 0];
    D*:=p^Maximum([0] cat [Ceiling(-v[1]/(d-v[2])):v in vs]);
  end for;
  Lxy:=Parent(Q);
  return &+[Lxy|b[i+1]*D^(d-i)*Lxy.1^i:i in [0..d]], u*D;
end function;


// ---------------------------------------------------------------------------------------------
// Models

model_from_plane:=function(F,base,L,C,FF,desc)

  // The model of the plane curve F(u_1,u_2,u_3) = 0 in its affine patch u_3 = 1:
  // x = u_1/u_3 and y = u_2/u_3, made monic and integral by lc_scaling.
  // Input:  F homogeneous in L[X,Y,Z]; base = [u_1,u_2,u_3] in FF with F(u_1,u_2,u_3) = 0
  //         and u_3 ne 0.

  Lx<x>:=PolynomialRing(L); Lxy<y>:=PolynomialRing(Lx);
  Q0:=Evaluate(F,[Lxy!x,y,1]);
  if Degree(Q0) lt 1 then
    error "model_from_plane: the equation does not involve y in this affine patch";
  end if;
  Q,c:=lc_scaling(Q0);
  K:=BaseRing(C);
  cK:=PolynomialRing(K)![from_model_field(a,K):a in Coefficients(c)];
  xf:=base[1]/base[3];
  yf:=Evaluate(cK,xf)*base[2]/base[3];
  return rec<model_format|Q:=Q,L:=L,C:=C,FF:=FF,xf:=xf,yf:=yf,F:=F,base:=base,c:=c,desc:=desc>;
end function;


model_from_equation:=function(M,Q,xf,yf,desc)

  // The model of the same curve as M with equation Q(x,y) = 0 in L[x][y] and functions
  // xf, yf (with Q(xf,yf) = 0), made monic and integral by lc_scaling; its plane equation is
  // the homogenization of Q, with base = [x, y, 1]. Second value: the polynomial c over L of
  // lc_scaling, so that the function y of the model is c(xf)*yf.

  Qm,c:=lc_scaling(Q);
  K:=BaseRing(M`C);
  yf:=Evaluate(PolynomialRing(K)![from_model_field(a,K):a in Coefficients(c)],xf)*yf;
  return rec<model_format|Q:=Qm,L:=M`L,C:=M`C,FF:=M`FF,xf:=xf,yf:=yf,F:=homogenization(Qm),
                          base:=[xf,yf,M`FF!1],c:=PolynomialRing(M`L)!1,desc:=M`desc cat [desc]>, c;
end function;


transform_plane_model:=function(M,g:label:="")

  // The model of the plane curve of M in the coordinates v' = g^(-1)*v, v = (u_1,u_2,u_3):
  // the equation F'(v') = F(g*v') and the functions g^(-1)*base, then model_from_plane.
  // Input:  M a model; g an invertible 3 x 3 matrix over Z, Q or L.

  L:=M`L; F:=M`F; R:=Parent(F);
  g:=ChangeRing(g,L);
  v:=[R.i:i in [1..3]];
  Fg:=Evaluate(F,[&+[g[i,j]*v[j]:j in [1..3]]:i in [1..3]]);
  K:=BaseRing(M`C);
  gi:=g^(-1);
  base:=[&+[from_model_field(gi[i,j],K)*M`base[j]:j in [1..3]]:i in [1..3]];
  label:=(label eq "") select Sprintf("coordinates g^(-1)*(u1,u2,u3) with g = %o",Eltseq(g)) else label;
  return model_from_plane(Fg,base,L,M`C,M`FF,M`desc cat [label]);
end function;


mobius_model:=function(M,A)

  // The model of the curve of M with the coordinate x' of x = (a*x'+b)/(c*x'+e),
  // A = [[a,b],[c,e]] in GL_2(Z): y' = y*(c*x'+e)^k with the least k such that
  //   Q'(x',y') = (c*x'+e)^(k*d) * Q((a*x'+b)/(c*x'+e), y'/(c*x'+e)^k)
  // is a polynomial (deg a_i <= k*(d-i) for Q = sum_i a_i(x)*y^i). The degree d in y is
  // unchanged, so is the monic leading coefficient; for a hyperelliptic model y^2 = f(x) this
  // is the usual change of the Weierstrass model, with k = g+1.
  // Further values: k and the polynomial c over L of lc_scaling (a constant unless Q' has a
  // non-constant leading coefficient): the function y of the new model is
  // c(x')*y*(c*x'+e)^k, which converts the coordinates of points (quadratic_points.m).

  Q:=M`Q; L:=M`L; d:=Degree(Q);
  a:=A[1,1]; b:=A[1,2]; c:=A[2,1]; e:=A[2,2];
  if a*e-b*c eq 0 then
    error "mobius_model: the matrix must be invertible";
  end if;
  k:=Maximum([1] cat [Ceiling(Degree(Coefficient(Q,i))/(d-i)):i in [0..d-1]|Coefficient(Q,i) ne 0]);
  Lx<x>:=PolynomialRing(L); Lxy<y>:=PolynomialRing(Lx);
  Xn:=a*x+b; Zn:=c*x+e;
  // a_i((a*x+b)/(c*x+e))*(c*x+e)^(k*(d-i)), via the homogenization of a_i of degree k*(d-i)
  coef:=func<ai,n|&+[Lx|Coefficient(ai,j)*Xn^j*Zn^(n-j):j in [0..Degree(ai)]]>;
  Qn:=&+[Lxy|coef(Coefficient(Q,i),k*(d-i))*y^i:i in [0..d]];
  xf:=(e*M`xf-b)/(a-c*M`xf);
  yf:=M`yf*(c*xf+e)^k;
  Mn,cn:=model_from_equation(M,Qn,xf,yf,Sprintf("x = (%o*x'+%o)/(%o*x'+%o), y = y'/(%o*x'+%o)^%o",a,b,c,e,c,e,k));
  return Mn,k,cn;
end function;


plane_projection:=function(C)

  // A birational projection of the projective curve C in P^n, n >= 2, to the plane.
  // Output: the plane curve D in P^2 and linear forms l_1, l_2, l_3 in the coordinates of P^n
  //         with D the image of C under (l_1 : l_2 : l_3).
  // Method: repeated projection from points with small coordinates that do not lie on the
  //         curve; a projection is accepted if it preserves the degree, i.e. is birational
  //         onto its image.

  D:=C;
  forms:=[Ambient(C).i:i in [1..Dimension(Ambient(C))+1]];
  while Dimension(Ambient(D)) gt 2 do
    n:=Dimension(Ambient(D));
    cands:=[[(j eq i) select 1 else 0:j in [1..n+1]]:i in [1..n+1]]
           cat [[1:j in [1..n+1]],[j:j in [1..n+1]],[(-1)^j*j^2+1:j in [1..n+1]]];
    found:=false;
    for c in cands do
      pt:=Ambient(D)!c;
      if pt in D then
        continue;
      end if;
      E,pr:=Projection(D,pt);
      if Dimension(E) eq 1 and Degree(E) eq Degree(D) then
        forms:=[Evaluate(l,forms):l in DefiningPolynomials(pr)];
        D:=E;
        found:=true;
        break;
      end if;
    end for;
    if not found then
      error "plane_projection: no birational projection to the plane found; give a plane model of the curve";
    end if;
  end while;
  return D, forms;
end function;


curve_model:=function(C)

  // A model of a curve for the library.
  // Input:  C a Curve over Q or a number field (in the affine or projective plane, or in a
  //         higher-dimensional affine or projective space), or a polynomial Q(x,y) in K[x][y]
  //         or K[x,y].
  // Output: a model record (see the file header). For a plane curve F(X,Y,Z) = 0 (or f(x,y)
  //         = 0) the model is the affine patch Z = 1 with x = X/Z and y = Y/Z, made monic and
  //         integral by lc_scaling. A curve in a higher-dimensional space is first projected to
  //         a plane curve (plane_projection). If the leading coefficient a(x) in y is not
  //         constant (if (0:1:0) lies on the plane curve), the zeros of a(x) become bad
  //         x-coordinates; affine_patches finds patches in which these residue discs are good
  //         (at the price of a larger degree in y).
  // Errors: if C is not an integral curve.

  if Type(C) in {RngMPolElt,RngUPolElt} then
    Q:=C;
    if Type(Q) eq RngMPolElt then
      if Rank(Parent(Q)) ne 2 then
        error "curve_model: a polynomial must be in two variables x, y";
      end if;
      A2<a,b>:=AffineSpace(BaseRing(Parent(Q)),2);
      C:=Curve(A2,Evaluate(Q,[a,b]));
    else
      A2<a,b>:=AffineSpace(BaseRing(BaseRing(Parent(Q))),2);
      C:=Curve(A2,&+[Evaluate(Coefficient(Q,i),a)*b^i:i in [0..Degree(Q)]]);
    end if;
  end if;
  if not ISA(Type(C),Crv) then
    error "curve_model: the input must be a Curve, or a polynomial in x and y";
  end if;
  if not (IsReduced(C) and IsIrreducible(C)) then
    error "curve_model: the curve must be reduced and irreducible";
  end if;
  K:=BaseRing(C);
  L,emb:=model_field(K);
  FF:=FunctionField(C);
  Cp:=IsAffine(C) select ProjectiveClosure(C) else C;
  desc:=[];
  if Dimension(Ambient(Cp)) gt 2 then
    D,forms:=plane_projection(Cp);
    desc:=[Sprintf("projection to the plane by %o",forms)];
  else
    D:=Cp; forms:=[Ambient(Cp).i:i in [1..3]];
  end if;
  R<X,Y,Z>:=PolynomialRing(L,3);
  F:=map_coefficients(DefiningPolynomial(D),R,emb);
  // the coordinate functions, with a denominator that does not vanish on the curve
  k:=[k:k in [3,2,1]|not (Ambient(D).k in Ideal(D))][1];
  base:=[FF!(forms[i]/forms[k]):i in [1..3]];
  return model_from_plane(F,base,L,C,FF,desc);
end function;


model_is_consistent:=function(M)

  // Whether the functions of the model satisfy its equation: Q(xf,yf) = 0 in FF.

  K:=BaseRing(M`C); Kx:=PolynomialRing(K);
  coef:=func<a|Evaluate(Kx![from_model_field(c,K):c in Coefficients(a)],M`xf)>;
  return &+[coef(Coefficient(M`Q,i))*M`yf^i:i in [0..Degree(M`Q)]] eq 0;
end function;


// ---------------------------------------------------------------------------------------------
// The good-reduction assumptions at a prime: reduction_test_data and good_reduction_at are
// in integrals.m (coleman_data runs them with the option full_check)


frobenius_check:=function(Q,L,P,N)

  // A trial run of coleman_data at P with precision N: whether it succeeds and the
  // characteristic polynomial of the Frobenius matrix agrees modulo pi^(N-1) with the one
  // given by the zeta function of the reduction (T^(2g)*L(1/T), L the L-polynomial).
  // Output: true and "", or false and the reason.

  try
    data:=coleman_data(Q,L,P,N:verbose:=false);
  catch e
    return false, "coleman_data fails: " cat e`Object;
  end try;
  Fq,res:=ResidueClassField(P);
  Fqx:=PolynomialRing(Fq); Fqxy:=PolynomialRing(Fqx);
  Qt:=&+[Fqxy|reduce_poly_mod_P(Coefficient(Q,i),res,Fqx)*Fqxy.1^i:i in [0..Degree(Q)]];
  Lp:=LPolynomial(FunctionField(Qt));
  g:=data`g;
  expected:=[Coefficient(Lp,2*g-i):i in [0..2*g]]; // the coefficients of T^(2g)*L(1/T)
  cp:=Coefficients(CharacteristicPolynomial(ChangeRing(data`F,data`m)));
  if #cp ne 2*g+1 or not &and[Valuation(cp[i]-expected[i]) ge Minimum(N,data`N)-1:i in [1..2*g+1]] then
    return false, "the Frobenius matrix does not match the zeta function of the reduction";
  end if;
  return true, "";
end function;


primes_up_to_norm:=function(L,bound)

  // The prime ideals of O_L of norm at most bound, ordered by norm.

  OL:=MaximalOrder(L);
  Ps:=[Pp[1]:Pp in Decomposition(OL,p),p in PrimesUpTo(bound)];
  Ps:=[P:P in Ps|Norm(P) le bound];
  Sort(~Ps,func<P1,P2|Norm(P1)-Norm(P2)>);
  return Ps;
end function;


good_primes:=function(M:bound:=50,primes:=[],check:=false,N:=6,verbose:=false)

  // The good primes of a model: the primes P at which the triple (Q, W^0, W^inf) passes the
  // tests of good_reduction_at (all good-reduction assumptions of the article).
  // Input:  M a model (curve_model), or a polynomial Q(x,y) or Curve accepted by curve_model.
  //         bound: the primes of norm <= bound are tested (unless primes is given);
  //         primes: a sequence of prime ideals of O_L, or of rational primes (then all primes
  //           above them), to test instead;
  //         check: also run coleman_data at precision N and compare the Frobenius matrix with
  //           the zeta function of the reduction (frobenius_check; slower);
  //         verbose: print the outcome for every prime.
  // Output: the sequence of good primes (prime ideals of O_L, ordered by norm), and a sequence
  //         of <P, reason> for the other primes.
  // A good prime of norm q and residue characteristic p gives K with residue field F_q; the
  // cost of coleman_data grows linearly in q (or in p for the p-power lift), and the solver
  // (effective_chabauty) needs P unramified.

  if Type(M) ne Rec then
    M:=curve_model(M);
  end if;
  Q:=M`Q; L:=M`L; OL:=MaximalOrder(L);
  if #primes eq 0 then
    Ps:=primes_up_to_norm(L,bound);
  else
    Ps:=&cat[(Type(p) eq RngIntElt) select [Pp[1]:Pp in Decomposition(OL,p)] else [OL!!p]:p in primes];
  end if;
  T:=reduction_test_data(Q);
  good:=[]; bad:=[];
  for P in Ps do
    ok,why:=good_reduction_at(T,P);
    if ok and check then
      ok,why:=frobenius_check(Q,L,P,N);
    end if;
    if ok then
      Append(~good,P);
    else
      Append(~bad,<P,why>);
    end if;
    if verbose then
      printf "good_primes: prime of norm %o above %o: %o\n",Norm(P),Minimum(P),ok select "good" else "bad: " cat why;
    end if;
  end for;
  return good, bad;
end function;


model_coleman_data:=function(M,P,N:aux:=false,extension:=0,lift:="auto",verbose:=false,full_check:=false)

  // coleman_data for the model M at the prime P of O_L (L = M`L), or, with aux := true, at the
  // prime above P of the quadratic extension L2 = L(sqrt u) of inert_quadratic_extension: then
  // K is the unramified quadratic extension of L_P, with residue field F_(q^2). The integral
  // bases W0, Winf are computed over L in both cases, so that the functions b^0, b^inf of the
  // data are functions on the curve over its base field (point_records and holomorphic_forms
  // evaluate them in M`FF); a model over Q keeps the rational branch of coleman_data.
  // Input:  M a model, P a prime ideal of O_L at which M has good reduction (of odd residue
  //         characteristic if aux), N the precision; extension (with aux): the triple
  //         <L2, P2, u> of inert_quadratic_extension to use (data of several models of a curve
  //         must share one field L2: a second call of inert_quadratic_extension builds another
  //         copy of it); lift, verbose, full_check as in coleman_data.
  // Output: the data, and u (1 without aux).

  L:=M`L; P:=MaximalOrder(L)!!P;
  if not aux then
    return coleman_data(M`Q,L,P,N:lift:=lift,verbose:=verbose,full_check:=full_check), 1;
  end if;
  if Type(extension) eq Tup then
    L2,P2,u:=Explode(extension);
  else
    L2,P2,u:=inert_quadratic_extension(L,P);
  end if;
  L2x:=PolynomialRing(L2); L2xy:=PolynomialRing(L2x); L2t:=FieldOfFractions(L2x);
  toL2x:=func<f|L2x![L2!c:c in Coefficients(f)]>;
  toL2:=func<W|Matrix(L2t,NumberOfRows(W),NumberOfColumns(W),[toL2x(Numerator(a))/toL2x(Denominator(a)):a in Eltseq(W)])>;
  Q2:=L2xy![toL2x(a):a in Coefficients(M`Q)];
  data:=coleman_data(Q2,L2,P2,N:W0:=toL2(mat_W0(M`Q)),Winf:=toL2(mat_Winf(M`Q)),lift:=lift,verbose:=verbose,full_check:=full_check);
  return data, u;
end function;


// ---------------------------------------------------------------------------------------------
// Better models

model_height:=function(Q)

  // The size of the coefficients of Q: the maximal absolute value of the numerators and
  // denominators of their rational coordinates.

  return Maximum([1] cat [Maximum(Abs(Numerator(r)),Abs(Denominator(r))):r in Eltseq(c),c in Coefficients(a),a in Coefficients(Q)]);
end function;


minimal_models_over_Q:=function(M)

  // For a model over Q: the reduced minimal Weierstrass model if M`Q = y^2 + h(x)*y - f(x)
  // (a hyperelliptic curve), and the minimized and reduced plane quartic
  // (MinimizeReducePlaneQuartic) if M`F is a smooth plane quartic. Otherwise [].

  if Degree(M`L) gt 1 then
    return [];
  end if;
  out:=[];
  Q:=M`Q; d:=Degree(Q);
  Qx:=PolynomialRing(Rationals());
  toQ:=func<a|Qx![Rationals()!c:c in Coefficients(a)]>;
  if d eq 2 then
    h:=toQ(Coefficient(Q,1)); f:=-toQ(Coefficient(Q,0));
    ok,H:=IsHyperellipticCurve([f,h]);
    if ok and Genus(H) ge 2 then
      try
        H2,phi:=ReducedMinimalWeierstrassModel(H);
        f2,h2:=HyperellipticPolynomials(H2);
        Lx<x>:=PolynomialRing(M`L); Lxy<y>:=PolynomialRing(Lx);
        Q2:=y^2+(Lx!h2)*y-(Lx!f2);
        ev:=[Evaluate(p,[M`xf,M`yf,M`FF!1]):p in DefiningPolynomials(phi)];
        g:=Genus(H);
        Append(~out,model_from_equation(M,Q2,ev[1]/ev[3],ev[2]/ev[3]^(g+1),"reduced minimal Weierstrass model"));
      catch e
        ;
      end try;
    end if;
  end if;
  F:=M`F;
  if TotalDegree(F) eq 4 and IsHomogeneous(F) then
    try
      R:=PolynomialRing(Rationals(),3);
      FQ:=map_coefficients(F,R,func<c|Rationals()!c>);
      FQ*:=LCM([Denominator(c):c in Coefficients(FQ)]);
      FQ/:=GCD([Integers()!c:c in Coefficients(FQ)]);
      _,T:=MinimizeReducePlaneQuartic(FQ);
      Append(~out,transform_plane_model(M,T:label:="MinimizeReducePlaneQuartic"));
    catch e
      ;
    end try;
  end if;
  return out;
end function;


improve_model:=function(M:bound:=50,verbose:=true,mobius:=true,coordinates:=true)

  // Models of the curve of M obtained by transformations that preserve the curve, ranked by
  // their good primes.
  // Input:  M a model, or a Curve or polynomial accepted by curve_model; bound: the primes
  //         of norm <= bound are tested; verbose: print the candidates; mobius, coordinates:
  //         include the candidates of these kinds.
  // Output: the sequence of <model, good primes> sorted by: the norm of the smallest good
  //         prime, then the number of good primes of norm <= bound (more is better), then the
  //         degree d in y; on a tie M itself comes first, the others by their degree in x and
  //         the size of their coefficients. The first entry is the best model.
  // Candidates: M; for coordinates, the changes of coordinates of the plane curve by the
  //         permutations of the coordinates combined with small shears (if they do not
  //         increase the degree in y, i.e. the degree of the map x); for mobius, the
  //         changes x = 1/x' + t, t in {0,1,-1,2,-2}, of the coordinate x with the weighted
  //         change of y (mobius_model; for a hyperelliptic curve the changes of the
  //         Weierstrass model); over Q also minimal_models_over_Q. A transformation preserves
  //         the curve, so all its points can be converted by point_records for every
  //         candidate; it changes which points lie in bad residue discs.

  if Type(M) ne Rec then
    M:=curve_model(M);
  end if;
  d:=Degree(M`Q);
  cands:=[<M,"the given model">];
  if coordinates then
    perms:=[PermutationMatrix(Integers(),s):s in Sym(3)];
    shears:=[Matrix(Integers(),3,3,e):e in [[1,0,0,0,1,0,0,0,1],[1,1,0,0,1,0,0,0,1],[1,0,0,1,1,0,0,0,1],
                                           [1,0,1,0,1,0,0,0,1],[1,0,0,0,1,1,0,0,1]]];
    gs:=[p*sh:sh in shears,p in perms];
    gs:=[gs[i]:i in [1..#gs]|gs[i] notin gs[1..i-1] and not IsOne(gs[i])];
    for g in gs do
      try
        Mg:=transform_plane_model(M,g);
        if Degree(Mg`Q) le d then
          Append(~cands,<Mg,Sprintf("coordinates g^(-1)*(u1,u2,u3), g = %o",Eltseq(g))>);
        end if;
      catch e
        ;
      end try;
    end for;
  end if;
  if mobius then
    for t in [0,1,-1,2,-2] do
      try
        Append(~cands,<mobius_model(M,Matrix(Integers(),2,2,[t,1,1,0])),Sprintf("x = 1/x' + %o",t)>);
      catch e
        ;
      end try;
    end for;
  end if;
  for Mq in minimal_models_over_Q(M) do
    Append(~cands,<Mq,Mq`desc[#Mq`desc]>);
  end for;

  ranked:=[];
  for i:=1 to #cands do
    c:=cands[i];
    try
      good:=good_primes(c[1]:bound:=bound);
    catch e
      good:=[];
    end try;
    pmin:=(#good gt 0) select Norm(good[1]) else bound+1;
    Q:=c[1]`Q;
    // on equal primes the given model is kept
    key:=[pmin,-#good,Degree(Q),(i eq 1) select 0 else 1,Maximum([Degree(a):a in Coefficients(Q)]),model_height(Q)];
    Append(~ranked,<key,c[1],good,c[2]>);
    if verbose then
      printf "improve_model: %o: d = %o, good primes of norm <= %o: %o\n",c[2],Degree(Q),bound,[Norm(P):P in good];
    end if;
  end for;
  Sort(~ranked,func<a,b|(a[1] lt b[1]) select -1 else ((a[1] eq b[1]) select 0 else 1)>);
  return [<r[2],r[3]>:r in ranked];
end function;


// ---------------------------------------------------------------------------------------------
// Affine patches

patch_candidates:=function(maxtries)

  // The coordinate changes g (3 x 3 matrices over Z, the plane coordinates u = g*u') that
  // affine_patches tries, in this order: the identity, the permutations of the coordinates
  // combined with small shears (as in improve_model), and products of unipotent upper and
  // lower triangular matrices with entries in {-1,0,1}; at most maxtries of them.

  perms:=[PermutationMatrix(Integers(),s):s in Sym(3)];
  shears:=[Matrix(Integers(),3,3,e):e in [[1,0,0,0,1,0,0,0,1],[1,1,0,0,1,0,0,0,1],[1,0,0,1,1,0,0,0,1],
                                         [1,0,1,0,1,0,0,0,1],[1,0,0,0,1,1,0,0,1]]];
  upper:=[Matrix(Integers(),3,3,[1,a,b,0,1,c,0,0,1]):a,b,c in [0,1,-1]];
  lower:=[Matrix(Integers(),3,3,[1,0,0,a,1,0,b,c,1]):a,b,c in [0,1,-1]];
  gs:=[IdentityMatrix(Integers(),3)] cat [p*sh:sh in shears,p in perms] cat [U*Lo:Lo in lower,U in upper];
  gs:=[gs[i]:i in [1..#gs]|gs[i] notin gs[1..i-1]];
  return gs[1..Minimum(#gs,maxtries)];
end function;


reduced_good_test:=function(Mg,g,P,res)

  // For the model Mg of the plane curve of a model M in the coordinates u' = g^(-1)*u
  // (transform_plane_model, or M itself for g = 1): a function that decides whether a point of
  // the reduction modulo P, given by its projective coordinates u in the plane coordinates of M
  // over the residue field reached by res : L -> k, lies in a good residue disc of Mg (u' is
  // finite and r(u'_1/u'_3) ne 0 modulo P); false if r is not P-integral with a unit leading
  // coefficient, so that no disc of Mg counts as good. A cheap test: the model must still pass
  // good_reduction_at.

  L:=Mg`L; OL:=MaximalOrder(L);
  r:=auxpolys(Mg`Q);
  if not is_P_integral_poly(r,P) or Valuation(LeadingCoefficient(r),P) gt 0 then
    return false;
  end if;
  k:=Parent(res(L!1));
  rt:=PolynomialRing(k)![res(c):c in Coefficients(r)];
  gti:=Transpose(Matrix(k,3,3,[res(c):c in Eltseq(ChangeRing(ChangeRing(g,L)^(-1),OL))]));
  return function(u)
    w:=Vector(k,u)*gti; // the point in the coordinates of Mg
    return w[3] ne 0 and Evaluate(rt,w[1]/w[3]) ne 0;
  end function;
end function;


affine_patches:=function(M,P:verbose:=true,maxtries:=300,data:=0)

  // Plane models (affine patches of the plane curve of M, in other coordinates) whose good
  // residue discs at P together contain all smooth F_q-points of the reduction of the plane
  // curve. A disc is good for a model if its point lies in the affine patch u_3 ne 0 and its
  // x-coordinate is not a zero of r mod P; computing the zeros of the integrals in a disc
  // with a model in which it is good avoids the expensive auxiliary extension of bad discs.
  // Input:  M a model; P a prime ideal of O_L at which M has good reduction; maxtries: the
  //         number of coordinate changes tried at most; data (optional): coleman_data of M
  //         at P (e.g. model_coleman_data with aux): the points are then taken over the
  //         residue field of data`K (F_(q^2) with aux), in Magma's field object of that
  //         residue field, with the reduction through data`m.
  // Output: a record with
  //           patches   the models (M first if it is among them),
  //           transforms for every model the matrix g over Z of its coordinates: its plane
  //                     coordinates u' and those u of M satisfy u = g*u' (transform_plane_model),
  //           points    for every model, the points of the reduction (projective
  //                     coordinates in the coordinates of M`F over F_q) whose disc is good
  //                     for it and not for an earlier one,
  //           singular  the singular F_q-points of the reduced plane curve: their discs
  //                     (one for every branch) are bad for every plane model and are treated
  //                     as bad discs by the library,
  //           uncovered the smooth points in no good disc of the models tried.
  // Method: the candidates are M, the coordinate changes of improve_model (permutations and
  // shears) and, while points remain uncovered, products of unipotent upper and lower
  // triangular matrices with entries in {-1,0,1}; a greedy cover chooses the candidate with
  // the most uncovered good points (on a tie the one of smaller degree d in y; a patch can
  // have a larger d than M, e.g. if (0:1:0) lies on the curve for M but not for the patch),
  // and a chosen model must pass all tests of good reduction at P (good_reduction_at),
  // otherwise it is discarded.

  L:=M`L;
  OL:=MaximalOrder(L);
  P:=OL!!P;
  if Type(data) eq Rec then // the residue field of data`K, reached through data`m
    OK:=RingOfIntegers(data`K);
    Fq,resK:=ResidueClassField(OK);
    res:=func<c|resK(OK!data`m(data`L!(L!c)))>;
  else
    Fq,res:=ResidueClassField(P);
  end if;
  F:=M`F;
  // the reduction of the plane curve, scaled to be primitive at P
  v:=Minimum([Valuation(c,P):c in Coefficients(F)]);
  piP:=UniformizingElement(P);
  R3:=PolynomialRing(Fq,3);
  Ft:=map_coefficients(F,R3,func<c|res(c/piP^v)>);
  pts:=[p:p in Points(Scheme(ProjectiveSpace(R3),Ft))];
  grad:=[Derivative(Ft,i):i in [1..3]];
  sing:=[p:p in pts|&and[Evaluate(gr,Eltseq(p)) eq 0:gr in grad]];
  smooth:=[p:p in pts|p notin sing];

  // the coordinate changes, in the order in which they are tried
  gs:=patch_candidates(maxtries);

  // the good points of the model in the coordinates g^(-1)*v (a cheap test: only r mod P)
  good_points:=function(g)
    Mg:=IsOne(g) select M else transform_plane_model(M,g);
    isgood:=reduced_good_test(Mg,g,P,res);
    if Type(isgood) eq BoolElt then
      return Mg,{};
    end if;
    return Mg,{p:p in smooth|isgood(Eltseq(p))};
  end function;

  patches:=[]; transforms:=[]; covered:=[]; todo:={p:p in smooth};
  cands:=[]; next:=1;
  while #todo gt 0 do
    // evaluate more candidates while none covers an uncovered point
    while next le #gs and forall{c:c in cands|#(c[2] meet todo) eq 0} do
      try
        Mg,good:=good_points(gs[next]);
        Append(~cands,<Mg,good,gs[next]>);
      catch e
        ;
      end try;
      next+:=1;
    end while;
    counts:=[#(c[2] meet todo):c in cands];
    if #counts eq 0 or Maximum(counts) eq 0 then
      break;
    end if;
    // the most uncovered good points; on a tie the smallest degree d of the model
    _,best:=Maximum([<counts[i],-Degree(cands[i][1]`Q)>:i in [1..#cands]]);
    if good_reduction_at(reduction_test_data(cands[best][1]`Q),P) then
      Append(~patches,cands[best][1]);
      Append(~transforms,cands[best][3]);
      Append(~covered,[p:p in cands[best][2] meet todo]);
      todo diff:=cands[best][2];
    end if;
    Remove(~cands,best);
  end while;
  if verbose then
    printf "affine_patches: %o smooth points of the reduction mod P (norm %o) in %o patch(es)",#smooth-#todo,Norm(P),#patches;
    printf "; %o singular point(s), %o smooth point(s) in no good disc of the models tried.\n",#sing,#todo;
  end if;
  fmt:=recformat<patches,transforms,points,singular,uncovered>;
  return rec<fmt|patches:=patches,transforms:=transforms,points:=covered,singular:=sing,uncovered:=[p:p in todo]>;
end function;


// ---------------------------------------------------------------------------------------------
// Points of the curve as point records

model_basis_functions:=function(M,W)

  // The functions b_i = sum_j W[i,j](x)*y^(j-1) of the model M in its function field, for
  // W = data`W0 or data`Winf (over L(x), over Q(x) in the rational branch, or over the field
  // L2 of model_coleman_data with aux, with coefficients in L).

  K:=BaseRing(M`C);
  Kx:=PolynomialRing(K);
  ev:=func<a|Evaluate(Kx![to_curve_field(c,M):c in Coefficients(Numerator(a))],M`xf)/
             Evaluate(Kx![to_curve_field(c,M):c in Coefficients(Denominator(a))],M`xf)>;
  d:=NumberOfRows(W);
  return [&+[ev(W[i,j])*M`yf^(j-1):j in [1..d]|W[i,j] ne 0]:i in [1..d]];
end function;


residue_field_embeddings:=function(pl,M,data)

  // The embeddings into K = data`K of the residue field of the place pl of M`FF that extend
  // the map from the base field of the curve to K (into M`L, then into data`L, then data`m),
  // as functions on the residue field: one for every root in K of the defining polynomial of
  // the residue field over the base field. There are none if the residue field does not embed
  // into K, e.g. for a quadratic field ramified at P when K is unramified.

  Kb:=BaseRing(M`C); _,emb:=model_field(Kb);
  K:=data`K;
  toK:=func<c|data`m(data`L!emb(c))>;
  E:=ResidueClassField(pl);
  hK:=PolynomialRing(K)![toK(c):c in Coefficients(DefiningPolynomial(E))];
  embedding:=function(r)
    return func<z|&+[K|toK(cs[i])*r^(i-1):i in [1..#cs]] where cs:=Eltseq(E!z)>;
  end function;
  return [embedding(K!rt[1]):rt in Roots(hK)];
end function;


point_records:=function(M,data,pts)

  // The point records (set_bad_point) of points of the curve of the model M.
  // Input:  M a model; data the output of coleman_data for M`Q (and M`L), or of
  //         model_coleman_data for M (also with aux);
  //         pts a sequence (or list) of points of M`C (over its base field, or over a finite
  //         extension of it), places of its function field (of any degree), effective divisors
  //         of M`C, or pairs [x0, y0] of coordinates of the model M`Q over the base field.
  // Output: the sequence of point records, and for every record the index in pts of the
  //         element it comes from. A place of degree k (a point over an extension of degree k
  //         of the base field) gives one record for every embedding of its residue field into
  //         K: k records if K contains the residue field (e.g. the points of degree 2 whose
  //         field is unramified at P, for model_coleman_data with aux), none if it does not
  //         embed. An effective divisor gives the records of the places of its support, each
  //         repeated according to its multiplicity. A point of M`C at which the curve is
  //         singular can give several records (one for every place above it). A point at
  //         infinity of the model (x = infinity) gives an infinite point record (1/x and
  //         b^inf).
  // Errors: if a point does not lie on the curve, or a divisor is not effective.

  K:=BaseRing(M`C); _,emb:=model_field(K);
  b0:=model_basis_functions(M,data`W0);
  binf:=model_basis_functions(M,data`Winf);
  records:=[]; which:=[];
  for k:=1 to #pts do
    pt:=pts[k];
    if Type(pt) eq SeqEnum then
      // a point of the model: the places of degree 1 where x = x0 and y = y0
      x0:=K!pt[1]; y0:=K!pt[2];
      pls:=[<pl,1>:pl in Zeros(M`xf-x0)|Degree(pl) eq 1 and Evaluate(M`yf,pl) eq y0];
      if #pls eq 0 then
        error Sprintf("point_records: (%o, %o) is not a point of the model",pt[1],pt[2]);
      end if;
    elif ISA(Type(pt),Pt) then
      if Ring(Parent(pt)) cmpeq K then
        pls:=[<pl,1>:pl in Places(pt)|Degree(pl) eq 1];
      else // a point over an extension of the base field: its closed point
        pls:=[<Place(pt),1>];
      end if;
    elif Type(pt) eq DivCrvElt then
      supp,mult:=Support(pt);
      if exists{a:a in mult|a lt 0} then
        error "point_records: a divisor must be effective";
      end if;
      pls:=[<supp[i],mult[i]>:i in [1..#supp]];
    else
      pls:=[<pt,1>];
    end if;
    for t in pls do
      pl:=t[1];
      inf:=Valuation(M`xf,pl) lt 0;
      s:=inf select 1/M`xf else M`xf; bs:=inf select binf else b0;
      if Degree(pl) eq 1 then
        Rs:=[set_bad_point(emb(Evaluate(s,pl)),[emb(Evaluate(b,pl)):b in bs],inf,data)];
      else
        Rs:=[set_bad_point(e(Evaluate(s,pl)),[e(Evaluate(b,pl)):b in bs],inf,data):e in residue_field_embeddings(pl,M,data)];
      end if;
      for i:=1 to t[2] do
        records cat:=Rs; which cat:=[k:R in Rs];
      end for;
    end for;
  end for;
  return records, which;
end function;


// ---------------------------------------------------------------------------------------------
// Chabauty-Coleman for a curve

reduced_curve_function_field:=function(M,P)

  // The function field over F_q of the reduction of the model M modulo the prime P.

  Fq,res:=ResidueClassField(P);
  Fqx:=PolynomialRing(Fq);
  return FunctionField(PolynomialRing(Fqx)![reduce_poly_mod_P(c,res,Fqx):c in Coefficients(M`Q)]);
end function;


function_field_over:=function(M,L)

  // The algorithmic function field of the curve of M with its field of constants extended to
  // the number field L (data`L: the field of M itself, or L2 of model_coleman_data with aux),
  // and the map from M`FF to it.

  AF,phi:=AlgorithmicFunctionField(M`FF);
  if Degree(L) eq Degree(M`L) then
    return AF,phi;
  end if;
  E,emb:=ConstantFieldExtension(AF,L);
  return E,phi*emb;

end function;


holomorphic_forms:=function(M,data:field:=0)

  // The holomorphic forms omega_1, ..., omega_g of the basis of data (coleman_data for M`Q:
  // the first g entries of data`basis, omega_i = sum_k basis[i][k](x)*b^0_k dx/z with
  // z = r/lc(r)) as differentials of the algorithmic function field of the curve of M, with its
  // constants extended to data`L if the data are over an extension of M`L
  // (function_field_over), and the map from M`FF to that field. field: a pair <E, phi> of
  // function_field_over to compute in (holomorphic_transition passes one field for two models).

  if Type(field) eq Tup then
    E,phi:=Explode(field);
  else
    E,phi:=function_field_over(M,data`L);
  end if;
  CE:=ConstantField(E);
  extended:=Degree(data`L) ne Degree(M`L);
  coef:=func<c|extended select CE!(data`L!c) else to_curve_field(c,M)>;
  ev:=func<f|Evaluate(PolynomialRing(CE)![coef(c):c in Coefficients(f)],phi(M`xf))>;
  b0:=[phi(b):b in model_basis_functions(M,data`W0)];
  z:=ev(data`r/LeadingCoefficient(data`r));
  dx:=Differential(phi(M`xf));
  return [(&+[ev(data`basis[i][k])*b0[k]:k in [1..#b0]]/z)*dx:i in [1..data`g]], phi;

end function;


holomorphic_transition:=function(M,data,Mi,datai)

  // The g x g matrix T with omega_j = sum_k T[j,k]*omega'_k for the holomorphic forms omega_j of
  // data (model M) and omega'_k of datai (another model Mi of the same curve, with data over the
  // same field), from their coordinates in a basis of the holomorphic differentials of the
  // function field. T is over the base field of the curve, or over data`L if the data are over
  // an extension of M`L (model_coleman_data with aux). A vanishing differential v (w.r.t. the
  // omega_j) is v*T w.r.t. the omega'_k.

  if not (data`L cmpeq datai`L) then
    error "holomorphic_transition: the data of the two models must be over the same number field; with aux, compute them with the same extension (model_coleman_data)";
  end if;
  E,phi:=function_field_over(M,data`L);
  forms:=holomorphic_forms(M,data:field:=<E,phi>);
  formsi:=holomorphic_forms(Mi,datai:field:=<E,phi>); // (the models are of the same curve: the same function field)
  V,mV:=SpaceOfHolomorphicDifferentials(E);
  coords:=func<fs|Matrix([Eltseq(w@@mV):w in fs])>;
  return coords(forms)*coords(formsi)^(-1);

end function;


plane_reduction:=function(M,data,R)

  // The reduction modulo P of the finite point record R of the model M (data = coleman_data for
  // M`Q) as a point of the plane curve M`F over F_q: the coordinates (x*c(x) : y : c(x)) of
  // u = (x : y/c(x) : 1), divided by their content, with y from the values of b^0
  // (b^0 = W0*(1,y,...)) and c = M`c.

  K:=data`K; L:=data`L; m:=data`m;
  OK:=RingOfIntegers(K); Fq,res:=ResidueClassField(OK);
  y:=(Vector(R`b)*Transpose(eval_mat(data`W0^(-1),L,K,m,R`x)))[2];
  cx:=Evaluate(PolynomialRing(K)![m(L!a):a in Coefficients(M`c)],R`x);
  u:=[R`x*cx,y,cx];
  v:=Minimum([Valuation(a):a in u|not IsWeaklyZero(a)]);
  return [res(OK!(a/UniformizingElement(K)^v)):a in u];

end function;


jacobian_rank_bounds:=function(M)

  // Lower and upper bounds for the Mordell-Weil rank of the Jacobian of the curve of the
  // model M over its field L, where Magma provides them: for a model y^2 + h(x)*y = f(x) of
  // genus 2, over Q RankBounds of the Jacobian (2-descent), over a number field the upper
  // bound RankBound (2-descent) and the lower bound 0. Returns [lo, hi], or [] if no bounds
  // are available.

  Q:=M`Q;
  if Degree(Q) ne 2 then
    return [];
  end if;
  rational:=Degree(M`L) eq 1;
  R:=rational select Rationals() else M`L;
  Rx:=PolynomialRing(R);
  h:=Rx![R!c:c in Coefficients(Coefficient(Q,1))];
  f:=-Rx![R!c:c in Coefficients(Coefficient(Q,0))];
  try
    H:=HyperellipticCurve(f,h);
    if Genus(H) ne 2 then
      return [];
    end if;
    if rational then
      lo,hi:=RankBounds(Jacobian(H));
    else
      lo:=0; hi:=RankBound(Jacobian(H));
    end if;
  catch err
    return [];
  end try;
  return [lo,hi];

end function;


curve_chabauty:=function(C,pts:P:=0,N:=10,bound:=50,improve:=true,e:=0,verbose:=true,htbound:=10^5,rank_check:=false,primes:=1,maxN:=0,patches:=false)

  // Chabauty-Coleman for a curve given as a Curve (or a polynomial): the L-rational points,
  // from known points, if the Mordell-Weil rank of its Jacobian is less than its genus.
  // Input:  C a Curve or a polynomial (curve_model); pts the known L-rational points: points
  //         of C (or places, or pairs [x0,y0] of the model, see point_records), at least two;
  //         P (optional) the prime, by default the good prime of smallest norm with residue
  //         degree 1 and ramification index 1, preferring primes with p not dividing #J(F_p);
  //         N the precision of coleman_data; bound the bound for the norms of the primes
  //         tested; improve: choose the model by improve_model (otherwise curve_model); e as in
  //         coleman_integrals_on_basis; htbound the height bound for the recognition of new
  //         points (recognize_in_F); rank_check: compute bounds for the rank of the Jacobian
  //         (jacobian_rank_bounds: genus 2); primes: the number of good primes to use
  //         at most, a further one only while some candidate is neither a known point nor
  //         recognized as an L-rational point; maxN: if the computation at a prime fails
  //         for lack of precision (an error asking to increase N), it is repeated with twice
  //         the precision, up to maxN (default 4*N); patches: treat the finite bad residue
  //         discs of the model in affine patches of its plane curve where they are good
  //         (affine_patches), with the vanishing differentials transported through the
  //         function field (holomorphic_transition); the infinite discs and the discs above
  //         singular points of the reduced plane curve stay with the model.
  // Output: a record with
  //           model, prime, data   the model, the (first) prime and its coleman_data,
  //           known                the point records of pts,
  //           candidates           the points of X(K) found by effective_chabauty,
  //           matched              for every candidate the index of the known point it agrees
  //                                with (0 if none),
  //           new                  the indices of the candidates that agree with no known point,
  //           recognized           <index, x0, ys> for those of these candidates whose x (or
  //                                1/x in an infinite disc) is recognized as an element x0 of
  //                                L of small height, where ys are the y with (x0, y) an
  //                                L-rational point of the model (not empty): an L-rational
  //                                point that was not among pts,
  //           rank                 [lo, hi] bounds for the rank of the Jacobian (rank_check;
  //                                [] if not computed or not available),
  //           complete             whether at one of the primes used every candidate was a
  //                                known or a recognized point: then the L-rational points are
  //                                the known and the recognized ones,
  //           primes               the primes used,
  //           models, model_index  the models used (the model first, then the patches) and for
  //                                every candidate the index of the model of its point record
  //                                (its matched known point is the record of the same point of
  //                                the curve in the model; recognized points are given in the
  //                                coordinates of the model).
  // The candidates contain all L-rational points of the curve if the known points generate a
  // subgroup of finite index of a Mordell-Weil group of rank < g (with rank_check this is
  // verified when the upper bound for the rank is g - 1 or less and the known points have
  // that rank, which is not checked). A candidate that is neither known nor recognized is
  // either an L-rational point of large height or a p-adic point that is not L-rational; a
  // further prime at which every candidate is known or recognized excludes the latter
  // (X(L) lies in the candidates at every prime).

  if improve then
    ranked:=improve_model(C:bound:=bound,verbose:=verbose);
    M:=ranked[1][1]; good:=ranked[1][2];
  else
    M:=(Type(C) eq Rec) select C else curve_model(C);
    good:=good_primes(M:bound:=bound);
  end if;
  // the primes of residue degree 1 and ramification index 1, those with p not dividing #J(F_p)
  // first: otherwise det(F-I) is divisible by p and the linear solve of the Coleman integrals
  // loses precision
  cands:=[Q:Q in good|InertiaDegree(Q) eq 1 and RamificationIndex(Q) eq 1];
  anomalous:=func<Q|IsDivisibleBy(Evaluate(LPolynomial(reduced_curve_function_field(M,Q)),1),Norm(Q))>;
  ordered:=[Q:Q in cands|not anomalous(Q)] cat [Q:Q in cands|anomalous(Q)];
  if P cmpeq 0 then
    if #ordered eq 0 then
      error Sprintf("curve_chabauty: no good prime of residue degree 1 of norm <= %o; increase bound or give P",bound);
    end if;
    P:=ordered[1];
  end if;
  if verbose then
    printf "curve_chabauty: the model %o (%o), at the prime of norm %o\n",M`Q,M`desc,Norm(P);
  end if;

  rank:=rank_check select jacobian_rank_bounds(M) else [];

  // the candidates at the prime Q from the known points `known`, which of them agree with a
  // known point, and the new ones that are recognized as L-rational points
  // the recognized L-rational points of the candidates with the indices new of the model Mi
  recognize:=function(Mi,datai,candidates,new)
    Ly:=PolynomialRing(Mi`L);
    recognized:=[];
    for i in new do
      c:=candidates[i];
      if Valuation(c`x) lt 0 then
        continue;
      end if;
      ok,z:=recognize_in_F(c`x,datai:htbound:=htbound); // x, resp. 1/x in an infinite disc
      if not ok or (c`inf and z eq 0) then
        continue;
      end if;
      x0:=c`inf select 1/z else z;
      ys:=[rt[1]:rt in Roots(Ly![Evaluate(a,x0):a in Coefficients(Mi`Q)])];
      if #ys gt 0 then
        Append(~recognized,<i,x0,ys>);
      end if;
    end for;
    return recognized;
  end function;
  // the known point a candidate agrees with: x and b agree to the precision of the candidate
  agrees:=func<A,B|A`inf eq B`inf and IsWeaklyZero(A`x-B`x) and &and[IsWeaklyZero(A`b[i]-B`b[i]):i in [1..#A`b]]>;
  run_at:=function(Q,known,Nrun)
    data:=coleman_data(M`Q,M`L,Q,Nrun:verbose:=false);
    recs:=point_records(M,data,known);
    discsM:=0; others:=[]; delegate:=[];
    if patches then
      // the finite bad discs of M whose reduction is a good point of another patch are treated
      // there: delegate[i] holds these reductions (points of the plane curve of M) for patch i
      pat:=affine_patches(M,Q:verbose:=false);
      Fq:=ResidueClassField(RingOfIntegers(data`K));
      same:=func<u,w|Rank(Matrix(Fq,[Eltseq(u),Eltseq(w)])) eq 1>;
      others:=[i:i in [1..#pat`patches]|pat`transforms[i] ne IdentityMatrix(Integers(),3)];
      owner:=function(u)
        for i in others do
          if exists{p:p in pat`points[i]|same(Eltseq(p),u)} then
            return i;
          end if;
        end for;
        return 0;
      end function;
      delegate:=[[]:i in [1..#pat`patches]];
      for R in Qq_points(data:points:=recs) do
        if not R`inf and is_bad(R,data) then
          u:=plane_reduction(M,data,R);
          if owner(u) gt 0 then
            Append(~delegate[owner(u)],u);
          end if;
        end if;
      end for;
      discsM:=func<R|R`inf or not is_bad(R,data) or owner(plane_reduction(M,data,R)) eq 0>;
    end if;
    candidates,v:=effective_chabauty(data:Kpoints:=recs,e:=e,discs:=discsM);
    matched:=[Maximum([0] cat [j:j in [1..#recs]|agrees(c,recs[j])]):c in candidates];
    new:=[i:i in [1..#candidates]|matched[i] eq 0];
    recognized:=recognize(M,data,candidates,new);
    models:=[M]; model:=[1:c in candidates];
    // the records of the known points, by point (a singular point can give several)
    recsM:=[point_records(M,data,[* pt *]):pt in known];
    first:=[1+&+[Integers()|#recsM[k]:k in [1..j-1]]:j in [1..#known]]; // the index in recs of the first record of the j-th point
    for i in [i:i in others|#delegate[i] gt 0] do
      Mi:=pat`patches[i]; g:=pat`transforms[i];
      datai:=coleman_data(Mi`Q,Mi`L,Q,Nrun:verbose:=false);
      recsi:=point_records(Mi,datai,known);
      // the vanishing differentials, w.r.t. the holomorphic forms of Mi
      T:=holomorphic_transition(M,data,Mi,datai);
      _,toL:=model_field(BaseRing(M`C));
      Ki:=ChangePrecision(datai`K,Precision(Parent(v[1][1])));
      vi:=[Vector(Ki,[datai`m(&+[Inverse(data`m)(vk[j])*toL(T[j,k]):j in [1..data`g]]):k in [1..data`g]]):vk in v];
      gF:=ChangeRing(g,Fq);
      filt:=func<R|not R`inf and not is_bad(R,datai)
                   and exists{u:u in delegate[i]|same(u,Eltseq(Vector(Fq,plane_reduction(Mi,datai,R))*Transpose(gF)))}>;
      cands:=effective_chabauty(datai:Kpoints:=recsi,e:=e,vanishing:=vi,discs:=filt);
      // the known points they agree with, as indices of the records of M of the same points
      pointof:=&cat[[k:r in point_records(Mi,datai,[* known[k] *])]:k in [1..#known]];
      matchedi:=[Maximum([0] cat [j:j in [1..#recsi]|agrees(c,recsi[j])]):c in cands];
      newi:=[j:j in [1..#cands]|matchedi[j] eq 0];
      offset:=#candidates;
      // recognized points, in the coordinates of M (u = g*u')
      for r in recognize(Mi,datai,cands,newi) do
        ci:=Evaluate(Mi`c,r[2]);
        ys:=[];
        for y0 in r[3] do
          u:=Vector(M`L,[r[2]*ci,y0,ci])*Transpose(ChangeRing(g,M`L));
          if u[3] ne 0 then
            xM:=u[1]/u[3];
            Append(~ys,Evaluate(M`c,xM)*u[2]/u[3]);
          end if;
        end for;
        if #ys gt 0 then
          Append(~recognized,<offset+r[1],u[1]/u[3],ys>);
        end if;
      end for;
      candidates cat:=cands;
      matched cat:=[(j eq 0) select 0 else first[pointof[j]]:j in matchedi];
      new cat:=[offset+j:j in newi];
      Append(~models,Mi);
      model cat:=[#models:c in cands];
    end for;
    return data,recs,candidates,matched,new,recognized,model,models;
  end function;
  // the same, repeated with twice the precision while it fails for lack of precision
  Nlimit:=(maxN gt 0) select maxN else 4*N;
  run:=function(Q,known)
    Nrun:=N;
    repeat
      try
        data,recs,candidates,matched,new,recognized,model,models:=run_at(Q,known,Nrun);
        return data,recs,candidates,matched,new,recognized,model,models;
      catch err
        if Position(err`Object,"increase") eq 0 or 2*Nrun gt Nlimit then
          error err;
        end if;
        Nrun:=2*Nrun;
        if verbose then
          printf "curve_chabauty: at the prime of norm %o the precision does not suffice; repeating with N = %o\n",Norm(Q),Nrun;
        end if;
      end try;
    until false;
  end function;

  data,recs,candidates,matched,new,recognized,model,models:=run(P,pts);
  if rank_check and verbose then
    if #rank eq 0 then
      print "curve_chabauty: no bounds for the rank of the Jacobian available (models y^2 + h(x)*y = f(x) of genus 2 only)";
    else
      printf "curve_chabauty: %o <= rank of the Jacobian <= %o; the genus is %o%o\n",rank[1],rank[2],data`g,
             (rank[2] lt data`g) select " (the rank condition of Chabauty-Coleman holds)" else " (the rank condition is NOT verified)";
    end if;
  end if;
  if verbose then
    printf "curve_chabauty: %o candidate(s): %o agree with the %o known point records, %o do not",#candidates,#candidates-#new,#recs,#new;
    printf "%o.\n",(#recognized gt 0) select Sprintf("; %o of them are recognized as L-rational points with x = %o",#recognized,[r[2]:r in recognized]) else "";
  end if;
  complete:=#new eq #recognized;
  used:=[P];
  found:=[[r[2],y]:y in r[3],r in recognized]; // the recognized L-rational points, as pairs [x0,y0]
  for Q in [Q:Q in ordered|Q ne P] do
    if complete or #used ge primes then
      break;
    end if;
    _,_,candidates2,_,new2,recognized2:=run(Q,[* R:R in pts *] cat [* R:R in found *]); // the known and the recognized points
    Append(~used,Q);
    complete:=#new2 eq #recognized2;
    found cat:=[[r[2],y]:y in r[3],r in recognized2|[r[2],y] notin found];
    if verbose then
      printf "curve_chabauty: at the prime of norm %o: %o candidate(s), %o of them neither known nor recognized\n",
             Norm(Q),#candidates2,#new2-#recognized2;
    end if;
  end for;
  if verbose and primes gt 1 then
    printf "curve_chabauty: %o\n",complete select Sprintf("the L-rational points are the %o known and %o recognized point(s) (every candidate at the prime of norm %o is one of them)",#recs,#found,Norm(used[#used]))
                                                 else Sprintf("not every candidate is known or recognized at the %o prime(s) used",#used);
  end if;
  fmt:=recformat<model,prime,data,known,candidates,matched,new,recognized,rank,complete,primes,models,model_index>;
  return rec<fmt|model:=M,prime:=P,data:=data,known:=recs,candidates:=candidates,matched:=matched,new:=new,
                 recognized:=recognized,rank:=rank,complete:=complete,primes:=used,models:=models,model_index:=model>;
end function;
