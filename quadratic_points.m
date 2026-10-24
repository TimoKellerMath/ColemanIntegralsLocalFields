// quadratic_points.m -- the F-rational effective divisors of degree 2 (the quadratic points
// and the sums of two F-rational points) of a curve over a number field F, given as a Curve or
// a polynomial: symmetric Chabauty at a prime of F, residue class by residue class, with the
// models, good primes and point records of models.m.
//
//   curve_quadratic_points(C, known)   the F-rational points of the symmetric square C^(2)
//                                      that the known ones determine at one or more primes:
//                                      every residue class of C^(2) is shown to contain no
//                                      F-rational divisor, or a single one (a known divisor or
//                                      a recognized new one), or only pullbacks along the
//                                      hyperelliptic (or a given) involution, or it is
//                                      reported as unresolved.
//
// Method at a prime P of F (unramified, of residue characteristic p >= 5 by default, with good
// reduction of the model; preferably p dividing #J(F_q), see "excluded" in (5)):
//  (1) Residue classes. An F-rational effective divisor D of degree 2 reduces to a divisor of
//      degree 2 of the reduction over the residue field F_q of P: 2*Pb or Pb + Qb with Pb, Qb
//      in X(F_q), or a closed point of degree 2, whose two points are Frobenius-conjugate
//      points of X(F_(q^2)). Over the unramified quadratic extension K of F_P
//      (model_coleman_data with aux: the completion of L2 = F(sqrt u) at the prime above P,
//      u a non-square modulo P) these are the pairs {a, b} of residue discs over K that are
//      stable under the Frobenius x -> x^q of F_(q^2)/F_q: split classes {a, b} of two
//      F_q-rational discs, diagonal classes {a, a}, and conjugate classes {a, Frob(a)}.
//      Without aux only the split and diagonal classes are treated.
//  (2) Residue discs. Every point of the reduction over the residue field of K is the centre
//      of a disc in a model in which it is good (its home): the finite good discs of the
//      model M; for a model of degree 2 in y (y^2 + h(x)*y = f(x)) the discs at infinity in
//      two Moebius patches x = t + 1/x' (mobius_model) and the Weierstrass discs in M itself,
//      centred at their Weierstrass point, which is a very bad point of the patches as well;
//      for the other models the infinite and finite bad discs at smooth points of the reduced
//      plane curve in linear patches where they are good (affine_patches), further linear
//      patches for the pairs of discs that are good in no common model (cover_classes), and
//      the bad discs at singular points of the reduced plane curve in M itself, centred at
//      their very bad point (include_bad; their integrals need the auxiliary extension of
//      integrals.m); discs at singular points at infinity are not covered.
//  (3) Integrals. For a base point B0 (the centre of the first good disc of M) the integrals
//      J = int_(B0)^(c) of the holomorphic forms omega_1..omega_g of M to every centre c,
//      computed in the home model of the disc: through a point that is good in both models
//      and the transition matrix of holomorphic_transition. For a Weierstrass point W of a
//      model of degree 2 in y, int_(B0)^(W) = 1/2 int_(B0)^(iota(B0)) with the hyperelliptic
//      involution iota (it acts by -1 on the holomorphic forms; W is fixed), with no
//      auxiliary extension. The integral to a point of a disc is J of its centre plus a tiny
//      integral.
//  (4) The annihilating differentials V: the holomorphic forms whose integrals vanish on the
//      differences D - D0 of the known divisors (D0 the first known divisor whose points are
//      defined over K) and on the given generators; a saturated basis (basis_kernel). If the
//      known divisors and the generators generate a subgroup of finite index of J(F), the
//      integrals of all omega in V vanish on every F-rational divisor of degree 0, and dim V
//      >= g - rank J(F); symmetric Chabauty needs dim V >= 2.
//  (5) Every class {a, b} is treated in a model h in which both discs are good (or a bad disc
//      has its very bad point). The integrals I_k(t1,t2) = int_(D0)^(D(t1,t2)) omega_k, omega_k in
//      V, of the divisors D(t1,t2) of the class (t1, t2 the parameters of the two discs) are
//      I_k(0,0) plus the tiny integrals in the two discs:
//        excluded   some I_k(0,0) is a unit: no divisor of the class is a zero of I_k, so the
//                   class contains no F-rational divisor (possible only if p divides #J(F_q):
//                   the class contains an F_P-rational divisor D, and I_k(0,0) is congruent
//                   modulo P to the logarithm of [D - D0] in J(F_P));
//        certified  the linear terms of two of the forms have rank 2 modulo P (Siksek's
//                   criterion; for a diagonal class the jet (a_0, a_1) at the centre): the
//                   class contains at most one zero of the two, found by Newton's method in
//                   (t1, t2) (in (t1+t2, t1*t2) for a diagonal class, newton_symmetric);
//                   a known divisor in a certified class is its only F-rational divisor
//                   (known); otherwise the class is excluded if another form of V does not
//                   vanish at the zero, and else the symmetric functions of x at the zero are
//                   recognized as elements of F of small height (recognize_in_F) and verified:
//                   a divisor over F with these values of x whose points lie in the two discs
//                   is the only F-rational divisor of the class (recovered; a point of degree
//                   2 ramified at P has no points over K and lies in the diagonal class of its
//                   reduction, which place_key computes);
//        family     rank < 2 on a class of pullback type Qb + iota(Qb) (iota the
//                   hyperelliptic involution for a model of degree 2 in y, or sigma) with a
//                   unit linear term: every F-rational divisor of the class is a pullback
//                   (trace-zero differentials, see symmetric_chabauty_classify);
//        unresolved everything else (rank drop, a zero that is not recognized or not verified:
//                   a value of small height that is no divisor in the class is a spurious match
//                   of the recognition, for lack of precision).
// The result is complete if no class is unresolved and every disc is covered: then the
// F-rational effective divisors of degree 2 are the known and the recovered ones and the
// pullbacks in the family classes -- provided that V annihilates J(F) (the known divisors and
// the generators generate a subgroup of finite index of J(F); this is not checked). For
// dim V = 2 (rank J(F) = g - 2, or g = 2 and rank 0) every certified class that is not
// excluded has a p-adic zero, so a single prime gives a complete result only if p divides
// #J(F_q) (where unit integrals exclude classes) or with a Mordell-Weil sieve (the option
// reachable); for dim V >= 3 the further forms exclude most classes.
//
// Load after symmetric_chabauty.m and models.m.


// ---------------------------------------------------------------------------------------------
// p-adic numbers and points between the data of several models

K_to_K:=function(z,dfrom,dto)

  // The element z of dfrom`K as an element of dto`K, with the absolute precision of z. The
  // data of the models of a curve are over the same number field L = dfrom`L = dto`L and the
  // same prime, but their completions K are different Magma objects, between which coercion
  // fails: z goes through L.

  if dfrom`K cmpeq dto`K then
    return z;
  end if;
  a:=AbsolutePrecision(z);
  if IsWeaklyZero(z) then
    return (Type(a) eq Infty) select dto`K!0 else O(dto`pi^a);
  end if;
  zz:=dto`m(z @@ dfrom`m);
  // adding O(pi^a) caps the precision and stays in dto`K (ChangePrecision would not)
  return (Type(a) eq Infty) select zz else zz+O(dto`pi^a);
end function;


y_of_record:=function(R,data)

  // y at the good finite point record R: the second entry of (1,y,...,y^(d-1)) = W0^(-1)*b.

  return (Vector(R`b)*Transpose(eval_mat(data`W0^(-1),data`L,data`K,data`m,R`x)))[2];
end function;


record_from_xy:=function(x,y,data)

  // The finite point record of the point (x, y) in K^2 of the model of data, with the values
  // b^0 = W0(x)*(1,y,...,y^(d-1)); for good points (where W0(x) is defined).

  d:=Degree(data`Q);
  ys:=[data`K!1];
  for i:=2 to d do
    Append(~ys,ys[i-1]*y);
  end for;
  b:=Eltseq(Vector(ys)*Transpose(eval_mat(data`W0,data`L,data`K,data`m,x)));
  return set_bad_point(x,b,false,data:check:=false);
end function;


eval_L_poly:=function(f,z,data)

  // f(z) for a polynomial f over the field of a model (or over data`L) and z in data`K.

  return Evaluate(PolynomialRing(data`K)![data`m(data`L!c):c in Coefficients(f)],z);
end function;


// ---------------------------------------------------------------------------------------------
// The models of the sweep: M and its patches

// A model of the sweep: the model and its data, how its coordinates relate to those of M, the
// transition matrix T of its holomorphic forms (omega_j = sum_k T[j,k] omega'_k, omega_j those
// of M) over its data`K and TM over the K of M, and a base point good in M and in it with the
// integrals from B0.
//   kind    "model" (M itself), "linear" (plane coordinates u = g*u', u those of M) or
//           "mobius" (x = t + 1/x', y' = c(x')*y*x'^k);
//   base    a good point record of the patch whose image in M is good, offset the integrals
//           int_(B0)^(base) of the holomorphic forms of M (over the K of M), Noffset their
//           precision.
sweep_model_format:=recformat<model,data,kind,g,t,k,c,T,TM,base,offset,Noffset>;


plane_coordinates:=function(R,S)

  // The plane coordinates u = (x, y/c(x), 1) of the good finite point record R of the sweep
  // model S (S`model`c the polynomial c of the model, y = c(x)*u_2/u_3), over its K.

  data:=S`data;
  x:=R`x; y:=y_of_record(R,data);
  return [x,y/eval_L_poly(S`model`c,x,data),data`K!1];
end function;


transfer_coordinates:=function(R,S1,S2)

  // The coordinates (x2, y2) over S2`data`K in the sweep model S2 of the point given by the
  // finite point record R of the sweep model S1 (see transfer_point): true, x2, y2 if the point
  // is a finite point of S2, false (and 0, 0) otherwise.

  d1:=S1`data; d2:=S2`data;
  if S1`kind eq "mobius" or S2`kind eq "mobius" then
    // through the coordinates (x, y) of M, without division by x' at x' = 0
    x1:=R`x; y1:=y_of_record(R,d1);
    if S1`kind eq "model" then
      x:=K_to_K(x1,d1,d2); y:=K_to_K(y1,d1,d2);
      t:=d2`K!S2`t;
      if Valuation(x-t) gt 0 then
        return false, 0, 0;
      end if;
      x2:=1/(x-t);
      y2:=eval_L_poly(S2`c,x2,d2)*y*x2^S2`k;
    elif S2`kind eq "model" then
      if Valuation(x1) gt 0 then // at infinity of M
        return false, 0, 0;
      end if;
      x:=d1`K!S1`t+1/x1;
      y:=y1/(eval_L_poly(S1`c,x1,d1)*x1^S1`k);
      x2:=K_to_K(x,d1,d2); y2:=K_to_K(y,d1,d2);
    else // two Moebius patches: x2' = x1'/(1+(t1-t2)*x1'), y2' = (c2(x2')/c1(x1'))*y1'*(x2'/x1')^k
      u:=1+(d1`K!(S1`t-S2`t))*x1;
      if Valuation(u) gt 0 then
        return false, 0, 0;
      end if;
      x2:=x1/u;
      y2:=eval_L_poly(S2`c,x2,d1)/eval_L_poly(S1`c,x1,d1)*y1*u^(-S1`k);
      x2:=K_to_K(x2,d1,d2); y2:=K_to_K(y2,d1,d2);
    end if;
  else
    // linear patches (or M): through the plane coordinates of M
    u1:=[K_to_K(a,d1,d2):a in plane_coordinates(R,S1)];
    g:=(S1`kind eq "model") select IdentityMatrix(Integers(),3) else S1`g;
    g2:=(S2`kind eq "model") select IdentityMatrix(Integers(),3) else S2`g;
    h:=ChangeRing(g2,Rationals())^(-1)*ChangeRing(g,Rationals());
    u2:=[&+[(d2`K!h[i,j])*u1[j]:j in [1..3]]:i in [1..3]];
    if Valuation(u2[3]) gt Minimum([Valuation(a):a in u2|not IsWeaklyZero(a)]) then
      return false, 0, 0; // at infinity of S2
    end if;
    x2:=u2[1]/u2[3];
    y2:=eval_L_poly(S2`model`c,x2,d2)*u2[2]/u2[3];
  end if;
  if Valuation(x2) lt 0 then
    return false, 0, 0;
  end if;
  return true, x2, y2;
end function;


transfer_point:=function(R,S1,S2:very_bad:=false)

  // The point record of the sweep model S2 of the point given by the finite point record R of
  // the sweep model S1 (models of the same curve). Both are linear patches of M (or M), or
  // both are Moebius patches of M (or M). R is a good point of S1, or with very_bad the very
  // bad point of a bad disc of S1 (a Weierstrass point of a model of degree 2 in y, which is a
  // very bad point of every such model).
  // Output: true and the record if the point is a good finite point of S2, or with very_bad
  // also a very bad point of S2 (the centre of its disc there); false and 0 otherwise.

  if S1`model`Q eq S2`model`Q and S1`kind eq S2`kind and (S1`kind eq "model" or (S1`kind eq "linear" and S1`g eq S2`g) or (S1`kind eq "mobius" and S1`t eq S2`t)) then
    return true, R;
  end if;
  d2:=S2`data;
  try // the coordinates of a bad point need not be defined in the other model
    ok,x2,y2:=transfer_coordinates(R,S1,S2);
    if ok then
      R2:=record_from_xy(x2,y2,d2);
    end if;
  catch e
    if not very_bad then
      error e;
    end if;
    ok:=false;
  end try;
  if not ok or (is_bad(R2,d2) and not (very_bad and is_very_bad(R2,d2))) then
    return false, 0;
  end if;
  return true, R2;
end function;


hyperelliptic_involution:=function(R,data)

  // The image of the good finite point record R of a model y^2 + a_1(x)*y + a_0(x) = 0 (of
  // degree 2 in y) under the hyperelliptic involution (x, y) -> (x, -y - a_1(x)).

  y:=y_of_record(R,data);
  return record_from_xy(R`x,-y-eval_L_poly(Coefficient(data`Q,1),R`x,data),data);
end function;


reduce_point:=function(u,data)

  // The reduction modulo P of the projective point u (a sequence over data`K, not all
  // weakly zero), as a normalised sequence over the residue field of data`K.

  OK:=RingOfIntegers(data`K); _,res:=ResidueClassField(OK);
  v:=Minimum([Valuation(a):a in u|not IsWeaklyZero(a)]);
  w:=[res(OK!(a/data`pi^v)):a in u];
  i:=[j:j in [1..#w]|w[j] ne 0][1];
  return [a/w[i]:a in w];
end function;


// ---------------------------------------------------------------------------------------------
// The known divisors

known_places:=function(D,M)

  // The places with multiplicities <place, n> of an effective divisor D of the curve of M,
  // given as an effective divisor (DivCrvElt), a place, a point over the base field or over
  // an extension of it (its closed point), a pair [x0, y0] of coordinates of the model over
  // the base field, or a sequence or list of such (their sum).

  Kb:=BaseRing(M`C);
  if Type(D) eq DivCrvElt then
    supp,mult:=Support(D);
    if exists{a:a in mult|a lt 0} then
      error "curve_quadratic_points: a known divisor must be effective";
    end if;
    return [<supp[i],mult[i]>:i in [1..#supp]];
  elif Type(D) eq PlcCrvElt then
    return [<D,1>];
  elif ISA(Type(D),Pt) then
    if Ring(Parent(D)) cmpeq Kb then
      pls:=Places(D);
      if #pls ne 1 then
        error "curve_quadratic_points: a known point is a singular point of the curve with several places above it; give the place instead";
      end if;
      return [<pls[1],1>];
    end if;
    return [<Place(D),1>];
  elif Type(D) eq SeqEnum and #D eq 2 and forall{c:c in D|Type(c) notin {SeqEnum,List,Tup} and IsCoercible(Kb,c)} then
    // (a pair of scalars: Magma would also coerce a sequence [a, b] of rationals into Kb)
    x0:=Kb!D[1]; y0:=Kb!D[2];
    pls:=[pl:pl in Zeros(M`xf-x0)|Degree(pl) eq 1 and Evaluate(M`yf,pl) eq y0];
    if #pls ne 1 then
      error Sprintf("curve_quadratic_points: (%o, %o) is not a point of the model, or not a single one",x0,y0);
    end if;
    return [<pls[1],1>];
  elif Type(D) in {SeqEnum,List} then
    return &cat[$$(E,M):E in D];
  end if;
  error "curve_quadratic_points: a known divisor must be an effective divisor, a place, a point, a pair [x0, y0], or a sequence of these";
end function;


places_divisor:=function(pls)

  // The divisor sum n*place of a sequence of pairs <place, n>.

  return &+[t[2]*Divisor(t[1]):t in pls];
end function;


x_polynomial:=function(D,M)

  // The polynomial prod (X - x(Q)) over the points Q of the effective divisor D (over the
  // base field of the curve, X the variable of a univariate polynomial ring), or 0 if x has a
  // pole at a point of D.

  KbX:=PolynomialRing(BaseRing(M`C));
  supp,mult:=Support(D);
  f:=KbX!1;
  for i:=1 to #supp do
    if Valuation(M`xf,supp[i]) lt 0 then
      return KbX!0;
    end if;
    xi:=Evaluate(M`xf,supp[i]);
    f*:=((Degree(supp[i]) eq 1) select (KbX.1-xi) else KbX!CharacteristicPolynomial(xi))^mult[i];
  end for;
  return f;
end function;


// ---------------------------------------------------------------------------------------------
// Residue discs and classes

// A residue disc of the sweep:
//   home    the index of its model in the list of sweep models,
//   centre  its centre: a good point record of the home model, or the very bad point of a bad
//           disc (bad = true),
//   key     the reduction <x, b> of the centre, over the residue field of the home data,
//   frob    the index of its image under the Frobenius of F_(q^2)/F_q (itself without aux),
//   J, NJ   the integrals int_(B0)^(centre) of the holomorphic forms of M (over the K of M) and
//           their precision.
disc_format:=recformat<home,centre,bad,key,frob,J,NJ>;

// A residue class {a, b} of the sweep: its discs (a <= b), kind ("split", "diagonal" or
// "conjugate"), the model in which it was treated (0 if none), its status ("excluded",
// "known", "recovered", "family", "unresolved"), a note (the reason, one of a few fixed
// phrases), details (e.g. the spurious value of an unrecognized zero; "" if none), and the
// index of its divisor in the list of divisors of the result (0 if none).
class_format:=recformat<a,b,kind,model,status,note,detail,divisor>;


disc_key:=function(R,data)

  // The reduction <inf, x, b> of the point record R (inf: whether R is infinite, x then 1/x),
  // over the residue field of data`K: two points lie in the same disc iff their keys agree.

  OK:=RingOfIntegers(data`K); _,res:=ResidueClassField(OK);
  return <R`inf,res(OK!R`x),[res(OK!c):c in R`b]>;
end function;


place_key:=function(pl,Mh,datah)

  // The reduction <inf, x, b> (as disc_key) of a place pl of degree 2 of the curve of the
  // model Mh that reduces to a single point over the residue field k of datah`K, with
  // multiplicity 2: a point of degree 2 whose field is ramified at P, which gives no point
  // records over K. The values at pl of x (1/x at infinity) and of b^0 (b^inf) have minimal
  // polynomials over the base field whose reductions are (X - c)^2 (or X - c), c the reduction.
  // Output: true and the key, or false and 0 if pl does not reduce to a single point over k
  // (e.g. a point of degree 2 inert at P, without aux).

  Kb:=BaseRing(Mh`C); _,emb:=model_field(Kb);
  OK:=RingOfIntegers(datah`K); k,res:=ResidueClassField(OK);
  toK:=func<c|datah`m(datah`L!emb(c))>;
  E:=ResidueClassField(pl);
  inf:=Valuation(Mh`xf,pl) lt 0;
  fs:=[inf select 1/Mh`xf else Mh`xf] cat model_basis_functions(Mh,inf select datah`Winf else datah`W0);
  key:=[];
  for f in fs do
    mp:=MinimalPolynomial(E!Evaluate(f,pl));
    try
      rts:=Roots(PolynomialRing(k)![res(OK!toK(c)):c in Coefficients(mp)]);
    catch e // a value that is not integral at P
      return false, 0;
    end try;
    if #rts ne 1 or rts[1][2] ne Degree(mp) then
      return false, 0;
    end if;
    Append(~key,rts[1][1]);
  end for;
  return true, <inf,key[1],key[2..#key]>;
end function;


frobenius_images:=function(discs,q0)

  // For every disc the index of its image under x -> x^q0 (the Frobenius of the residue field
  // of K over that of F_P, q0 = #F_q), among the discs of the same home model. Error if an
  // image is missing (the discs do not form a Frobenius-stable set).

  frob:=[];
  for i:=1 to #discs do
    key:=discs[i]`key;
    img:=<key[1],key[2]^q0,[c^q0:c in key[3]]>;
    js:=[j:j in [1..#discs]|discs[j]`home eq discs[i]`home and discs[j]`key cmpeq img];
    if #js ne 1 then
      error "curve_quadratic_points: the residue discs are not stable under Frobenius (internal error)";
    end if;
    Append(~frob,js[1]);
  end for;
  return frob;
end function;


frobenius_stable_classes:=function(frob)

  // The residue classes {a, b}, a <= b, stable under the Frobenius permutation frob of the
  // discs: <a, b, kind> with kind "diagonal" (a = b, a fixed), "split" (a < b, both fixed) or
  // "conjugate" (b = frob(a) ne a).

  n:=#frob;
  fixed:=[i:i in [1..n]|frob[i] eq i];
  cls:=[<a,a,"diagonal">:a in fixed] cat [<fixed[i],fixed[j],"split">:j in [i+1..#fixed],i in [1..#fixed]];
  cls cat:=[<a,frob[a],"conjugate">:a in [1..n]|frob[a] gt a];
  return cls;
end function;


// ---------------------------------------------------------------------------------------------
// The sweep at one prime: models, discs, integrals

matrix_to_K:=function(T,M,data)

  // The matrix T over the base field of the curve of M, over M`L or over data`L, mapped into
  // data`K (the transition matrices of holomorphic_transition).

  _,emb:=model_field(BaseRing(M`C));
  coerce:=function(c)
    ok,cL:=IsCoercible(data`L,c);
    return ok select cL else data`L!emb(c);
  end function;
  return Matrix(data`K,NumberOfRows(T),NumberOfColumns(T),[data`m(coerce(c)):c in Eltseq(T)]);
end function;


cover_classes:=function(sweep,discs,reds,M,P,N,aux,extension)

  // Further linear patches (patch_candidates of models.m) for the residue classes {a, b} of a
  // sweep of linear patches whose discs are good in no common model: affine_patches covers
  // every point by a patch, but every Frobenius-stable pair of discs has to be treated in one
  // model. reds holds the reductions of the centres of the discs in the plane coordinates of
  // M; the availability of a disc in a model is decided by the cheap test reduced_good_test (as
  // in affine_patches), and a model is added only if it passes good_reduction_at. A class
  // with a bad disc (at a singular point of the reduced plane curve, bad in every plane model)
  // stays with the home of that disc.
  // Output: the sweep with the further patches (no discs have them as their home).

  dataM:=sweep[1]`data;
  OK:=RingOfIntegers(dataM`K); _,resK:=ResidueClassField(OK);
  res:=func<c|resK(OK!dataM`m(dataM`L!(M`L!c)))>;
  gof:=func<S|(S`kind eq "model") select IdentityMatrix(Integers(),3) else S`g>;
  available:=function(i,h,test) // disc i in sweep model h
    return discs[i]`home eq h or (not discs[i]`bad and Type(test) ne BoolElt and test(reds[i]));
  end function;
  tests:=[reduced_good_test(S`model,gof(S),P,res):S in sweep];
  avail:=[{h:h in [1..#sweep]|available(i,h,tests[h])}:i in [1..#discs]];
  open:=[c:c in frobenius_stable_classes([D`frob:D in discs])|#(avail[c[1]] meet avail[c[2]]) eq 0
         and not (discs[c[1]]`bad or discs[c[2]]`bad)];
  used:=[gof(S):S in sweep];
  for g in patch_candidates(300) do
    if #open eq 0 then
      break;
    end if;
    if g in used then
      continue;
    end if;
    try
      Mg:=transform_plane_model(M,g);
      test:=reduced_good_test(Mg,g,P,res);
    catch e
      continue;
    end try;
    if Type(test) eq BoolElt then
      continue;
    end if;
    closes:=[c:c in open|test(reds[c[1]]) and test(reds[c[2]])];
    if #closes eq 0 or not good_reduction_at(reduction_test_data(Mg`Q),P) then
      continue;
    end if;
    datag:=model_coleman_data(Mg,P,N:aux:=aux,extension:=extension);
    Append(~sweep,rec<sweep_model_format|model:=Mg,data:=datag,kind:="linear",g:=g>);
    open:=[c:c in open|c notin closes];
  end for;
  return sweep;
end function;


sweep_setup:=function(M,P,N,aux,include_bad,verbose)

  // The models and the residue discs of the sweep at the prime P of M`L (steps (2), (3) of
  // the method in the file header), without the integrals.
  // Output: the sweep models (sweep_model_format; M first, then the patches), the discs
  //         (disc_format, without J), the number of points of the reduction in no disc of the
  //         sweep (uncovered), and the number of residue classes of points of degree 2 of the
  //         reduction that the sweep does not see (without aux: the closed points of degree 2).

  d:=Degree(M`Q);
  L:=M`L; P:=MaximalOrder(L)!!P;
  extension:=0;
  if aux then
    L2,P2,u:=inert_quadratic_extension(L,P);
    extension:=<L2,P2,u>;
  end if;
  dataM:=model_coleman_data(M,P,N:aux:=aux,extension:=extension);
  g:=dataM`g;
  idK:=func<data|IdentityMatrix(data`K,g)>;
  S1:=rec<sweep_model_format|model:=M,data:=dataM,kind:="model",T:=idK(dataM)>;
  sweep:=[S1];
  ptsM,dataM:=Qq_points(dataM);
  sweep[1]`data:=dataM;
  discs:=[];
  for R in ptsM do
    if not R`inf and not is_bad(R,dataM) then
      Append(~discs,rec<disc_format|home:=1,centre:=R,bad:=false,key:=disc_key(R,dataM)>);
    end if;
  end for;
  ntotal:=#ptsM;
  nbadfinite:=#[R:R in ptsM|not R`inf and is_bad(R,dataM)];
  ninf:=#[R:R in ptsM|R`inf];

  if d eq 2 then
    // the Weierstrass discs in M, centred at their Weierstrass point (very bad: r(x) = 0)
    for R in ptsM do
      if not R`inf and is_bad(R,dataM) then
        Append(~discs,rec<disc_format|home:=1,centre:=R,bad:=true,key:=disc_key(R,dataM)>);
      end if;
    end for;
    // the discs at infinity in Moebius patches x = t + 1/x': two of them (t1 ne t2 mod p), so
    // that every finite disc is good in one of them
    if ninf gt 0 then
      p:=dataM`p; ts:=[];
      for t in [0,1,-1,2,-2,3,-3,4,-4,5,-5] do
        if #ts eq 2 then
          break;
        end if;
        if exists{s:s in ts|(t-s) mod p eq 0} then
          continue;
        end if;
        try
          Mp,k,c:=mobius_model(M,Matrix(Integers(),2,2,[t,1,1,0]));
          if not good_reduction_at(reduction_test_data(Mp`Q),P) then
            continue;
          end if;
          datap:=model_coleman_data(Mp,P,N:aux:=aux,extension:=extension);
        catch e
          continue;
        end try;
        Append(~ts,t);
        Append(~sweep,rec<sweep_model_format|model:=Mp,data:=datap,kind:="mobius",t:=t,k:=k,c:=c>);
      end for;
      if #ts eq 0 then
        error "curve_quadratic_points: no Moebius patch x = t + 1/x' with good reduction at P";
      end if;
      // the discs at infinity of M: the discs above x' = 0 of the first patch
      S:=sweep[2];
      ptsp,datap:=Qq_points(S`data);
      sweep[2]`data:=datap;
      for R in ptsp do
        if not R`inf and Valuation(R`x) gt 0 then
          Append(~discs,rec<disc_format|home:=2,centre:=R,bad:=is_bad(R,datap),key:=disc_key(R,datap)>);
        end if;
      end for;
    end if;
  else
    // linear patches for the bad and infinite discs at smooth points of the reduced plane
    // curve (in the residue field of the data of M), M itself for the bad discs at singular
    // points (include_bad)
    pat:=affine_patches(M,P:data:=dataM,verbose:=false);
    kM:=ResidueClassField(RingOfIntegers(dataM`K));
    seqs:=func<pts|[Eltseq(pt):pt in pts]>;
    // the reductions of the centres in the plane coordinates of M (cover_classes)
    reds:=[reduce_point(plane_coordinates(D`centre,S1),dataM):D in discs];
    for i:=1 to #pat`patches do
      gi:=pat`transforms[i];
      if IsOne(gi) then
        continue;
      end if;
      Mi:=pat`patches[i];
      datai:=model_coleman_data(Mi,P,N:aux:=aux,extension:=extension);
      Si:=rec<sweep_model_format|model:=Mi,data:=datai,kind:="linear",g:=gi>;
      Append(~sweep,Si);
      h:=#sweep;
      ptsi,datai:=Qq_points(datai);
      sweep[h]`data:=datai;
      Si`data:=datai;
      covered:=seqs(pat`points[i]);
      for R in ptsi do
        if R`inf or is_bad(R,datai) then
          continue;
        end if;
        u:=[K_to_K(a,datai,dataM):a in plane_coordinates(R,Si)];
        uM:=reduce_point([&+[(dataM`K!gi[a,b])*u[b]:b in [1..3]]:a in [1..3]],dataM);
        if exists{c:c in covered|Rank(Matrix(kM,[c,uM])) eq 1} then
          Append(~discs,rec<disc_format|home:=h,centre:=R,bad:=false,key:=disc_key(R,datai)>);
          Append(~reds,uM);
        end if;
      end for;
    end for;
    if include_bad then
      FFq,mm:=reduced_function_field(dataM);
      singular:=seqs(pat`singular);
      for R in ptsM do
        if R`inf or not is_bad(R,dataM) then
          continue;
        end if;
        _,_,place:=local_data(R,dataM);
        xb:=mm(R`x); yb:=Evaluate(FFq.1,place);
        cb:=Evaluate(PolynomialRing(kM)![mm(dataM`m(dataM`L!a)):a in Coefficients(M`c)],xb);
        uM:=(cb ne 0) select [xb,yb/cb,kM!1] else [kM!0,kM!1,kM!0];
        if exists{c:c in singular|Rank(Matrix(kM,[c,uM])) eq 1} then
          Append(~discs,rec<disc_format|home:=1,centre:=R,bad:=true,key:=disc_key(R,dataM)>);
          Append(~reds,uM);
        end if;
      end for;
    end if;
  end if;
  uncovered:=ntotal-#discs;
  // the Frobenius of the residue field of K over that of F_P
  q0:=#ResidueClassField(P);
  frob:=frobenius_images(discs,q0);
  for i:=1 to #discs do
    discs[i]`frob:=frob[i];
  end for;
  // further linear patches for the pairs of discs without a common model
  nextra:=0;
  if d ne 2 then
    n0:=#sweep;
    sweep:=cover_classes(sweep,discs,reds,M,P,N,aux,extension);
    nextra:=#sweep-n0;
  end if;
  unseen:=aux select 0 else #Places(reduced_function_field(dataM),2);
  if verbose then
    printf "curve_quadratic_points: %o residue discs over F_%o (%o finite good in the model, %o finite bad, %o at infinity) in %o model(s)%o%o",
      ntotal,#ResidueClassField(RingOfIntegers(dataM`K)),ntotal-nbadfinite-ninf,nbadfinite,ninf,#sweep,
      (nextra gt 0) select Sprintf(" (%o of them for pairs of discs)",nextra) else "",
      (uncovered gt 0) select Sprintf("; %o disc(s) not covered",uncovered) else "";
    printf "%o.\n",(unseen gt 0) select Sprintf("; %o class(es) of points of degree 2 not seen (no aux)",unseen) else "";
  end if;
  return sweep, discs, uncovered, unseen;
end function;


sweep_integrals:=function(sweep,discs,M,verbose)

  // The integrals J = int_(B0)^(centre) of the holomorphic forms of M (over the K of M) for
  // every disc, the transition matrices and base points of the patches (step (3) of the
  // method), B0 the centre of the first good disc of M.
  // Output: sweep and discs with T, base, offset and J, NJ filled in, the base point B0, and
  //         int_(B0)^(iota(B0))/2 for a model of degree 2 in y (0 otherwise), with its precision.

  S1:=sweep[1]; dataM:=S1`data; g:=dataM`g;
  // det(F - I) = +-#J(F_q) (over the residue field of K): its valuation is the loss of the
  // linear solve of every integral (coleman_integrals_on_basis warns once per integral)
  vdet:=Valuation(Determinant(ChangeRing(dataM`F-IdentityMatrix(dataM`L,NumberOfRows(dataM`F)),dataM`m)));
  if vdet gt 0 then
    printf "curve_quadratic_points: WARNING: p divides #J of the reduction (det(F-I) has valuation %o); the integrals lose %o digits in the linear solve\n",vdet,2*vdet;
  end if;
  hol:=function(I,NI)
    return change_abs_precision_vec(Vector(dataM`K,[I[j]:j in [1..g]]),NI);
  end function;
  i0:=[i:i in [1..#discs]|discs[i]`home eq 1 and not discs[i]`bad][1];
  B0:=discs[i0]`centre;
  side:=0; t0:=Cputime();
  ngood:=#[i:i in [1..#discs]|discs[i]`home eq 1 and not discs[i]`bad];
  count:=0;
  for i:=1 to #discs do
    if discs[i]`home eq 1 and not discs[i]`bad then
      I,NI,side:=coleman_integrals_on_basis(B0,discs[i]`centre,dataM:side1:=side,return_side:=true,verbose:=false,warn:=false);
      discs[i]`J,discs[i]`NJ:=hol(I,NI);
      count+:=1;
      if verbose and (count mod 50 eq 0 or count eq ngood) then
        printf "  integrals in the model: %o/%o (%o s)\n",count,ngood,Cputime(t0);
      end if;
    end if;
  end for;
  // Weierstrass points: int_(B0)^(W) = 1/2*int_(B0)^(iota(B0)) for every Weierstrass point W
  Jw:=0; NJw:=0;
  if Degree(M`Q) eq 2 then
    I,NI:=coleman_integrals_on_basis(B0,hyperelliptic_involution(B0,dataM),dataM:verbose:=false,warn:=false);
    Jw,NJw:=hol(I/2,NI);
  end if;
  for i:=1 to #discs do
    if discs[i]`home eq 1 and discs[i]`bad then
      if Degree(M`Q) eq 2 then
        discs[i]`J:=Jw; discs[i]`NJ:=NJw;
      else // a bad disc at a singular point: the auxiliary extension of integrals.m
        I,NI:=coleman_integrals_on_basis(B0,discs[i]`centre,dataM:verbose:=false,warn:=false);
        discs[i]`J,discs[i]`NJ:=hol(I,NI);
      end if;
    end if;
  end for;
  // the patches: the transition matrix, a base point good in M and in the patch, and the
  // integrals from it
  for h:=2 to #sweep do
    Sh:=sweep[h]; datah:=Sh`data;
    T:=holomorphic_transition(M,dataM,Sh`model,datah);
    sweep[h]`T:=matrix_to_K(T,M,datah);
    TM:=matrix_to_K(T,M,dataM);
    sweep[h]`TM:=TM;
    found:=false;
    for i in [i:i in [1..#discs]|discs[i]`home eq 1 and not discs[i]`bad] do
      ok,Rh:=transfer_point(discs[i]`centre,S1,Sh);
      if ok then
        sweep[h]`base:=Rh; sweep[h]`offset:=discs[i]`J; sweep[h]`Noffset:=discs[i]`NJ;
        found:=true;
        break;
      end if;
    end for;
    if not found then
      error "curve_quadratic_points: no point good in the model and in a patch (internal error)";
    end if;
    sideh:=0;
    for i in [i:i in [1..#discs]|discs[i]`home eq h] do
      if discs[i]`bad then // a Weierstrass point at infinity of M
        discs[i]`J:=Jw; discs[i]`NJ:=NJw;
        continue;
      end if;
      I,NI,sideh:=coleman_integrals_on_basis(sweep[h]`base,discs[i]`centre,datah:side1:=sideh,return_side:=true,verbose:=false,warn:=false);
      Ih:=Vector(dataM`K,[K_to_K(I[j],datah,dataM):j in [1..g]]);
      discs[i]`J,discs[i]`NJ:=change_abs_precision_vec(sweep[h]`offset+Ih*Transpose(TM),Minimum(NI,sweep[h]`Noffset));
    end for;
  end for;
  if verbose then
    printf "curve_quadratic_points: integrals to the centres of the %o discs computed (%o s); precision at least %o.\n",
      #discs,Cputime(t0),Minimum([D`NJ:D in discs]);
  end if;
  return sweep, discs, B0, Jw, NJw;
end function;


match_disc:=function(R,h,discs,datah)

  // The index of the disc of home h that contains the point record R of the model of home h
  // (0 if none).

  key:=disc_key(R,datah);
  js:=[j:j in [1..#discs]|discs[j]`home eq h and discs[j]`key cmpeq key];
  return (#js gt 0) select js[1] else 0;
end function;


divisor_points:=function(pls,sweep,discs)

  // The points of the effective divisor sum n*place (pls: pairs <place, n>) in the discs of the
  // sweep: the pairs <disc index, point record in the data of the home of the disc>, each
  // repeated according to its multiplicity.
  // Output: true and the pairs, or false and [] if a point is not defined over K or lies in a
  //         disc that the sweep does not cover.

  out:=[];
  for t in pls do
    pl:=t[1];
    found:=[];
    for h:=1 to #sweep do
      recs:=point_records(sweep[h]`model,sweep[h]`data,[pl]);
      if #recs ne Degree(pl) then
        return false, [];
      end if;
      for R in recs do
        j:=match_disc(R,h,discs,sweep[h]`data);
        if j gt 0 and not exists{f:f in found|f[1] eq j and lie_in_same_disc(f[2],R,sweep[h]`data)} then
          Append(~found,<j,R>);
        end if;
      end for;
      if #found eq Degree(pl) then
        break;
      end if;
    end for;
    if #found ne Degree(pl) then
      return false, [];
    end if;
    for i:=1 to t[2] do
      out cat:=found;
    end for;
  end for;
  return true, out;
end function;


points_integral:=function(pts,sweep,discs)

  // The sum of the integrals int_(B0)^(R) of the holomorphic forms of M over the points <j, R>
  // of divisor_points (J of the centre of the disc j plus the tiny integral from the centre
  // to R in the home model, transformed by T), over the K of M, and its precision.

  dataM:=sweep[1]`data; g:=dataM`g;
  I:=Vector(dataM`K,[0:j in [1..g]]); NI:=Infinity();
  for pr in pts do
    D:=discs[pr[1]]; Sh:=sweep[D`home];
    tiny,Nt:=tiny_integrals_on_basis(D`centre,pr[2],Sh`data);
    th:=Vector(dataM`K,[K_to_K(tiny[j],Sh`data,dataM):j in [1..g]]);
    if D`home gt 1 then
      th:=th*Transpose(Sh`TM);
    end if;
    I+:=D`J+th;
    NI:=Minimum([NI,D`NJ,Nt]);
  end for;
  return I, NI;
end function;


// ---------------------------------------------------------------------------------------------
// The residue classes

// The data of a disc in a model of the sweep: whether the disc is available there (its home,
// or its centre is a good point there, or for a bad disc the very bad point there), the centre
// R (a point record of that model), the tiny integrals ser of the forms of V from R, as series
// in the local parameter of local_coord over the K of the model, the expansion xt of x, and
// for every form of V the coefficients [a_0, a_1] of omega/dt at R (jet).
local_format:=recformat<ok,R,ser,xt,jet>;


disc_in_model:=procedure(~cache,i,h,sweep,discs,Vs)

  // Fills cache[[i,h]] (local_format) for the disc i in the sweep model h; Vs[h] holds the
  // forms of V w.r.t. the holomorphic forms of the model h, over its K. A bad disc is
  // available in another model only if its centre (its very bad point) is a very bad point
  // there too, as a Weierstrass point of a model of degree 2 in y is in the Moebius patches.

  if IsDefined(cache,[i,h]) then
    return;
  end if;
  D:=discs[i]; Sh:=sweep[h];
  loc:=rec<local_format|ok:=false>;
  if D`home eq h then
    ok:=true; R:=D`centre;
  else // a bad disc at its very bad point
    ok,R:=transfer_point(D`centre,sweep[D`home],Sh:very_bad:=D`bad);
  end if;
  if ok then
    datah:=Sh`data; g:=datah`g;
    ser,xt:=tiny_integrals_on_basis_to_z(R,datah);
    serV:=[&+[Vs[h][k][j]*ser[j]:j in [1..g]]:k in [1..#Vs[h]]];
    loc`ok:=true; loc`R:=R; loc`ser:=serV; loc`xt:=xt;
    loc`jet:=[[Coefficient(Derivative(s),0),Coefficient(Derivative(s),1)]:s in serV];
  end if;
  cache[[i,h]]:=loc;
end procedure;


reduce_K:=function(z,data)

  // The reduction of the integral element z of data`K in the residue field.

  OK:=RingOfIntegers(data`K); _,res:=ResidueClassField(OK);
  return res(OK!z);
end function;


verify_divisor:=function(mp,h,Ra,Rb,sweep)

  // An effective divisor of degree 2 of the curve over its base field whose values of the
  // function x of the sweep model h are the roots of mp (a monic quadratic polynomial over the
  // base field) and whose points lie in the discs of Ra and Rb (point records of that model): a
  // place of degree 2, or two places of degree 1. If Ra and Rb lie in the same disc, a place of
  // degree 2 without points over K (a point of degree 2 ramified at P, which reduces to twice a
  // point) is accepted if its reduction (place_key) is that of the disc.
  // Output: true and the divisor, or false and 0.

  Mh:=sweep[h]`model; datah:=sweep[h]`data;
  KbX:=Parent(mp);
  xpoly:=function(pl) // the polynomial of the values of x at the points of pl
    x0:=Evaluate(Mh`xf,pl);
    return (Degree(pl) eq 1) select KbX.1-x0 else KbX!CharacteristicPolynomial(ResidueClassField(pl)!x0);
  end function;
  Z:=[pl:pl in Zeros(Evaluate(mp,Mh`xf))|Degree(pl) le 2];
  pls1:=[pl:pl in Z|Degree(pl) eq 1];
  cands:=[[pl]:pl in Z|Degree(pl) eq 2 and xpoly(pl) eq mp]
         cat [[pls1[i],pls1[j]]:j in [i..#pls1],i in [1..#pls1]|xpoly(pls1[i])*xpoly(pls1[j]) eq mp];
  same:=lie_in_same_disc(Ra,Rb,datah);
  for c in cands do
    recs:=point_records(Mh,datah,c);
    if #recs eq 2 and ((lie_in_same_disc(recs[1],Ra,datah) and lie_in_same_disc(recs[2],Rb,datah))
                       or (lie_in_same_disc(recs[1],Rb,datah) and lie_in_same_disc(recs[2],Ra,datah))) then
      return true, &+[Divisor(pl):pl in c];
    end if;
    if #recs eq 0 and #c eq 1 and same then
      ok,key:=place_key(c[1],Mh,datah);
      if ok and key cmpeq disc_key(Ra,datah) then
        return true, Divisor(c[1]);
      end if;
    end if;
  end for;
  return false, 0;
end function;


solve_class:=procedure(cl,sweep,discs,Vs,u,c0,knownin,opts,~cache,~divisors,~out)

  // Treats the residue class cl = <a, b, kind> (step (5) of the method in the file header) and
  // sets out (class_format); a recovered divisor is added to divisors if it is new.
  //   Vs, u, c0  the forms of V in every sweep model, the V-integrals u[i] of the centres and
  //              c0 of D0 (over the K of M);
  //   knownin    an associative array: [a, b] -> the index of a known divisor in that class;
  //   opts       a record with htbound, basis (O_F inside L for recognize_in_F), sigma,
  //              trace_zero, reachable, hyperelliptic.

  a:=cl[1]; b:=cl[2]; kind:=cl[3];
  out:=rec<class_format|a:=a,b:=b,kind:=kind,model:=0,status:="unresolved",note:="",detail:="",divisor:=0>;
  M:=sweep[1]`model; dataM:=sweep[1]`data;
  // the model: a home of the two discs, else another one in which both are good
  hs:=[discs[a]`home,discs[b]`home] cat [h:h in [1..#sweep]|h notin [discs[a]`home,discs[b]`home]];
  h:=0;
  for hh in hs do
    disc_in_model(~cache,a,hh,sweep,discs,Vs);
    disc_in_model(~cache,b,hh,sweep,discs,Vs);
    if cache[[a,hh]]`ok and cache[[b,hh]]`ok then
      h:=hh;
      break;
    end if;
  end for;
  if h eq 0 then
    out`note:="no model in which both discs are good";
    return;
  end if;
  out`model:=h;
  datah:=sweep[h]`data; K:=datah`K;
  la:=cache[[a,h]]; lb:=cache[[b,h]];
  nV:=#Vs[1];

  // (i) the integrals I_k(0,0): excluded if one of them is a unit
  IV:=[u[a][k]+u[b][k]-c0[k]:k in [1..nV]];
  Nmin:=Minimum([AbsolutePrecision(x):x in IV]);
  if Nmin lt 1 then
    out`note:="integrals not known modulo P"; out`detail:="increase N";
    return;
  end if;
  if exists{x:x in IV|Valuation(x) eq 0} then
    out`status:="excluded"; out`note:="a unit integral";
    return;
  end if;

  // (ii) the linear terms modulo P: rank 2 for two of the forms certifies the class
  red:=func<x|reduce_K(x,datah)>;
  rows:=(kind eq "diagonal") select [[red(la`jet[k][1]),red(-la`jet[k][2])]:k in [1..nV]]
                                else [[red(la`jet[k][1]),red(lb`jet[k][1])]:k in [1..nV]];
  pivots:=[[k1,k2]:k2 in [k1+1..nV],k1 in [1..nV]|rows[k1][1]*rows[k2][2]-rows[k1][2]*rows[k2][1] ne 0];
  if #pivots eq 0 then
    // a class of pullback type with trace-zero differentials and a unit linear term
    pullback:=false;
    if opts`hyperelliptic then
      if kind eq "diagonal" then
        pullback:=discs[a]`bad; // a Weierstrass point
      elif not discs[a]`bad and not discs[b]`bad then
        pullback:=lie_in_same_disc(hyperelliptic_involution(la`R,datah),lb`R,datah);
      end if;
    elif Type(opts`sigma) ne RngIntElt and opts`trace_zero and not discs[a]`bad and not discs[b]`bad
         and sweep[h]`kind ne "mobius" then
      gh:=(sweep[h]`kind eq "model") select IdentityMatrix(Integers(),3) else sweep[h]`g;
      inM:=function(R)
        v:=[K_to_K(x,datah,dataM):x in plane_coordinates(R,sweep[h])];
        return reduce_point([&+[(dataM`K!gh[i,j])*v[j]:j in [1..3]]:i in [1..3]],dataM);
      end function;
      ua:=inM(la`R); ub:=inM(lb`R);
      kM:=Universe(ua);
      Sb:=Matrix(kM,3,3,[reduce_K(dataM`m(dataM`L!c),dataM):c in Eltseq(opts`sigma)]);
      su:=Eltseq(Vector(kM,ua)*Transpose(Sb));
      pullback:=Rank(Matrix(kM,[su,ub])) eq 1;
    end if;
    if pullback and exists{k:k in [1..nV]|rows[k][1] ne 0} then
      out`status:="family"; out`note:="pullbacks";
    else
      out`note:="rank drop";
    end if;
    return;
  end if;
  k1:=pivots[1][1]; k2:=pivots[1][2];
  if kind eq "diagonal" and datah`p lt 5 then // (the formal immersion argument behind the jet)
    out`note:="diagonal class, p < 5"; out`detail:="the jet criterion for a diagonal class needs p >= 5";
    return;
  end if;

  // (iii) a known divisor in a certified class is its only F-rational divisor
  if IsDefined(knownin,[a,b]) then
    out`status:="known"; out`divisor:=knownin[[a,b]];
    return;
  end if;
  if Type(opts`reachable) ne RngIntElt then
    if not opts`reachable(rec<class_format|a:=a,b:=b,kind:=kind,model:=h>,discs) then
      out`status:="excluded"; out`note:="reachability";
      return;
    end if;
  end if;

  // (iv) the zero of the forms k1, k2 (Newton), and the other forms there
  IVh:=[K_to_K(x,dataM,datah):x in IV];
  sA:=la`ser; sB:=lb`ser;
  if kind eq "diagonal" then
    sig1,sig2:=newton_symmetric([IVh[k1],IVh[k2]],[sA[k1],sA[k2]],K);
    n:=Minimum([AbsolutePrecision(s):s in sA])-1;
    p,_,_:=power_sums(sig1,sig2,n);
    value:=func<k|IVh[k]+&+[cs[j+1]*p[j+1]:j in [1..n]] where cs:=series_coefficients(sA[k],n)>;
  else
    t1,t2:=newton_pair([IVh[k1],IVh[k2]],[sA[k1],sA[k2]],[sB[k1],sB[k2]],K);
    value:=func<k|IVh[k]+(Evaluate(sA[k],t1)-Coefficient(sA[k],0))+(Evaluate(sB[k],t2)-Coefficient(sB[k],0))>;
  end if;
  Nchk:=Minimum([AbsolutePrecision(x):x in IVh])-1;
  if exists{k:k in [k1,k2]|not IsWeaklyZero(value(k)) and Valuation(value(k)) lt Nchk} then
    out`note:="Newton's method did not converge";
    return;
  end if;
  for k in [k:k in [1..nV]|k notin [k1,k2]] do
    v:=value(k);
    if not IsWeaklyZero(v) and Valuation(v) lt Nchk then
      out`status:="excluded"; out`note:="another form of V"; out`detail:=Sprintf("form %o of V",k);
      return;
    end if;
  end for;

  // (v) the symmetric functions of x at the zero, recognized in F, and the divisor
  if kind eq "diagonal" then
    e1,e2:=symmetric_x(la`xt,sig1,sig2);
  else
    x1:=Evaluate(la`xt,t1); x2:=Evaluate(lb`xt,t2);
    e1:=x1+x2; e2:=x1*x2;
  end if;
  ok1,r1:=recognize_in_F(e1,datah:basis:=opts`basis,htbound:=opts`htbound);
  ok2,r2:=recognize_in_F(e2,datah:basis:=opts`basis,htbound:=opts`htbound);
  if not (ok1 and ok2) then
    out`note:="zero not recognized";
    return;
  end if;
  // a value of small height that is no divisor in the class is a spurious match of the
  // recognition (too little precision for the height bound), not a divisor
  KbX:=PolynomialRing(BaseRing(M`C));
  mp:=KbX.1^2-to_curve_field(r1,M)*KbX.1+to_curve_field(r2,M);
  ok:=on_curve_degree2(PolynomialRing(datah`L)![datah`L!r2,-datah`L!r1,1],datah);
  if ok then
    ok,D:=verify_divisor(mp,h,la`R,lb`R,sweep);
  end if;
  if not ok then
    out`note:="zero not recognized";
    out`detail:=Sprintf("spurious value %o of x%o (no divisor in the class)",mp,(h eq 1) select "" else Sprintf(" of model %o",h));
    return;
  end if;
  j:=Position([E eq D:E in divisors],true);
  if j eq 0 then
    Append(~divisors,D);
    j:=#divisors;
  end if;
  out`status:="recovered"; out`divisor:=j;
end procedure;


// ---------------------------------------------------------------------------------------------
// The sweep at a prime, and the driver

// The result of the sweep at one prime (quadratic_points_at) and of curve_quadratic_points:
//   model, prime, data   the model M, the prime P of its field and the data of M at P,
//   models               the sweep models (sweep_model_format: M, then the patches),
//   discs                the residue discs (disc_format),
//   V                    the annihilating differentials, w.r.t. the holomorphic forms of M,
//   D0                   the index of the base divisor in divisors,
//   classes              the residue classes (class_format), with their status,
//   divisors             the known divisors (first), then the recovered new ones, as effective
//                        divisors of the curve,
//   known, new           the indices of the known and of the new divisors in divisors,
//   xpolys               for every divisor prod (X - x(Q)) over its points (x of M; 0 if a
//                        point is at infinity),
//   families             the indices of the classes of pullbacks,
//   unresolved           the indices of the unresolved classes,
//   uncovered, unseen    the numbers of discs and of classes of points of degree 2 that the
//                        sweep does not reach,
//   complete             whether no class is unresolved and nothing is uncovered or unseen,
//   primes               the primes used (curve_quadratic_points), complete if at one of them,
//   rank, annihilating   with rank_check (curve_quadratic_points): bounds [lo, hi] for the rank
//                        of J(F) ([] if none are available), and whether hi shows that V
//                        annihilates J(F) (false if this is not shown).
quadratic_result_format:=recformat<model,prime,data,models,discs,V,D0,classes,divisors,known,new,xpolys,
                                   families,unresolved,uncovered,unseen,complete,primes,rank,annihilating>;


quadratic_points_at:=function(M,P,known,generators:N:=15,aux:=true,include_bad:=true,htbound:=10^5,
                              sigma:=0,trace_zero:=false,reachable:=0,verbose:=true)

  // The sweep of curve_quadratic_points at the prime P of M`L (see the file header).
  // Input:  M a model; known a sequence of effective divisors of degree 2 (as sequences of
  //         pairs <place, n>, known_places); generators a sequence of pairs [D1, D2] of such
  //         sequences (D1 - D2 of degree 0); options as in curve_quadratic_points.
  // Output: a record of quadratic_result_format.

  t0:=Cputime();
  if verbose then
    nJ:=Evaluate(LPolynomial(reduced_curve_function_field(M,MaximalOrder(M`L)!!P)),1);
    printf "curve_quadratic_points: #J(F_q) = %o is %o\n",nJ,IsDivisibleBy(nJ,Minimum(P))
      select "divisible by p: an integral to a class can be a unit and exclude the class"
      else "prime to p: the integrals to the classes lie in pi*O_K, so none excludes a class";
  end if;
  sweep,discs,uncovered,unseen:=sweep_setup(M,P,N,aux,include_bad,verbose);
  sweep,discs:=sweep_integrals(sweep,discs,M,verbose);
  dataM:=sweep[1]`data; KM:=dataM`K; g:=dataM`g;

  // the known divisors and the generators: their points in the discs and their integrals
  dpts:=[]; dint:=[]; ok:=[];
  for D in known do
    okD,pts:=divisor_points(D,sweep,discs);
    Append(~ok,okD); Append(~dpts,pts);
    if okD then
      I,NI:=points_integral(pts,sweep,discs);
      Append(~dint,<I,NI>);
    else
      Append(~dint,<0,0>);
    end if;
  end for;
  i0:=Position(ok,true);
  if i0 eq 0 then
    error "curve_quadratic_points: no known divisor has its points over K at this prime (a quadratic point ramified at P is not); add a divisor such as P1 + P2 of two F-rational points";
  end if;
  I0:=dint[i0][1];
  cols:=[<dint[j][1]-I0,Minimum(dint[j][2],dint[i0][2])>:j in [1..#known]|ok[j] and j ne i0];
  for G in generators do
    ok1,p1:=divisor_points(G[1],sweep,discs);
    ok2,p2:=divisor_points(G[2],sweep,discs);
    if not (ok1 and ok2) then
      error "curve_quadratic_points: the points of a generator are not defined over K at this prime, or lie in discs that the sweep does not cover";
    end if;
    I1,N1:=points_integral(p1,sweep,discs);
    I2,N2:=points_integral(p2,sweep,discs);
    Append(~cols,<I1-I2,Minimum(N1,N2)>);
  end for;

  // the annihilating differentials V (step (4))
  if #cols eq 0 then
    V:=[Vector(KM,[(i eq j) select 1 else 0:j in [1..g]]):i in [1..g]];
  else
    Nint:=Minimum([c[2]:c in cols]);
    Kint:=ChangePrecision(KM,Nint);
    A:=Matrix(Kint,g,#cols,[Kint!cols[j][1][i]:j in [1..#cols],i in [1..g]]);
    if forall{x:x in Eltseq(A)|Valuation(x) ge Nint} then // all integrals vanish: rank 0
      V:=[Vector(KM,[(i eq j) select 1 else 0:j in [1..g]]):i in [1..g]];
    else
      Vk:=basis_kernel(A:zero_ok:=true);
      V:=[Vector(KM,[KM!c:c in Eltseq(v)]):v in Vk];
    end if;
  end if;
  if #V lt 2 then
    error Sprintf("curve_quadratic_points: the known divisors and generators span a subgroup of rank %o >= g - 1 = %o of J(F), so symmetric Chabauty does not apply (it needs dim V = g - rank >= 2)",g-#V,g-1);
  end if;
  if verbose then
    printf "curve_quadratic_points: genus %o, dim V = %o (from %o known divisor(s) and %o generator(s)).\n",g,#V,#known,#generators;
  end if;
  // V in every sweep model (a list: a sequence would coerce the vectors over the K of a patch
  // into the vector space over the K of M), and the V-integrals of the centres and of D0
  Vs:=[* V *];
  for h:=2 to #sweep do
    datah:=sweep[h]`data;
    Append(~Vs,[Vector(datah`K,[K_to_K(c,dataM,datah):c in Eltseq(v)])*sweep[h]`T:v in V]);
  end for;
  u:=[[&+[V[k][j]*D`J[j]:j in [1..g]]:k in [1..#V]]:D in discs];
  c0:=[&+[V[k][j]*I0[j]:j in [1..g]]:k in [1..#V]];

  // the known divisors in their classes; a point of degree 2 ramified at P (no points over K)
  // lies in the diagonal class of its reduction
  knownin:=AssociativeArray();
  for j in [1..#known] do
    if ok[j] then
      knownin[Sort([pr[1]:pr in dpts[j]])]:=j;
    elif #known[j] eq 1 and known[j][1][2] eq 1 and Degree(known[j][1][1]) eq 2 then
      for h:=1 to #sweep do
        okh,key:=place_key(known[j][1][1],sweep[h]`model,sweep[h]`data);
        js:=okh select [i:i in [1..#discs]|discs[i]`home eq h and discs[i]`key cmpeq key] else [];
        if #js gt 0 then
          knownin[[js[1],js[1]]]:=j;
          break;
        end if;
      end for;
    end if;
  end for;

  // the classes (step (5))
  classes:=frobenius_stable_classes([D`frob:D in discs]);
  hyper:=Degree(M`Q) eq 2;
  opts:=rec<recformat<htbound,basis,sigma,trace_zero,reachable,hyperelliptic>|htbound:=htbound,
            basis:=[dataM`L!(M`L!c):c in Basis(MaximalOrder(M`L))],sigma:=sigma,trace_zero:=trace_zero,
            reachable:=reachable,hyperelliptic:=hyper>;
  divisors:=[* places_divisor(D):D in known *];
  cache:=AssociativeArray();
  results:=[];
  t1:=Cputime();
  for i:=1 to #classes do
    solve_class(classes[i],sweep,discs,Vs,u,c0,knownin,opts,~cache,~divisors,~res);
    Append(~results,res);
    if verbose and (i mod 100 eq 0 or i eq #classes) then
      printf "  classes %o/%o (%o s)\n",i,#classes,Cputime(t1);
    end if;
  end for;

  // the result (a recovered divisor that is a known one counts as known)
  for i in [i:i in [1..#results]|results[i]`status eq "recovered" and results[i]`divisor le #known] do
    results[i]`status:="known";
  end for;
  status:=func<s|[i:i in [1..#results]|results[i]`status eq s]>;
  unresolved:=status("unresolved");
  complete:=#unresolved eq 0 and uncovered eq 0 and unseen eq 0;
  new:=[#known+1..#divisors];
  if verbose then
    printf "curve_quadratic_points: %o residue classes at the prime of norm %o (%o s): %o excluded, %o with a known divisor, %o recovered (%o new divisor(s)), %o of pullbacks, %o unresolved.\n",
      #classes,Norm(P),Cputime(t0),#status("excluded"),#status("known"),#status("recovered"),#new,#status("family"),#unresolved;
    if #unresolved gt 0 then
      notes:={* results[i]`note:i in unresolved *};
      printf "  unresolved: %o\n",[<n,Multiplicity(notes,n)>:n in Set(notes)];
    end if;
  end if;
  return rec<quadratic_result_format|model:=M,prime:=P,data:=dataM,models:=sweep,discs:=discs,V:=V,D0:=i0,
             classes:=results,divisors:=[D:D in divisors],known:=[1..#known],new:=new,
             xpolys:=[x_polynomial(D,M):D in divisors],families:=status("family"),unresolved:=unresolved,
             uncovered:=uncovered,unseen:=unseen,complete:=complete,primes:=[P]>;
end function;


curve_quadratic_points:=function(C,known:P:=0,N:=15,bound:=50,improve:=true,generators:=[],aux:=true,
                                 include_bad:=true,htbound:=10^5,sigma:=0,trace_zero:=false,reachable:=0,
                                 primes:=1,minp:=5,rank_check:=false,verbose:=true)

  // The F-rational effective divisors of degree 2 (the quadratic points and the sums of two
  // F-rational points) of a curve C over a number field F (or Q), by symmetric Chabauty from
  // known ones (see the file header for the method and the meaning of the result).
  // Input:  C a Curve or a polynomial (curve_model), or a model; known the known F-rational
  //         effective divisors of degree 2, each an effective divisor of C, a place of degree
  //         2, a point over a quadratic extension of F, or a pair of points of C(F) (or places
  //         of degree 1, or pairs [x0, y0] of coordinates of the model); at least one of them
  //         must have its points defined over K (over the residue field of K: not ramified at
  //         P), e.g. P1 + P2 for two F-rational points, as the base divisor D0.
  // Options:
  //   P          the prime of F (default: a good prime of residue characteristic >= minp that
  //              is unramified over p: one with p dividing #J(F_q) if there is one, since only
  //              there can a class be excluded by a unit integral (for dim V = 2 a single prime
  //              can only give a complete result there); the smallest norm among them, since
  //              the cost grows about like q^3);
  //   N          the precision of coleman_data (the recognition of the zeros needs a few
  //              digits more than the height of the divisors);
  //   bound      the bound for the norms of the primes tested (good_primes);
  //   improve    choose the model by improve_model (otherwise curve_model; not with sigma,
  //              which refers to the plane coordinates of curve_model);
  //   generators pairs [D1, D2] of effective divisors (in any of the forms of known) of the
  //              same degree whose differences, with those of the known divisors, generate a
  //              subgroup of finite index of J(F) (the differences D - D0 of the known divisors
  //              are used in any case);
  //   aux        compute over the unramified quadratic extension of F_P, which covers the
  //              classes of the points of degree 2 of the reduction (default true);
  //   include_bad  treat the bad discs at singular points of the reduced plane curve (for a
  //              model of degree >= 3 in y; their integrals need the auxiliary extension);
  //   htbound    the height bound of the recognition (recognize_in_F);
  //   sigma, trace_zero  an involution of the curve as a 3 x 3 matrix on the plane
  //              coordinates of the model (of the plane curve of C for a Curve, of (x : y : 1)
  //              for a polynomial; column convention, as in symmetric_chabauty_classify)
  //              and the assertion that V consists of trace-zero differentials for it: rank-drop
  //              classes of pullback type are then classes of pullbacks (for a model of degree 2
  //              in y the hyperelliptic involution is used automatically);
  //   reachable  a function (class, discs) -> boolean, false if the class contains no
  //              F-rational divisor (e.g. a Mordell-Weil sieve: the class of the reduction is
  //              not in the reduction of J(F)); see class_format, disc_format;
  //   primes     the number of primes to use at most: a further one while the result is not
  //              complete, with the divisors recovered so far added to the known ones;
  //   minp       the least residue characteristic of the default primes (p >= 5 makes the
  //              diagonal classes certifiable through the jet (a_0, a_1));
  //   rank_check bounds for the rank of J(F) (jacobian_rank_bounds: models y^2 + h(x)*y = f(x)
  //              of genus 2, by 2-descent): the integrals of the known divisors and the
  //              generators have rank g - dim V, at most the rank of the subgroup they span, so
  //              an upper bound <= g - dim V shows that this subgroup has finite index in J(F)
  //              and V annihilates J(F) (res`annihilating); otherwise a warning;
  //   verbose    print the progress.
  // Output: a record of quadratic_result_format (the last prime), with primes the primes used
  //         and complete true if the result at one of them is complete.

  if improve and Type(C) ne Rec and Type(sigma) eq RngIntElt then
    M:=improve_model(C:bound:=bound,verbose:=false)[1][1];
  else
    M:=(Type(C) eq Rec) select C else curve_model(C);
  end if;
  knownp:=[known_places(D,M):D in known];
  if exists{D:D in knownp|&+[t[2]*Degree(t[1]):t in D] ne 2} then
    error "curve_quadratic_points: every known divisor must have degree 2";
  end if;
  gens:=[[known_places(G[1],M),known_places(G[2],M)]:G in generators];
  // the primes
  if P cmpne 0 then
    Ps:=[MaximalOrder(M`L)!!P];
    if RamificationIndex(Ps[1]) gt 1 or (aux and IsEven(Minimum(Ps[1]))) then
      error "curve_quadratic_points: P must be unramified over p (the recognition of the zeros by LLL assumes it), and of odd residue characteristic for aux";
    end if;
  else
    good:=good_primes(M:bound:=bound);
    Ps:=[Q:Q in good|RamificationIndex(Q) eq 1 and Minimum(Q) ge minp and IsOdd(Minimum(Q))];
    // the primes with p dividing #J(F_q) first: only there can an integral to a class be a unit
    // and exclude the class (every Frobenius-stable class contains an F_P-rational divisor D,
    // and the integral to it is congruent to log[D - D0] in log J(F_P), which lies in pi*O_K^g
    // if p does not divide #J(F_q)); each group by norm (the cost grows about like q^3: q^2
    // discs and classes over F_(q^2))
    an:=[IsDivisibleBy(Evaluate(LPolynomial(reduced_curve_function_field(M,Q)),1),Minimum(Q)) select 0 else 1:Q in Ps];
    idx:=[1..#Ps];
    Sort(~idx,func<i,j|(an[i] ne an[j]) select an[i]-an[j] else Norm(Ps[i])-Norm(Ps[j])>);
    Ps:=[Ps[i]:i in idx];
    if #Ps eq 0 then
      error Sprintf("curve_quadratic_points: no good prime of norm <= %o unramified over a p >= %o; increase bound or give P",bound,minp);
    end if;
  end if;
  if verbose then
    printf "curve_quadratic_points: the model %o (%o)\n",M`Q,M`desc;
  end if;
  used:=[]; res:=0;
  for Q in Ps do
    if #used ge primes then
      break;
    end if;
    if verbose then
      printf "curve_quadratic_points: at the prime of norm %o above %o%o\n",Norm(Q),Minimum(Q),aux select " (over the unramified quadratic extension)" else "";
    end if;
    try
      resQ:=quadratic_points_at(M,Q,knownp,gens:N:=N,aux:=aux,include_bad:=include_bad,htbound:=htbound,
                                sigma:=sigma,trace_zero:=trace_zero,reachable:=reachable,verbose:=verbose);
    catch e
      if P cmpne 0 or Position(e`Object,"no known divisor") eq 0 then
        error e;
      end if;
      if verbose then
        print "curve_quadratic_points: no known divisor is defined over K at this prime; trying the next one";
      end if;
      continue;
    end try;
    Append(~used,Q);
    if res cmpeq 0 then
      res:=resQ;
    else // keep the divisors in their order: the known ones, then the new ones of all primes
      divs:=res`divisors;
      for D in resQ`divisors do
        if not exists{E:E in divs|E eq D} then
          Append(~divs,D);
        end if;
      end for;
      cmpl:=res`complete or resQ`complete;
      res:=resQ;
      res`divisors:=divs; res`known:=[1..#known]; res`new:=[#known+1..#divs];
      res`xpolys:=[x_polynomial(D,M):D in divs];
      res`complete:=cmpl;
    end if;
    res`primes:=used;
    if res`complete then
      break;
    end if;
    // the recovered divisors are known at the next prime
    knownp:=[known_places(D,M):D in res`divisors];
  end for;
  if res cmpeq 0 then
    error "curve_quadratic_points: no prime could be used";
  end if;
  // whether V annihilates J(F): the integrals of the known divisors and the generators have rank
  // g - dim V, at most the rank of the subgroup they span
  res`rank:=[]; res`annihilating:=false;
  if rank_check then
    res`rank:=jacobian_rank_bounds(M);
    r0:=res`data`g-#res`V;
    res`annihilating:=#res`rank eq 2 and res`rank[2] le r0;
    if verbose then
      if #res`rank eq 0 then
        print "curve_quadratic_points: no bounds for the rank of J(F) available (models y^2 + h(x)*y = f(x) of genus 2 only)";
      else
        printf "curve_quadratic_points: %o <= rank J(F) <= %o; the known divisors and generators span a subgroup of rank >= %o%o\n",
          res`rank[1],res`rank[2],r0,res`annihilating select ", of finite index: V annihilates J(F)"
            else "; WARNING: V need not annihilate J(F), so the statuses are not proved (give further generators)";
      end if;
    end if;
  end if;
  if verbose then
    printf "curve_quadratic_points: %o divisor(s) (%o known, %o new); %o\n",#res`divisors,#known,#res`new,
      res`complete select Sprintf("complete at the prime of norm %o: these and the pullbacks of the %o family class(es) are all F-rational effective divisors of degree 2%o",
                                  Norm(res`prime),#res`families,res`annihilating select "" else " (if V annihilates J(F))")
                   else "not complete";
  end if;
  return res;
end function;
