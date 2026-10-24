// solver.m: effective Chabauty over the completion K = L_P, the solver of Balakrishnan-Tuitman
// on top of the Coleman integrals of integrals.m.
//
// Main functions (data is the output of coleman_data):
//   effective_chabauty(data : Kpoints, bound, e)
//       the common zeros, residue disc by residue disc, of the integrals of the vanishing
//       differentials (vanishing_differentials) from a known point: a finite subset of X(K)
//       containing the L-rational points of X if the known points generate a subgroup of
//       finite index of a Mordell-Weil group of rank < g;
//   ros_chabauty(datas, known : e, htbound)
//       Chabauty-Coleman for the restriction of scalars: the completions at several primes
//       above p at once (datas: coleman_data at each of them), residue polydisc by residue
//       polydisc; needs rank <= (g-1)*sum_j [K_j:Q_p] instead of rank < g;
//   torsion_packet(Pt, data : bound, e)
//       the points of X(K) whose difference with Pt is torsion in the Jacobian (the common
//       zeros of the integrals of all holomorphic forms from Pt);
//   vanishing_differentials(points, data : e), zeros_on_disk(P1, P2, v, data : ...)
//       the two steps of effective_chabauty;
//   K_points(data, bound), Fq_points(data), Qq_points(data : points)
//       L-rational points of small height, the points of the reduction modulo P, and a point
//       over K in every residue disc.
//
// Names: L is the number field of the model, K = data`K its completion at P and m = data`m
// the map L -> K; "K_points" are L-rational points and "Qq_points" are points over K (the
// names of Balakrishnan-Tuitman, where L = Q and K = Q_q). Points are point records
// (set_point, set_bad_point in integrals.m). Load after integrals.m.

forward roots_with_precision;

Lx_to_Kx:=function(f,m,Kx)

  // The polynomial f over L as a polynomial in Kx over K = BaseRing(Kx), coefficientwise by
  // m: L -> K.

  K:=BaseRing(Kx);
  return Kx![K|m(c):c in Coefficients(f)];
end function;


L_or_Lx_to_Kx:=function(f,Kx,m)

  // An element f of L, or a polynomial over L, as a polynomial in Kx, coefficientwise by
  // m: L -> K.

  if Type(f) eq FldNumElt then
    f:=PolynomialRing(Parent(f))!f;
  end if;
  C:=Coefficients(f);
  return &+[Kx|m(C[k])*Kx.1^(k-1):k in [1..#C]];
end function;


evaluate_matrix_K:=function(M,K,x0,m)

  // The matrix M over L(x) evaluated at x0 in K (or an extension of K): numerators and
  // denominators of the entries are mapped to K[x] by m and evaluated at x0. Requires that
  // no denominator vanishes at x0.

  Kx:=PolynomialRing(K);
  ev:=func<a|Evaluate(L_or_Lx_to_Kx(Numerator(a),Kx,m),x0)/Evaluate(L_or_Lx_to_Kx(Denominator(a),Kx,m),x0)>;
  return Matrix(Parent(x0),Nrows(M),Ncols(M),[ev(a):a in Eltseq(M)]);
end function;


reduced_basis:=function(FFq,W,red_ratfun)

  // The reductions b_i mod P = sum_j (W[i,j] mod P)*y^(j-1) of the basis functions, in the
  // function field FFq of the reduction (reduced_function_field in integrals.m).

  d:=NumberOfRows(W);
  return [&+[FFq|red_ratfun(W[i,j])*FFq.1^(j-1):j in [1..d]]:i in [1..d]];
end function;


Fq_points:=function(data)

  // The points of the reduction modulo P of the curve given by data.
  //
  // Output: a list of [* x, b, inf, index *], one for every place of degree 1 of the
  //         function field of the reduction over F_q: inf tells whether the place is
  //         infinite (x = infinity); x is the value of x (resp. 1/x) and b the values of b^0
  //         (resp. b^inf) at the place, in F_q; index is the index of an integral local
  //         parameter at the place (0: x - x(P), resp. 1/x - 1/x(P); i > 0: b_i - b_i(P),
  //         as in local_data). An error is raised if there is none.
  //
  // Requires: the reduction of the model (Q, W0, Winf) modulo P is defined (the
  // good-reduction assumptions).

  d:=Degree(data`Q);
  FFq,mm,Fqx,red_ratfun:=reduced_function_field(data);
  Fq:=BaseRing(Fqx);
  b0modp:=reduced_basis(FFq,data`W0,red_ratfun);
  binfmodp:=reduced_basis(FFq,data`Winf,red_ratfun);
  xfun:=FFq!Fqx.1;

  // the index of an integral local parameter at the place pl: 0 if s - s(pl) is one (s = x,
  // resp. 1/x), otherwise the least i with b_i - b_i(pl) a uniformizer
  local_index:=function(s,b,pl)
    if Valuation(s-Evaluate(s,pl),pl) eq 1 then
      return 0;
    end if;
    idx:=[j:j in [1..d]|Valuation(b[j]-Evaluate(b[j],pl),pl) eq 1];
    if #idx eq 0 then
      error "Fq_points: no local uniformizer among x (resp. 1/x) and the reduced integral basis at a point of the reduction (the model does not have good reduction at P)";
    end if;
    return idx[1];
  end function;

  Fqpts:=[];
  for pl in Places(FFq,1) do
    if Valuation(xfun,pl) ge 0 then
      Append(~Fqpts,[*Evaluate(xfun,pl),[Fq!Evaluate(b,pl):b in b0modp],false,local_index(xfun,b0modp,pl)*]);
    else
      Append(~Fqpts,[*Evaluate(1/xfun,pl),[Fq!Evaluate(b,pl):b in binfmodp],true,local_index(1/xfun,binfmodp,pl)*]);
    end if;
  end for;
  return Fqpts;

end function;


Qq_points:=function(data:points:=[])

  // A point over K in every residue disc of the curve given by data.
  //
  // Input:  points (optional): points (point records) to use for the residue discs they lie
  //         in, e.g. the known L-rational points.
  // Output: a list of point records over K, one for every point of the reduction
  //         (Fq_points): an element of points if one reduces to it, otherwise a lift. In a
  //         bad disc the very bad point is returned (find_bad_point_in_disc). Second value:
  //         data, with the minimal polynomials of the local parameters added
  //         (update_minpolys).
  //
  // At a good point with local parameter x - x(P), x is the coercion of the residue x(P)
  // into K and y is obtained by Hensel lifting; otherwise the coordinates are roots of the
  // minimal polynomials of the local parameters (update_minpolys), selected by their
  // reductions. An error is raised if no root reduces to the given residue.

  Q:=data`Q; N:=data`N; W0:=data`W0; K:=data`K; m:=data`m;
  d:=Degree(Q); Fq:=ResidueClassField(RingOfIntegers(K));

  // working precision: at least that of K, with a margin of N/2 for the precision that
  // Factorisation below can lose (clustered roots, factors that are inseparable mod P). The
  // polynomials are evaluated at the exact lifts of the residues, so their roots carry the
  // precision that Factorisation determines; they are rounded to K at the end.
  Nwork:=Maximum(Precision(K),Ceiling(N*1.5));
  Qq:=ChangePrecision(K,Nwork); Qqy:=PolynomialRing(Qq);
  over_Qq:=func<c,s0|Qq!Evaluate(Lx_to_Kx(c,m,PolynomialRing(Qq)),s0)>; // c in L[s] at s0 in Qq

  // the first root, in the order of the factorisation, of the polynomial with coefficients
  // c(s0) (c in L[s]) that reduces to res (Roots has some problems that Factorisation does not).
  // Factorisation fails for a multiple root, e.g. 1/x = 0 at a point at infinity where 1/x
  // vanishes to higher order in the local parameter; then the roots are found digit by digit
  // (roots_with_precision, on the polynomial scaled to be integral).
  lift_root:=function(poly,s0,res)
    fy:=Qqy![over_Qq(c,s0):c in Coefficients(poly)];
    try
      zeros:=[-Coefficient(f[1],0)/Coefficient(f[1],1):f in Factorisation(fy)|Degree(f[1]) eq 1];
    catch err
      v:=Minimum([Valuation(c):c in Coefficients(fy)|not IsWeaklyZero(c)]);
      Zq:=RingOfIntegers(Qq);
      zeros:=[Qq!rt[1]:rt in roots_with_precision(PolynomialRing(Zq)![Zq!(c*Prime(Qq)^(-v)):c in Coefficients(fy)])];
    end try;
    cands:=[z:z in zeros|Valuation(z) ge 0 and Fq!z eq res]; // (a root of negative valuation reduces to no residue)
    if #cands eq 0 then
      error "Qq_points: no root of a minimal polynomial reduces to the coordinate of a point of the reduction (the root selection mod P failed); increase N";
    end if;
    return cands[1];
  end function;

  Qqpts:=[];
  for Fqpoint in Fq_points(data) do
    xres:=Fqpoint[1]; bres:=Fqpoint[2]; inf:=Fqpoint[3]; index:=Fqpoint[4];
    known:=[Pt:Pt in points|Pt`inf eq inf and Fq!(Pt`x) eq xres and [Fq!c:c in Pt`b] eq bres];
    if #known gt 0 then
      Pt:=known[1];
    else
      if not inf and index eq 0 and Valuation(Evaluate(Lx_to_Kx(data`r,m,PolynomialRing(Qq)),Qq!xres)) eq 0 then
        // a good point: x is the lift of the residue, y the Hensel lift
        x:=Qq!xres;
        y:=Qq!(Vector(bres)*ChangeRing(Transpose(evaluate_matrix_K(W0^-1,K,x,m)),Fq))[2];
        y:=HenselLift(Qqy![over_Qq(c,x):c in Coefficients(Q)],y);
        ypowers:=[Qq!1];
        for i:=2 to d do
          Append(~ypowers,ypowers[i-1]*y);
        end for;
        b:=Eltseq(Vector(ypowers)*Transpose(evaluate_matrix_K(W0,K,x,m)));
      else
        // the minimal polynomials of b^inf over L(1/x), resp. b^0 over L(x), and over L(b_index)
        data:=update_minpolys(data,inf,index);
        minpolys:=data`minpolys[inf select 2 else 1];
        if index eq 0 then // the local parameter is x - x(P) (resp. 1/x - 1/x(P))
          x:=Qq!xres;
          b:=[lift_root(minpolys[1,j+1],x,bres[j]):j in [1..d]];
        else // the local parameter is b_index - b_index(P)
          bindex:=Qq!bres[index];
          x:=lift_root(minpolys[index+1,1],bindex,xres);
          b:=[(j eq index) select bindex else lift_root(minpolys[index+1,j+1],bindex,bres[j]):j in [1..d]];
        end if;
      end if;
      // x, b were computed over Qq = ChangePrecision(K,Nwork); store the point over K = data`K
      // itself, otherwise the vector arithmetic in coleman_integrals_on_basis mixes vectors
      // over different copies of K
      Pt:=set_bad_point(K!x,[K!c:c in b],inf,data);
    end if;
    if is_bad(Pt,data) and not is_very_bad(Pt,data) then
      Pt:=find_bad_point_in_disc(Pt,data);
    end if;
    Append(~Qqpts,Pt);
  end for;

  return Qqpts,data;

end function;


search_small_points:=function(Q,bound,L)

  // The affine points (x,y) with y in L on Q(x,y) = 0 whose x-coordinate is a/c, where a runs
  // through the elements of L with coordinates in [-bound..bound] w.r.t. the power basis of L
  // and c through [1..bound]. Output: a sequence of pairs [x,y].

  n:=Degree(L);
  xs:={(&+[L|a[i]*L.1^(i-1):i in [1..n]])/c:a in CartesianPower([-bound..bound],n),c in [1..bound]};
  Ly:=PolynomialRing(L);
  return [[x,rt[1]]:rt in Roots(Ly![Evaluate(c,x):c in Coefficients(Q)]),x in xs];

end function;


K_points:=function(data,bound)

  // L-rational points of small height on the curve given by data (not guaranteed to be
  // complete).
  //
  // Output: a list of point records: every point of degree 1 above the x-coordinates of the
  // affine points of search_small_points(Q,bound,L) (finite points, or infinite points if
  // x is not P-integral), and the points of degree 1 above x = infinity.
  // Prints the number of points found at verbosity level 1 (SetVerbose("User1", 1)).

  L:=data`L; P:=data`P;
  t:=Cputime();
  xs:={pt[1]:pt in search_small_points(data`Q,bound,L)};
  vprintf User1, 1: "K_points: %o x-coordinates of small height with points above them (%o s).\n",#xs,Cputime(t);

  FF,Lt:=model_function_field(data);
  b0fun:=basis_functions(FF,data`W0);
  binffun:=basis_functions(FF,data`Winf);

  pointlist:=[];
  for x in xs do
    for pl in [pl:pl in Decomposition(FF,Zeros(Lt.1-x)[1])|Degree(pl) eq 1] do
      if Valuation(x,P) ge 0 then
        Append(~pointlist,set_bad_point(x,[Evaluate(b,pl):b in b0fun],false,data));
      else
        Append(~pointlist,set_bad_point(1/x,[Evaluate(b,pl):b in binffun],true,data));
      end if;
    end for;
  end for;
  for pl in [pl:pl in InfinitePlaces(FF)|Degree(pl) eq 1] do
    Append(~pointlist,set_bad_point(0,[Evaluate(b,pl):b in binffun],true,data));
  end for;
  return pointlist;

end function;


roots_with_precision:=function(f)

  // The roots in Zq of a non-zero polynomial f over Zq (the ring of integers of a p-adic
  // field, possibly ramified, with uniformizer pi; valuations and precisions in units of
  // v(pi) = 1), with their precisions. Roots of Magma requires a unit leading coefficient,
  // which is usually not the case here.
  //
  // Output: a list of pairs [* z0, Nz *]: z0 a root and Nz the precision to which it is
  //         determined, Nz = N_h - v(f'(z0)) with N_h the coefficient precision after
  //         removing the content pi^val (the Hensel bound: any polynomial that agrees with f
  //         to precision N_h has a unique root within |pi|^Nz of z0).
  //
  // Residue classes are explored digit by digit until each ball provably contains a single
  // root (Hensel's criterion) or the precision is exhausted, so clustered roots are reported
  // with their (smaller) precision rather than merged, also if the representative of a residue
  // class is itself a root.

  if f eq 0 then
    error "roots_with_precision: the polynomial must be nonzero";
  end if;

  Zq:=BaseRing(Parent(f));
  Fq:=ResidueClassField(Zq);
  Fqs:=PolynomialRing(Fq);
  p:=Characteristic(Fq);
  unramified:=Valuation(Zq!p) eq 1;

  Nf:=Precision(Zq);
  val:=Minimum([Valuation(c):c in Eltseq(f)]);
  Zq:=ChangePrecision(Zq,Nf-val);
  Zqs:=PolynomialRing(Zq);
  pi:=unramified select p else UniformizingElement(Zq); // the uniformizer (the integer p if Zq is unramified)
  f:=Zqs![c/pi^val:c in Eltseq(f)];

  // the root 0 (of multiplicity lcindex) is split off
  lcindex:=Minimum([i:i in [0..Degree(f)]|Coefficient(f,i) ne 0]);
  zero:=lcindex gt 0;
  if zero then
    f:=Zqs!Coefficients(f)[lcindex+1..#Coefficients(f)];
  end if;

  // The balls z + pi^Nz*Zq that can contain roots: a ball is final if Hensel's criterion
  // v(f(z)) > 2*v(f'(z)) and Nz >= v(f'(z))+1 holds (it contains exactly one root), or if no
  // further digit can be determined; otherwise it is split into the balls of the next digit
  // that can contain roots: the roots mod pi of f(z + pi^Nz*T) divided by its content (if the
  // reduction is a nonzero constant, the ball contains no root).
  hensel_ok:=func<z,Nz|v2 lt Infinity() and v1 gt 2*v2 and Nz ge v2+1
                       where v1:=Valuation(Evaluate(f,z)) where v2:=Valuation(Evaluate(Derivative(f),z))>;
  Zqroots:=[[*Zq!rt[1],1*]:rt in Roots(Fqs!f)];
  i:=1;
  while i le #Zqroots do
    z:=Zqroots[i][1];
    Nz:=Zqroots[i][2];
    fz:=Evaluate(f,z+pi^Nz*Zqs.1);
    c:=Minimum([Infinity()] cat [Valuation(a):a in Coefficients(fz)]); // the content (Infinity() if fz vanishes)
    if hensel_ok(z,Nz) or Nz ge Nf-val or c ge Nf-val then // final
      i+:=1;
    elif Fqs![a/pi^c:a in Coefficients(fz)] eq 0 then // final: the coefficients are inexact zeros (a multiple root), no further digit
      i+:=1;
    else // refine by one digit
      Remove(~Zqroots,i);
      for rt in Roots(Fqs![a/pi^c:a in Coefficients(fz)]) do
        Insert(~Zqroots,i,[*z+pi^Nz*(Zq!rt[1]),Nz+1*]);
      end for;
    end if;
  end while;

  for i:=1 to #Zqroots do
    z:=Zqroots[i][1];
    v2:=Valuation(Evaluate(Derivative(f),z));
    if Valuation(Evaluate(f,z)) lt Nf-val and hensel_ok(z,Zqroots[i][2]) then
      Zqroots[i][1]:=HenselLift(f,z);
    end if;
    Zqroots[i][2]:=Nf-val-v2;
  end for;

  if zero then
    Append(~Zqroots,[*Zq!0,Nf-val*]);
  end if;
  return Zqroots;

end function;


basis_kernel:=function(A:zero_ok:=false)

  // A basis of the left kernel {v : v*A = 0} of the matrix A over Qq, computed with the Smith
  // form over the ring of integers after scaling A to be integral (rows in Hermite form,
  // with entries in the ring of integers). An error is raised if the kernel is zero, unless
  // zero_ok (then the empty sequence is returned). Second value: the absolute precision of
  // the kernel vectors if the entries of A are correct to the precision of Qq: that of the
  // scaled matrix minus the largest valuation of its nonzero elementary divisors (a
  // perturbation E of the scaled matrix moves the kernel by E times the inverse of the
  // diagonal of its Smith form).

  Qq:=BaseRing(A);
  val:=Minimum([0] cat [Valuation(x):x in Eltseq(A)]);
  N:=Precision(Qq)-val;
  A:=Prime(Qq)^(-val)*A;
  Zq:=RingOfIntegers(ChangePrecision(Qq,N));
  S,P1:=SmithForm(Matrix(Zq,NumberOfRows(A),NumberOfColumns(A),[Zq!a:a in Eltseq(A)]));
  b:=[P1[i]:i in [Rank(S)+1..NumberOfRows(A)]];
  Nker:=N-Maximum([0] cat [Valuation(S[i,i]):i in [1..Rank(S)]]);
  if #b eq 0 and zero_ok then
    return [],Nker;
  end if;
  if #b eq 0 then
    error "basis_kernel: the kernel is zero; the integrals span the whole space of holomorphic forms, so the known points generate a subgroup of rank >= g (Chabauty-Coleman needs rank < g)";
  end if;
  return RowSequence(ChangeRing(HermiteForm(Matrix(b)),Qq)),Nker;

end function;


attach_expansions:=function(Pt,data,e)

  // Pt with its local expansions xt, bt, index (local_coord) attached: at a good point to the
  // t-adic precision tadicprec(data,1), at a very bad point to tadicprec(data,max(e,1)); a bad
  // point that is not very bad is returned unchanged (its disc is expanded at the very bad
  // point when needed).

  if is_bad(Pt,data) and not is_very_bad(Pt,data) then
    return Pt;
  end if;
  prec:=is_bad(Pt,data) select tadicprec(data,Maximum(e,1)) else tadicprec(data,1);
  Pt`xt,Pt`bt,Pt`index:=local_coord(Pt,prec,data);
  return Pt;

end function;


integrals_from_first:=function(points,data,fname:e:=0)

  // The Coleman integrals of the basis forms from points[1] to points[i+1], i = 1..#points-1
  // (point records over K), their precisions, and the part of the computation that depends
  // on points[1] only (coleman_integrals_on_basis, return_side). An error is raised if an
  // integral has no correct digits. Prints its progress, as the function fname, at verbosity
  // level 1 (SetVerbose("User1", 1)).

  IP1Pi:=[];
  NIP1Pi:=[];
  side1:=0; // the points[1]-half of the integrals is computed once and reused
  for i:=1 to #points-1 do
    tint:=Cputime();
    vprintf User1, 1: "%o: integral %o/%o ...\n", fname, i, #points-1;
    Ci,Ni,side1:=coleman_integrals_on_basis(points[1],points[i+1],data:e:=e,side1:=side1,return_side:=true);
    vprintf User1, 1: "%o: integral %o/%o done (precision %o, %o s).\n", fname, i, #points-1, Ni, Cputime(tint);
    if Ni le 0 then
      error Sprintf("%o: integral %o/%o has precision %o <= 0, no meaningful digits remain; increase N (or e)",fname,i,#points-1,Ni);
    end if;
    Append(~IP1Pi,Ci);
    Append(~NIP1Pi,Ni);
  end for;
  return IP1Pi,NIP1Pi,side1;

end function;


vanishing_differentials:=function(points,data:e:=0)

  // The holomorphic forms whose integrals vanish between all given points.
  //
  // Input:  points  point records over K (at least two; pairs [x0,y0] of good points are
  //                 accepted as well),
  //         e       as in coleman_integrals_on_basis (0: chosen automatically).
  // Output: v, a basis of the vanishing differentials: vectors of length g with respect to
  //         the holomorphic forms omega_1, ..., omega_g of data`basis (over K at the common
  //         precision of the integrals); the integrals IP1Pi from points[1] to points[i+1] and
  //         their precisions NIP1Pi; and side1, the part of the integrals that depends on
  //         points[1] only (coleman_integrals_on_basis, return_side).
  //
  // If the points generate a subgroup of finite index of a Mordell-Weil group of rank
  // r < g, then v spans a space of dimension g - r (up to precision). An error is raised if
  // an integral has no correct digits or if the kernel is zero. Prints its progress at
  // verbosity level 1 (SetVerbose("User1", 1)).

  if #points lt 2 then
    error "vanishing_differentials: at least two points are needed";
  end if;
  points:=[as_point(Pt,data,"vanishing_differentials"):Pt in points];
  K:=data`K; g:=data`g;

  IP1Pi,NIP1Pi,side1:=integrals_from_first(points,data,"vanishing_differentials":e:=e);

  Nint:=Minimum(NIP1Pi);
  vprintf User1, 1: "vanishing_differentials: solving for the kernel at common precision %o.\n", Nint;
  if Nint lt 3 then
    print "WARNING: vanishing_differentials: only",Nint,"correct digit(s) remain for the kernel; increase N (or choose a prime p not dividing #J(F_p))";
  end if;
  Kint:=ChangePrecision(K,Nint);
  M:=Matrix(Kint,g,#points-1,[Kint!IP1Pi[j][i]:j in [1..#points-1],i in [1..g]]);
  v:=basis_kernel(M);

  return v,IP1Pi,NIP1Pi,side1;

end function;


zeros_on_disk:=function(P1,P2,v,data:prec:=0,e:=0,integral:=[**],side1:=0)

  // The common zeros in the residue disc of P2 of the integrals from P1 of the forms v[i].
  //
  // Input:  P1, P2  point records over K; P2 carries its local expansions (local_coord),
  //         v       vectors of length g (the forms sum_j v[i][j]*omega_j, e.g. the output
  //                 of vanishing_differentials),
  //         prec    (optional) the t-adic precision of the tiny integrals on the disc,
  //         e       as in coleman_integrals_on_basis,
  //         integral (optional) [* int_P1^P2 omega, its precision *] if already known,
  //         side1   (optional) the part of the integrals that depends on P1 only
  //                 (coleman_integrals_on_basis, return_side).
  // Output: a list of point records P in the residue disc of P2, x(P) = x(t(pi*z)),
  //         b(P) = b(t(pi*z)) (pi a uniformizer of K, p if K is unramified), one for every
  //         candidate zero z; and side1 for reuse.
  //
  // Precision: F_i(z) = sum_j v[i][j]*int_P1^z omega_j is represented by the polynomial
  // h_i(t) = F_i(pi*t), which agrees with F_i to the working precision: the Coleman and tiny
  // integrals carry certified precisions NIP1P2, NP2toz > 0 (checked), and the t-adic
  // truncation is included in that bound (tadicprec, tiny_integral_prec). roots_with_precision
  // returns every root z0 of h_i with its precision Nz = N_h - v(h_i'(z0)) (an error is raised
  // if Nz <= 0), so the corresponding zero of F_i lies within |pi|^Nz of z0. Roots of
  // different h_i are matched at the minimum of their precisions: a candidate is kept iff it
  // agrees with a root of every other h_i at the available precision. The output is
  // therefore a superset of the set of common zeros: a common zero is never lost. Spurious
  // candidates (a z0 with F_i(z0) = 0 only to the working precision, or two nearby roots
  // matched at the minimum precision) have to be eliminated by the caller (by matching with
  // known points, algebraic recognition, a Mordell-Weil sieve at a second prime, or a larger
  // N). Over a ramified K the coefficients pi^j*c_j of h_i can have negative valuation (the
  // denominators j of the integration exceed j*v(pi) for small p and large e_K); h_i is
  // then divided by its content.

  p:=data`p; L:=data`L; m:=data`m; K:=data`K; g:=data`g;
  OL:=RingOfIntegers(L);

  if integral eq [**] then
    IP1P2,NIP1P2,side1:=coleman_integrals_on_basis(P1,P2,data:e:=e,side1:=side1,return_side:=true);
  else
    IP1P2:=integral[1];
    NIP1P2:=integral[2];
  end if;
  if NIP1P2 le 0 then
    error Sprintf("zeros_on_disk: the Coleman integral has precision %o <= 0, no meaningful output; increase N (or e)",NIP1P2);
  end if;
  tinyP2toz,xt,bt,NP2toz:=tiny_integrals_on_basis_to_z(P2,data:prec:=prec);
  if NP2toz le 0 then
    error Sprintf("zeros_on_disk: the tiny integrals on the disk have precision %o <= 0, no meaningful output; increase N",NP2toz);
  end if;

  Zq:=ChangePrecision(RingOfIntegers(K),Precision(Parent(v[1][1])));
  Zqt:=PolynomialRing(Zq);

  // for every form: the roots, with their precisions, of h(t) = f(pi*t), f(z) = int_P1^z;
  // the substitution z = pi*t maps the roots in pi*Zq to the unit ball (cf. Evaluate(xt,pi*z)
  // below), and m(OL!(pi^j*m^(-1)(c))) = pi^j*c checks the integrality in O_L
  piL:=(data`eK eq 1) select L!p else L!UniformizingElement(data`P);
  piK:=m(piL);
  zerolist:=[];
  for vi in v do
    f:=&+[vi[j]*(IP1P2[j]+tinyP2toz[j]):j in [1..g]];
    cL:=[piL^j*(Inverse(m)(Coefficient(f,j))):j in [0..Degree(f)]];
    vmin:=Minimum([0] cat [Valuation(c,data`P):c in cL|c ne 0]); // negative only over a ramified K
    if vmin eq 0 then
      h:=Zqt![Zq!m(OL!c):c in cL];
    else
      h:=Zqt![Zq!m(c*piL^(-vmin)):c in cL]; // divided by the content pi^vmin
    end if;
    if h eq 0 then
      error "zeros_on_disk: the integral vanishes to the working precision on the whole disc, no meaningful output; increase N (or use another prime)";
    end if;
    zeros:=roots_with_precision(h);
    if exists(z){z:z in zeros|z[2] le 0} then
      error Sprintf("zeros_on_disk: a root was found with precision %o <= 0, no meaningful output; increase N",z[2]);
    end if;
    Append(~zerolist,zeros);
  end for;

  // the roots of the first h that agree with a root of every other h at the available precision
  common:=[z1[1]:z1 in zerolist[1]|forall{zs:zs in zerolist[2..#zerolist]|exists{z:z in zs|Valuation(z[1]-z1[1]) ge Minimum(z[2],z1[2])}}];

  pointlist:=[set_bad_point(Evaluate(xt,piK*z),Eltseq(Evaluate(bt,piK*z)),P2`inf,data):z in common];
  return pointlist,side1;

end function;


effective_chabauty:=function(data:Kpoints:=[],bound:=0,e:=0,vanishing:=[],discs:=0)

  // Effective Chabauty for the curve given by data.
  //
  // Input:  Kpoints (optional) known L-rational points (point records, or pairs [x0,y0] of
  //         good points); if empty, they are searched with K_points(data,bound), bound > 0;
  //         e as in coleman_integrals_on_basis;
  //         vanishing (optional): the vanishing differentials to use (vectors over K w.r.t. the
  //         holomorphic forms of data`basis), instead of computing them from the known points
  //         (e.g. transported from another model of the curve, as in curve_chabauty);
  //         discs (optional): a function of a point record that selects the residue discs to
  //         treat (their centres from Qq_points); all of them by default.
  // Output: the list of candidate points over K (zeros_on_disk, residue disc by residue
  //         disc), and the vanishing differentials v.
  //
  // Method: the local expansions of the known points; the vanishing differentials from the
  // integrals between the known points; a point over K in every residue disc (Qq_points);
  // and the common zeros of the integrals of v from Kpoints[1] in every disc. The integrals
  // from Kpoints[1] share its part of the computation (side1). Prints its progress at
  // verbosity level 1 (SetVerbose("User1", 1)).

  if #Kpoints eq 0 then
    if bound le 0 then
      error "effective_chabauty: give the known points (Kpoints) or a positive search bound (bound)";
    end if;
    Kpoints:=K_points(data,bound);
  end if;
  Kpoints:=[as_point(Pt,data,"effective_chabauty"):Pt in Kpoints];
  if #Kpoints lt 2 then
    error "effective_chabauty: at least two known points are needed for the vanishing differentials";
  end if;

  ttotal:=Cputime();
  tphase:=Cputime();
  vprintf User1, 1: "effective_chabauty: computing local expansions of the %o K-points ...\n", #Kpoints;
  for i:=1 to #Kpoints do
    _,index:=local_data(Kpoints[i],data);
    data:=update_minpolys(data,Kpoints[i]`inf,index);
    Kpoints[i]:=attach_expansions(Kpoints[i],data,e);
  end for;
  vprintf User1, 1: "effective_chabauty: local expansions of the K-points: %o s.\n", Cputime(tphase);

  tphase:=Cputime();
  vprintf User1, 1: "effective_chabauty: computing vanishing differentials from %o known points ...\n", #Kpoints;
  if #vanishing gt 0 then
    v:=vanishing; IP1Pi:=[]; NIP1Pi:=[]; side1:=0;
  else
    v,IP1Pi,NIP1Pi,side1:=vanishing_differentials(Kpoints,data:e:=e); // side1 caches the Kpoints[1]-half of the integrals
  end if;
  vprintf User1, 1: "effective_chabauty: computed %o vanishing differentials (%o s).\n", #v, Cputime(tphase);

  tphase:=Cputime();
  Qqpoints,data:=Qq_points(data:points:=Kpoints);
  if Type(discs) ne RngIntElt then
    Qqpoints:=[Pt:Pt in Qqpoints|discs(Pt)];
  end if;
  vprintf User1, 1: "effective_chabauty: computed %o K_p-points (%o s).\n", #Qqpoints, Cputime(tphase);
  tphase:=Cputime();
  vprintf User1, 1: "effective_chabauty: computing local expansions of the K_p-points ...\n";
  Qqpoints:=[attach_expansions(Pt,data,e):Pt in Qqpoints];
  vprintf User1, 1: "effective_chabauty: local expansions of the K_p-points: %o s.\n", Cputime(tphase);

  vprintf User1, 1: "effective_chabauty: computing common zeros of the vanishing differentials on the %o residue disks ...\n", #Qqpoints;
  pointlist:=[];
  for i:=1 to #Qqpoints do
    tdisk:=Cputime();
    vprintf User1, 1: "effective_chabauty: disk %o/%o%o ...\n", i, #Qqpoints, is_bad(Qqpoints[i],data) select " (bad)" else "";
    // the known point in this disc, if any: its integral was computed by vanishing_differentials
    k:=(#IP1Pi eq 0) select 0 else Maximum([0] cat [j:j in [1..#Kpoints]|Qqpoints[i]`x eq Kpoints[j]`x and Qqpoints[i]`b eq Kpoints[j]`b and Qqpoints[i]`inf eq Kpoints[j]`inf]);
    if k lt 2 then
      pts,side1:=zeros_on_disk(Kpoints[1],Qqpoints[i],v,data:e:=e,side1:=side1); // the Kpoints[1]-half of the integral is cached across the disks
    else
      pts:=zeros_on_disk(Kpoints[1],Qqpoints[i],v,data:e:=e,integral:=[*IP1Pi[k-1],NIP1Pi[k-1]*]);
    end if;
    vprintf User1, 1: "effective_chabauty: disk %o/%o: found %o point(s) (%o s); %o point(s) in total so far.\n", i, #Qqpoints, #pts, Cputime(tdisk), #pointlist+#pts;
    pointlist cat:=pts;
  end for;

  vprintf User1, 1: "effective_chabauty: found %o point(s) in total (%o s).\n", #pointlist, Cputime(ttotal);
  return pointlist, v;

end function;


torsion_packet:=function(Pt,data:bound:=0,e:=0)

  // The torsion packet of Pt: the points P over K in all residue discs with
  // int_Pt^P omega = 0 for all holomorphic forms omega (a superset, cf. zeros_on_disk).
  //
  // Input:  Pt     a point record over K (or a pair [x0,y0] of a good point),
  //         bound  (optional) if > 0, the L-rational points of K_points(data,bound) are used
  //                as the points of their residue discs,
  //         e      as in coleman_integrals_on_basis.
  // Output: the list of candidate points.

  Pt:=as_point(Pt,data,"torsion_packet");
  v:=RowSequence(IdentityMatrix(ChangePrecision(data`K,data`N),data`g));

  _,index:=local_data(Pt,data);
  data:=update_minpolys(data,Pt`inf,index);
  Pt:=attach_expansions(Pt,data,e);

  if bound ne 0 then
    Qqpoints,data:=Qq_points(data:points:=K_points(data,bound));
  else
    Qqpoints,data:=Qq_points(data);
  end if;
  Qqpoints:=[attach_expansions(R,data,e):R in Qqpoints];

  pointlist:=[];
  side1:=0; // the Pt-half of the Coleman integral is cached across the disks (Pt is the fixed base point)
  for R in Qqpoints do
    pts,side1:=zeros_on_disk(Pt,R,v,data:e:=e,side1:=side1);
    pointlist cat:=pts;
  end for;
  return pointlist;

end function;


recognize_in_F := function(z, data : htbound := 10^4, slack := 3, basis := [])

  // An element of the number field L = data`L of small height whose image under the
  // completion map data`m is the integral p-adic number z in K = data`K (unramified over
  // Q_p), by LLL on the lattice of the elements of O_L (or of the Z-span of basis) mapped to
  // K: the vectors (a_1, ..., a_n, a_0) with sum_i a_i*m(B_i) - a_0*z = 0 modulo p^M, M about
  // the precision of z (minus slack), give x = (sum_i a_i*B_i)/a_0 with m(x) = z to
  // precision M.
  // Returns: true and x if such an x with coordinates (numerators and denominators) at most
  //          htbound reproduces z to the available precision, false and 0 otherwise.
  // M is the absolute precision of z (at most the precision of K) minus slack: the congruence
  // is modulo p^M, so a z of positive valuation (e.g. the product of the x-coordinates of two
  // points one of which has x = 0) keeps all its digits, and an inexact zero is recognized as
  // 0 only if it is known to more than 3 digits.
  L := data`L; K := data`K; m := data`m;
  ZZ := Integers();
  p := Prime(K);
  fK := AbsoluteDegree(K);                  // = e_P*f_P; e_P = 1 throughout, so fK = f_P
  M := Minimum(AbsolutePrecision(z), Precision(K)) - slack;
  if M le 3 then return false, L!0; end if;
  if IsWeaklyZero(z) then return true, L!0; end if;
  if Valuation(z) lt 0 then return false, L!0; end if;     // only integral targets here
  pM := p^M;

  // Z-coordinates of an element of K w.r.t. the power basis of K over Q_p.
  // For f_P = 1 this is a single p-adic digit vector; for
  // f_P > 1 an element of K carries fK independent Q_p-coordinates, each of
  // which has to be matched, so the congruence below is a system of fK
  // congruences and the lattice acquires fK reduction columns.
  Kco := function(a)
    if fK eq 1 then
      return [ ZZ | ZZ!(ChangePrecision(K!a, M)) ];
    end if;
    return [ ZZ | ZZ!(ChangePrecision(c, M)) : c in Eltseq(K!a) ];
  end function;

  if #basis eq 0 then
    B := [ L!b : b in Basis(MaximalOrder(L)) ];   // integral basis (handles denominators like (s-1)/2)
  else
    B := [ L!b : b in basis ];                    // caller-supplied target order (e.g. O_F inside L)
  end if;
  n := #B;
  sig := [ Kco(m(b)) : b in B ];
  Zc  := Kco(z);

  // kernel lattice { (a_1..a_n, a_0) : sum_i a_i sig_i - a_0 Z = 0 mod p^M in K }
  // (then x = (sum a_i B_i)/a_0 satisfies m(x) = z to precision M).
  // The fK residue columns carry the weight C, chosen larger than the norm of
  // any admissible coefficient vector: a lattice vector with a non-zero residue
  // then has norm >= C and cannot be shorter than the sought one, so LLL reduces
  // inside the residue-zero sublattice. (Without the weight the vector
  // (1,0,...,0 | 1) -- coefficient B_1 = 1, residue 1 -- would be shorter than
  // the target, and LLL would return a useless basis.)
  C := 2*(n+2)*Maximum(htbound, 1);
  rows := [];
  for i := 1 to n do
    v := [ ZZ | 0 : j in [1..n+1+fK] ];
    v[i] := 1;
    for j := 1 to fK do v[n+1+j] := C*(sig[i][j] mod pM); end for;
    Append(~rows, v);
  end for;
  v := [ ZZ | 0 : j in [1..n+1+fK] ];
  v[n+1] := 1;
  for j := 1 to fK do v[n+1+j] := C*((-Zc[j]) mod pM); end for;
  Append(~rows, v);
  for j := 1 to fK do
    v := [ ZZ | 0 : jj in [1..n+1+fK] ];
    v[n+1+j] := C*pM;
    Append(~rows, v);
  end for;
  Lred := LLL(Matrix(ZZ, rows));

  // Among the rows that reproduce z, prefer the one that reproduces it BEST and
  // only then the one of smallest height: the true value agrees with z to the
  // full available precision, whereas a spurious short vector agrees only to
  // about M. Ranking by height alone can pick a spurious vector when M is small
  // relative to the height of the answer -- which happens more easily for
  // f_K > 1, since the lattice then has n+1+f_K columns.
  best := false; bestx := L!0; besth := htbound + 1; bestv := -1;
  for r in Rows(Lred) do
    a0 := r[n+1];
    if a0 eq 0 then continue; end if;
    x := (&+[ r[i]*B[i] : i in [1..n] ]) / a0;
    vx := Valuation(m(x) - z);
    if vx ge M - slack then
      h := Maximum([ ZZ | AbsoluteValue(Numerator(ci)) : ci in Eltseq(x) ]
             cat [ ZZ | AbsoluteValue(Denominator(ci)) : ci in Eltseq(x) ]);
      if (vx gt bestv) or (vx eq bestv and h lt besth) then
        best := true; bestx := x; besth := h; bestv := vx;
      end if;
    end if;
  end for;
  if best and besth le htbound then return true, bestx; end if;
  return false, L!0;
end function;


// ---------------------------------------------------------------------------------------------
// Chabauty-Coleman for the restriction of scalars

qp_coordinates:=function(a,Qp)

  // The coordinates of the element a of a p-adic field K (as built by Completion) in Qp (a
  // p-adic field over the same p) with respect to the Z_p-basis qp_basis(K) of O_K.

  if AbsoluteDegree(Parent(a)) eq 1 then
    return [Qp!a];
  end if;
  return &cat[$$(c,Qp):c in Eltseq(a)];

end function;


qp_basis:=function(K)

  // A Z_p-basis of the ring of integers of the p-adic field K (as built by Completion): the
  // products of the powers of the generators of the steps of the tower K/Q_p (an unramified
  // step with a unit generator, a totally ramified step with a uniformizer), ordered as the
  // coordinates of qp_coordinates. An error is raised for a step of another kind.

  if AbsoluteDegree(K) eq 1 then
    return [K!1];
  end if;
  if Degree(K) gt 1 and InertiaDegree(K) ne Degree(K) and Valuation(K.1) ne 1 then
    error "qp_basis: a step of the tower of K is neither unramified nor generated by a uniformizer";
  end if;
  B:=$$(BaseField(K));
  return [K.1^j*K!c:c in B,j in [0..Degree(K)-1]]; // c varies fastest, as in qp_coordinates

end function;


ros_left_inverse:=function(A,Nw)

  // A left inverse B of the matrix A over Qp (more rows than columns) with the least
  // denominators, from the Smith form P*A*Q = S over the integers at precision Nw: B =
  // Q*S^+*P, S^+ the inverse of the diagonal part. Returns false if A has a zero elementary
  // divisor at this precision; otherwise true, B and delta with v(B) >= -delta.

  Qp:=BaseRing(A); p:=Prime(Qp);
  vmin:=Minimum([0] cat [Valuation(a):a in Eltseq(A)|not IsWeaklyZero(a)]);
  Zw:=pAdicRing(p,Maximum(Nw-vmin,1));
  S,P1,Q1:=SmithForm(Matrix(Zw,Nrows(A),Ncols(A),[Zw!(a*p^(-vmin)):a in Eltseq(A)]));
  n:=Ncols(A);
  if exists{i:i in [1..n]|IsWeaklyZero(S[i,i])} then
    return false,0,0;
  end if;
  Splus:=Matrix(Qp,n,Nrows(A),[(r eq c) select 1/(Qp!S[r,r]) else Qp!0:c in [1..Nrows(A)],r in [1..n]]);
  B:=Qp!p^(-vmin)*ChangeRing(Q1,Qp)*Splus*ChangeRing(P1,Qp);
  return true,B,Maximum([Valuation(S[i,i]):i in [1..n]])+vmin;

end function;


ros_chabauty:=function(datas,known:e:=0,htbound:=10^4)

  // Chabauty-Coleman for the restriction of scalars (Siksek, "Explicit Chabauty over number
  // fields"): the L-rational points of the curve from known points, with the completions
  // K_1, ..., K_k of L at several primes P_1, ..., P_k above p at once, as a Q_p-analytic
  // problem. This needs rank <= (g-1)*n, n = sum_j [K_j:Q_p], instead of rank < g for a
  // single completion (effective_chabauty).
  //
  // Input:  datas    the outputs of coleman_data for the same model (the same polynomial Q)
  //                  over the same number field L at distinct primes above the same p (e.g.
  //                  all of them);
  //         known    the known L-rational points, at least two: pairs [x0, y0] of coordinates
  //                  of good points (set_point at every prime), or lists [* R_1, ..., R_k *] of
  //                  the point records of a point at the primes of datas;
  //         e        as in coleman_integrals_on_basis;
  //         htbound  the height bound of recognize_in_F, for new points.
  // Output: a record with
  //           functionals  the vanishing functionals, the rows of a matrix over Q_p: Q_p-linear
  //                        forms in the integrals of the holomorphic forms omega_1, ...,
  //                        omega_g of data`basis at all primes (the columns: the coordinates
  //                        qp_coordinates of int omega_i at P_j, ordered by j, then i) that
  //                        vanish on the integrals between the known points,
  //           discs        for every prime the centres of its residue discs (Qq_points),
  //           polydiscs    for every residue polydisc D_1 x ... x D_k (a residue disc at every
  //                        prime) a record with the fields
  //                          discs   the indices of the D_j in discs,
  //                          known   the indices of the known points in it,
  //                          status  "known": it contains exactly one L-rational point, the
  //                                  known one; "empty": none; "one": the functionals have
  //                                  exactly one common zero in it, not a known point, whose
  //                                  approximations at the primes are in points, and point =
  //                                  [x0, y0] if it is recognized as an L-rational point
  //                                  (else []); "unresolved": none of these could be shown,
  //           new          the recognized L-rational points [x0, y0] that are not known,
  //           complete     whether every polydisc is "known", "empty", or "one" with a
  //                        recognized point: then the L-rational points are the known and the
  //                        new ones.
  // The conclusions about L-rational points hold if the known points generate a subgroup of
  // finite index of the Mordell-Weil group of the Jacobian over L. A polydisc "one" with an
  // unrecognized zero needs another argument (e.g. a Mordell-Weil sieve); for rank exactly
  // (g-1)*n this is the typical case of the polydiscs without known points.
  //
  // Method. The integrals int_Q1^Q omega at the primes P_j (Q1 = known[1]) of an L-rational
  // point Q lie in K_1^g x ... x K_k^g, a Q_p-space of dimension g*n, and those of the known
  // points span a subspace of dimension r (the rank); the vanishing functionals are its
  // annihilator, of dimension kappa = g*n - r >= n (the left kernel of the matrix of the
  // Q_p-coordinates, basis_kernel). On a polydisc with centres T_j (Qq_points) and local
  // parameters z_j = pi_j*sum_b t_jb*theta_jb (theta_j the Z_p-basis qp_basis(K_j) of O_{K_j},
  // t in Z_p^n), the functionals of int_Q1^T_j omega + tiny(T_j -> z_j) are power series
  //   F(t) = c + A*t + H(t),   H of order >= 2.
  // If A has a left inverse B over Q_p (ros_left_inverse) with all coefficients of B*H in
  // p*Z_p, then t -> -B*c - B*H(t) is a contraction of Z_p^n (a form of Siksek's criterion):
  // B*F has no zero in Z_p^n if B*c is not integral and exactly one otherwise, found by the
  // iteration t -> t - B*F(t); if kappa > n, the common zeros of F are among it, and none if
  // F does not vanish there. The coefficient of t^alpha (|alpha| = m) in z_j^m is
  // pi_j^m*gamma_alpha with gamma_alpha in O_{K_j}, a Z_p-combination of the theta_jb, so the
  // coefficients of B*H are bounded by the values of B*lambda on s_m*pi_j^m*theta_jb (s_m the
  // coefficients of the tiny integrals); the omitted tail and the errors of the values are
  // below p^(Nw-delta), where v(B) >= -delta and Nw is the precision of the values: that of
  // the integrals, and that of the functionals (basis_kernel: the precision of the
  // integrals between the known points minus the valuation of the largest elementary
  // divisor of their matrix). If the criterion fails, a polydisc without known points is
  // still empty if a functional has a constant term of smaller valuation than all its other
  // coefficients.

  k:=#datas;
  if k eq 0 then
    error "ros_chabauty: give the output of coleman_data for at least one prime";
  end if;
  D1:=datas[1]; p:=D1`p; g:=D1`g; L:=D1`L;
  if exists{D:D in datas|D`p ne p or not (D`L cmpeq L) or not (D`Q cmpeq D1`Q)} then
    error "ros_chabauty: the data must be for the same model over the same number field, at primes above the same p";
  end if;
  if #{D`P:D in datas} lt k then
    error "ros_chabauty: the primes of the data must be distinct";
  end if;
  if #known lt 2 then
    error "ros_chabauty: at least two known points are needed";
  end if;
  // the point record of the known point Q at the j-th prime
  record_at:=function(Q,j)
    if Type(Q) eq List then
      return Q[j];
    end if;
    return as_point(Q,datas[j],"ros_chabauty");
  end function;
  // whether the point records R, S reduce to the same point modulo P (the same residue disc)
  same_disc:=func<R,S,Fq|R`inf eq S`inf and Fq!(R`x) eq Fq!(S`x) and [Fq!c:c in R`b] eq [Fq!c:c in S`b]>;
  Qp:=pAdicField(p,Maximum([D`Nmax:D in datas]));
  ttotal:=Cputime();

  // ---- at every prime: the integrals from Q1 to the known points and to the centres of the
  // residue discs (Q_p-coordinates of the holomorphic part, precisions in units of v_p) and
  // the tiny integrals on the discs
  // (lists, not sequences, for the objects over the K_j: a sequence would coerce the elements
  // over K_2, ... into its universe, the objects over K_1)
  nj:=[]; thetas:=[**]; pis:=[**];
  centres:=[**]; disc:=[];
  Ic:=[]; NI:=[];   // Ic[j][a]: the coordinates of int_Q1^Qa omega at P_j, NI[j] the precisions (a >= 2)
  Tc:=[]; NT:=[];   // the same for the centres
  tiny:=[**];       // tiny[j][i]: <tiny integrals of omega_1..omega_g, xt, bt> at the i-th centre
  for j:=1 to k do
    D:=datas[j]; K:=D`K; eK:=D`eK;
    tprime:=Cputime();
    vprintf User1, 1: "ros_chabauty: the prime %o/%o (residue field of size %o) ...\n", j, k, #ResidueClassField(D`P);
    theta:=qp_basis(K);
    Append(~thetas,theta); Append(~nj,#theta);
    piL:=(eK eq 1) select L!p else L!UniformizingElement(D`P); // the disc parameter z = pi*t, as in zeros_on_disk
    Append(~pis,D`m(piL));
    coords:=func<I|&cat[qp_coordinates(I[i],Qp):i in [1..g]]>;
    pts:=[record_at(Q,j):Q in known];
    for a:=1 to #pts do
      _,index:=local_data(pts[a],D);
      D:=update_minpolys(D,pts[a]`inf,index);
      pts[a]:=attach_expansions(pts[a],D,e);
    end for;
    IP1Pi,NIP1Pi,side1:=integrals_from_first(pts,D,"ros_chabauty":e:=e);
    Append(~Ic,[coords([K!0:i in [1..g]])] cat [coords(I):I in IP1Pi]);
    Append(~NI,[Floor(N/eK):N in NIP1Pi]);
    T,D:=Qq_points(D:points:=pts);
    T:=[attach_expansions(R,D,e):R in T];
    Fq:=ResidueClassField(RingOfIntegers(K));
    dj:=[Index([same_disc(R,S,Fq):S in T],true):R in pts];
    if 0 in dj then
      error "ros_chabauty: a known point lies in none of the residue discs of Qq_points";
    end if;
    Append(~disc,dj); Append(~centres,T);
    TcJ:=[]; NTJ:=[]; tinyJ:=[**];
    for i:=1 to #T do
      a:=Index([T[i]`x eq R`x and T[i]`b eq R`b and T[i]`inf eq R`inf:R in pts],true);
      if a eq 1 then // the base point: the integral is 0
        Append(~TcJ,Ic[j][1]); Append(~NTJ,Floor(D`Nmax/eK));
      elif a gt 1 then
        Append(~TcJ,Ic[j][a]); Append(~NTJ,NI[j][a-1]);
      else
        I,N,side1:=coleman_integrals_on_basis(pts[1],T[i],D:e:=e,side1:=side1,return_side:=true);
        if N le 0 then
          error Sprintf("ros_chabauty: the integral to the centre of disc %o at the prime %o has precision %o <= 0; increase N (or e)",i,j,N);
        end if;
        Append(~TcJ,coords(I)); Append(~NTJ,Floor(N/eK));
      end if;
      ser,xt,bt:=tiny_integrals_on_basis_to_z(T[i],D);
      Append(~tinyJ,[*[ser[i0]:i0 in [1..g]],xt,bt*]);
    end for;
    Append(~Tc,TcJ); Append(~NT,NTJ); Append(~tiny,tinyJ);
    datas[j]:=D;
    vprintf User1, 1: "ros_chabauty: the prime %o/%o: %o residue discs (%o s).\n", j, k, #T, Cputime(tprime);
  end for;

  // ---- the vanishing functionals
  n:=&+nj;
  Nw0:=Minimum(&cat NI);
  Qw:=ChangePrecision(Qp,Maximum(Nw0,1));
  M:=Transpose(Matrix(Qw,[[Qw!c:c in &cat[Ic[j][a]:j in [1..k]]]:a in [2..#known]]));
  Lam,NL:=basis_kernel(M:zero_ok:=true); // NL: the precision of the functionals (integral vectors)
  if #Lam lt n then
    error Sprintf("ros_chabauty: %o vanishing functional(s), fewer than the dimension %o of the residue polydiscs: the known points generate a subgroup of rank > (g-1)*%o",#Lam,n,n);
  end if;
  if NL lt 3 then
    print "WARNING: ros_chabauty: the vanishing functionals have only",NL,"correct digit(s); increase N";
  end if;
  Lam:=Matrix(Qp,[[Qp!c:c in Eltseq(v)]:v in Lam]);
  kappa:=Nrows(Lam);
  vprintf User1, 1: "ros_chabauty: %o vanishing functional(s) on polydiscs of dimension %o (precision %o).\n", kappa, n, NL;

  // ---- for every disc: the values of the functionals at the centre (the constant terms) and
  // on the terms s_m*(pi*theta_b)^... of the tiny integrals: rows (m-1)*n_j+b, m >= 1
  offs:=[g*&+[Integers()|nj[jj]:jj in [1..j-1]]:j in [1..k]];
  offn:=[&+[Integers()|nj[jj]:jj in [1..j-1]]:j in [1..k]];
  Lamj:=[Transpose(ColumnSubmatrix(Lam,offs[j]+1,g*nj[j])):j in [1..k]]; // (g*n_j) x kappa
  cst:=[[Vector(Qp,[Qp!c:c in Tc[j][i]])*Lamj[j]:i in [1..#Tc[j]]]:j in [1..k]];
  // the precision of the values: an error p^NL of the functionals times an input of negative
  // valuation (not the case for integral forms and points) lowers it
  vneg:=func<S|Minimum([0] cat [Valuation(c):c in S|not IsWeaklyZero(c)])>;
  Nc:=[[Minimum(NT[j][i],NL+vneg(Tc[j][i])):i in [1..#Tc[j]]]:j in [1..k]];
  coef:=[]; Nco:=[];
  for j:=1 to k do
    coefj:=[**]; Ncoj:=[];
    for i:=1 to #tiny[j] do
      ser:=tiny[j][i][1];
      mt:=Minimum([AbsolutePrecision(s):s in ser])-1; // the last computed coefficient
      rows:=[&cat[qp_coordinates(Coefficient(ser[i0],m)*pis[j]^m*thetas[j][b],Qp):i0 in [1..g]]:b in [1..nj[j]],m in [1..mt]];
      Append(~coefj,Matrix(Qp,rows)*Lamj[j]);
      Append(~Ncoj,NL+vneg(&cat rows));
    end for;
    Append(~coef,coefj); Append(~Nco,Ncoj);
  end for;

  // the values of the functionals at the point t of the polydisc with discs ii (inner
  // functions: their local names differ from those of ros_chabauty, which they import)
  values_at:=function(ii,t)
    vv:=&+[cst[jj][ii[jj]]:jj in [1..k]];
    for jj:=1 to k do
      Kj:=datas[jj]`K;
      zz:=pis[jj]*&+[Kj!(Integers()!t[offn[jj]+bb])*thetas[jj][bb]:bb in [1..nj[jj]]];
      vv+:=Vector(Qp,&cat[qp_coordinates(Evaluate(sr,zz),Qp):sr in tiny[jj][ii[jj]][1]])*Lamj[jj];
    end for;
    return vv;
  end function;
  // the points with coordinates t at the primes, to absolute precision cap (units of v_p)
  points_at:=function(ii,t,cap)
    out:=[**];
    for jj:=1 to k do
      Dj:=datas[jj]; Kj:=Dj`K;
      zz:=pis[jj]*&+[Kj!(Integers()!t[offn[jj]+bb])*thetas[jj][bb]:bb in [1..nj[jj]]];
      er:=O(Kj!p^cap);
      Append(~out,set_bad_point(Evaluate(tiny[jj][ii[jj]][2],zz)+er,[cc+er:cc in Eltseq(Evaluate(tiny[jj][ii[jj]][3],zz))],centres[jj][ii[jj]]`inf,Dj:check:=false));
    end for;
    return out;
  end function;
  // an L-rational point [x0,y0] whose point records at the primes agree with zero, the
  // unique common zero of the functionals in its polydisc: an L-rational point in the
  // polydisc is that zero (if the hypothesis holds), so few digits suffice (slack 1)
  recognize:=function(zero)
    for j0:=1 to k do
      Dj:=datas[j0]; Rj:=zero[j0];
      if Dj`eK ne 1 or Rj`inf or Valuation(Rj`x) lt 0 then
        continue;
      end if;
      if IsWeaklyZero(Rj`x) then
        okr:=true; x0:=L!0;
      else
        okr,x0:=recognize_in_F(Rj`x,Dj:htbound:=htbound,slack:=1);
      end if;
      if not okr then
        continue;
      end if;
      for rt in Roots(PolynomialRing(L)![Evaluate(cc,x0):cc in Coefficients(Dj`Q)]) do
        y0:=rt[1];
        agree:=true;
        for jj:=1 to k do
          try
            Sj:=set_point(x0,y0,datas[jj]);
          catch er
            agree:=false;
          end try;
          if not agree or Sj`inf ne zero[jj]`inf or not IsWeaklyZero(Sj`x-zero[jj]`x) or exists{bb:bb in [1..#Sj`b]|not IsWeaklyZero(Sj`b[bb]-zero[jj]`b[bb])} then
            agree:=false;
            break;
          end if;
        end for;
        if agree then
          return true,[x0,y0];
        end if;
      end for;
    end for;
    return false,[];
  end function;

  // ---- the polydiscs
  fmt:=recformat<discs,known,status,points,point>;
  polydiscs:=[]; new:=[];
  for idx in CartesianProduct([[1..#centres[j]]:j in [1..k]]) do
    ii:=[idx[j]:j in [1..k]];
    kn:=[a:a in [1..#known]|forall{j:j in [1..k]|disc[j][a] eq ii[j]}];
    c:=&+[cst[j][ii[j]]:j in [1..k]];
    A:=Transpose(RowSubmatrix(coef[1][ii[1]],1,nj[1])); // kappa x n: the linear terms
    for j:=2 to k do
      A:=HorizontalJoin(A,Transpose(RowSubmatrix(coef[j][ii[j]],1,nj[j])));
    end for;
    H:=[*RowSubmatrix(coef[j][ii[j]],nj[j]+1,Nrows(coef[j][ii[j]])-nj[j]):j in [1..k]*]; // the terms of order >= 2
    vH:=[Minimum(&cat[[Valuation(H[j][r,l]):r in [1..Nrows(H[j])]]:j in [1..k]]):l in [1..kappa]]; // per functional
    Nw:=Minimum([NL] cat [Nc[j][ii[j]]:j in [1..k]] cat [Nco[j][ii[j]]:j in [1..k]]);
    status:="unresolved"; zero:=[**]; point:=[];
    ok,B,delta:=ros_left_inverse(A,Nw);
    if ok and Nw-delta ge 1 then
      cap:=Nw-delta;
      hB:=Minimum([cap] cat &cat[[Valuation(x):x in Eltseq(H[j]*Transpose(B))]:j in [1..k]]);
      if hB ge 1 then // the criterion holds: B*F has at most one zero
        w:=c*Transpose(B);
        if Minimum([Valuation(x):x in Eltseq(w)]) lt 0 then
          if #kn eq 0 then
            status:="empty";
          else // a known point is a zero: only for lack of precision
            printf "WARNING: ros_chabauty: the polydisc %o contains a known point but the functionals have no zero there (precision too low?)\n", ii;
          end if;
        elif #kn eq 1 then
          status:="known";
        elif #kn eq 0 then
          // the zero of B*F, by the contraction t -> t - B*F(t)
          t:=-w;
          for it:=1 to cap+1 do
            Ft:=values_at(ii,t);
            dt:=Ft*Transpose(B);
            t-:=dt;
            if Minimum([Valuation(x):x in Eltseq(dt)]) ge cap then
              break;
            end if;
          end for;
          // the other functionals at the zero: a value of smaller valuation than its error
          // (Nw, and the error of t times the size of the coefficients) excludes a common zero
          Ft:=values_at(ii,t);
          bound:=[Minimum([Nw,vH[l]+cap] cat [Valuation(A[l,b])+cap:b in [1..n]]):l in [1..kappa]];
          if exists{l:l in [1..kappa]|Valuation(Ft[l]) lt bound[l]} then
            status:="empty";
          else
            status:="one";
            zero:=points_at(ii,t,cap);
            ok,point:=recognize(zero);
            if ok and point notin new then
              Append(~new,point);
            end if;
          end if;
        end if;
      end if;
    end if;
    if status eq "unresolved" and #kn eq 0 then
      // a functional whose constant term dominates its other coefficients has no zero
      if exists{l:l in [1..kappa]|Valuation(c[l]) lt Minimum([Nw,vH[l]] cat [Valuation(A[l,b]):b in [1..n]])} then
        status:="empty";
      end if;
    end if;
    Append(~polydiscs,rec<fmt|discs:=ii,known:=kn,status:=status,points:=zero,point:=point>);
  end for;

  complete:=forall{P:P in polydiscs|P`status in {"known","empty"} or (P`status eq "one" and #P`point gt 0)};
  count:=func<s|#[P:P in polydiscs|P`status eq s]>;
  vprintf User1, 1: "ros_chabauty: %o polydisc(s): %o known, %o empty, %o with one zero (%o recognized), %o unresolved (%o s).\n",
          #polydiscs, count("known"), count("empty"), count("one"), #[P:P in polydiscs|P`status eq "one" and #P`point gt 0], count("unresolved"), Cputime(ttotal);
  out:=recformat<functionals,discs,polydiscs,new,complete>;
  return rec<out|functionals:=Lam,discs:=centres,polydiscs:=polydiscs,new:=new,complete:=complete>;

end function;
