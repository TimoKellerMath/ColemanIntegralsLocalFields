// cohobasis.m -- integral bases, connection matrices and a basis of H^1_dR.
//
// Article: section "Good models" (the matrices W^0, W^inf), the proposition on the matrix of
// the differential in section "Computing a Frobenius lift" (G^0, G^inf and their residue
// matrices), and section "Computing a basis of H^1_dR(U)" (the spaces E_0, E_inf, B_0, B_inf
// and the algorithm "Computing cohomology basis", implemented by basis_coho).
//
// Matrix convention: the code's matrices are the TRANSPOSES of the article's. Basis vectors
// of functions are columns: b^0 = W0*(1,y,...,y^(d-1))^T, b^inf = Winf*(1,y,...,y^(d-1))^T,
// b^inf = W*b^0 with W = Winf*W0^(-1), and d(b^0) = G0*b^0 dx; coefficient vectors of
// functions and forms are rows, and matrices act on them from the right. The orders ord_0,
// ord_inf and ord_r of a matrix do not depend on this.
//
// Notation and conventions: see "Conventions and notation" in README.md.

mat_W0:=function(Q)

  // The integral basis b^0 of the function field L(X) over L[x], as the matrix W0 over
  // L(x) with b^0_(i-1) = sum_j W0[i,j]*y^(j-1) (the transpose of the article's W^0).
  // Input:   Q in L[x][y] (or O_L[x][y]), monic and irreducible in y, defining a
  //          geometrically integral curve.
  // Returns: W0 in M_d(L(x)), from Magma's MaximalOrderFinite. The integral closure of L[x]
  //          is computed over the number field L; its basis stays an integral basis after
  //          extending scalars to the completion K = L_P.

  Lt:=FieldOfFractions(BaseRing(Q));
  F:=ext<Lt|Q>; // Eltseq gives the coordinates w.r.t. 1,y,...,y^(d-1)
  return Matrix(Lt,[Eltseq(F!b):b in Basis(MaximalOrderFinite(F))]);

end function;


mat_Winf:=function(Q)

  // The integral basis b^inf of L(X) over L[1/x], as the matrix Winf over L(x) with
  // b^inf_(i-1) = sum_j Winf[i,j]*y^(j-1) (the transpose of the article's W^inf).
  // Input:   Q as in mat_W0.
  // Returns: Winf in M_d(L(x)).
  // Method:  substitute x -> 1/t in Q, take the integral closure of L[t] in L(t)[y]/(Q) with
  //          MaximalOrderFinite, and substitute t -> 1/x back.

  Lt:=FieldOfFractions(BaseRing(Q));
  Qt:=PolynomialRing(Lt)![Evaluate(c,1/Lt.1):c in Coefficients(Q)];
  F:=ext<Lt|Qt>; // L(t)[y]/(Q(1/t,y))
  return Evaluate(Matrix(Lt,[Eltseq(F!b):b in Basis(MaximalOrderFinite(F))]),1/Lt.1);

end function;


ddx:=function(f)

  // The partial derivative df/dx of f in L[x][y] (coefficientwise in y).

  return Parent(f)![Derivative(c):c in Coefficients(f)];
end function;


ddx_mat:=function(A)

  // The entrywise derivative d/dx of a matrix A over L(x).

  return Matrix(BaseRing(A),NumberOfRows(A),NumberOfColumns(A),[Derivative(a):a in Eltseq(A)]);
end function;


ddx_vec:=function(v)

  // The entrywise derivative d/dx of a vector v over L(x) (or L[x]).

  return Parent(v)![Derivative(a):a in Eltseq(v)];
end function;


reduce_mod_Q_exact:=function(f,Q)

  // The remainder of f modulo Q (division in y): f = a*Q + rem with deg_y(rem) < deg_y(Q),
  // i.e. the representative of f in R[y]/(Q) in the basis 1,y,...,y^(d-1).
  // Requires: f, Q in R[y] for a field R (here L(x)), Q monic in y.

  return f mod Q;
end function;


polys_to_vec:=function(polys,degx)

  // The coefficient vector (in the monomial basis x^j b^0_i of basis_coho) of a sequence of
  // polynomials: polys = [w_0,...,w_(d-1)] in L[x] gives the vector of the coefficients of
  // x^0,...,x^degx of w_0, then of w_1, etc. (coefficients beyond x^degx are dropped).

  return VectorSpace(BaseRing(polys[1]),#polys*(degx+1))![Coefficient(w,j):j in [0..degx],w in polys];
end function;


max_ramification_indices:=function(J0,Jinf)

  // The maximal ramification indices e_0 and e_inf of x : X -> P^1 at the points of X \ U
  // above the zeros of r, resp. above infinity (article: e_0 and e_inf in the precision
  // bounds for the reduction).
  // Input:   J0 the list of Jordan forms of the residue matrices of G0 at the zeros of r
  //          (jordan_0), Jinf the Jordan form of the residue matrix at infinity (jordan_inf).
  // Returns: e_0 (0 if r has no zeros), e_inf.
  // Method:  by the proposition on the matrix of the differential, the exponents at x_0 are
  //          0, 1/e_P, ..., (e_P-1)/e_P for the points P above x_0, so e_P is the largest
  //          denominator of a diagonal entry.

  d:=NumberOfRows(Jinf);
  e_0:=Maximum([0] cat [Denominator(Rationals()!J[j,j]):j in [1..d],J in J0]);
  e_inf:=Maximum([Denominator(Rationals()!Jinf[j,j]):j in [1..d]]);
  return e_0,e_inf;
end function;


connection_matrix:=function(Q,Delta,s)

  // The connection matrix G of the basis 1,y,...,y^(d-1): d(y^(i-1)) = sum_j G[i,j]*y^(j-1) dx
  // (the transpose of the article's convention, see the header).
  // Input:   Q in L[x][y], monic in y; Delta, s from auxpolys (s*dQ/dy = Delta mod Q).
  // Returns: G in M_d(L(x)), with entries in L[x,1/Delta].
  // Method:  dy/dx = -(dQ/dx)/(dQ/dy) = -(dQ/dx)*s/Delta, so d(y^(i-1))/dx =
  //          -(i-1)*y^(i-2)*(s/Delta)*dQ/dx, reduced modulo Q.

  d:=Degree(Q);
  Lx<x>:=RationalFunctionField(BaseRing(Coefficient(Q,1)));
  Lxy<y>:=PolynomialRing(Lx);
  Delta:=Lx!Delta;
  Q:=Lxy!Q;
  s:=Lxy!s;
  dQdx:=ddx(Q);
  rows:=[Lxy!0] cat [reduce_mod_Q_exact(-(i-1)*y^(i-2)*(s/Delta)*dQdx,Q):i in [2..d]];
  return Matrix(Lx,d,d,[Coefficient(rows[i],j-1):j in [1..d],i in [1..d]]); // row i: d(y^(i-1))/dx

end function;


connection_matrices_0_inf:=function(G,W0,Winf)

  // The connection matrices of the integral bases: d(b^0) = G0*b^0 dx and
  // d(b^inf) = Ginf*b^inf dx, with b^0, b^inf as columns (the transposes of the article's
  // G^0, G^inf in the proposition on the matrix of the differential).
  // Input:   G from connection_matrix; W0, Winf from mat_W0, mat_Winf.
  // Returns: G0 = W0*G*W0^(-1) + W0'*W0^(-1) and Ginf = Winf*G*Winf^(-1) + Winf'*Winf^(-1);
  //          under good reduction G0 = M0/r with M0 integral, i.e. G0 dx has at most simple
  //          poles at the zeros of r.

  gauge:=func<W|W*Evaluate(G,BaseRing(W).1)*W^(-1)+ddx_mat(W)*W^(-1)>;
  return gauge(W0), gauge(Winf);

end function;


jordan_inf:=function(Ginf)

  // The residue matrix Ginf_(-1) = -(x*Ginf)|_(x=inf) of the connection at infinity (article:
  // G^inf_(-1) in the proposition on the eigenspace at infinity) and its Jordan form.
  // Returns: Jinf, Tinf, Tinf^(-1) with Jinf = Tinf*Ginf_(-1)*Tinf^(-1).

  t:=BaseRing(Ginf).1;
  Jinf,Tinf:=JordanForm(-Evaluate((1/t)*Evaluate(Ginf,1/t),0));
  return Jinf,Tinf,Tinf^(-1);
end function;


jordan_0:=function(r,G0)

  // The residue matrices of G0 at the zeros of r and their Jordan forms.
  // Input:   r in L[x] squarefree; G0 with at most simple poles at the zeros of r.
  // Returns: lists J0, T0, T0inv, one entry for each irreducible factor g_i of r over L:
  //          with s_i a root of g_i (in L, or in the field L(s_i) = L[x]/(g_i)) and
  //          res_i = (r*G0/r')(s_i) = M0(s_i)/r'(s_i) the residue matrix at s_i,
  //          J0[i] = T0[i]*res_i*T0inv[i] is its Jordan form. The entries of the lists live
  //          over different fields, hence the lists [* *].

  L:=BaseRing(BaseRing(G0));
  r:=PolynomialRing(L)!r;
  rG0:=G0*r/Derivative(r);
  J0:=[**]; T0:=[**]; T0inv:=[**];
  for fac in Factorization(r) do
    if Degree(fac[1]) eq 1 then
      s:=-Evaluate(fac[1],0);
    else
      _<s>:=ext<L|fac[1]>;
    end if;
    J,T:=JordanForm(Evaluate(rG0,s)); // T*res*T^(-1) = J
    Append(~J0,J); Append(~T0,T); Append(~T0inv,T^(-1));
  end for;
  return J0,T0,T0inv;
end function;


ord_0:=function(f)

  // The order ord_0(f) of f in L(x) at x = 0 (Infinity() for f = 0).

  return Valuation(Numerator(f))-Valuation(Denominator(f));
end function;


ord_0_mat:=function(A)

  // ord_0(A) for a matrix A over L(x): the minimal order of its entries at x = 0
  // (Infinity() for the zero matrix).

  v:=Minimum([Infinity()] cat [ord_0(a):a in Eltseq(A)|a ne 0]);
  return v;
end function;


ord_factors:=function(f,fac)

  // The minimum over the irreducible polynomials g in fac of the order of f in L(x) at g.

  num:=Numerator(f); den:=Denominator(f);
  R:=Parent(num);
  v:=Minimum([Valuation(num,R!g)-Valuation(den,R!g):g in fac]);
  return v;
end function;


ord_r:=function(f,r)

  // ord_r(f) for f in L(x) and r in L[x] squarefree: the minimum over the irreducible
  // factors g of r of the order of f at (the zeros of) g, i.e. the largest n with
  // f in r^n * L[x]_(r) (Infinity() for f = 0).

  if f eq 0 then
    return Infinity();
  end if;
  return ord_factors(f,[fac[1]:fac in Factorization(PolynomialRing(BaseRing(r))!r)]);
end function;


ord_r_mat:=function(A,r)

  // ord_r(A) for a matrix A over L(x): the minimal ord_r of its entries (Infinity() for the
  // zero matrix).

  fac:=[fac[1]:fac in Factorization(PolynomialRing(BaseRing(r))!r)];
  v:=Minimum([Infinity()] cat [ord_factors(a,fac):a in Eltseq(A)|a ne 0]);
  return v;
end function;


ord_inf:=function(f)

  // The order ord_inf(f) = deg(denominator) - deg(numerator) of f in L(x) at x = infinity
  // (Infinity() for f = 0).

  if f eq 0 then
    return Infinity();
  end if;
  return Degree(Denominator(f))-Degree(Numerator(f));
end function;


ord_inf_mat:=function(A)

  // ord_inf(A) for a matrix A over L(x): the minimal order of its entries at infinity
  // (Infinity() for the zero matrix).

  v:=Minimum([Infinity()] cat [ord_inf(a):a in Eltseq(A)|a ne 0]);
  return v;
end function;


res_0:=function(w,Q,r,J0,T0inv)

  // The finite residue map res_0 of the form omega = sum_i w_i b^0_i dx/r, in the form used
  // by the residue criterion of the article (the proposition on res_0 in section "Computing
  // a basis of H^1_dR(U)"): res_0(omega) = 0 iff, at every zero s of r, the component of
  // w(s) in the 0-eigenspace of the residue matrix of G0 at s vanishes.
  // Input:   w in L[x]^d; Q the model; r squarefree; J0, T0inv from jordan_0(r,G0), whose
  //          entries are indexed by the irreducible factors of r in the same order.
  // Returns: the vector over L of these components (for a factor of degree > 1, the
  //          coordinates over L of the components in L(s)); its kernel conditions are linear
  //          in w, which is how basis_coho uses it.

  d:=Degree(Q);
  L:=BaseRing(r);
  fac:=Factorization(PolynomialRing(L)!r); // in the order of J0 and T0inv
  res_list:=[L|];
  for i:=1 to #fac do
    F:=BaseRing(T0inv[i]); // the field L(s_i) of jordan_0
    linear:=Degree(fac[i][1]) eq 1;
    s:=linear select F!(-Coefficient(fac[i][1],0)) else F.1; // the root s_i of g_i
    v:=Vector(Evaluate(w,s))*T0inv[i]; // the coordinates of w(s_i) in the Jordan basis
    for j in [j:j in [1..d]|J0[i][j,j] eq 0] do
      res_list cat:=linear select [v[j]] else Eltseq(v[j]); // (Eltseq of an element of L would give coordinates over Q)
    end for;
  end for;
  return Vector(L,res_list);

end function;


val_Lttinv_d:=function(v)

  // The valuation of a vector v of Laurent series, i.e. the minimal valuation of its entries.

  val:=Minimum([Valuation(a):a in Eltseq(v)]);
  return val;
end function;


res_inf:=function(w,Q,r,W0,Winf,Ginf,Jinf,Tinfinv)

  // The residue map res_inf at the points above infinity of omega = sum_i w_i b^0_i dx/r, in
  // the form of the proposition on the eigenspace at infinity: res_inf(omega) = 0 iff the
  // component of v = x^(1-deg r)*w'|_(x=inf) in the 0-eigenspace of Ginf_(-1) vanishes,
  // where w' are the coordinates w.r.t. b^inf dx/r and ord_inf(w') > -deg(r).
  // Input:   w in L[x]^d; Q, r, W0, Winf, Ginf as in coleman_data; Jinf, Tinfinv from
  //          jordan_inf(Ginf).
  // Returns: the vector of these components over L.
  // Method:  pass to w' = w*W^(-1), W = Winf*W0^(-1), in the parameter t = 1/x; while
  //          ord_inf(w') <= -deg(r), subtract the exact form d(vbar*x^m*b^inf) of the infinite
  //          reduction (the proposition on the reduction of a cohomology class, part (2)),
  //          which changes neither the cohomology class nor the residues; then read off v.

  d:=Degree(Q);
  degr:=Degree(r);
  L:=BaseRing(r);
  Ld:=RSpace(L,d);
  Lttinv<t>:=LaurentSeriesRing(L);
  Lttinvd:=RSpace(Lttinv,d);

  W:=Winf*W0^(-1);
  w:=(Lttinvd!Evaluate(w,t^(-1)))*Evaluate(W^(-1),t^(-1));

  X:=BaseRing(Winf).1;
  res_Ginf:=-Evaluate((1/X)*Evaluate(Ginf,1/X),0);

  // reduce to a cohomologous form with ord_inf(w') > -deg(r), i.e. with at most logarithmic
  // poles at the points above infinity:

  while val_Lttinv_d(w) lt -degr+1 do
    m:=-val_Lttinv_d(w)-degr+1; // mu in the article
    rhs:=Ld![Coefficient(-w[i],-m-degr+1)/LeadingCoefficient(r):i in [1..d]]; // -(leading coefficient of w')/lc(r)
    vbar:=ChangeRing(rhs*(res_Ginf-m*IdentityMatrix(L,d))^(-1),Lttinv);
    w:=w-vbar*t^(-m)*Evaluate(r*Ginf,t^(-1))-Evaluate(r,1/t)*m*t^(1-m)*vbar; // w' - r*(v*Ginf + v'), v = vbar*x^m
  end while;

  // now sum_i w'_i b^inf_i dx/r has at most logarithmic poles above infinity; the components
  // of v in the 0-eigenspace of Ginf_(-1) (coordinates in the Jordan basis)

  w:=w*t^(degr-1);
  v:=Ld![Coefficient(w[i],0):i in [1..d]]*Tinfinv;
  return Vector(L,[L|v[i]:i in [1..d]|Jinf[i,i] eq 0]); // of dimension dim V_0, V_0 the 0-eigenspace of Ginf_(-1)
end function;


basis_coho:=function(Q,P,r,W0,Winf,G0,Ginf,J0,Jinf,T0inv,Tinfinv,useU,basis0,basis1,basis2)

  // A basis of H^1_dR(X) (or of H^1_dR(U)) inside E_0 cap E_inf, together with the data for
  // the final reduction (article: the theorem computing H^1_dR(U) from E_0, E_inf, B_0,
  // B_inf, the algorithm "Computing cohomology basis", and the change of basis for the
  // final reduction).
  // Input:    Q, r, W0, Winf, G0, Ginf from coleman_data; J0, T0inv (jordan_0) and Jinf,
  //           Tinfinv (jordan_inf) for the residue maps; P the prime (an ideal of O_L, or p
  //           in the rational branch), only used to make the basis integral at P;
  //           useU: false for a basis of H^1_dR(X), true for one of H^1_dR(U);
  //           basis0, basis1, basis2: optional sequences of forms, each given as d
  //           polynomials [w_0,...,w_(d-1)] for sum_i w_i b^0_i dx/z, that replace the
  //           automatically chosen bases of H^0(X,Omega^1), of a complement of it in
  //           H^1_dR(X), and of H^1_dR(U)/H^1_dR(X) (the classes with residues only at the
  //           points above infinity); [] for automatic.
  // Returns:  basis: the forms omega_1,...,omega_n (n = 2g, or dim H^1_dR(U) if useU) as
  //             vectors w in L[x]^d, meaning sum_i w_i b^0_i dx/z with z = r/lc(r);
  //             omega_1..omega_g are holomorphic, omega_1..omega_2g represent H^1_dR(X);
  //           exact_primitives: functions g_j in B_0 cap B_inf, as vectors in L[x]^d
  //             w.r.t. b^0, such that the dg_j are the exact elements of the basis of E_0;
  //           monomial_to_basis: the matrix converting the coordinates (a row vector) of a
  //             form in E_0 w.r.t. the monomial basis x^j b^0_i dx/z into its coordinates
  //             w.r.t. the full basis of E_0 below (C_end^(-1) of the article, transposed).
  // Method:   E_0 is truncated to the monomials x^j b^0_i dx/r with j <= D = deg(r) -
  //           ord_0(W) - ord_inf(W) - 2 (the remark on E_0 cap E_inf); kernels of linear
  //           maps cut out E_0 cap E_inf, the forms with at most logarithmic poles above
  //           infinity, the forms with vanishing residues (res_0, res_inf) and B_0 cap B_inf.
  //           The full basis of E_0 is ordered as in the article:
  //             b0 (H^0(X,Omega^1)), b1 (the rest of H^1_dR(X)), b2, b3 (the rest of
  //             H^1_dR(U)), b4 (a complement of E_0 cap E_inf in E_0), b5 (the exact forms
  //             dg_j).
  //           Inside this function the coordinates refer to dx/r; read with dx/z they
  //           describe lc(r) times the same forms, which spans the same subspaces, and the
  //           primitives are scaled by lc(r) accordingly.

  L:=BaseRing(Coefficients(Q)[1]);
  Lx<x>:=PolynomialRing(L);
  d:=Degree(Q);
  Lxd:=RSpace(Lx,d);
  degr:=Degree(r);
  if Type(P) eq RngOrdIdl then
    P:=MaximalOrder(L)!!P;
    pi:=UniformizingElement(P);
  else
    pi:=P;
  end if;

  W:=Winf*W0^(-1); // b^inf = W*b^0 (columns)
  Winv:=W^(-1);
  ord0W:=ord_0_mat(W);
  ordinfW:=ord_inf_mat(W);
  ord0Winv:=ord_0_mat(Winv);
  ordinfWinv:=ord_inf_mat(Winv);

  // The coefficient of x^e in x^j*Winv[i+1,k+1], i.e. of x^e b^inf_k in x^j b^0_i (an
  // element of L[x,1/x], made a polynomial by the factor x^(-ord_0(W^(-1)))). For a list of
  // monomials [i,j] and the exponents e = e0+k', 0 <= k' <= n-1, the rows of the matrix of
  // these coefficients, ordered by k and then by k'.
  X:=BaseRing(W).1;
  Winvx:=X^(-ord0Winv)*Winv;
  binf_coefficients:=func<monomials,e0,n|Matrix(L,#monomials,d*n,
    [Coefficient(Numerator(X^m[2]*Winvx[m[1]+1,k+1]),kk+e0-ord0Winv):kk in [0..n-1],k in [0..d-1],m in monomials])>;
  monomial_form:=func<m|Lxd![(i eq m[1]) select x^m[2] else 0:i in [0..d-1]]>; // x^j b^0_i for m = [i,j]

  // (1) the monomial basis of the truncated E_0: x^j b^0_i dx/r, 0 <= j <= D, 0 <= i <= d-1,
  //     ordered first by i, then by j; basisE0[k] = [i,j]

  deg_bound_E0:=degr-ord0W-ordinfW-2;
  basisE0:=[[i,j]:j in [0..deg_bound_E0],i in [0..d-1]]; // b^0_0, x*b^0_0, x^2*b^0_0, ...
  dimE0:=#basisE0;
  E0:=VectorSpace(L,dimE0);

  // (2) E_0 cap E_inf: the kernel of the map that writes a form w.r.t. b^inf dx/r and keeps
  //     the coefficients of the excluded monomials x^i b^inf_j dx/r, i.e. those with
  //     -ord_0(W)+deg(r)-1 <= i <= -ord_inf(W)-ord_inf(W^(-1))-ord_0(W)+deg(r)-2

  E0nEinf:=Kernel(binf_coefficients(basisE0,-ord0W+degr-1,-ordinfW-ordinfWinv));

  // (4) the forms with at most logarithmic poles (order >= -1) at the points above infinity:
  //     the kernel of the projection onto x^i b^inf_j dx/r with
  //     deg(r) <= i <= -ord_inf(W)-ord_inf(W^(-1))-ord_0(W)+deg(r)-2

  logforms:=E0nEinf meet Kernel(binf_coefficients(basisE0,degr,-ord0W-ordinfW-ordinfWinv-1));

  // (3) the forms of the second kind: the kernels of the residue maps, evaluated on the
  //     monomial basis (rows), at the zeros of r and at the points above infinity

  res0s:=[res_0(monomial_form(m),Q,r,J0,T0inv):m in basisE0];
  matres0:=Matrix(L,dimE0,Degree(res0s[1]),[L|c:c in Eltseq(v),v in res0s]);
  resinfs:=[res_inf(monomial_form(m),Q,r,W0,Winf,Ginf,Jinf,Tinfinv):m in basisE0];
  matresinf:=Matrix(L,dimE0,Degree(resinfs[1]),[L|c:c in Eltseq(v),v in resinfs]);

  forms2ndkind:=Kernel(matres0) meet Kernel(matresinf); // forms in E_0 with all residues 0
  cocyc:=E0nEinf meet forms2ndkind;     // the forms of the second kind in E_0 cap E_inf (V in the article)
  forms1stkind:=logforms meet forms2ndkind; // the holomorphic forms H^0(X,Omega^1)

  // (5) B_0 cap B_inf, with B_0 truncated to the functions x^j b^0_i,
  //     0 <= j <= -ord_0(W)-ord_inf(W)-1 (the remark on E_0 cap E_inf); basisB0[k] = [i,j]:
  //     the kernel of the coefficients w.r.t. b^inf of the monomials x^i b^inf_j excluded
  //     from B_inf

  basisB0:=[[i,j]:j in [0..-ord0W-ordinfW-1],i in [0..d-1]];
  B0nBinf:=Kernel(binf_coefficients(basisB0,-ord0W,-ordinfW-ordinfWinv)); // its echelonised basis starts with the constant 1 = b^0_0
  basisB0nBinf:=Basis(B0nBinf);

  // the functions sum_i v_i b^0_i of B_0 cap B_inf (v in L[x]^d), and d(B_0 cap B_inf) as a
  // subspace of E_0: dv = (r*(v'+v*G0)) b^0 dx/r in monomial coordinates
  function_of:=func<vec|Lxd![&+[Lx|vec[k]*x^basisB0[k][2]:k in [1..#basisB0]|basisB0[k][1] eq i]:i in [0..d-1]]>;
  rG0:=ChangeRing(r*G0,Lx);
  differential:=function(vec)
    v:=function_of(vec);
    dv:=v*rG0+r*ddx_vec(v);
    return E0![Coefficient(dv[m[1]+1],m[2]):m in basisE0];
  end function;
  list:=[differential(vec):vec in basisB0nBinf];

  // (6) the bases

  cobound:=sub<cocyc|list>; // d(B_0 cap B_inf), the exact forms in E_0 cap E_inf

  b0:=(basis0 eq []) select Basis(forms1stkind) else [polys_to_vec(w,deg_bound_E0):w in basis0];
  b5:=list[2..#list]; // basis of d(B_0 cap B_inf); the first function is the constant 1, with d1 = 0
  dualspace:=Complement(cocyc,forms1stkind+cobound); // any complement: the algorithm does not need a basis adapted to the cup product
  b1:=(basis1 eq []) select Basis(dualspace) else [polys_to_vec(w,deg_bound_E0):w in basis1];
  dimH1X:=#b0+#b1;

  finiteregularlogarithmic:=logforms meet Kernel(matres0); // logarithmic forms with residues only above infinity
  H1YmodH1X:=Complement(finiteregularlogarithmic,forms1stkind); // H^1_dR(Y)/H^1_dR(X), Y = X minus the points above infinity
  b2:=(basis2 eq []) select Basis(H1YmodH1X) else [polys_to_vec(w,deg_bound_E0):w in basis2];
  b3:=Basis(Complement(E0nEinf,cocyc+H1YmodH1X)); // the rest of H^1_dR(U)
  b4:=Basis(Complement(E0,E0nEinf)); // the forms xi of the article, completing a basis of E_0

  b:=b0 cat b1 cat b2 cat b3 cat b4 cat b5;
  dim:=useU select #b0+#b1+#b2+#b3 else dimH1X;

  // make the returned basis forms integral at P (they need not be primitive)
  for i:=1 to dim do
    b[i]:=pi^(-Minimum([0] cat [Valuation(c,P):c in Eltseq(b[i])|c ne 0]))*b[i];
  end for;

  matb:=Matrix(b); // row k: the k-th basis form of E_0 in the monomial basis (= C_end^T in the article)
  monomial_to_basis:=matb^(-1); // v*monomial_to_basis: the coordinates w.r.t. the rows of matb of the form with monomial coordinates v

  // the primitives g_j of the exact basis forms b5, as functions sum_i g_(j,i) b^0_i; the
  // factor lc(r): the forms are read w.r.t. dx/z, z = r/lc(r), not dx/r
  exact_primitives:=[Lxd|LeadingCoefficient(r)*function_of(vec):vec in basisB0nBinf[2..#basisB0nBinf]];

  // monomial coordinates -> the polynomials w_i of sum_i w_i b^0_i dx/z
  basis:=[Lxd|Lxd![&+[Lx|(L!b[k][j])*x^basisE0[j][2]:j in [1..dimE0]|basisE0[j][1] eq i]:i in [0..d-1]]:k in [1..dim]];

  return basis,exact_primitives,monomial_to_basis;

end function;
