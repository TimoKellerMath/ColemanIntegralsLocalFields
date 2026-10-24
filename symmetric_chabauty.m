// symmetric_chabauty.m
//
// Siksek symmetric Chabauty for degree-2 (quadratic) points, built on the
// Cai-Keller Coleman-integration + effective-Chabauty code (integrals.m, solver.m).
// Load AFTER integrals.m and solver.m.
//
// Target use case: a curve C/F over a number field F, find the quadratic points
// X^{(2)}(F) (= effective F-rational degree-2 divisors) at a prime P of F, given
// rank J(F) <= g-2. In the rank-0 case the annihilating space V is the full space
// of holomorphic differentials and no Mordell-Weil integration is needed.
//
// The local criterion (Siksek, "Chabauty for symmetric powers of curves", Thm 3.2):
// for a residue disc-pair carrying a known degree-2 divisor Q_1+Q_2, the matrix of
// leading Taylor coefficients of the annihilating differentials, reduced mod P, has
// rank 2  ==>  that disc-pair contains AT MOST ONE F-rational quadratic point.
//   split  (Q_1 != Q_2 mod P):  column_i = ( a_0(Q_i, omega_j) )_j
//   diagonal (Q_1 = Q_2 = Q):   columns   = ( a_0(Q,omega_j) )_j , ( -a_1(Q,omega_j) )_j
// where a_l(Q,omega) is the l-th Taylor coefficient of omega/dt at Q.
//
// TWO SPACES OF DIFFERENTIALS.  The
// rank-2 test above may use ANY subspace V of the annihilator of J(F), presented by
// a SATURATED (integral) basis -- see differentials_are_saturated.  The rank-DROP
// branch is a different statement and needs a different space: the conclusion
// "every degree-2 point of this class is a pullback rho^*(P) along a degree-2 map
// rho : X -> C'" holds only
//   (i)  for classes that are themselves of pullback type, Qbar + sigma(Qbar), and
//   (ii) using TRACE-ZERO differentials, W \subseteq V \cap ker(rho_*) =
//        V \cap H^0(X,Omega)^{sigma^* = -1}  (the Prym differentials),
// because only for those is the whole pullback family contained in the zero locus
// of the Chabauty equations (see the proof sketch at symmetric_chabauty_classify).
// A rank-1 class that is NOT of pullback type ("cross" class: two points with the
// same image under X -> P(W^*), but not sigma-conjugate) is certified by NOTHING at
// first order.  So a rank-1 class must not be labelled "family/pullback-certified"
// in general: at q = 41 on X(s3,ns5), 32 of the 74 rank-1 classes are cross classes,
// not family classes.  symmetric_chabauty_classify returns them separately, in `cross`.
//
// Status: the criterion is implemented for all three disc-pair kinds -- split,
// diagonal, and Frobenius-conjugate (degree-2 closed points of X/F_q) -- for any
// genus g and any annihilating space V with dim V >= 2. The criterion matrices use
// ALL differentials of V as rows (any subspace of the annihilating space is
// admissible in Siksek's rank-2 criterion; extra rows can only increase the rank,
// i.e. certify more disc-pairs; for dim V = 2, as in every run for the paper, this
// is the same as using the first two differentials). Recovery of the
// quadratic points is implemented for split disc-pairs (2x2 Newton in the two disc
// parameters + LLL recognition over O_F + rigorous on-curve verification), for diagonal
// disc-pairs (Newton in the symmetric functions t1+t2, t1*t2 of the disc parameters,
// newton_symmetric; the Jacobian in (t1,t2) is singular on the diagonal), and, with the
// option include_bad of quadratic_points_split, in the finite bad discs (expanded at their
// very bad point). Frobenius-conjugate disc-pairs (degree-2 places of X/F_q) are split
// disc-pairs over a K with f_K = 2 (run over such a K); the infinite discs are not covered.
// What is not recovered is COUNTED explicitly, never dropped silently.
//
// Current restrictions of this layer (the integration layer below is more general):
//  (1) P unramified (e_P = 1): the LLL recognition (recognize_in_F) assumes it.
//  (2) Any residue degree f(P) is allowed: the LLL
//      recognition runs against the f_P Q_p-coordinates of an element of
//      K = Q_{p^{f_P}} coordinatewise, so it works for any residue degree; the
//      target order can be supplied via the `basis` parameter (use O_F when the
//      value is known to be Galois-fixed, which keeps the lattice small). This
//      is what makes the Frobenius-conjugate disc-pairs recoverable: see the
//      note at quadratic_points_split.
//  (3) Qq_points (solver.m), used here to enumerate disc centres, reduces the
//      model through L -> K -> F_q, so the model may have arbitrary coefficients in
//      L, as in the integration layer (tests/examples/quadratic-points-over-F.m:
//      curves genuinely defined over Q(sqrt 5)).
//  (4) The PULLBACK branch needs the involution sigma as a 3 x 3 matrix on the
//      plane model and the caller's assertion trace_zero (that W consists of
//      trace-zero differentials for that sigma).  Without them no class is ever
//      labelled pullback and every rank-drop class is reported as uncertified --
//      the conservative default.
// Validated configurations: g = 2, rank 0, V = full holomorphic space
// (X(b3,ns5)/Q(sqrt(5)) at P | 11, test-symchab-Xb3ns5.m), and g = 3, rank 1,
// dim V = 2 from vanishing_differentials (X(s3,ns5)/Q(sqrt(5)) at q = 19, 41, 79, 89;
// test-symchab-Xs3ns5.m).  For X(s3,ns5) the cross classes are disposed of by the
// Mordell-Weil sieve of appendix-A-sieve.m.
// curve_quadratic_points (quadratic_points.m) applies this layer to every residue class
// of a curve given as a Curve, the infinite and bad discs included (in patches of the
// model), and reports the status of every class.


// ---------------------------------------------------------------------------
// Leading Taylor coefficients of the g holomorphic differentials at a disc.
// Returns a g x ncoeffs matrix A over K_P = data`K with
//   A[k][l] = a_{l-1}(Pt, omega_k) = (l-1)-th Taylor coeff of omega_k / dt at Pt,
// where omega_1,...,omega_g is the holomorphic part of the de Rham basis (the first
// g entries of data`basis) and t is the local parameter chosen by local_coord.
// ncoeffs=1 gives the Siksek leading coefficients; ncoeffs>=2 supplies a_1 for the
// diagonal (coinciding) disc and the higher-order test.
// ---------------------------------------------------------------------------
leading_coeffs_at_disc := function(Pt, data : ncoeffs:=1, prec:=0)

  g := data`g;
  K := data`K;
  // tiny_integrals_on_basis_to_z returns the indefinite integrals of ALL 2g basis
  // forms as Laurent series in the local parameter t (plus a constant shift that
  // dies under Derivative); Derivative(ser[k]) is exactly the integrand series of
  // basis form k, whose Taylor coefficients are the a_l we need.
  ser, xt, bt, NPt := tiny_integrals_on_basis_to_z(Pt, data : prec:=prec);
  if NPt le 0 then
    error Sprintf("leading_coeffs_at_disc: tiny-integral precision %o <= 0; increase N", NPt);
  end if;

  A := ZeroMatrix(K, g, ncoeffs);
  for k := 1 to g do                       // first g = holomorphic differentials
    di := Derivative(ser[k]);
    for l := 1 to ncoeffs do
      A[k][l] := Coefficient(di, l-1);
    end for;
  end for;
  return A, NPt, xt, bt;
end function;


// ---------------------------------------------------------------------------
// Annihilating differentials V as coefficient vectors against the holomorphic
// basis omega_1..omega_g. rank-0 case: V is the full space, returned as the g
// standard basis vectors (for rank > 0 a smaller V comes from vanishing_differentials).
// Returns: list V of length-g coefficient vectors (sequences over Z), and dim V = g.
// The function is trivial by design: it gives the rank-0 case the same V-interface,
// so that the criterion and recovery code is the same whether V comes from here
// (rank 0) or from vanishing_differentials (rank > 0).
// ---------------------------------------------------------------------------
annihilating_differentials_full := function(data)
  g := data`g;
  V := [ [ (i eq j select 1 else 0) : j in [1..g] ] : i in [1..g] ];
  return V, g;
end function;


// ---------------------------------------------------------------------------
// Combine a g x ncoeffs leading-coefficient matrix A (basis forms) with an
// annihilating differential v (length-g coeff vector) to get the Taylor
// coefficients (a_0,...,a_{ncoeffs-1}) of the differential omega_v = sum_k v_k omega_k.
// ---------------------------------------------------------------------------
diff_coeffs := function(A, v, data)
  K := data`K;
  g := data`g;
  ncoeffs := Ncols(A);
  return [ &+[ K!v[k] * A[k][l] : k in [1..g] ] : l in [1..ncoeffs] ];
end function;


// ---------------------------------------------------------------------------
// SATURATION of the annihilating space ("integral basis of V").  Siksek's criterion reduces the differentials of V modulo P, so V has
// to be presented by a basis of the SATURATED O_{K_P}-lattice
//     V_{O} = V  \cap  H^0(X_{O_{K_P}}, Omega^1)  =  V \cap O_{K_P}^g
// (coordinates against the holomorphic part omega_1,...,omega_g of data`basis).
// If a basis of a non-saturated sublattice is used -- e.g. {v, v + p w} instead of
// {v, w} -- then the reduction Vbar mod P has too small a dimension and the
// criterion matrix loses rank: the outcome is conservative (fewer classes are
// certified), never unsound, but it can silently destroy an otherwise valid
// certificate.  `vanishing_differentials` (solver.m) already returns a saturated
// basis -- `basis_kernel` reads the kernel off the rows of the unimodular Smith
// transform P1, and a direct summand of O^g is what that produces -- so V coming
// from there needs no repair; the two functions below let a hand-supplied V be
// tested and, if necessary, replaced.
//
// NOTE (model hypothesis).  Saturating inside O_{K_P}^g is the right thing only if
// omega_1,...,omega_g is itself an O_{K_P}-basis of H^0 of the smooth model, which
// is part of Tuitman's good-model hypotheses on (Q,W^0,W^inf) and is assumed
// throughout, exactly as it is for the reduction of the criterion matrix itself.
// ---------------------------------------------------------------------------
differentials_are_saturated := function(V, data)
  K := data`K; OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  g := data`g;
  if #V eq 0 then return true; end if;
  A := Matrix(K, [ [ K!V[i][j] : j in [1..g] ] : i in [1..#V] ]);
  val := Minimum([ Valuation(z) : z in Eltseq(A) | z ne 0 ]);
  A := (K!1/K!(UniformizingElement(K)^val)) * A;              // make primitive
  Abar := Matrix(Fq, #V, g, [ red(OK!A[i][j]) : j in [1..g], i in [1..#V] ]);
  return Rank(Abar) eq #V;
end function;

// NB the two kernel computations each go through a Smith form over O_{K_P} at the
// working precision, so the saturated basis agrees with the exact one only to about
// N-1 digits (verified: the returned vectors pair to valuation N-1, not N, against a
// kernel vector of the original span).  That is irrelevant for the mod-P reduction the
// criterion performs, but do not feed the output into a full-precision Newton solve.
saturate_differentials := function(V, data)
  // A basis of the saturation in O_K^g of the lattice spanned by V, to about N-1 digits.
  K := data`K; g := data`g;
  if #V eq 0 or #V eq g then return V; end if;
  A := Matrix(K, [ [ K!V[i][j] : j in [1..g] ] : i in [1..#V] ]);
  N1 := basis_kernel(Transpose(A));            // saturated basis of {v in O^g : A.v^T = 0}
  M1 := Matrix(K, N1);
  S  := basis_kernel(Transpose(M1));           // saturated basis of its orthogonal = sat(V)
  if #S ne #V then
    error Sprintf("saturate_differentials: saturation has dimension %o, expected %o", #S, #V);
  end if;
  return [ [ S[i][j] : j in [1..g] ] : i in [1..#S] ];
end function;


// ---------------------------------------------------------------------------
// The bielliptic/degree-2-quotient involution on residue classes.
//
// `sigma` is a 3 x 3 matrix over data`L (or over Q) acting on the plane model of
// data`Q by the COLUMN convention  (x:y:z) |-> sigma * (x,y,z)^t.
// The two functions below reduce it mod P and
// report which residue classes of degree 2 are of PULLBACK type, i.e. of the shape
// Qbar + sigma(Qbar):
//    split     {Qbar_i, Qbar_j} : sigma(Qbar_i) = Qbar_j
//    diagonal  2 Qbar_i         : sigma(Qbar_i) = Qbar_i  (a ramification point of rho)
//    conjugate {Q, Q^(q)}       : sigma(Q) = Q^(q)  in X(F_{q^2})
// These are exactly the classes into which the infinite family rho^*C'(F) reduces,
// and the only ones for which the rank-1 branch of the criterion says anything.
// ---------------------------------------------------------------------------
reduce_L_scalar := function(z, data)
  K := data`K; OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  mz := data`m(data`L!z);
  if mz ne 0 and Valuation(mz) lt 0 then
    error "reduce_L_scalar: entry of sigma is not integral at P";
  end if;
  return red(OK!mz);
end function;

// (xbar,ybar) of the good (finite, r != 0) disc centres, read off the reduced
// b^0-coordinates: b_j = sum_i W0[j][i] y^(i-1), so (1,y,...,y^(d-1)) = W0^(-1) b.
disc_plane_points := function(good, data)
  K := data`K; OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  d := Degree(data`Q); W0 := data`W0;
  _, _, Fqx, red_ratfun := reduced_function_field(data);
  W0bar := Matrix(Fqx, d, d, [ red_ratfun(W0[i][j]) : j in [1..d], i in [1..d] ]);
  out := [];
  for i := 1 to #good do
    xb := red(OK!(K!good[i]`x));
    Wb := Matrix(Fq, d, d, [ Evaluate(W0bar[a][b], xb) : b in [1..d], a in [1..d] ]);
    bb := Vector(Fq, [ red(OK!(K!good[i]`b[j])) : j in [1..d] ]);
    v  := Solution(Transpose(Wb), bb);        // v * W0bar^t = b  <=>  W0bar * v^t = b^t
    Append(~out, <xb, v[2]>);
  end for;
  return out;
end function;

// index j with sigma(disc i) = disc j among the good discs (0 if sigma sends the
// disc to a bad/infinite one, which is then reported and never certified).
sigma_partner_discs := function(good, data, sigma)
  Fq := ResidueClassField(RingOfIntegers(data`K));
  xy := disc_plane_points(good, data);
  Sb := Matrix(Fq, 3, 3, [ reduce_L_scalar(sigma[i][j], data) : j in [1..3], i in [1..3] ]);
  idx := AssociativeArray();
  for i := 1 to #good do idx[xy[i]] := i; end for;
  part := [ 0 : i in [1..#good] ];
  for i := 1 to #good do
    v := Vector(Fq, [xy[i][1], xy[i][2], Fq!1]) * Transpose(Sb);   // = Sb * (x,y,1)^t
    if v[3] eq 0 then continue; end if;                            // image at infinity
    key := <v[1]/v[3], v[2]/v[3]>;
    if IsDefined(idx, key) then part[i] := idx[key]; end if;
  end for;
  return part, xy;
end function;


// ---------------------------------------------------------------------------
// The d=2 criterion on a single disc-pair.
//   kind = "split":    pairpts = [Q1, Q2], Q1 != Q2 mod P (point records over K_P)
//   kind = "diagonal": pairpts = [Q],      the fat point 2Q
// V: list of >= 2 annihilating differentials (length-g coeff vectors). ALL of V
//    is used: the criterion matrix has one row per differential (any subspace of
//    the annihilating space is admissible, and more rows can only increase the
//    rank). For rank 0 pass annihilating_differentials_full(data).
// Returns: certified (rank eq 2), the reduced #V x 2 matrix Mbar over F_q, its
//          rank, and the unreduced matrix M over K_P.
// ---------------------------------------------------------------------------
symmetric_chabauty_criterion_pair := function(kind, pairpts, V, data : prec:=0)

  K := data`K;
  Fq, red := ResidueClassField(RingOfIntegers(K));
  nV := #V;
  if nV lt 2 then error "symmetric_chabauty_criterion_pair: need dim V >= 2"; end if;

  if kind eq "split" then
    Q1 := pairpts[1]; Q2 := pairpts[2];
    A1 := leading_coeffs_at_disc(Q1, data : ncoeffs:=1, prec:=prec);
    A2 := leading_coeffs_at_disc(Q2, data : ncoeffs:=1, prec:=prec);
    // row j = ( a_0(Q_1, omega_{V[j]}), a_0(Q_2, omega_{V[j]}) )
    M := Matrix(K, [ [ diff_coeffs(A1, V[j], data)[1], diff_coeffs(A2, V[j], data)[1] ] : j in [1..nV] ]);

  elif kind eq "diagonal" then
    Q := pairpts[1];
    A := leading_coeffs_at_disc(Q, data : ncoeffs:=2, prec:=prec);
    // row j = ( a_0(Q, omega_{V[j]}), -a_1(Q, omega_{V[j]}) )
    M := Matrix(K, [ [ diff_coeffs(A, V[j], data)[1], -diff_coeffs(A, V[j], data)[2] ] : j in [1..nV] ]);

  else
    error "symmetric_chabauty_criterion_pair: kind must be \"split\" or \"diagonal\"";
  end if;

  Mbar := Matrix(Fq, [ [ red(M[j][1]), red(M[j][2]) ] : j in [1..nV] ]);
  rk := Rank(Mbar);
  return (rk eq 2), Mbar, rk, M;
end function;


// ---------------------------------------------------------------------------
// Reduce a polynomial over L = data`L to a univariate polynomial over the
// residue field F_q (= ResidueClassField(O_{K_P})), via c |-> red(O_K ! m(c)).
// Errors if a coefficient is non-integral at P (then the leading-coeff reduction
// must instead be done p-adically over K_{P,2} -- see note in conjugate_disc_criterion).
// ---------------------------------------------------------------------------
reduce_Lpoly_to_Fq := function(poly, data, Fqpol)
  m := data`m; K := data`K; OK := RingOfIntegers(K);
  Fq, red := ResidueClassField(OK);
  cs := Coefficients(poly);
  out := Fqpol!0;
  for k := 1 to #cs do
    mc := m(cs[k]);
    if mc ne 0 and Valuation(mc) lt 0 then
      error "reduce_Lpoly_to_Fq: non-integral coefficient at P (need p-adic reduction route)";
    end if;
    out +:= red(OK!mc) * Fqpol.1^(k-1);
  end for;
  return out;
end function;


// The value at x0 (in an extension of F_q, e.g. the residue field of a place of degree 2)
// of a polynomial p over F_q, coefficientwise.
eval_Fq_poly := function(p, x0)
  F := Parent(x0);
  return &+[ F | (F!Coefficient(p,k)) * x0^k : k in [0..Degree(p)] ];
end function;


// ---------------------------------------------------------------------------
// The d=2 criterion on the Frobenius-conjugate disc-pairs: degree-2 closed points
// of X/F_q (one closed point with two geometric points Q, Q^sigma over F_{q^2}).
// At a good place, a_0(Q,omega_i) = ( sum_j basis_bar[i][j](xbar0) * bbar_j ) / r_monic_bar(xbar0)
// is an algebraic evaluation in F_{q^2}; the conjugate column is the q-power
// Frobenius twist. rank 2 over F_{q^2} ==> at most one quadratic point reduces here.
// Returns counts and details; counts (does not handle) bad/infinite degree-2 places.
// RANK-0 ONLY: this standalone tool uses the holomorphic BASIS
// forms as the annihilating differentials (all g of them as rows), which is valid
// precisely when rank J(F) = 0. For general V (rank > 0) use
// symmetric_chabauty_classify, whose conjugate section takes V. This is the
// rank-0 tool of test-symchab-Xb3ns5.m.
// TRACE ZERO (cf. the rank-1 branch): for a HYPERELLIPTIC curve
// the hyperelliptic involution acts by -1 on the whole of H^0(X,Omega), so V = the
// full holomorphic space is automatically trace zero and the pullback branch is
// applicable here without further hypotheses -- but only, as always, on classes of
// pullback type Qbar + iota(Qbar). The rank-drop places reported below are labelled,
// not certified; `pull_details` records x0 and whether x0 lies in F_q, which for a
// hyperelliptic model is exactly the test "the degree-2 place is {Q, iota Q}".
// ---------------------------------------------------------------------------
conjugate_disc_criterion := function(data : verbose:=true)

  Q := data`Q; d := Degree(Q); W0 := data`W0;
  K := data`K; OK := RingOfIntegers(K);
  g := data`g;
  Fq := ResidueClassField(OK);
  q := #Fq;
  Fqpol := PolynomialRing(Fq);

  // the function field of X/F_q, and b^0_j mod P as functions on it
  FFq, _, Fqx, red_ratfun := reduced_function_field(data);
  b0modp := reduced_basis(FFq, W0, red_ratfun);

  // reduced holomorphic basis-form coefficients and reduced r_monic
  basis := data`basis; r := data`r;
  Lx := PolynomialRing(data`L);
  rmon_bar := reduce_Lpoly_to_Fq(Lx!(r/LeadingCoefficient(r)), data, Fqpol);
  basis_bar := [ [ reduce_Lpoly_to_Fq(Lx!basis[i][j], data, Fqpol) : j in [1..d] ] : i in [1..g] ];

  places2 := Places(FFq, 2);
  ncert := 0; npull := 0; nbad := 0; ninf := 0;
  pull_details := [* *];
  for pl in places2 do
    // infinite place (x has a pole)?
    if Valuation(FFq!Fqx.1, pl) lt 0 then ninf +:= 1; continue; end if;
    F2 := ResidueClassField(pl);            // F_{q^2}
    x0 := Evaluate(FFq!Fqx.1, pl);          // in F2
    rden := eval_Fq_poly(rmon_bar, x0);
    if rden eq 0 then nbad +:= 1; continue; end if;   // branch/bad place
    bbar := [ Evaluate(b0modp[j], pl) : j in [1..d] ];
    c := [ (&+[ F2 | eval_Fq_poly(basis_bar[i][j], x0) * bbar[j] : j in [1..d] ]) / rden : i in [1..g] ];
    // row i = ( a_0(Q,omega_i), a_0(Q,omega_i)^q ), for ALL g basis forms (rank 0:
    // every holomorphic form annihilates; for g = 2 this is Siksek's 2x2 matrix)
    M := Matrix(F2, [ [ c[i], c[i]^q ] : i in [1..g] ]);
    rk := Rank(M);
    if rk eq 2 then
      ncert +:= 1;
    else
      npull +:= 1;
      Append(~pull_details, <x0, x0^q eq x0>);   // x0 in F_q <=> "type-b" inert hyperelliptic pair
    end if;
  end for;

  if verbose then
    printf "conjugate_disc_criterion: %o degree-2 places -- %o certified (rank 2), %o pullback (rank<2), %o bad, %o infinite.\n",
       #places2, ncert, npull, nbad, ninf;
  end if;
  return ncert, npull, nbad, ninf, pull_details;
end function;


// ---------------------------------------------------------------------------
// General classifier: given annihilating differentials V (a list of >= 2 length-g
// coefficient vectors against the holomorphic basis, e.g. from
// vanishing_differentials, or annihilating_differentials_full at rank 0), apply
// the d=2 Siksek criterion to every residue disc-pair (split, diagonal and
// Frobenius-conjugate).  V must be a SATURATED (integral) basis; it is tested and
// repaired if not (see differentials_are_saturated / saturate_differentials).
//
// THREE outcomes per residue class (a two-way split "rank 2 / rank 1 = family"
// would not be sound):
//
//   CERTIFIED  rk(Abar_V) = 2 : the class contains at most one point of X^(2)(F).
//              (Siksek; valid for any V inside the annihilator of J(F).)
//
//   PULLBACK   the class is itself of pullback type, Qbar + sigma(Qbar), AND the
//              differentials used have TRACE ZERO, i.e. lie in ker(rho_*) =
//              H^0(X,Omega)^{sigma^* = -1}, AND rk(Abar_W) >= 1 : then every point
//              of X^(2)(F) in the class is a pullback rho^*(P), P in C'(F).
//              Reason: for a trace-zero omega and D_0 = rho^*(pt), transporting the
//              disc parameter by sigma gives f_omega(t_1,t_2) = g(t_1) - g(t_2),
//              which factors as (t_1-t_2)*h with h(0,0) = a_0(Qbar,omega); if some
//              omega in W has a_0 a unit then h is a unit on the whole polydisc
//              (p > 2), so t_1 = t_2, i.e. the point is rho^*(P).  The SAME
//              argument, with the parameter at a ramification point normalised so
//              that sigma(t) = -t, covers the diagonal class 2Qbar at a fixed point
//              of sigma, and it covers a conjugate class {Q,Q^(q)} with
//              sigma(Q) = Q^(q) after base change to the unramified quadratic
//              extension, where that class becomes a split one.
//              NB the trace-zero hypothesis is essential: for omega in the full
//              annihilator that is NOT trace-zero, the pullback family is not
//              contained in the zero locus of f_omega and the factorisation fails.
//
//   UNCERTIFIED everything else.  In particular rk(Abar) = 1 on a class that is NOT
//              of pullback type ("CROSS" classes: two points with the same image
//              under the map X -> P(W^*) defined by W, but not sigma-conjugate).
//              These are NOT family classes and nothing is proved about them here;
//              they are returned explicitly in `cross` so that they can be disposed
//              of by other means (a Mordell-Weil / reachability argument, or a
//              second prime).  For C = X(s3,ns5) there are 32 of them at q = 41
//              against 42 genuine pullback classes.
//
// Optional parameters:
//   sigma      3 x 3 matrix over data`L (or Q) giving the involution on the plane
//              model, column convention (x:y:z) |-> sigma*(x,y,z)^t.  Without it no
//              class is ever labelled PULLBACK: rank-drop classes are all reported
//              as uncertified.
//   trace_zero assert that the differentials of W are trace zero for that sigma.
//              Required for the PULLBACK conclusion.  (For X(s3,ns5) it holds for
//              a structural reason: J ~ E x A with rk A(F) = 0, so the 2-dimensional
//              Prym = trace-zero space is annihilating and already exhausts
//              dim V = g - rk J(F) = 2, whence V = W is the trace-zero space.)
//   W          the trace-zero subspace to use in the PULLBACK test; defaults to V.
//
// Returns a record with the counts and the classified lists.
// ---------------------------------------------------------------------------
symmetric_chabauty_classify := function(data, V : prec:=0, verbose:=true,
                                        sigma:=0, trace_zero:=false, W:=[])

  K := data`K; OK := RingOfIntegers(K); g := data`g; d := Degree(data`Q);
  Fq, red := ResidueClassField(OK); q := #Fq;
  if #V lt 2 then error "symmetric_chabauty_classify: need dim V >= 2 (Chabauty rank <= g-2)"; end if;
  if not differentials_are_saturated(V, data) then
    printf "symmetric_chabauty_classify: WARNING -- V was not given by a saturated (integral) basis; saturating it.\n";
    V := saturate_differentials(V, data);
  end if;
  if #W eq 0 then W := V; end if;
  usesigma := (Type(sigma) ne RngIntElt);
  if usesigma and not trace_zero and verbose then
    printf "symmetric_chabauty_classify: NOTE -- sigma given but trace_zero is false; pullback-type classes are only LABELLED, not certified.\n";
  end if;
  if trace_zero and not usesigma then
    error "symmetric_chabauty_classify: trace_zero asserted but no sigma supplied";
  end if;

  // ---- split + diagonal over the good finite F_q-discs ----
  Qqpts, data := Qq_points(data);
  good := []; nbad := 0;
  for i := 1 to #Qqpts do
    if is_bad(Qqpts[i], data) then nbad +:= 1; continue; end if;
    Append(~good, Qqpts[i]);
  end for;
  LC := [* *];
  for i := 1 to #good do
    Append(~LC, leading_coeffs_at_disc(good[i], data : ncoeffs:=2, prec:=prec));
  end for;
  a  := function(i,j,l) return diff_coeffs(LC[i], V[j], data)[l+1]; end function;  // a_l(disc i, omega_{V[j]})
  aW := function(i,j,l) return diff_coeffs(LC[i], W[j], data)[l+1]; end function;  // ditto for W
  nV := #V; nW := #W;

  part := [ 0 : i in [1..#good] ];
  if usesigma then part := sigma_partner_discs(good, data, sigma); end if;

  cert_split := 0; cert_diag := 0; cert_conj := 0;
  uncert := [* *]; pull := [* *]; cross := [* *]; nr0 := 0;

  for i := 1 to #good do
    for jj := i+1 to #good do
      M := Matrix(Fq, [ [red(a(i,j,0)), red(a(jj,j,0))] : j in [1..nV] ]);
      rk := Rank(M);
      if rk eq 2 then cert_split +:= 1; continue; end if;
      Append(~uncert, <"split",i,jj>);
      ispull := usesigma and (part[i] eq jj);
      rkW := ispull select Rank(Matrix(Fq, [ [red(aW(i,j,0))] : j in [1..nW] ])) else 0;
      if trace_zero and ispull and rkW ge 1 then
        Append(~pull, <"split",i,jj>);
      else
        Append(~cross, <"split",i,jj,rk,ispull>);
        if rk eq 0 then nr0 +:= 1; end if;
      end if;
    end for;
  end for;

  for i := 1 to #good do
    M := Matrix(Fq, [ [red(a(i,j,0)), red(-a(i,j,1))] : j in [1..nV] ]);
    rk := Rank(M);
    if rk eq 2 then cert_diag +:= 1; continue; end if;
    Append(~uncert, <"diagonal",i,i>);
    ispull := usesigma and (part[i] eq i);
    rkW := ispull select Rank(Matrix(Fq, [ [red(aW(i,j,0))] : j in [1..nW] ])) else 0;
    if trace_zero and ispull and rkW ge 1 then
      Append(~pull, <"diagonal",i,i>);
    else
      Append(~cross, <"diagonal",i,i,rk,ispull>);
      if rk eq 0 then nr0 +:= 1; end if;
    end if;
  end for;

  // ---- conjugate (F_{q^2}) disc-pairs: reduced algebraic a_0 + Frobenius twist ----
  Fqpol := PolynomialRing(Fq);
  FFq, _, Fqx, red_ratfun := reduced_function_field(data);
  b0modp := reduced_basis(FFq, data`W0, red_ratfun);
  Lx := PolynomialRing(data`L);
  rmon := reduce_Lpoly_to_Fq(Lx!(data`r/LeadingCoefficient(data`r)), data, Fqpol);
  basis_bar := [ [ reduce_Lpoly_to_Fq(Lx!data`basis[i][j], data, Fqpol) : j in [1..d] ] : i in [1..g] ];
  Vbar := [ [ red(OK!(K!V[jj][k])) : k in [1..g] ] : jj in [1..nV] ];   // V reduced mod P
  Wbar := [ [ red(OK!(K!W[jj][k])) : k in [1..g] ] : jj in [1..nW] ];   // W reduced mod P
  Sb := usesigma select Matrix(Fq, 3, 3, [ reduce_L_scalar(sigma[i][j], data) : j in [1..3], i in [1..3] ])
                  else ZeroMatrix(Fq,3,3);

  nconj_bad := 0;
  for pl in Places(FFq, 2) do
    if Valuation(FFq!Fqx.1, pl) lt 0 then nconj_bad +:= 1; continue; end if;
    F2 := ResidueClassField(pl); x0 := Evaluate(FFq!Fqx.1, pl);
    rden := eval_Fq_poly(rmon, x0);
    if rden eq 0 then nconj_bad +:= 1; continue; end if;
    bb := [ Evaluate(b0modp[j], pl) : j in [1..d] ];
    abas := [ (&+[F2| eval_Fq_poly(basis_bar[i][j], x0)*bb[j] : j in [1..d]])/rden : i in [1..g] ];  // a_0 of basis forms
    cV := [ &+[F2| (F2!Vbar[jj][k])*abas[k] : k in [1..g]] : jj in [1..nV] ];                 // a_0 of V-forms
    M := Matrix(F2, [ [cV[jj], cV[jj]^q] : jj in [1..nV] ]);
    rk := Rank(M);
    if rk eq 2 then cert_conj +:= 1; continue; end if;
    Append(~uncert, <"conjugate", x0, 0>);
    ispull := false;
    if usesigma then
      y0 := Evaluate(FFq.1, pl);
      v := Vector(F2, [x0, y0, F2!1]) * Transpose(ChangeRing(Sb, F2));   // = sigma*(x0,y0,1)^t
      ispull := (Rank(Matrix(F2, 2, 3, [ v[1],v[2],v[3], x0^q, y0^q, F2!1 ])) eq 1);
    end if;
    rkW := 0;
    if ispull then
      cW := [ &+[F2| (F2!Wbar[jj][k])*abas[k] : k in [1..g]] : jj in [1..nW] ];
      rkW := Rank(Matrix(F2, [ [cW[jj]] : jj in [1..nW] ]));
    end if;
    if trace_zero and ispull and rkW ge 1 then
      Append(~pull, <"conjugate", x0, 0>);
    else
      Append(~cross, <"conjugate", x0, 0, rk, ispull>);
      if rk eq 0 then nr0 +:= 1; end if;
    end if;
  end for;

  ncert := cert_split + cert_diag + cert_conj;
  if verbose then
    printf "symmetric_chabauty_classify (g=%o, dimV=%o, dimW=%o, sigma=%o, trace_zero=%o): %o good discs, %o bad/inf finite discs.\n",
       g, #V, #W, usesigma, trace_zero, #good, nbad;
    printf "  CERTIFIED (rk = 2, <= 1 quadratic point): %o split + %o diagonal + %o conjugate = %o\n",
       cert_split, cert_diag, cert_conj, ncert;
    printf "  PULLBACK  (class = Qbar + sigma Qbar, trace-zero W, rk >= 1: only pullbacks): %o\n", #pull;
    printf "  UNCERTIFIED: %o (of which rank 0: %o) ; bad/inf conjugate: %o\n", #cross, nr0, nconj_bad;
    if #cross gt 0 and usesigma then
      ncross1 := 0; for t in cross do if t[4] eq 1 then ncross1 +:= 1; end if; end for;
      printf "    NOTE: %o of the uncertified classes have rank 1 but are NOT of pullback type (\"cross\" classes);\n", ncross1;
      printf "          nothing is certified for them here -- dispose of them separately (e.g. by a Mordell-Weil sieve).\n";
    end if;
  end if;
  fmt := recformat< good, uncert, pull, cross, ncert, npull, ncross, nbad, nconj_bad, nrank0 >;
  return rec< fmt | good:=good, uncert:=uncert, pull:=pull, cross:=cross, ncert:=ncert,
                    npull:=#pull, ncross:=#cross, nbad:=nbad, nconj_bad:=nconj_bad, nrank0:=nr0 >, data;
end function;


// ---------------------------------------------------------------------------
// Driver: quadratic points of a genus-2 curve with rank J(F) = 0.
// Enumerates good residue discs of X/F_q, forms split + diagonal disc-pairs,
// applies the criterion, and classifies each pair:
//   "certified"  rank 2: at most one quadratic point reduces here;
//   "pullback"   rank<2: the hyperelliptic-conjugate locus (parametrised family).
// Counts (but does not treat) the Frobenius-conjugate (F_{q^2}) disc-pairs and
// the bad/infinite discs, so the residual completeness gap is explicit.
//
// Returns a record with the classification and the explicit gap counts.
//
// PIPELINES: this driver + recovery_candidates_rank0 +
// recover_point_in_pair form the g=2/rank-0 pipeline (used by
// test-symchab-Xb3ns5.m). It is the specialization, via
// V = annihilating_differentials_full, of the general-V pipeline
// symmetric_chabauty_classify + recovery_candidates_V + recover_point_V /
// quadratic_points_split (used for X(s3,ns5)).
// ---------------------------------------------------------------------------
quadratic_points_genus2_rank0 := function(data : prec:=0, verbose:=true)

  if data`g ne 2 then error "quadratic_points_genus2_rank0: expects genus 2"; end if;

  K := data`K;
  Fq, red := ResidueClassField(RingOfIntegers(K));
  V := annihilating_differentials_full(data);   // full holomorphic space (rank 0)

  // --- enumerate residue discs (one lifted K_P-point per disc of X/F_q) ---
  Qqpts, data := Qq_points(data);
  good := []; xbar := [];
  nbad := 0;
  for i := 1 to #Qqpts do
    if is_bad(Qqpts[i], data) then nbad +:= 1; continue; end if;
    Append(~good, Qqpts[i]);
    Append(~xbar, red(K!Qqpts[i]`x));
  end for;
  if verbose then
    printf "quadratic_points_genus2_rank0: %o residue discs (%o good finite, %o bad/infinite).\n",
       #Qqpts, #good, nbad;
  end if;

  // --- precompute leading coefficients (ncoeffs=2) once per good disc ---
  LC := [* *];
  for i := 1 to #good do
    A := leading_coeffs_at_disc(good[i], data : ncoeffs:=2, prec:=prec);
    Append(~LC, A);
  end for;

  // a_l(omega_j) at disc i, from the precomputed basis-form matrix
  coeff := function(i, j, l) // l in {0,1}
    return diff_coeffs(LC[i], V[j], data)[l+1];
  end function;

  certified := [];   // disc-pairs proven to hold <= 1 quadratic point
  pullback  := [];   // rank-drop disc-pairs (hyperelliptic locus)

  // split pairs
  for a := 1 to #good do
    for b := a+1 to #good do
      M := Matrix(Fq, 2, 2,
        [ red(coeff(a,1,0)), red(coeff(b,1,0)),
          red(coeff(a,2,0)), red(coeff(b,2,0)) ]);
      rk := Rank(M);
      if rk eq 2 then
        Append(~certified, <"split", a, b>);
      else
        Append(~pullback, <"split", a, b>);
      end if;
    end for;
  end for;

  // diagonal (fat) pairs
  for a := 1 to #good do
    M := Matrix(Fq, 2, 2,
      [ red(coeff(a,1,0)), red(-coeff(a,1,1)),
        red(coeff(a,2,0)), red(-coeff(a,2,1)) ]);
    rk := Rank(M);
    if rk eq 2 then
      Append(~certified, <"diagonal", a, a>);
    else
      Append(~pullback, <"diagonal", a, a>);
    end if;
  end for;

  // --- explicit completeness gap: conjugate (F_{q^2}) discs + bad discs ---
  // number of degree-2 places of X/F_q = (#X(F_{q^2}) - #X(F_q)) / 2
  FFq := reduced_function_field(data);
  nconj := #Places(FFq, 2);                        // degree-2 closed points

  if verbose then
    printf "  split+diagonal disc-pairs: %o certified (rank 2), %o on the pullback locus (rank<2).\n",
       #certified, #pullback;
    printf "  COMPLETENESS GAP (not treated here): %o Frobenius-conjugate (F_{q^2}) disc-pair(s), %o bad/infinite disc(s).\n",
       nconj, nbad;
  end if;

  format := recformat< good, xbar, certified, pullback, nconj, nbad, V, LC >;
  out := rec< format |
    good := good, xbar := xbar, certified := certified, pullback := pullback,
    nconj := nconj, nbad := nbad, V := V, LC := LC >;
  return out, data;
end function;


// ---------------------------------------------------------------------------
// RECOVERY (rank 0): which certified split/diagonal disc-pairs actually contain
// a quadratic point. With rank J(F)=0 the Coleman integral int_{D0}^{D} omega
// vanishes for every F-rational degree-2 divisor D (its class is torsion), so a
// quadratic point sits in a disc-pair iff the integral to the disc CENTRE
//   I_k = int_{D0}^{Q_a + Q_b} omega_k          (D0 = R1 + R2 a fixed base divisor)
// reduces to 0 mod P (then a tiny in-disc Newton correction lands an actual point;
// if I_k is a unit the disc-pair is empty). We compute I_k via coleman_integrals_on_basis
//   I = ( int_{R1}^{Q_a} + int_{R1}^{Q_b} - int_{R1}^{R2} )   (holomorphic part, first g)
// caching the R1-side across discs. Returns the list of candidate disc-pairs (those
// with I == 0 mod P) for the subsequent Newton recovery.
// R1, R2: point records of two F-rational GOOD points with distinct x (D0 not the
// hyperelliptic class). data threaded for the minpoly cache.
// ---------------------------------------------------------------------------
recovery_candidates_rank0 := function(data, res, R1, R2 : verbose:=true)

  g := data`g; K := data`K; OK := RingOfIntegers(K);
  Fq, red := ResidueClassField(OK);
  good := res`good;

  // base integral c = int_{R1}^{R2} (holomorphic part)
  cfull := coleman_integrals_on_basis(R1, R2, data : verbose:=false);
  c := [ cfull[k] : k in [1..g] ];

  // J_i = int_{R1}^{Q_i} for each good disc centre, caching the R1-side
  J := [* *]; side1 := 0;
  for i := 1 to #good do
    Ji, Ni, side1 := coleman_integrals_on_basis(R1, good[i], data : side1:=side1, return_side:=true, verbose:=false);
    Append(~J, [ Ji[k] : k in [1..g] ]);
  end for;

  candidates := [];
  for t in res`certified do
    kind := t[1]; a := t[2]; b := t[3];
    if kind eq "split" then
      I := [ J[a][k] + J[b][k] - c[k] : k in [1..g] ];
    else // diagonal: D ~ 2*(point near Q_a)
      I := [ 2*J[a][k] - c[k] : k in [1..g] ];
    end if;
    if &and[ red(OK!I[k]) eq 0 : k in [1..g] ] then
      Append(~candidates, <kind, a, b, [I[k] : k in [1..g]]>);
    end if;
  end for;

  if verbose then
    printf "recovery_candidates_rank0: %o of %o certified split/diagonal disc-pairs are candidates (Coleman integral to centre == 0 mod P).\n",
       #candidates, #res`certified;
  end if;
  return candidates, J, c;
end function;


// ---------------------------------------------------------------------------
// The recovery of a point in a DIAGONAL disc-pair: both points of the degree-2 divisor lie in
// the residue disc of one centre, with disc parameters t1, t2. The function
//   F_k(t1,t2) = I[k] + (s[k](t1) - s[k](0)) + (s[k](t2) - s[k](0)),   k = 1, 2,
// is symmetric, so its Jacobian in (t1,t2) is singular on the diagonal t1 = t2, where Newton's
// method in (t1,t2) starts. With s[k](t) - s[k](0) = sum_{j>=1} a_kj*t^j it is a function of
// sigma1 = t1 + t2 and sigma2 = t1*t2: F_k = I[k] + sum_j a_kj*p_j(sigma1,sigma2) for the power
// sums p_j = t1^j + t2^j (p_0 = 2, p_1 = sigma1, p_j = sigma1*p_(j-1) - sigma2*p_(j-2)), and its
// Jacobian in (sigma1,sigma2) at (0,0) is [[a_k1, -2*a_k2]] = [[c_k0, -c_k1]] (c_kl the Taylor
// coefficients of omega_k/dt): the matrix of Siksek's criterion for a diagonal disc-pair, so
// for a certified one Newton's method in (sigma1,sigma2) converges to the unique zero. The
// x-coordinates are symmetric as well: x1 + x2 = sum_j x_j*p_j and x1*x2 =
// ((x1+x2)^2 - (x1^2+x2^2))/2 with x1^2 + x2^2 = sum_j y_j*p_j, for x(t) = sum_j x_j*t^j and
// x(t)^2 = sum_j y_j*t^j; t1, t2 themselves are not needed.
// ---------------------------------------------------------------------------
power_sums := function(sigma1, sigma2, n)
  // [p_0..p_n] and their derivatives by sigma1 and sigma2 (index j+1 for p_j)
  R := Parent(sigma1);
  p := [R!2, sigma1]; d1 := [R!0, R!1]; d2 := [R!0, R!0];
  for j := 2 to n do
    Append(~p, sigma1*p[j] - sigma2*p[j-1]);
    Append(~d1, p[j] + sigma1*d1[j] - sigma2*d1[j-1]);
    Append(~d2, sigma1*d2[j] - p[j-1] - sigma2*d2[j-1]);
  end for;
  return p, d1, d2;
end function;

series_coefficients := function(f, n)
  // the coefficients of t^0, ..., t^n of the power series f (0 beyond the known ones)
  C, v := Coefficients(f);
  return [ (j ge v and j-v+1 le #C) select C[j-v+1] else 0 : j in [0..n] ];
end function;

diagonal_jacobian_invertible := function(s, K)
  // whether the Jacobian of the diagonal Newton step at (0,0), [[a_k1, -2*a_k2]]_(k=1,2), is
  // invertible modulo P: the diagonal disc-pair is certified by its first two differentials
  OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  ds := [ Derivative(s[k]) : k in [1..2] ];
  J0 := Matrix(Fq,2,2,[ red(OK!Coefficient(ds[1],0)), red(OK!(-Coefficient(ds[1],1))),
                        red(OK!Coefficient(ds[2],0)), red(OK!(-Coefficient(ds[2],1))) ]);
  return Rank(J0) eq 2;
end function;

newton_symmetric := function(I, s, K : maxit := 40)
  // the zero (sigma1, sigma2) of F_k = I[k] + sum_j a_kj*p_j(sigma1,sigma2), k = 1, 2, by
  // Newton's method from (0,0) (only the first two entries of I and s are used)
  n := Minimum([ AbsolutePrecision(s[k]) : k in [1..2] ]) - 1;
  a := [ series_coefficients(s[k], n) : k in [1..2] ];
  sig1 := K!0; sig2 := K!0;
  for it := 1 to maxit do
    p, d1, d2 := power_sums(sig1, sig2, n);
    Fv := [ I[k] + &+[ a[k][j+1]*p[j+1] : j in [1..n] ] : k in [1..2] ];
    Jac := Matrix(K,2,2,[ &+[ a[1][j+1]*d1[j+1] : j in [1..n] ], &+[ a[1][j+1]*d2[j+1] : j in [1..n] ],
                          &+[ a[2][j+1]*d1[j+1] : j in [1..n] ], &+[ a[2][j+1]*d2[j+1] : j in [1..n] ] ]);
    if IsWeaklyZero(Determinant(Jac)) or Valuation(Determinant(Jac)) ge Precision(K) then break; end if; // (an inexact zero can have a smaller precision)
    u := Jac^(-1)*Matrix(K,2,1,Fv);
    sig1 -:= u[1][1]; sig2 -:= u[2][1];
    if Minimum([ Valuation(Fv[1]), Valuation(Fv[2]) ]) ge Precision(K)-2 then break; end if;
  end for;
  return sig1, sig2;
end function;

symmetric_x := function(xt, sig1, sig2)
  // x1 + x2 and x1*x2 for the points with disc parameters t1, t2, t1 + t2 = sig1, t1*t2 = sig2,
  // from the expansion xt of x at the centre
  n := AbsolutePrecision(xt) - 1;
  p := power_sums(sig1, sig2, n);
  xs := series_coefficients(xt, n); ys := series_coefficients(xt^2, n);
  e1 := &+[ xs[j+1]*p[j+1] : j in [0..n] ];
  return e1, (e1^2 - &+[ ys[j+1]*p[j+1] : j in [0..n] ])/2;
end function;


// ---------------------------------------------------------------------------
// The Newton step of the recovery of a point in a split disc-pair. For the pair (t1,t2) of
// disc parameters and the V-projected tiny-integral series sA, sB of the two discs (two
// forms each), the zero of
//   F_k(t1,t2) = I[k] + (sA[k](t1) - sA[k](0)) + (sB[k](t2) - sB[k](0)),   k = 1, 2,
// is found by Newton's method from (0,0) (only the first two entries of I, sA, sB are used);
// it stops when F vanishes to the precision of K,
// when the Jacobian has lost its precision, or after maxit steps.
// newton_jacobian_invertible: whether the Jacobian at (0,0) is invertible modulo P (the
// leading 2x2 matrix of the criterion has rank 2), so that the zero is unique.
// ---------------------------------------------------------------------------
newton_jacobian_invertible := function(sA, sB, K)
  OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  dA := [ Derivative(sA[k]) : k in [1..2] ]; dB := [ Derivative(sB[k]) : k in [1..2] ];
  Jac0 := Matrix(Fq,2,2,[ red(OK!Coefficient(dA[1],0)), red(OK!Coefficient(dB[1],0)),
                          red(OK!Coefficient(dA[2],0)), red(OK!Coefficient(dB[2],0)) ]);
  return Rank(Jac0) eq 2;
end function;

newton_pair := function(I, sA, sB, K : maxit := 40)
  // The zero (t1, t2) of the system F_k above, by Newton's method from (0,0).
  cA := [ Coefficient(sA[k],0) : k in [1..2] ]; cB := [ Coefficient(sB[k],0) : k in [1..2] ];
  dA := [ Derivative(sA[k]) : k in [1..2] ]; dB := [ Derivative(sB[k]) : k in [1..2] ];
  t1 := K!0; t2 := K!0;
  for it := 1 to maxit do
    Fv := [ I[k] + (Evaluate(sA[k],t1)-cA[k]) + (Evaluate(sB[k],t2)-cB[k]) : k in [1..2] ];
    Jac := Matrix(K,2,2,[Evaluate(dA[1],t1),Evaluate(dB[1],t2), Evaluate(dA[2],t1),Evaluate(dB[2],t2)]);
    if IsWeaklyZero(Determinant(Jac)) or Valuation(Determinant(Jac)) ge Precision(K) then break; end if; // (an inexact zero can have a smaller precision)
    u := Jac^(-1)*Matrix(K,2,1,[Fv[1],Fv[2]]);
    t1 -:= u[1][1]; t2 -:= u[2][1];
    if Minimum([Valuation(Fv[1]),Valuation(Fv[2])]) ge Precision(K)-2 then break; end if;
  end for;
  return t1, t2;
end function;

// Whether every irreducible factor of the x-polynomial mp over L belongs to points of the
// curve: Q(x,Y) has a root Y over L[X]/(factor) (spurious LLL matches fail this).
on_curve_degree2 := function(mp, data)
  Lpol := Parent(mp); d := Degree(data`Q);
  for fc in Factorisation(mp) do
    if Degree(fc[1]) eq 1 then
      xr := -Coefficient(fc[1],0)/Coefficient(fc[1],1);
      if #Roots(Lpol![ Evaluate(Coefficient(data`Q,i),xr) : i in [0..d] ]) eq 0 then return false; end if;
    else
      A2<xb> := quo< Lpol | fc[1] >;
      if #Roots(PolynomialRing(A2)![ Evaluate(Coefficient(data`Q,i),xb) : i in [0..d] ]) eq 0 then return false; end if;
    end if;
  end for;
  return true;
end function;

// ---------------------------------------------------------------------------
// V-aware split/diagonal recovery for ANY genus / rank (V = annihilating diffs).
// candidate disc-pairs = those whose V-projected Coleman integral to the disc
// centre, I_V[k] = sum_j V[k]_j * ( int_{R1}^{Qa} + int_{R1}^{Qb} - int_{R1}^{R2} )_j,
// reduces to 0 mod P (necessary for a quadratic point to reduce there).
// Returns candidates as <kind,a,b,I_V> and the cached side integrals.
// ---------------------------------------------------------------------------
recovery_candidates_V := function(data, good, V, R1, R2 : verbose:=true)
  g := data`g; K := data`K; OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  cfull := coleman_integrals_on_basis(R1, R2, data : verbose:=false);
  c := [ cfull[k] : k in [1..g] ];
  J := [* *]; side1 := 0;
  for i := 1 to #good do
    Ji, Ni, side1 := coleman_integrals_on_basis(R1, good[i], data : side1:=side1, return_side:=true, verbose:=false);
    Append(~J, [ Ji[k] : k in [1..g] ]);
  end for;
  projV := function(Ihol)   // -> [I_V[1..#V]]; ALL of V is tested mod P (recover_point_V uses the first 2)
    return [ &+[ K!V[kk][j] * Ihol[j] : j in [1..g] ] : kk in [1..#V] ];
  end function;
  cand := [* *];
  for a := 1 to #good do
    for b := a to #good do
      Ihol := [ J[a][j] + J[b][j] - c[j] : j in [1..g] ];
      if a eq b then Ihol := [ 2*J[a][j] - c[j] : j in [1..g] ]; end if;
      IV := projV(Ihol);
      if &and[ red(OK!IV[k]) eq 0 : k in [1..#V] ] then
        Append(~cand, < (a eq b) select "diagonal" else "split", a, b, IV >);
      end if;
    end for;
  end for;
  if verbose then printf "recovery_candidates_V: %o split/diagonal candidate disc-pair(s).\n", #cand; end if;
  return cand, J, c;
end function;


// ---------------------------------------------------------------------------
// Newton-recover the quadratic point in a candidate disc-pair (V-projected,
// any genus). Returns <found, mp, kind>: mp = minpoly of x over F; kind in
// {"quadratic","rational-pair"}; found=false if unrecognized or not on the curve.
// Verifies on the (general plane) curve: the recovered x satisfies a degree-2 mp
// over F and Q(x,Y) has a y in F[X]/(mp) matching (point is F-rational of degree 2).
// ---------------------------------------------------------------------------
recover_point_V := function(pairdata, good, V, data : prec:=0, maxit:=40, htbound:=10^5)
  K := data`K; g := data`g; L := data`L;
  Lpol<XX> := PolynomialRing(L);
  kind := pairdata[1]; a := pairdata[2]; b := pairdata[3]; IV := pairdata[4];

  serA, xtA, btA := tiny_integrals_on_basis_to_z(good[a], data : prec:=prec);
  if kind eq "split" then serB, xtB, btB := tiny_integrals_on_basis_to_z(good[b], data : prec:=prec);
  else serB := serA; xtB := xtA; btB := btA; end if;
  // V-projected tiny series (k=1,2)
  sA := [ &+[ K!V[k][j]*serA[j] : j in [1..g] ] : k in [1..2] ];
  sB := [ &+[ K!V[k][j]*serB[j] : j in [1..g] ] : k in [1..2] ];

  // certified disc-pairs (leading 2x2 V-matrix rank 2) give an invertible Newton Jacobian;
  // rank-drop disc-pairs need the higher-order criterion -- skip. A diagonal disc-pair is
  // solved in the symmetric functions sigma1 = t1+t2, sigma2 = t1*t2 (newton_symmetric).
  if kind eq "diagonal" then
    if not diagonal_jacobian_invertible(sA, K) then return false, Lpol!0, "rank-drop"; end if;
    sig1, sig2 := newton_symmetric(IV, sA, K : maxit:=maxit);
    xsum, xprod := symmetric_x(xtA, sig1, sig2);
  else
    if not newton_jacobian_invertible(sA, sB, K) then return false, Lpol!0, "rank-drop"; end if;
    t1, t2 := newton_pair(IV, sA, sB, K : maxit:=maxit);
    x1 := Evaluate(xtA, t1); x2 := Evaluate(xtB, t2);
    xsum := x1+x2; xprod := x1*x2;
  end if;
  ok1, e1 := recognize_in_F(xsum, data : htbound:=htbound);
  ok2, e2 := recognize_in_F(xprod, data : htbound:=htbound);
  if not (ok1 and ok2) then return false, Lpol!0, "unrecognized"; end if;
  mp := XX^2 - e1*XX + e2;
  // verify a degree-2 F-rational point with this x lies on Q(x,Y)=0
  if not on_curve_degree2(mp, data) then return false, mp, "spurious"; end if;
  fac := Factorisation(mp);
  knd := (#fac eq 1 and fac[1][2] eq 1) select "quadratic" else "rational-pair";
  return true, mp, knd;
end function;


// ---------------------------------------------------------------------------
// Newton-solve one certified disc-pair for the (unique) quadratic point in it and
// recognize it globally. With rank J(F)=0 every certified disc-pair has a p-adic
// solution, so the genuine F-quadratic points are exactly those whose symmetric
// functions x1+x2, x1*x2 are recognized in F (small height). Returns
//   <found, minpoly, kind>  where found is a boolean, minpoly = X^2-(x1+x2)X+x1x2
//   over F (the field of definition of x), and kind in {"rational-pair","quadratic"}.
// pairdata: <kind, a, b, I> from recovery_candidates_rank0; good = res`good.
// (Part of the g=2/rank-0 pipeline; general-V counterparts: recover_point_V /
// quadratic_points_split. See the pipeline note at quadratic_points_genus2_rank0.)
// ---------------------------------------------------------------------------
recover_point_in_pair := function(pairdata, good, data, fpoly : prec := 0, maxit := 40, htbound := 10^5)
  K := data`K; L := data`L;
  Fpol<X> := PolynomialRing(L);
  kind := pairdata[1]; a := pairdata[2]; b := pairdata[3]; I := pairdata[4];

  // tiny-integral series s_i^k(t) = int_{Q_i}^{P(t)} omega_k and the x-expansion xt_i
  serA, xtA := tiny_integrals_on_basis_to_z(good[a], data : prec:=prec);
  if kind eq "split" then
    serB, xtB := tiny_integrals_on_basis_to_z(good[b], data : prec:=prec);
  else
    serB := serA; xtB := xtA;  // diagonal: both points in the same disc
  end if;
  // multivariate Newton on F_k(t1,t2) = I_k + (serA_k(t1)-serA_k(0)) + (serB_k(t2)-serB_k(0)),
  // k = 1, 2 (the first two forms); for a diagonal pair in the symmetric functions of (t1,t2)
  if kind eq "split" then
    t1, t2 := newton_pair(I, serA, serB, K : maxit:=maxit);
    x1 := Evaluate(xtA, t1);
    x2 := Evaluate(xtB, t2);
    xsum := x1+x2; xprod := x1*x2;
  else
    sig1, sig2 := newton_symmetric(I, serA, K : maxit:=maxit);
    xsum, xprod := symmetric_x(xtA, sig1, sig2);
  end if;
  ok1, e1 := recognize_in_F(xsum, data : htbound:=htbound);
  ok2, e2 := recognize_in_F(xprod, data : htbound:=htbound);
  if not (ok1 and ok2) then
    return false, Fpol!0, "unrecognized";
  end if;
  mp := X^2 - e1*X + e2;

  // RIGOROUS verification: a recovered x is a real point iff f(x) is a square in
  // the F-algebra F[X]/(mp) (spurious LLL matches fail this). Handles mp reducible
  // (rational pair: check each root in F) and irreducible (the quadratic field).
  fac := Factorisation(mp);
  is_point := true;
  for fc in fac do
    if Degree(fc[1]) eq 1 then
      r := -Coefficient(fc[1],0)/Coefficient(fc[1],1);   // root in F
      if not IsSquare(Evaluate(fpoly, r)) then is_point := false; end if;
    else
      A<xx> := quo< Fpol | fc[1] >;                       // quadratic field F(x)
      if not IsSquare(Evaluate(fpoly, xx)) then is_point := false; end if;
    end if;
  end for;
  if not is_point then
    return false, mp, "spurious";
  end if;

  knd := (#fac eq 1 and fac[1][2] eq 1) select "quadratic" else "rational-pair";
  return true, mp, knd;
end function;


// ---------------------------------------------------------------------------
// Helpers of quadratic_points_split.
// ---------------------------------------------------------------------------

centre_integrals := function(R1, pts, data, verbose, label, t0)
  // The integrals of the holomorphic basis forms omega_1..omega_g from R1 to each point of
  // pts (the centres of the residue discs), sharing the part of the computation that
  // depends on R1 (side1 of coleman_integrals_on_basis). With verbose, the progress is
  // printed every 25 points ("centre integrals<label> i/n", the time since t0).
  g := data`g; J := [* *]; side1 := 0;
  for i := 1 to #pts do
    Ji,_,side1 := coleman_integrals_on_basis(R1, pts[i], data : side1:=side1, return_side:=true, verbose:=false);
    Append(~J, [ Ji[k] : k in [1..g] ]);
    if verbose and (i mod 25 eq 0 or i eq #pts) then
      printf "  centre integrals%o %o/%o (%o s)\n", label, i, #pts, Cputime(t0);
    end if;
  end for;
  return J;
end function;

match_discs := function(good, data, goodF, datafilter, JF)
  // The integrals JF at the discs goodF of a low-precision datafilter, reordered to match
  // the discs good of data by their reductions, and whether the matching succeeded (if
  // not, the entries are placeholders).
  K := data`K; OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  KF := datafilter`K; OKF := RingOfIntegers(KF); FqF, redF := ResidueClassField(OKF);
  posF := AssociativeArray();
  for i := 1 to #goodF do
    posF[<redF(OKF!goodF[i]`x), [ redF(OKF!bb) : bb in goodF[i]`b ]>] := i;
  end for;
  Jlow := [* *]; okmatch := true;
  // Match the two disc lists by their reductions.  Two hazards:
  //  * a direct p-adic coercion KF!(K!z) between two precisions is illegal in Magma;
  //  * Fq = ResidueClassField(OK) and FqF = ResidueClassField(OKF) are two independent
  //    constructions of F_(p^f) when K and KF are built as completions, so a coercion
  //    between them may be undefined -- and even when Magma supplies one, it is only
  //    determined up to a power of Frobenius, which would silently pair each disc with
  //    a Frobenius conjugate.  We therefore try the reduction, and on ANY failure fall
  //    back to the single-precision path rather than risk a wrong identification.
  for i := 1 to #good do
    okk := true; ky := <FqF!0, [ FqF | ]>;
    try
      ky := <FqF!red(OK!(K!good[i]`x)), [ FqF!red(OK!(K!bb)) : bb in good[i]`b ]>;
    catch e
      okk := false;
    end try;
    if okk and IsDefined(posF, ky) then Append(~Jlow, JF[posF[ky]]);
    else okmatch := false; Append(~Jlow, JF[1]); end if;
  end for;
  return Jlow, okmatch;
end function;

disc_frobenius := function(good, data, verbose)
  // The action of the p-power Frobenius on the residue discs good, by their reductions:
  // frob[i] the index of the image of the disc i (0 if it is not among good), and whether
  // all images were found.
  K := data`K; OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  pp := data`p;
  dkey  := func< Pt | <red(OK!Pt`x), [ red(OK!bb) : bb in Pt`b ]> >;
  dkeyF := func< Pt | <red(OK!Pt`x)^pp, [ red(OK!bb)^pp : bb in Pt`b ]> >;
  pos := AssociativeArray();
  for i := 1 to #good do pos[dkey(good[i])] := i; end for;
  frob := []; frobok := true;
  for i := 1 to #good do
    k := dkeyF(good[i]);
    if IsDefined(pos, k) then frob[i] := pos[k]; else frob[i] := 0; frobok := false; end if;
  end for;
  if verbose then
    printf "quadratic_points_split: Frobenius on discs matched: %o", frobok;
    if frobok then printf " (%o fixed, %o in 2-cycles)",
       #[ i : i in [1..#good] | frob[i] eq i ], #[ i : i in [1..#good] | frob[i] ne i ]; end if;
    printf "\n";
  end if;
  return frob, frobok;
end function;

tiny_series_V := function(good, V, data, verbose)
  // For each disc of good: the tiny integrals of the first two differentials of V (in the
  // holomorphic basis) as series in the local parameter (tiny_integrals_on_basis_to_z), and
  // the expansion of x.
  K := data`K; g := data`g;
  serV := [* *]; xts := [* *]; t0 := Cputime();
  for i := 1 to #good do
    if verbose and (i mod 25 eq 0 or i eq #good) then
      printf "  tiny series %o/%o (%o s)\n", i, #good, Cputime(t0);
    end if;
    ser, xt := tiny_integrals_on_basis_to_z(good[i], data);
    Append(~serV, [ &+[ K!V[k][j]*ser[j] : j in [1..g] ] : k in [1..2] ]);
    Append(~xts, xt);
  end for;
  return serV, xts;
end function;


// ---------------------------------------------------------------------------
// Driver: genuine quadratic points in the certified SPLIT disc-pairs (any genus /
// rank <= g-2). V = annihilating differentials; D0 = R1 + R2 a fixed rational
// degree-2 base divisor. Precomputes the per-disc tiny series (V-projected) once.
// Returns the set of x-minpolys over L of the genuine quadratic points found.
// Frobenius-conjugate ("inert") disc-pairs are covered by running this SAME
// driver over K = F_r^{unr,2}, the unramified quadratic extension of the
// completion: over K a conjugate disc-pair IS a split disc-pair, and the loop
// below then sweeps the F_r-split and the F_r-conjugate disc-pairs together.
// That requires Coleman integration with f_K = 2, i.e. the algorithm of the
// article; with Coleman integration over Q_p only, one has to run several split
// primes and hope that every quadratic point splits at one of them -- which
// enumerates but does not prove completeness. In that mode pass
//   basis := [ L | b : b in Basis(MaximalOrder(F)) ]
// so that the LLL recognition targets O_F (rank 2 lattice + f_K residue columns)
// instead of the larger O_L: the symmetric functions x1+x2, x1*x2 of an
// F-rational degree-2 divisor are Galois-fixed, hence already lie in F.
// NOTE: diagonal/rank-drop disc-pairs are still not covered here.
// ---------------------------------------------------------------------------
quadratic_points_split := function(data, V, R1, R2 : verbose:=true, basis:=[], htbound:=10^5,
                                    datafilter:=0, reachable:=0, include_bad:=false)
  g := data`g; K := data`K; OK := RingOfIntegers(K); Fq, red := ResidueClassField(OK);
  L := data`L; Lpol<XX> := PolynomialRing(L);
  Qqpts, data := Qq_points(data);
  // the residue discs: the good ones, and with include_bad also the finite bad ones (their
  // centre is the very bad point, where the local parameter of local_coord is integral, so
  // the disc parameters lie in pi*O_K as for the good discs; the integrals to the centre use
  // the auxiliary extension K(pi^(1/e)) and are less precise)
  good := [ Qqpts[i] : i in [1..#Qqpts] | not is_bad(Qqpts[i],data) or (include_bad and not Qqpts[i]`inf) ];
  cfull := coleman_integrals_on_basis(R1, R2, data : verbose:=false); cc := [ cfull[k] : k in [1..g] ];
  if verbose then printf "quadratic_points_split: %o %o residue discs over F_%o.\n", #good, include_bad select "good and finite bad" else "good", #Fq; end if;

  // ---- TWO-PHASE PRECISION (optional) --------------------------------------
  // The candidate filter below only reads the centre integrals MOD P, while the
  // Newton solve and the LLL recognition need them to full precision N. Passing a
  // low-precision `datafilter` (a coleman_data for the same curve and prime with a
  // small N) computes all #good centre integrals cheaply for the filter, and the
  // full-precision integrals are then computed on demand, memoised, only for the
  // discs occurring in a surviving pair. The residue discs of the two data objects
  // are matched by their reduction, so the low-N run may list them in any order.
  twophase := (Type(datafilter) ne RngIntElt);
  J := [* *]; t0 := Cputime();
  if twophase then
    goodF := [ Pt : Pt in Qq_points(datafilter) | not is_bad(Pt,datafilter) or (include_bad and not Pt`inf) ];
    ccF := coleman_integrals_on_basis(R1, R2, datafilter : verbose:=false);
    JF := centre_integrals(R1, goodF, datafilter, verbose, " (filter precision)", t0);
    Jlow, okmatch := match_discs(good, data, goodF, datafilter, JF); // reorder the low-precision integrals to match `good`
    if not okmatch then
      if verbose then print "  two-phase: disc matching failed, falling back to single precision"; end if;
      twophase := false;
    end if;
  end if;
  if not twophase then
    J := centre_integrals(R1, good, data, verbose, "", t0);
  end if;
  // ---- Frobenius action on the residue discs -------------------------------
  // An F-rational degree-2 divisor reduces to a degree-2 divisor over the residue
  // field of F_r, so the PAIR of K-discs carrying it must be stable under
  // Gal(k/k_0) = <x :-> x^p>. Restricting to Frobenius-stable pairs is therefore
  // no loss, and it cuts the pair loop from ~#good^2/2 to ~#good. When f_K = 1
  // every disc is k_0-rational and this is a no-op. If the reductions cannot be
  // matched up (a model whose W0 is not defined over the base), all pairs are used.
  frob, frobok := disc_frobenius(good, data, verbose);

  // ---- hoist the candidate filter out of the pair loop ----------------------
  // IV[k] = sum_j V[k][j]*(J[a][j] + J[b][j] - cc[j]) = u[a][k] + u[b][k] - c[k],
  // so the g multiplications per pair become one addition. When all the pieces are
  // integral we reduce them ONCE per disc and run the whole filter in the residue
  // field, which removes the per-pair OK!-coercion (the actual bottleneck).
  if twophase then
    KF := datafilter`K; OKF := RingOfIntegers(KF); FqF, redF := ResidueClassField(OKF);
    uK := [ [ &+[ KF!V[k][j]*Jlow[i][j] : j in [1..g] ] : k in [1..#V] ] : i in [1..#good] ];
    cK := [ &+[ KF!V[k][j]*ccF[j] : j in [1..g] ] : k in [1..#V] ];
    OKf := OKF; redf := redF;
  else
    uK := [ [ &+[ K!V[k][j]*J[i][j] : j in [1..g] ] : k in [1..#V] ] : i in [1..#good] ];
    cK := [ &+[ K!V[k][j]*cc[j] : j in [1..g] ] : k in [1..#V] ];
    OKf := OK; redf := red;
  end if;
  fastfilter := &and[ Valuation(uK[i][k]) ge 0 : k in [1..#V], i in [1..#good] ]
            and &and[ Valuation(cK[k]) ge 0 : k in [1..#V] ];
  if fastfilter then
    ubar := [ [ redf(OKf!uK[i][k]) : k in [1..#V] ] : i in [1..#good] ];
    cbar := [ redf(OKf!cK[k]) : k in [1..#V] ];
  end if;
  if verbose then printf "quadratic_points_split: residue-field filter: %o\n", fastfilter; end if;

  serV, xts := tiny_series_V(good, V, data, verbose);
  quads := {}; nrat := 0; nspur := 0; nunrec := 0; ndrop := 0;
  // irreducibility over the base field F of the divisors: F = L, or the subfield of L spanned
  // by basis (the auxiliary-field mode)
  if #basis gt 0 then
    Fsub, embF := sub< L | [ L!b : b in basis ] >;
    irreducible_over_F := func< mp | IsIrreducible(PolynomialRing(Fsub)![ c @@ embF : c in Coefficients(mp) ]) >;
  else
    irreducible_over_F := func< mp | IsIrreducible(mp) >;
  end if;
  // ---- on-demand full-precision centre integrals (two-phase mode) -----------
  Jfull := AssociativeArray(); sideH := 0;
  getJ := function(i, sd)
    if IsDefined(Jfull, i) then return Jfull[i], sd; end if;
    Ji,_,sd2 := coleman_integrals_on_basis(R1, good[i], data : side1:=sd, return_side:=true, verbose:=false);
    v := [ Ji[k] : k in [1..g] ];
    return v, sd2;
  end function;

  npair := 0; nreach := 0;
  for a := 1 to #good do for b := a+1 to #good do
    // only Frobenius-stable pairs can carry an F-rational degree-2 divisor
    if frobok and not ((frob[a] eq a and frob[b] eq b) or (frob[a] eq b and frob[b] eq a)) then
      continue;
    end if;
    // OPTIONAL caller-supplied reachability test (a Mordell-Weil sieve condition:
    // [Qa + Qb - D0] must lie in red_P(J(F))). This is a free finite-field filter,
    // but note that it RE-INTRODUCES the dependence on generators of J(F) that the
    // f_K > 1 method is meant to remove, so it is off by default and should not be
    // used when the point of the computation is to avoid Mordell-Weil input.
    if Type(reachable) ne RngIntElt then
      if not reachable(a,b) then nreach +:= 1; continue; end if;
    end if;
    npair +:= 1;
    // candidate filter: the V-projected centre integral must vanish mod P for ALL of V
    // (the Newton system below then uses the first two, guarded by the Jac0 rank check)
    if fastfilter then
      if not &and[ ubar[a][k] + ubar[b][k] - cbar[k] eq 0 : k in [1..#V] ] then continue; end if;
      IV := [ uK[a][k] + uK[b][k] - cK[k] : k in [1..#V] ];
    else
      IV := [ uK[a][k] + uK[b][k] - cK[k] : k in [1..#V] ];
      if not &and[ redf(OKf!IV[k]) eq 0 : k in [1..#V] ] then continue; end if;
    end if;
    if twophase then // the pair survived: now compute IV to full precision
      Ja, sideH := getJ(a, sideH); Jfull[a] := Ja;
      Jb, sideH := getJ(b, sideH); Jfull[b] := Jb;
      IV := [ &+[ K!V[k][j]*(Ja[j]+Jb[j]-cc[j]) : j in [1..g] ] : k in [1..#V] ];
    end if;
    sA := serV[a]; sB := serV[b];
    if not newton_jacobian_invertible(sA, sB, K) then ndrop +:= 1; continue; end if;
    t1, t2 := newton_pair(IV, sA, sB, K);
    x1 := Evaluate(xts[a],t1); x2 := Evaluate(xts[b],t2);
    ok1,e1 := recognize_in_F(x1+x2,data : basis:=basis, htbound:=htbound);
    ok2,e2 := recognize_in_F(x1*x2,data : basis:=basis, htbound:=htbound);
    if not (ok1 and ok2) then nunrec +:= 1; continue; end if;
    mp := XX^2 - e1*XX + e2;
    if not on_curve_degree2(mp, data) then nspur +:= 1; continue; end if;
    // Rational-pair test.  IsIrreducible here is irreducibility over the AUXILIARY
    // field L (used only to realise K), not over the base field F, and the two differ
    // exactly when F(D) = L -- i.e. when the auxiliary u is, up to squares, the
    // discriminant of the point being sought.  A Frobenius-conjugate disc-pair can
    // never carry a sum of two F-rational points (an F-rational x reduces into the
    // residue field of F_r, whereas the two discs have conjugate reductions in
    // F_(q^2) \ F_q), so for such a pair mp is irreducible over F whatever it does
    // over L.  Rejecting on IsIrreducible there would silently discard a genuine
    // quadratic point, e.g. X^2 - 23/7 X + 47/28 on X(s3,ns5) at q = 19 with u = 2,
    // which has F(D) = F(sqrt 2).
    conjpair := frobok and (frob[a] eq b);
    if conjpair or irreducible_over_F(mp) then Include(~quads, mp); else nrat +:= 1; end if;
  end for; end for;

  // ---- diagonal disc-pairs: both points of the divisor in the disc a ----------
  // (a Frobenius-stable disc); Newton's method in the symmetric functions of the two disc
  // parameters (newton_symmetric), since the Jacobian in (t1,t2) is singular on the
  // diagonal. The two points can be conjugate over the unramified quadratic extension, with
  // reductions in the same F_q-rational disc, so the rational-pair test is irreducibility
  // over F (not over the auxiliary field L).
  ndiag := 0;
  for a := 1 to #good do
    if frobok and frob[a] ne a then continue; end if;
    if Type(reachable) ne RngIntElt then
      if not reachable(a,a) then nreach +:= 1; continue; end if;
    end if;
    ndiag +:= 1;
    IV := [ 2*uK[a][k] - cK[k] : k in [1..#V] ];
    if fastfilter then
      if not &and[ 2*ubar[a][k] - cbar[k] eq 0 : k in [1..#V] ] then continue; end if;
    else
      if not &and[ redf(OKf!IV[k]) eq 0 : k in [1..#V] ] then continue; end if;
    end if;
    if twophase then // the disc survived: now compute IV to full precision
      Ja, sideH := getJ(a, sideH); Jfull[a] := Ja;
      IV := [ &+[ K!V[k][j]*(2*Ja[j]-cc[j]) : j in [1..g] ] : k in [1..#V] ];
    end if;
    sA := serV[a];
    if not diagonal_jacobian_invertible(sA, K) then ndrop +:= 1; continue; end if;
    sig1, sig2 := newton_symmetric(IV, sA, K);
    xsum, xprod := symmetric_x(xts[a], sig1, sig2);
    ok1,e1 := recognize_in_F(xsum,data : basis:=basis, htbound:=htbound);
    ok2,e2 := recognize_in_F(xprod,data : basis:=basis, htbound:=htbound);
    if not (ok1 and ok2) then nunrec +:= 1; continue; end if;
    mp := XX^2 - e1*XX + e2;
    if not on_curve_degree2(mp, data) then nspur +:= 1; continue; end if;
    if irreducible_over_F(mp) then Include(~quads, mp); else nrat +:= 1; end if;
  end for;
  if verbose then
    printf "quadratic_points_split: %o pairs examined (of %o; Frobenius-stability and, if supplied, reachability removed the rest -- %o by reachability).\n",
       npair, (#good*(#good-1)) div 2, nreach;
    printf "quadratic_points_split: %o diagonal disc-pairs examined.\n", ndiag;
    printf "quadratic_points_split: %o genuine quadratic, %o rational-pair, %o spurious, %o unrec, %o rank-drop.\n",
       #quads, nrat, nspur, nunrec, ndrop;
  end if;
  return quads, good, data;
end function;
