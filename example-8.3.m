load "isrational.m";
load "auxpolys.m";
load "cohobasis.m";
load "frobenius.m";
load "reduction.m";
load "coercion.m";
load "expansion.m";
load "integrals.m";


SetLogFile("example-8.3.log" : Overwrite);

// Example 8.3 of the article: superelliptic genus-3 curve y^4-x(x-1)(x-cbrt(2))
// over L=Q(cbrt(2)), at the ramified prime P=(3,1+cbrt(2)) (3=P^3, L_P/Q_3 totally
// ramified of degree 3).

Qx:=PolynomialRing(Rationals());
h:=Qx.1^3-2;
L<a>:=NumberField(h);
Lx<x>:=PolynomialRing(L);
Lxy<y>:=PolynomialRing(Lx);
OL:=MaximalOrder(L);
D:=Decomposition(OL,3);
P:=D[1][1];
N:=20;

print "";
print "//////////////////////////";
print "// Example 8.3: superelliptic genus-3 curve over Q(cbrt(2)), P|3 ramified //";
print "//////////////////////////\n";
Q:=y^4-x*(x-1)*(x-a); 
data:=coleman_data(Q,L,P,N);
print "";
print "//////////////////////////";
print "// 8.1. W0, Winf, r //";
print "//////////////////////////\n";
data`W0;
data`Winf;
r:=data`r;
r;

print "";
print "//////////////////////////";
print "// 8.2. basis, first half is in H^1(X) //";
print "//////////////////////////\n";

data`basis;

print "";
print "//////////////////////////";
print "// 8.3. r(P) //";
print "//////////////////////////\n";
r:=data`r;
P1:=set_bad_point(0,[1,0,0,0],false,data);
P1;
P2:=set_bad_point(1,[1,0,0,0],false,data);
P2;
P3:=set_bad_point(a,[1,0,0,0],false,data);
P4:=set_bad_point(0,[1,0,0,0],true,data);
print "";
print "//////////////////////////";
print "// 8.4. integration //";
print "//////////////////////////\n";
// P1,P2,P3 are the ramification points (0,..),(1,..),(a,..) of the superelliptic
// curve y^n=x(x-1)(x-a); their pairwise differences are torsion in the Jacobian, so
// the holomorphic integrals between them must be weakly zero.
I,N:=coleman_integrals_on_basis(P1,P2,data); I; N;
"holomorphic integrals P1->P2 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P3,data); I; N;
"holomorphic integrals P1->P3 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P4,data); I; N;
"holomorphic integrals P1->P4 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
