load "isrational.m";
load "auxpolys.m";
load "cohobasis.m";
load "frobenius.m";
load "reduction.m";
load "coercion.m";
load "expansion.m";
load "integrals.m";

SetLogFile("example-8.1.log" : Overwrite);

// Example 8.1 of the article: hyperelliptic curve from Siksek, Section 6
print "";
print "//////////////////////////";
print "// Example 8.1: hyperelliptic curve in Siksek's paper, Section 6 //";
print "//////////////////////////\n";

Qx:=PolynomialRing(Rationals());
h:=Qx.1^3-2;
L<a>:=NumberField(h);
Lx<x>:=PolynomialRing(L);
Lxy<y>:=PolynomialRing(Lx);
OL:=MaximalOrder(L);
D:=Decomposition(OL,109);
P:=D[1][1];
N:=20;

Q:=y^2-3*(4*(1-a)^(-1)*x^5-(1-a)^2);
data:=coleman_data(Q,L,P,N);
print "";
print "//////////////////////////";
print "// 6.1. W0, Winf, r //";
print "//////////////////////////\n";
data`W0;
data`Winf;
r:=data`r;
r;

print "";
print "//////////////////////////";
print "// 6.2. basis, first half is in H^1(X) //";
print "//////////////////////////\n";

//data`basis;

print "";
print "//////////////////////////";
print "// 6.3. r(P) //";
print "//////////////////////////\n";
// paper notation: P1, P1'=(x(P1),-y(P1)), P2=(-1,3a+3), P2'=(-1,-(3a+3)), P3=infty
P1 :=set_point(-a^2-a-1,40*a^2+53*a+67,data);
P1d:=set_point(-a^2-a-1,-(40*a^2+53*a+67),data);
is_bad(P1d,data);
r1:=Evaluate(r,-a^2-a-1);
r1;
//mm(r1);
P2 :=set_point(-1,3*a+3,data);
P2d:=set_point(-1,-(3*a+3),data);
r2:=Evaluate(r,-1);
r2;
//mm(r2);
P3:=set_bad_point(0,[1,0],true,data); // very infinite point with b^infty=[1,0]
print "";
print "//////////////////////////";
print "// Example 8.1: integration //";
print "//////////////////////////\n";
I,N:=coleman_integrals_on_basis(P1,P1d,data); I; N;
"holomorphic integrals P1->P1' weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P2,data); I; N;
"holomorphic integrals P1->P2 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P2d,data); I; N;
"holomorphic integrals P1->P2' weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P3,data); I; N;
"holomorphic integrals P1->P3 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
