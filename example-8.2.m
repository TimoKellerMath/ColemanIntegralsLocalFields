load "isrational.m";
load "auxpolys.m";
load "cohobasis.m";
load "frobenius.m";
load "reduction.m";
load "coercion.m";
load "expansion.m";
load "integrals.m";


SetLogFile("example-8.2.log" : Overwrite);

// Example 8.2 of the article: modular curve X(b3,s5) over Q(sqrt(5)), P|7, N=20
print "";
print "//////////////////////////";
print "// Example 8.2: modular curve X(b3,s5) over Q(sqrt(5)) //";
print "//////////////////////////\n";
Qx:=PolynomialRing(Rationals());
h:=Qx.1^2-5;
L<a>:=NumberField(h);
Lx<x>:=PolynomialRing(L);
Lxy<y>:=PolynomialRing(Lx);
OL:=MaximalOrder(L);
D:=Decomposition(OL,7);
P:=D[1][1];
N:=20;
Q:=y^4+(-3*x+7)*y^3+2*(-3*x^2-19*x-7)*y^2+4*(-x-3)*y+8*(3*x^3+5*x^2+3*x);
data:=coleman_data(Q,L,P,N);
print "";
print "//////////////////////////";
print "// 7.1. W0, Winf, r //";
print "//////////////////////////\n";
data`W0;
data`Winf;
r:=data`r;
r;

print "";
print "//////////////////////////";
print "// 7.2. basis, first half is in H^1(X) //";
print "//////////////////////////\n";

//data`basis;

print "";
print "//////////////////////////";
print "// 7.3. r(P) //";
print "//////////////////////////\n";
P1:=set_point(0,0,data);
r1:=Evaluate(r,0);
P2:=set_point(1/2,-1,data);
r2:=Evaluate(r,1/2);
r2;
P3:=set_point(-2,-1+a,data);
r3:=Evaluate(r,-2);
r3;
P4:=set_point((1-a)/2,-6+2*a,data);
r4:=Evaluate(r,(1-a)/2);
r4;
P5:=set_point((1+a)/2,4+2*a,data);
r5:=Evaluate(r,(1+a)/2);   // x(P5) = (1+a)/2
r5;
P6:=set_bad_point(0,[1,0,0,0],true,data);
print "";
print "//////////////////////////";
print "// 7.4. integration //";
print "//////////////////////////\n";
I,N:=coleman_integrals_on_basis(P1,P2,data); I; N;
"holomorphic integrals P1->P2 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P3,data); I; N;
"holomorphic integrals P1->P3 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P4,data); I; N;
"holomorphic integrals P1->P4 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P5,data); I; N;
"holomorphic integrals P1->P5 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
I,N:=coleman_integrals_on_basis(P1,P6,data); I; N;
"holomorphic integrals P1->P6 weakly zero (torsion):", holomorphic_integrals_weakly_zero(I,data);
printf "\nresources: CPU time %o s, maximum memory %o MB\n", Cputime(), Round(GetMaximumMemoryUsage()/2^20);
