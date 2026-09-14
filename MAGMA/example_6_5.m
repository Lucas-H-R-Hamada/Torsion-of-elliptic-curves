///////////////////////////////////////////////////////////////////////////
// example_6_5.m
//
// Computational verification for Example 6.5 of
// "Torsion of Elliptic Curves over Quartic Number Fields
//  with Rational j-Invariant"
//
// This script verifies:
//   (1) the defining quartic number field;
//   (2) K/Q is cyclic of degree 4;
//   (3) the displayed elliptic curve has the claimed j-invariant;
//   (4) P = (0,0) has exact order 17;
//   (5) E(K)_tors is isomorphic to Z/17Z.
///////////////////////////////////////////////////////////////////////////

Q := Rationals();
R<x> := PolynomialRing(Q);


///////////////////////////////////////////////////////////////////////////
// 1. The quartic field
//
// In the paper the field is written as
//
//     K = Q(alpha),
//
// where alpha is a root of
//
//     f(X) = 2X^4 - 5X^3 - 7X^2 + 10X + 8.
//
// For some Magma number-field routines, including IsCyclic, it is
// preferable to use a monic integral defining polynomial.
//
// Put
//
//     beta = 2*alpha.
//
// Then beta satisfies
//
//     g(X) = X^4 - 5X^3 - 14X^2 + 40X + 64.
//
// Since alpha = beta/2, Q(alpha) = Q(beta).
///////////////////////////////////////////////////////////////////////////

f := 2*x^4 - 5*x^3 - 7*x^2 + 10*x + 8;

assert IsIrreducible(f);

g := x^4 - 5*x^3 - 14*x^2 + 40*x + 64;

assert IsIrreducible(g);

// Check algebraically that g(beta) comes from f(alpha)
// under beta = 2*alpha.
assert g eq Evaluate(8*f, x/2);

K<beta> := NumberField(g);

// Recover the generator alpha used in the paper.
alpha := beta/2;

assert Degree(K) eq 4;
assert IsCyclic(K);

print "Quartic field verification passed.";
print "[K:Q] =", Degree(K);
print "K/Q is cyclic.";
print "";


///////////////////////////////////////////////////////////////////////////
// 2. Parameters b and c
//
// These are written using alpha, exactly as in Example 6.5.
///////////////////////////////////////////////////////////////////////////

b := -(1337/32)*alpha^3
     + (3233/64)*alpha^2
     + (12285/64)*alpha
     + 1135/16;

c := -(59/16)*alpha^3
     + (147/32)*alpha^2
     + (535/32)*alpha
     + 45/8;


///////////////////////////////////////////////////////////////////////////
// 3. The elliptic curve
//
// Tate normal form:
//
//     E : y^2 + (1-c)xy - by = x^3 - bx^2.
//
// Magma uses the generalized Weierstrass form
//
//     y^2 + a1*x*y + a3*y
//         = x^3 + a2*x^2 + a4*x + a6.
//
// Hence
//
//     a1 = 1-c,
//     a2 = -b,
//     a3 = -b,
//     a4 = 0,
//     a6 = 0.
///////////////////////////////////////////////////////////////////////////

E := EllipticCurve([K | 1-c, -b, -b, 0, 0]);

assert Discriminant(E) ne 0;


///////////////////////////////////////////////////////////////////////////
// 4. Verify the j-invariant
///////////////////////////////////////////////////////////////////////////

jE := jInvariant(E);

j_expected := K!(-882216989/131072);

print "Computed j-invariant:";
print jE;

assert jE eq j_expected;

print "j-invariant verification passed.";
print "j(E) = -882216989/131072";
print "";


///////////////////////////////////////////////////////////////////////////
// 5. Verify that P = (0,0) has exact order 17
///////////////////////////////////////////////////////////////////////////

P := E![K!0, K!0, K!1];
O := E![K!0, K!1, K!0];

assert P ne O;

// Since 17 is prime, these two assertions already imply that
// P has exact order 17.
assert 17*P eq O;
assert Order(P) eq 17;

print "Point-order verification passed.";
print "P = (0,0) has exact order", Order(P);
print "";


///////////////////////////////////////////////////////////////////////////
// 6. Compute the full torsion subgroup
///////////////////////////////////////////////////////////////////////////

T, torsion_map := TorsionSubgroup(E);

invT := AbelianInvariants(T);

print "Torsion subgroup invariants:";
print invT;

assert invT eq [17];
assert #T eq 17;

assert Ngens(T) eq 1;

PT := torsion_map(T.1);

assert Order(PT) eq 17;

print "Full torsion verification passed.";
print "E(K)_tors is isomorphic to Z/17Z.";
print "";


///////////////////////////////////////////////////////////////////////////
// Final message
///////////////////////////////////////////////////////////////////////////

print "============================================================";
print "ALL CHECKS FOR EXAMPLE 6.5 PASSED.";
print "============================================================";
