///////////////////////////////////////////////////////////////////////////
// example_6_5.m
//
// Computational verification for Example 6.5 of
// "Torsion of Elliptic Curves over Quartic Number Fields
//  with Rational j-Invariant"
//
// This script verifies:
//   (1) the defining polynomial is irreducible over Q;
//   (2) K/Q has degree 4 and is cyclic;
//   (3) the displayed curve has the claimed j-invariant;
//   (4) P = (0,0) has exact order 17;
//   (5) E(K)_tors is isomorphic to Z/17Z.
///////////////////////////////////////////////////////////////////////////

Q := Rationals();
R<x> := PolynomialRing(Q);

// The quartic field K = Q(alpha).
f := 2*x^4 - 5*x^3 - 7*x^2 + 10*x + 8;

assert IsIrreducible(f);

// NumberField is given the monic scalar multiple of f.
// This defines exactly the same extension of Q.
fmon := f / LeadingCoefficient(f);
K<alpha> := NumberField(fmon);

assert Degree(K) eq 4;
assert IsCyclic(K);

print "Quartic field verification passed.";
print "[K:Q] =", Degree(K);
print "K/Q is cyclic.";
print "";

// Parameters in Jeon's Tate normal form.
b := -(1337/32)*alpha^3
     + (3233/64)*alpha^2
     + (12285/64)*alpha
     + 1135/16;

c := -(59/16)*alpha^3
     + (147/32)*alpha^2
     + (535/32)*alpha
     + 45/8;

// Generalized Weierstrass convention used by Magma:
//
//   y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6.
//
// Our curve is
//
//   y^2 + (1-c)xy - by = x^3 - bx^2,
//
// hence [a1,a2,a3,a4,a6] = [1-c,-b,-b,0,0].
E := EllipticCurve([K | 1-c, -b, -b, 0, 0]);

assert Discriminant(E) ne 0;

// Verify the rational j-invariant.
j_expected := K!(-882216989/131072);
jE := jInvariant(E);

print "Computed j-invariant:";
print jE;

assert jE eq j_expected;

print "j-invariant verification passed.";
print "j(E) = -882216989/131072";
print "";

// The distinguished point P = (0,0).
P := E![K!0, K!0, K!1];
O := E![K!0, K!1, K!0];

assert P ne O;
assert 17*P eq O;
assert Order(P) eq 17;

print "Point-order verification passed.";
print "P = (0,0) has exact order", Order(P);
print "";

// Compute the full torsion subgroup over K.
T, torsion_map := TorsionSubgroup(E);
invT := AbelianInvariants(T);

print "Torsion subgroup invariants:";
print invT;

assert invT eq [17];
assert #T eq 17;

// As an additional consistency check, a generator returned by Magma
// maps to a point of exact order 17 on E.
assert Ngens(T) eq 1;
PT := torsion_map(T.1);
assert Order(PT) eq 17;

print "Full torsion verification passed.";
print "E(K)_tors is isomorphic to Z/17Z.";
print "";
print "ALL CHECKS FOR EXAMPLE 6.5 PASSED.";
