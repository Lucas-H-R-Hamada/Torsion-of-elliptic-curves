///////////////////////////////////////////////////////////////////////////
// example_6_6.m
//
// Computational verification for Example 6.6 of
// "Torsion of Elliptic Curves over Quartic Number Fields
//  with Rational j-Invariant"
//
// This script verifies:
//   (1) the defining polynomial is irreducible over Q;
//   (2) K/Q has degree 4;
//   (3) the displayed curve has j-invariant 0;
//   (4) E(K)_tors is isomorphic to Z/21Z.
///////////////////////////////////////////////////////////////////////////

Q := Rationals();
R<x> := PolynomialRing(Q);

// The quartic field K = Q(alpha).
f := x^4 - x^3 + 2*x + 1;

assert IsIrreducible(f);

K<alpha> := NumberField(f);

assert Degree(K) eq 4;

print "Quartic field verification passed.";
print "[K:Q] =", Degree(K);
print "";

// Define
//
//   E : y^2 = x^3 - B,
//
// where B is the element displayed in Example 6.6.
B := 371952*alpha^3
     + 3373488*alpha^2
     + 3777840*alpha
     + 1228608;

// Magma's two-coefficient form [a4,a6] represents
//
//   y^2 = x^3 + a4*x + a6.
//
// Thus [0,-B] gives y^2 = x^3 - B.
E := EllipticCurve([K | 0, -B]);

assert Discriminant(E) ne 0;

// Verify j(E) = 0.
jE := jInvariant(E);

print "Computed j-invariant:";
print jE;

assert jE eq K!0;

print "j-invariant verification passed.";
print "j(E) = 0";
print "";

// Compute the full torsion subgroup over K.
T, torsion_map := TorsionSubgroup(E);
invT := AbelianInvariants(T);

print "Torsion subgroup invariants:";
print invT;

assert invT eq [21];
assert #T eq 21;

// Check that a generator returned by Magma maps to a point
// of exact order 21.
assert Ngens(T) eq 1;
P := torsion_map(T.1);
assert Order(P) eq 21;

print "Full torsion verification passed.";
print "E(K)_tors is isomorphic to Z/21Z.";
print "";
print "ALL CHECKS FOR EXAMPLE 6.6 PASSED.";
