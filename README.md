# Computational verification for
## Torsion of elliptic curves over quartic number fields with rational j-invariant

This repository contains the Magma computations accompanying the paper

**"Torsion of Elliptic Curves over Quartic Number Fields with Rational j-Invariant."**

The computations provide independent verification of several explicit
claims appearing in Section 6.

## Files

### `magma/example_6_5.m`

Verifies the elliptic curve in Example 6.5.

The script checks:

- the quartic number field;
- the elliptic curve in Tate normal form;
- the claimed rational j-invariant

  `j(E) = -882216989/131072`;

- that `P = (0,0)` has exact order 17;
- the torsion subgroup over the quartic field.

### `magma/example_6_6.m`

Verifies the example with 21-torsion.

The script checks:

- the defining quartic number field;
- the j-invariant `j(E) = 0`;
- the torsion subgroup over the quartic field.
