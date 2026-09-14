///////////////////////////////////////////////////////////////////////////
// lemma_6_3_group_checks.m
//
// Supplementary finite-group computations for Lemma 6.3 of
// "Torsion of Elliptic Curves over Quartic Number Fields
//  with Rational j-Invariant"
//
// These computations verify finite-group assertions used in the proof.
//
// Magma convention:
//     DihedralGroup(4)
// has order 8.  Thus it is the group denoted D4 in the paper.
///////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////
// Utility function
//
// Returns true if G has a quotient isomorphic to H.
//
// We first replace both groups by faithful permutation representations.
// This makes the normal-subgroup and quotient computations uniform for
// permutation groups and matrix groups.
///////////////////////////////////////////////////////////////////////////

function HasQuotientIsomorphicTo(G, H)

    // Quick order obstruction.
    if Order(G) mod Order(H) ne 0 then
        return false;
    end if;

    // Faithful permutation representation of G.
    phiG, PG := MinimalDegreePermutationRepresentation(G);

    // Faithful permutation representation of H.
    phiH, PH := MinimalDegreePermutationRepresentation(H);

    kernel_order := Order(PG) div Order(PH);

    // NormalSubgroups is used instead of
    //
    //     Subgroups(G : IsNormal := true)
    //
    // since the latter is not accepted for all relevant Magma
    // group categories.
    normals := NormalSubgroups(PG);

    for recN in normals do

        N := recN`subgroup;

        if Order(N) eq kernel_order then

            // Construct PG/N.
            Q, pi := quo< PG | N >;

            if IsIsomorphic(Q, PH) then
                return true;
            end if;

        end if;

    end for;

    return false;

end function;


///////////////////////////////////////////////////////////////////////////
// 1. No cyclic cubic quotient of S4 or D4
///////////////////////////////////////////////////////////////////////////

S4 := SymmetricGroup(4);
D4 := DihedralGroup(4);
C3 := CyclicGroup(3);

assert Order(S4) eq 24;
assert Order(D4) eq 8;
assert Order(C3) eq 3;

assert not HasQuotientIsomorphicTo(S4, C3);
assert not HasQuotientIsomorphicTo(D4, C3);

print "CHECK 1 PASSED:";
print "Neither S4 nor D4 has a quotient isomorphic to C3.";
print "";


///////////////////////////////////////////////////////////////////////////
// 2. S4 case
//
// A non-Galois quartic subfield of an S4-extension corresponds to
// a point stabilizer S3 < S4.
//
// Its maximality implies that the corresponding quartic field has
// no nontrivial proper intermediate field.
///////////////////////////////////////////////////////////////////////////

H_S4 := Stabilizer(S4, 1);

assert Order(H_S4) eq 6;
assert Index(S4, H_S4) eq 4;
assert IsMaximal(S4, H_S4);

print "CHECK 2 PASSED:";
print "A point stabilizer S3 < S4 has index 4 and is maximal.";
print "Therefore the associated quartic field has no";
print "nontrivial proper intermediate field.";
print "";


///////////////////////////////////////////////////////////////////////////
// 3. A4 case
//
// A quartic subfield of an A4-extension corresponds to a point
// stabilizer C3 < A4.
///////////////////////////////////////////////////////////////////////////

A4 := AlternatingGroup(4);
H_A4 := Stabilizer(A4, 1);

assert Order(A4) eq 12;
assert Order(H_A4) eq 3;
assert Index(A4, H_A4) eq 4;
assert IsMaximal(A4, H_A4);

print "CHECK 3 PASSED:";
print "A point stabilizer C3 < A4 has index 4 and is maximal.";
print "";


///////////////////////////////////////////////////////////////////////////
// 4. D4 case
//
// A non-Galois quartic subfield in a D4-extension is fixed by a
// reflection subgroup H of order 2.
//
// Quadratic intermediate fields of the quartic field correspond
// to order-4 subgroups J satisfying
//
//                H <= J <= D4.
//
// We verify that there is exactly one such subgroup J.
///////////////////////////////////////////////////////////////////////////

r := D4.1;
s := D4.2;

H_D4 := sub< D4 | s >;

assert Order(H_D4) eq 2;
assert Index(D4, H_D4) eq 4;

OvergroupsOfOrder4 := [];

for recJ in Subgroups(D4 : OrderEqual := 4) do

    J := recJ`subgroup;

    // Subgroups() returns conjugacy-class representatives.
    // We must inspect all conjugates in the class.
    for g in D4 do

        Jg := J^g;

        if H_D4 subset Jg then

            already_listed := false;

            for U in OvergroupsOfOrder4 do
                if U eq Jg then
                    already_listed := true;
                    break;
                end if;
            end for;

            if not already_listed then
                Append(~OvergroupsOfOrder4, Jg);
            end if;

        end if;

    end for;

end for;

assert #OvergroupsOfOrder4 eq 1;

print "CHECK 4 PASSED:";
print "A reflection subgroup of D4 is contained in exactly";
print "one subgroup of order 4.";
print "Hence the corresponding non-Galois quartic field has";
print "a unique quadratic intermediate field.";
print "";


///////////////////////////////////////////////////////////////////////////
// 5. Standard mod-3 image groups inside GL(2,F_3)
///////////////////////////////////////////////////////////////////////////

G3 := GL(2, 3);

assert Order(G3) eq 48;


// -----------------------------------------------------------------------
// 3Ns: normalizer of a split Cartan subgroup
// -----------------------------------------------------------------------

d1 := G3![
    2,0,
    0,1
];

d2 := G3![
    1,0,
    0,2
];

w := G3![
    0,1,
    1,0
];

Ns3 := sub< G3 | d1, d2, w >;

assert Order(Ns3) eq 8;


// -----------------------------------------------------------------------
// 3B: the upper triangular Borel subgroup
// -----------------------------------------------------------------------

u := G3![
    1,1,
    0,1
];

B3 := sub< G3 | d1, d2, u >;

assert Order(B3) eq 12;


// -----------------------------------------------------------------------
// 3Nn: normalizer of a nonsplit Cartan subgroup
//
// The matrix c has order 8.
// The matrix t has order 2.
// They satisfy
//
//                    c^t = c^3.
//
// Thus the generated group has the semidihedral presentation occurring
// for the nonsplit Cartan normalizer in GL(2,F_3).
// -----------------------------------------------------------------------

c := G3![
    1,2,
    1,1
];

t := G3![
    1,0,
    0,2
];

Nn3 := sub< G3 | c, t >;

assert Order(c) eq 8;
assert Order(t) eq 2;
assert c^t eq c^3;
assert Order(Nn3) eq 16;

print "CHECK 5 PASSED:";
print "Orders of the relevant mod-3 image groups:";
print "  |GL(2,3)| =", Order(G3);
print "  |3Ns|     =", Order(Ns3);
print "  |3B|      =", Order(B3);
print "  |3Nn|     =", Order(Nn3);
print "";
print "For 3Nn:";
print "  Order(c) = 8;";
print "  Order(t) = 2;";
print "  c^t = c^3.";
print "";


///////////////////////////////////////////////////////////////////////////
// 6. None of the possible mod-3 image groups has A4 as a quotient
//
// The four groups appearing in the relevant part of Lemma 6.3 are
//
//       GL(2,F_3),  3Ns,  3B,  3Nn.
//
// For 3Ns and 3Nn there is already an order obstruction:
//
//       12 does not divide 8,
//       12 does not divide 16.
//
// For 3B, both groups have order 12, so an A4 quotient would force
// 3B itself to be isomorphic to A4.
//
// We nevertheless let HasQuotientIsomorphicTo perform the checks
// uniformly.
///////////////////////////////////////////////////////////////////////////

assert not HasQuotientIsomorphicTo(G3,  A4);
assert not HasQuotientIsomorphicTo(Ns3, A4);
assert not HasQuotientIsomorphicTo(B3,  A4);
assert not HasQuotientIsomorphicTo(Nn3, A4);

print "CHECK 6 PASSED:";
print "None of";
print "";
print "    GL(2,3), 3Ns, 3B, 3Nn";
print "";
print "has a quotient isomorphic to A4.";
print "";


///////////////////////////////////////////////////////////////////////////
// 7. Cyclic quartic versus biquadratic extensions
//
// By Galois correspondence:
//
//   C4 has exactly one subgroup of order 2,
//   C2 x C2 has exactly three subgroups of order 2.
//
// Thus:
//
//   a cyclic quartic extension has one quadratic subfield;
//   a biquadratic extension has three quadratic subfields.
//
// This distinction is relevant in the D4 portion of Lemma 6.3.
///////////////////////////////////////////////////////////////////////////

C4 := CyclicGroup(4);
V4 := AbelianGroup(GrpPerm, [2,2]);

subsC4 := Subgroups(C4 : OrderEqual := 2);
subsV4 := Subgroups(V4 : OrderEqual := 2);

nC4 := &+[ recH`length : recH in subsC4 ];
nV4 := &+[ recH`length : recH in subsV4 ];

assert nC4 eq 1;
assert nV4 eq 3;

print "CHECK 7 PASSED:";
print "Number of order-2 subgroups of C4:", nC4;
print "Number of order-2 subgroups of C2 x C2:", nV4;
print "";

print "============================================================";
print "ALL SUPPLEMENTARY GROUP CHECKS FOR LEMMA 6.3 PASSED.";
print "============================================================";
