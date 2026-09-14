///////////////////////////////////////////////////////////////////////////
//
//  Supplementary computations for Lemma 6.3
//
//  This script verifies the finite-group assertions used in the proof:
//    (1) S4 and D4 have no cyclic quotient of order 3;
//    (2) the relevant stabilizers in S4 and A4 are maximal;
//    (3) a reflection subgroup of D4 has a unique order-4 overgroup;
//    (4) the groups GL(2,3), 3Ns, 3B, and 3Nn have no quotient A4;
//    (5) the standard models for 3Ns, 3B and 3Nn have orders
//        8, 12 and 16, respectively;
//    (6) C4 has one subgroup of order 2 whereas V4 has three.
//
//  Magma notation:
//       DihedralGroup(4) has order 8.
//       DihedralGroup(6) has order 12.
//
///////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////
// Utility: test whether G has a quotient isomorphic to H
///////////////////////////////////////////////////////////////////////////

function HasQuotientIsomorphicTo(G, H)

    // It is enough to inspect normal subgroups N for which
    // |G/N| = |H|.

    for rN in Subgroups(G : IsNormal := true) do

        N := rN`subgroup;

        if Order(G) eq Order(N) * Order(H) then

            Q := G / N;

            if IsIsomorphic(Q, H) then
                return true;
            end if;

        end if;

    end for;

    return false;

end function;


///////////////////////////////////////////////////////////////////////////
// 1. No cyclic cubic quotient of S4 or D4
//
// This is the group-theoretic ingredient behind Lemma 4.3.
// A cyclic cubic subextension of a Galois extension would give a
// quotient C3 of the corresponding Galois group.
///////////////////////////////////////////////////////////////////////////

S4 := SymmetricGroup(4);
D4 := DihedralGroup(4);       // order 8
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
// 2. Quartic S4 case: the S3 point stabilizer is maximal
//
// For a non-Galois quartic K whose Galois closure has group S4,
// K is fixed by a point stabilizer S3 < S4.
//
// Maximality of S3 shows that K/Q has no nontrivial intermediate field.
///////////////////////////////////////////////////////////////////////////

H_S4 := sub< S4 | (1,2), (1,2,3) >;

assert Order(H_S4) eq 6;
assert Index(S4, H_S4) eq 4;
assert IsMaximal(S4, H_S4);

print "CHECK 2 PASSED:";
print "The subgroup S3 < S4 defining a quartic subfield is maximal.";
print "Hence the corresponding quartic field has no proper";
print "nontrivial intermediate field.";
print "";


///////////////////////////////////////////////////////////////////////////
// 3. Quartic A4 case: the C3 stabilizer is maximal
//
// If the Galois closure has group A4, a quartic subfield corresponds
// to a subgroup C3 < A4.
///////////////////////////////////////////////////////////////////////////

A4 := AlternatingGroup(4);

H_A4 := sub< A4 | (1,2,3) >;

assert Order(A4) eq 12;
assert Order(H_A4) eq 3;
assert Index(A4, H_A4) eq 4;
assert IsMaximal(A4, H_A4);

print "CHECK 3 PASSED:";
print "The subgroup C3 < A4 defining a quartic subfield is maximal.";
print "";


///////////////////////////////////////////////////////////////////////////
// 4. Quartic D4 case: unique quadratic intermediate field
//
// A non-Galois quartic subfield in a D4-extension corresponds to a
// reflection subgroup H of order 2.
//
// Intermediate quadratic fields correspond to order-4 subgroups J
// satisfying
//
//              H <= J <= D4.
//
// We enumerate all order-4 subgroups containing H.
///////////////////////////////////////////////////////////////////////////

r := D4.1;
s := D4.2;

// In Magma's standard model, s is a reflection.
H_D4 := sub< D4 | s >;

assert Order(H_D4) eq 2;
assert Index(D4, H_D4) eq 4;

OvergroupsOfOrder4 := [];

for x in D4 do
    for y in D4 do

        J := sub< D4 | x, y >;

        if Order(J) eq 4 and
           H_D4 subset J and
           not (J in OvergroupsOfOrder4) then

            Append(~OvergroupsOfOrder4, J);

        end if;

    end for;
end for;

assert #OvergroupsOfOrder4 eq 1;

print "CHECK 4 PASSED:";
print "A reflection subgroup of D4 is contained in exactly";
print "one subgroup of order 4.";
print "Thus the associated non-Galois quartic field has";
print "a unique quadratic intermediate field.";
print "";


///////////////////////////////////////////////////////////////////////////
// 5. Construct the relevant mod-3 image groups inside GL(2,F_3)
///////////////////////////////////////////////////////////////////////////

G3 := GL(2,3);

assert Order(G3) eq 48;

/*
    3Ns: normalizer of the split Cartan.

    The split Cartan consists of invertible diagonal matrices.
    Adding the matrix which exchanges the two coordinate axes
    gives its normalizer.
*/

d1 := G3![2,0,
          0,1];

d2 := G3![1,0,
          0,2];

w  := G3![0,1,
          1,0];

Ns3 := sub< G3 | d1, d2, w >;

assert Order(Ns3) eq 8;
assert IsIsomorphic(Ns3, DihedralGroup(4));

print "3Ns has order", Order(Ns3);
print "3Ns is isomorphic to D4 (order 8).";
print "";


/*
    3B: the full Borel subgroup of upper triangular matrices.
*/

u := G3![1,1,
         0,1];

B3 := sub< G3 | d1, d2, u >;

assert Order(B3) eq 12;
assert IsIsomorphic(B3, DihedralGroup(6));

print "3B has order", Order(B3);
print "3B is isomorphic to D6 (order 12).";
print "";


/*
    3Nn: normalizer of a nonsplit Cartan.

    Let c represent multiplication by 1 + alpha in F_9,
    where alpha^2 = -1.

    The matrix c has order 8.

    The matrix t represents the Frobenius automorphism
           alpha |--> -alpha.

    One obtains
           c^t = c^3,

    which is the semidihedral relation.
*/

c := G3![1,2,
         1,1];

t := G3![1,0,
         0,2];

Nn3 := sub< G3 | c, t >;

assert Order(c) eq 8;
assert Order(t) eq 2;
assert c^t eq c^3;
assert Order(Nn3) eq 16;

print "3Nn has order", Order(Nn3);
print "Generators satisfy:";
print "  Order(c) = 8, Order(t) = 2, c^t = c^3.";
print "Thus 3Nn is the semidihedral group SD16.";
print "";


///////////////////////////////////////////////////////////////////////////
// 6. None of the possible groups has A4 as a quotient
//
// These are exactly the groups appearing in the argument concerning
// Gal(Q(E'[3])/Q):
//
//       GL(2,F3), 3Ns, 3B, 3Nn.
//
// We check every normal subgroup whose quotient could have order 12.
///////////////////////////////////////////////////////////////////////////

assert not HasQuotientIsomorphicTo(G3,  A4);
assert not HasQuotientIsomorphicTo(Ns3, A4);
assert not HasQuotientIsomorphicTo(B3,  A4);
assert not HasQuotientIsomorphicTo(Nn3, A4);

print "CHECK 5 PASSED:";
print "None of";
print "  GL(2,3), 3Ns, 3B, 3Nn";
print "has a quotient isomorphic to A4.";
print "";


///////////////////////////////////////////////////////////////////////////
// 7. Additional check relevant to the degree-4 case
//
// A cyclic quartic group C4 has exactly one subgroup of order 2,
// whereas V4 = C2 x C2 has three.
//
// Via Galois correspondence:
//    cyclic quartic extension -> one quadratic subfield,
//    biquadratic extension    -> three quadratic subfields.
//
// This is precisely why the two degree-4 possibilities must not be
// treated identically.
///////////////////////////////////////////////////////////////////////////

C4 := CyclicGroup(4);
V4 := AbelianGroup(GrpPerm, [2,2]);

function NumberOfSubgroupsOfOrder(G, n)

    total := 0;

    for rH in Subgroups(G : OrderEqual := n) do
        total +:= rH`length;
    end for;

    return total;

end function;

nC4 := NumberOfSubgroupsOfOrder(C4, 2);
nV4 := NumberOfSubgroupsOfOrder(V4, 2);

assert nC4 eq 1;
assert nV4 eq 3;

print "CHECK 6 PASSED:";
print "Number of order-2 subgroups of C4:", nC4;
print "Number of order-2 subgroups of V4:", nV4;
print "";

print "==========================================================";
print "ALL FINITE-GROUP CHECKS FOR LEMMA 6.3 PASSED.";
print "==========================================================";
