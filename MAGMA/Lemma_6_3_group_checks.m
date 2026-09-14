///////////////////////////////////////////////////////////////////////////
// lemma_6_3_group_checks.m
//
// Supplementary finite-group computations for Lemma 6.3 of
// "Torsion of Elliptic Curves over Quartic Number Fields
//  with Rational j-Invariant"
//
// These computations are sanity checks for the group-theoretic facts used
// in the proof.  They do not replace the theoretical proof.
//
// The script verifies:
//   (1) S4 and D4 have no quotient isomorphic to C3;
//   (2) the S3 point stabilizer in S4 is maximal;
//   (3) the C3 point stabilizer in A4 is maximal;
//   (4) a reflection subgroup of D4 is contained in exactly one
//       subgroup of order 4;
//   (5) standard matrix models for 3Ns, 3B, and 3Nn have orders
//       8, 12, and 16, respectively;
//   (6) none of GL(2,3), 3Ns, 3B, 3Nn has a quotient isomorphic to A4;
//   (7) C4 has one subgroup of order 2, whereas C2 x C2 has three.
//
// Magma convention: DihedralGroup(n) has order 2*n.  Thus
// DihedralGroup(4) is the dihedral group of order 8 used here as D4.
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
// Utility: determine whether a finite group G has a quotient isomorphic
// to a finite group H.
///////////////////////////////////////////////////////////////////////////

function HasQuotientIsomorphicTo(G, H)
    if Order(G) mod Order(H) ne 0 then
        return false;
    end if;

    kernel_order := Order(G) div Order(H);

    normals := Subgroups(G : IsNormal := true,
                             OrderEqual := kernel_order);

    for recN in normals do
        N := recN`subgroup;
        Q, pi := quo< G | N >;

        if IsIsomorphic(Q, H) then
            return true;
        end if;
    end for;

    return false;
end function;

///////////////////////////////////////////////////////////////////////////
// 1. No cyclic cubic quotient of S4 or D4.
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
// 2. In S4, the point stabilizer S3 is maximal.
//
// For a non-Galois quartic field whose Galois closure has group S4,
// this is the subgroup corresponding to the quartic field.  Maximality
// means the quartic field has no nontrivial proper intermediate field.
///////////////////////////////////////////////////////////////////////////

H_S4 := Stabilizer(S4, 1);

assert Order(H_S4) eq 6;
assert Index(S4, H_S4) eq 4;
assert IsMaximal(S4, H_S4);

print "CHECK 2 PASSED:";
print "A point stabilizer S3 < S4 has index 4 and is maximal.";
print "";

///////////////////////////////////////////////////////////////////////////
// 3. In A4, the point stabilizer C3 is maximal.
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
// 4. The relevant D4 subgroup lattice.
//
// A non-Galois quartic subfield of a D4-extension is fixed by a
// reflection subgroup H of order 2.  Quadratic intermediate fields
// correspond to subgroups J of order 4 satisfying H <= J <= D4.
// We verify that there is exactly one such J.
///////////////////////////////////////////////////////////////////////////

r := D4.1;
s := D4.2;
H_D4 := sub< D4 | s >;

assert Order(H_D4) eq 2;
assert Index(D4, H_D4) eq 4;

OvergroupsOfOrder4 := [];

for x in D4 do
    for y in D4 do
        J := sub< D4 | x, y >;

        if Order(J) eq 4 and H_D4 subset J then
            already_listed := false;

            for U in OvergroupsOfOrder4 do
                if U eq J then
                    already_listed := true;
                    break;
                end if;
            end for;

            if not already_listed then
                Append(~OvergroupsOfOrder4, J);
            end if;
        end if;
    end for;
end for;

assert #OvergroupsOfOrder4 eq 1;

print "CHECK 4 PASSED:";
print "A reflection subgroup of D4 is contained in exactly one";
print "subgroup of order 4.";
print "";

///////////////////////////////////////////////////////////////////////////
// 5. Standard mod-3 image groups inside GL(2,F_3).
///////////////////////////////////////////////////////////////////////////

G3 := GL(2, 3);
assert Order(G3) eq 48;

// 3Ns: normalizer of the split Cartan.
d1 := G3![2,0,
          0,1];

d2 := G3![1,0,
          0,2];

w := G3![0,1,
         1,0];

Ns3 := sub< G3 | d1, d2, w >;
assert Order(Ns3) eq 8;

// 3B: the upper-triangular Borel subgroup.
u := G3![1,1,
         0,1];

B3 := sub< G3 | d1, d2, u >;
assert Order(B3) eq 12;

// 3Nn: normalizer of a nonsplit Cartan.
//
// Let alpha^2 = -1 in F_9.  The matrix c represents multiplication
// by 1+alpha, which has order 8.  The matrix t represents Frobenius
// alpha |-> -alpha.  The relation c^t = c^3 is the semidihedral
// relation for the order-16 normalizer.
c := G3![1,2,
         1,1];

t := G3![1,0,
         0,2];

Nn3 := sub< G3 | c, t >;

assert Order(c) eq 8;
assert Order(t) eq 2;
assert c^t eq c^3;
assert Order(Nn3) eq 16;

print "CHECK 5 PASSED:";
print "Orders of the standard mod-3 image groups:";
print "  |3Ns| =", Order(Ns3);
print "  |3B|  =", Order(B3);
print "  |3Nn| =", Order(Nn3);
print "The generators of 3Nn satisfy c^t = c^3.";
print "";

///////////////////////////////////////////////////////////////////////////
// 6. No A4 quotient for the possible mod-3 image groups used in
// the A4 branch of Lemma 6.3.
///////////////////////////////////////////////////////////////////////////

assert not HasQuotientIsomorphicTo(G3,  A4);
assert not HasQuotientIsomorphicTo(Ns3, A4);
assert not HasQuotientIsomorphicTo(B3,  A4);
assert not HasQuotientIsomorphicTo(Nn3, A4);

print "CHECK 6 PASSED:";
print "None of GL(2,3), 3Ns, 3B, or 3Nn has a quotient";
print "isomorphic to A4.";
print "";

///////////////////////////////////////////////////////////////////////////
// 7. Cyclic quartic versus biquadratic extensions.
//
// By Galois correspondence, a C4-extension has exactly one quadratic
// subfield, while a V4-extension has exactly three.
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
print "Number of subgroups of order 2 in C4:", nC4;
print "Number of subgroups of order 2 in C2 x C2:", nV4;
print "";

print "============================================================";
print "ALL SUPPLEMENTARY GROUP CHECKS FOR LEMMA 6.3 PASSED.";
print "============================================================";
