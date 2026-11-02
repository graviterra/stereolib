import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace Rule3MolecularBondOrderFidelity

open ChemistryNormalizationResult




































/-! ## The two enumerations of one molecular bond multiset -/

/-- Atom list shared by both molecules.

```
        1 --- 2                 ring through the (non-tetrahedral) centre 0
         \   /
           0
          / \
         3   12          branch roots P and Q (P = 3, Q = 12)
         |    |
        ...  ...
```

Branch `P` carries two independent alkene units, `4=5` and `8=9`; branch `Q` carries the
isomorphic pair `13=14` and `17=18`.  Fluorines (6,7,10,11,15,16,19,20) make both ends of
every alkene chemically substituted, so each explicit `E/Z` assignment below is a genuine
alkene stereodescriptor rather than an uninterpreted triple. -/
def atoms : List AtomSpec :=
  [ { element := Element.C },  -- 0  centre (no tetrahedral annotation)
    { element := Element.C },  -- 1  ring
    { element := Element.C },  -- 2  ring
    { element := Element.C },  -- 3  branch root P
    { element := Element.C },  -- 4  P alkene endpoint, near
    { element := Element.C },  -- 5  P alkene endpoint, far
    { element := Element.F },  -- 6  substituent on 4
    { element := Element.F },  -- 7  substituent on 5
    { element := Element.C },  -- 8  P second alkene endpoint, near
    { element := Element.C },  -- 9  P second alkene endpoint, far
    { element := Element.F },  -- 10 substituent on 8
    { element := Element.F },  -- 11 substituent on 9
    { element := Element.C },  -- 12 branch root Q
    { element := Element.C },  -- 13 Q alkene endpoint, near
    { element := Element.C },  -- 14 Q alkene endpoint, far
    { element := Element.F },  -- 15 substituent on 13
    { element := Element.F },  -- 16 substituent on 14
    { element := Element.C },  -- 17 Q second alkene endpoint, near
    { element := Element.C },  -- 18 Q second alkene endpoint, far
    { element := Element.F },  -- 19 substituent on 17
    { element := Element.F } ] -- 20 substituent on 18

/-- One raw bond record. -/
def bond (source target : ℕ) (kind : ParsedBondKind) : RawBond :=
  { source := source, target := target, kind := kind }

/-- Bond enumeration A.

The two bonds out of `P` are listed `3-4` then `3-8`, and the two bonds out of `Q` are listed
`12-17` then `12-13`.  The breadth-first walk of `reachableAvoiding` follows exactly this list
order inside each layer. -/
def bondsA : List RawBond :=
  [ bond 0 1 ParsedBondKind.single,
    bond 1 2 ParsedBondKind.single,
    bond 2 0 ParsedBondKind.single,
    bond 0 3 ParsedBondKind.single,
    bond 0 12 ParsedBondKind.single,
    bond 3 4 ParsedBondKind.single,
    bond 3 8 ParsedBondKind.single,
    bond 4 5 ParsedBondKind.double,
    bond 4 6 ParsedBondKind.single,
    bond 5 7 ParsedBondKind.single,
    bond 8 9 ParsedBondKind.double,
    bond 8 10 ParsedBondKind.single,
    bond 9 11 ParsedBondKind.single,
    bond 12 17 ParsedBondKind.single,
    bond 12 13 ParsedBondKind.single,
    bond 13 14 ParsedBondKind.double,
    bond 13 15 ParsedBondKind.single,
    bond 14 16 ParsedBondKind.single,
    bond 17 18 ParsedBondKind.double,
    bond 17 19 ParsedBondKind.single,
    bond 18 20 ParsedBondKind.single ]

/-- Bond enumeration B.

This is literally the same list of bond records as `bondsA`; only the positions of the records
`3-4` / `3-8` and `12-13` / `12-17` are exchanged.  No atom, bond kind or bond endpoint changes. -/
def bondsB : List RawBond :=
  [ bond 0 1 ParsedBondKind.single,
    bond 1 2 ParsedBondKind.single,
    bond 2 0 ParsedBondKind.single,
    bond 0 3 ParsedBondKind.single,
    bond 0 12 ParsedBondKind.single,
    bond 3 8 ParsedBondKind.single,
    bond 3 4 ParsedBondKind.single,
    bond 4 5 ParsedBondKind.double,
    bond 4 6 ParsedBondKind.single,
    bond 5 7 ParsedBondKind.single,
    bond 8 9 ParsedBondKind.double,
    bond 8 10 ParsedBondKind.single,
    bond 9 11 ParsedBondKind.single,
    bond 12 13 ParsedBondKind.single,
    bond 12 17 ParsedBondKind.single,
    bond 13 14 ParsedBondKind.double,
    bond 13 15 ParsedBondKind.single,
    bond 14 16 ParsedBondKind.single,
    bond 17 18 ParsedBondKind.double,
    bond 17 19 ParsedBondKind.single,
    bond 18 20 ParsedBondKind.single ]

/-- Molecule A: atom list `atoms`, bond enumeration `bondsA`. -/
def molA : RawMolecule :=
  { atoms := atoms, bonds := bondsA }

/-- Molecule B: the same atom list, bond enumeration `bondsB`. -/
def molB : RawMolecule :=
  { atoms := atoms, bonds := bondsB }











def explicitStereo : StereobondSemantics where
  directionalBonds := []
  tetrahedralAtoms := []
  doubleBondAssignments :=
    [ (4, 5, DoubleBondStereo.Z),
      (8, 9, DoubleBondStereo.E),
      (13, 14, DoubleBondStereo.Z),
      (17, 18, DoubleBondStereo.E) ]

/-- The historical normalization result for A, with the common explicit stereo record. -/
def resultA : ChemistryNormalizationResult :=
  { (normalizeRawMolecule molA) with stereobonds := explicitStereo }

/-- The historical normalization result for B, with the common explicit stereo record. -/
def resultB : ChemistryNormalizationResult :=
  { (normalizeRawMolecule molB) with stereobonds := explicitStereo }

/-- Production analysis fuel for both molecules (identical atom counts). -/
def fuel : ℕ := analysisFuel molA

/-! ## The inputs are admitted and chemically identical -/

/-- Both molecules have the same atom list. -/
theorem atoms_agree : molA.atoms = molB.atoms := rfl

/-- Both molecules have the same number of atoms. -/
theorem atomCount_agree : molA.atomCount = molB.atomCount := rfl

/-- The two bond lists are permutations of the same records. -/
theorem bonds_perm : molA.bonds.Perm molB.bonds := by decide

/-- The two bond lists have the same entries, checked entry by entry as well. -/
theorem bonds_same_entries :
    molA.bonds.length = molB.bonds.length ∧
      molA.bonds.all (fun b => molB.bonds.contains b) = true ∧
      molB.bonds.all (fun b => molA.bonds.contains b) = true := by
  decide

/-- Molecule A passes the executable structural admission contract. -/
theorem molA_admissible : molA.admissible? = true := by decide

/-- Molecule B passes the executable structural admission contract. -/
theorem molB_admissible : molB.admissible? = true := by decide

/-- Molecule A also passes the stereochemical admission contract (exact written neighbours). -/
theorem molA_stereochemicalAdmissible : molA.stereochemicalAdmissible? = true := by decide

/-- Molecule B also passes the stereochemical admission contract (exact written neighbours). -/
theorem molB_stereochemicalAdmissible : molB.stereochemicalAdmissible? = true := by decide

/-- The stereo records handed to the Rule-3 path are identical. -/
theorem stereo_agree : resultA.stereobonds = resultB.stereobonds := rfl

/-- Both molecules have the same atom count, hence the same fuel. -/
theorem fuel_eq : fuel = analysisFuel molB := rfl

/-! ## The predecessor flat Rule-3 occurrences change -/

/-- Canonical Rule-3 occurrences of branch P in molecule A (flat diagnostic, retained
unchanged by the public repair).

The two units sit in the same breadth-first layer.  Their `distance` fields are the *list
indices* of the near endpoints (`4` before `8`), so the ascending distance sort places the
`Z` unit before the `E` unit. -/
theorem occurrencesA_P :
    canonicalRule3OccurrencesOnBranch resultA molA fuel 0 3 =
      [ { left := 4, right := 5, near := 4, distance := 1,
          geometry := OfficialRule3Geometry.seqcis },
        { left := 8, right := 9, near := 8, distance := 2,
          geometry := OfficialRule3Geometry.seqtrans } ] := by
  decide

/-- Canonical Rule-3 occurrences of branch P in molecule B.

Only the bond enumeration changed, yet the near endpoint `8` now has the smaller list index and
the sequence order is reversed. -/
theorem occurrencesB_P :
    canonicalRule3OccurrencesOnBranch resultB molB fuel 0 3 =
      [ { left := 8, right := 9, near := 8, distance := 1,
          geometry := OfficialRule3Geometry.seqtrans },
        { left := 4, right := 5, near := 4, distance := 2,
          geometry := OfficialRule3Geometry.seqcis } ] := by
  decide

/-- The canonical Rule-3 occurrence lists are not equal. -/
theorem canonicalOccurrences_differ :
    canonicalRule3OccurrencesOnBranch resultA molA fuel 0 3 ≠
      canonicalRule3OccurrencesOnBranch resultB molB fuel 0 3 := by
  decide

/-- In molecule A, branch Q (whose internal bonds were listed in the opposite relative order)
retains the opposite sequence. -/
theorem occurrencesA_Q :
    canonicalRule3OccurrencesOnBranch resultA molA fuel 0 12 =
      [ { left := 17, right := 18, near := 17, distance := 1,
          geometry := OfficialRule3Geometry.seqtrans },
        { left := 13, right := 14, near := 13, distance := 2,
          geometry := OfficialRule3Geometry.seqcis } ] := by
  decide

/-- In molecule B the Q sequence is reversed. -/
theorem occurrencesB_Q :
    canonicalRule3OccurrencesOnBranch resultB molB fuel 0 12 =
      [ { left := 13, right := 14, near := 13, distance := 1,
          geometry := OfficialRule3Geometry.seqcis },
        { left := 17, right := 18, near := 17, distance := 2,
          geometry := OfficialRule3Geometry.seqtrans } ] := by
  decide

/-- Canonical Rule-3 signature of P in A: `seqcis` (2) then `seqtrans` (1). -/
theorem signatureA_P : rule3CanonicalSignature resultA molA fuel 0 3 = [2, 1] := by
  decide

/-- Canonical Rule-3 signature of P in B: `seqtrans` (1) then `seqcis` (2). -/
theorem signatureB_P : rule3CanonicalSignature resultB molB fuel 0 3 = [1, 2] := by
  decide

/-- Canonical Rule-3 signature of Q in A is the reverse of P's. -/
theorem signatureA_Q : rule3CanonicalSignature resultA molA fuel 0 12 = [1, 2] := by
  decide

/-- Canonical Rule-3 signature of Q in B is the reverse of P's. -/
theorem signatureB_Q : rule3CanonicalSignature resultB molB fuel 0 12 = [2, 1] := by
  decide

/-- The unary canonical signature of the same physical branch changes under the bond-list
permutation.  This is the opponent-independent flat Rule-3 key itself, not a pairwise artefact.
It is a retained diagnostic of the predecessor algorithm. -/
theorem signature_depends_on_bond_order :
    rule3CanonicalSignature resultA molA fuel 0 3 ≠
      rule3CanonicalSignature resultB molB fuel 0 3 := by
  decide

/-! ## The predecessor `compareBranchesThroughRule3Legacy?` gate changes

The public repair keeps the old flat body under the name
`ChemistryNormalizationResult.compareBranchesThroughRule3Legacy?`.  All `gt` / `lt` assertions
in this section are scoped to that explicit legacy name.  They are statements about the
predecessor algorithm, not about the corrected public comparator. -/

/-- Legacy predecessor: in molecule A the two constitutionally identical branches P and Q are
ranked P above Q by the old flat Rule-3 gate. -/
theorem legacy_comparisonA_P_Q :
    compareBranchesThroughRule3Legacy? resultA molA fuel 0 3 12 = some Ordering.gt := by
  decide

/-- Historical name preserved as a legacy-scoped alias. -/
theorem comparisonA_P_Q :
    compareBranchesThroughRule3Legacy? resultA molA fuel 0 3 12 = some Ordering.gt :=
  legacy_comparisonA_P_Q

/-- Legacy predecessor: in molecule B the same pair is ranked the other way round by the old
flat Rule-3 gate. -/
theorem legacy_comparisonB_P_Q :
    compareBranchesThroughRule3Legacy? resultB molB fuel 0 3 12 = some Ordering.lt := by
  decide

/-- Historical name preserved as a legacy-scoped alias. -/
theorem comparisonB_P_Q :
    compareBranchesThroughRule3Legacy? resultB molB fuel 0 3 12 = some Ordering.lt :=
  legacy_comparisonB_P_Q

/-- Hence the predecessor flat Rule-3 comparison is not invariant under permutation of the
molecular bond list, even though atoms, bond multiset, bond kinds and stereo are unchanged.
This is a statement about `compareBranchesThroughRule3Legacy?` only. -/
theorem legacy_comparison_depends_on_bond_order :
    compareBranchesThroughRule3Legacy? resultA molA fuel 0 3 12 ≠
      compareBranchesThroughRule3Legacy? resultB molB fuel 0 3 12 := by
  decide

/-- Historical name preserved as a legacy-scoped alias. -/
theorem comparison_depends_on_bond_order :
    compareBranchesThroughRule3Legacy? resultA molA fuel 0 3 12 ≠
      compareBranchesThroughRule3Legacy? resultB molB fuel 0 3 12 :=
  legacy_comparison_depends_on_bond_order

/-! ## Kernel-authority guards -/

assert_kernel_only atoms_agree
assert_kernel_only atomCount_agree
assert_kernel_only bonds_perm
assert_kernel_only bonds_same_entries
assert_kernel_only molA_admissible
assert_kernel_only molB_admissible
assert_kernel_only molA_stereochemicalAdmissible
assert_kernel_only molB_stereochemicalAdmissible
assert_kernel_only stereo_agree
assert_kernel_only fuel_eq
assert_kernel_only occurrencesA_P
assert_kernel_only occurrencesB_P
assert_kernel_only canonicalOccurrences_differ
assert_kernel_only occurrencesA_Q
assert_kernel_only occurrencesB_Q
assert_kernel_only signatureA_P
assert_kernel_only signatureB_P
assert_kernel_only signatureA_Q
assert_kernel_only signatureB_Q
assert_kernel_only signature_depends_on_bond_order
assert_kernel_only legacy_comparisonA_P_Q
assert_kernel_only comparisonA_P_Q
assert_kernel_only legacy_comparisonB_P_Q
assert_kernel_only comparisonB_P_Q
assert_kernel_only legacy_comparison_depends_on_bond_order
assert_kernel_only comparison_depends_on_bond_order

end Rule3MolecularBondOrderFidelity
end OneCenter
end TetraStereo
