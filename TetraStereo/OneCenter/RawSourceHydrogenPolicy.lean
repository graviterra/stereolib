import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

/-!
# Source hydrogen policies for raw molecules

A `ParsedBondKind.unspecified` edge has bond order one (`ParsedBondKind.order`), exactly as it is
counted by `RawMolecule.incidentBondOrderSum`.  `freezeSourceHydrogenCounts` reads
`mol.hydrogenCountAt` on the graph it is handed and stores that exact count in every atom's
`explicitHydrogens?` field.  It performs no bond normalization of its own.

Consequently the frozen count is the count implied by the *supplied* bond orders:

* To freeze the count written in the source, call this function on the parser graph **before** any
  order-changing normalization.  The repository's P-93 quotient, for example, lowers oxo multiple
  bonds and therefore changes the count that `hydrogenCountAt` would report afterwards.
* The default-bond normalizer `normalizeUnspecifiedBonds` preserves every bond order
  (`normalizeUnspecifiedBond_order`), so freezing before or after *that* normalizer agrees on the
  hydrogen count; the compatibility lemma is recorded below.
* Freezing is a pure copy of the source count.  It neither checks nor establishes valence validity:
  the frozen `usedValenceAt` is exactly the frozen count plus the unchanged source bond-order sum,
  and no `ValenceOK` conclusion is exported.  Valence acceptance remains a separate obligation.

The function changes only the atom hydrogen policy.  Atom count, element, isotope, charge,
aromaticity, input parity, bond records, written-neighbour order, and source-introduction history
are preserved, so structural admission (`Admissible`), the exact written-neighbour view
(`WrittenNeighborExact`), and the combined stereochemical admission predicate are preserved.
-/

/-! ## Definition -/

/-- Index-aware map that replaces each atom's implicit/inline hydrogen policy by the exact total
hydrogen count computed on the source graph `mol`. -/
def freezeSourceHydrogenCountsAux (mol : RawMolecule) : Nat → List AtomSpec → List AtomSpec
  | _, [] => []
  | index, atom :: rest =>
      { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) } ::
        freezeSourceHydrogenCountsAux mol (index + 1) rest

/-- Freeze every atom's source hydrogen count.  Only the hydrogen policy changes; the atom
inventory, elements, isotopes, charges, parities, bonds, neighbour order, and introduction
predecessors are untouched. -/
def freezeSourceHydrogenCounts (mol : RawMolecule) : RawMolecule :=
  { mol with atoms := freezeSourceHydrogenCountsAux mol 0 mol.atoms }

/-! ## Direct field invariants -/

@[simp] theorem freezeSourceHydrogenCounts_atoms (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).atoms =
      freezeSourceHydrogenCountsAux mol 0 mol.atoms := rfl

@[simp] theorem freezeSourceHydrogenCounts_bonds (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).bonds = mol.bonds := rfl

@[simp] theorem freezeSourceHydrogenCounts_neighborOrder (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).neighborOrder = mol.neighborOrder := rfl

@[simp] theorem freezeSourceHydrogenCounts_introductionPredecessors (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).introductionPredecessors =
      mol.introductionPredecessors := rfl

@[simp] theorem length_freezeSourceHydrogenCountsAux (mol : RawMolecule) (offset : Nat)
    (atoms : List AtomSpec) :
    (freezeSourceHydrogenCountsAux mol offset atoms).length = atoms.length := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp [freezeSourceHydrogenCountsAux, ih]

/-- The atom count is unchanged. -/
@[simp] theorem freezeSourceHydrogenCounts_atomCount (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).atomCount = mol.atomCount := by
  simp [RawMolecule.atomCount, freezeSourceHydrogenCounts]

/-! ## Pointwise atom lookup -/

theorem listGet?_freezeSourceHydrogenCountsAux (mol : RawMolecule) (offset : Nat)
    (atoms : List AtomSpec) (index : Nat) :
    listGet? (freezeSourceHydrogenCountsAux mol offset atoms) index =
      (listGet? atoms index).map
        (fun atom =>
          { atom with explicitHydrogens? := some (mol.hydrogenCountAt (offset + index)) }) := by
  induction atoms generalizing offset index with
  | nil => simp [freezeSourceHydrogenCountsAux, listGet?]
  | cons atom rest ih =>
      cases index with
      | zero => simp [freezeSourceHydrogenCountsAux, listGet?]
      | succ index =>
          simpa [freezeSourceHydrogenCountsAux, listGet?, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (offset + 1) index

@[simp] theorem freezeSourceHydrogenCounts_atomAt? (mol : RawMolecule) (index : Nat) :
    (freezeSourceHydrogenCounts mol).atomAt? index =
      (mol.atomAt? index).map
        (fun atom => { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) }) := by
  simp [RawMolecule.atomAt?, freezeSourceHydrogenCounts, listGet?_freezeSourceHydrogenCountsAux]

/-- At a real atom, the frozen lookup is the source specification with its hydrogen policy
replaced by the exact source count. -/
theorem freezeSourceHydrogenCounts_atomAt?_spec (mol : RawMolecule) (index : Nat)
    (atom : AtomSpec) (lookup : mol.atomAt? index = some atom) :
    (freezeSourceHydrogenCounts mol).atomAt? index =
      some { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) } := by
  rw [freezeSourceHydrogenCounts_atomAt?, lookup]
  rfl

/-! ### Element, isotope, charge, aromaticity, and input parity -/

@[simp] theorem freezeSourceHydrogenCounts_atomAt?_element (mol : RawMolecule) (index : Nat) :
    ((freezeSourceHydrogenCounts mol).atomAt? index).map AtomSpec.element =
      (mol.atomAt? index).map AtomSpec.element := by
  rw [freezeSourceHydrogenCounts_atomAt?]
  cases mol.atomAt? index with
  | none => rfl
  | some atom => rfl

@[simp] theorem freezeSourceHydrogenCounts_atomAt?_isotope (mol : RawMolecule) (index : Nat) :
    ((freezeSourceHydrogenCounts mol).atomAt? index).map AtomSpec.isotope? =
      (mol.atomAt? index).map AtomSpec.isotope? := by
  rw [freezeSourceHydrogenCounts_atomAt?]
  cases mol.atomAt? index with
  | none => rfl
  | some atom => rfl

@[simp] theorem freezeSourceHydrogenCounts_atomAt?_charge (mol : RawMolecule) (index : Nat) :
    ((freezeSourceHydrogenCounts mol).atomAt? index).map AtomSpec.charge =
      (mol.atomAt? index).map AtomSpec.charge := by
  rw [freezeSourceHydrogenCounts_atomAt?]
  cases mol.atomAt? index with
  | none => rfl
  | some atom => rfl

@[simp] theorem freezeSourceHydrogenCounts_atomAt?_aromatic (mol : RawMolecule) (index : Nat) :
    ((freezeSourceHydrogenCounts mol).atomAt? index).map AtomSpec.aromatic =
      (mol.atomAt? index).map AtomSpec.aromatic := by
  rw [freezeSourceHydrogenCounts_atomAt?]
  cases mol.atomAt? index with
  | none => rfl
  | some atom => rfl

/-- Tetrahedral input parity is preserved at every index. -/
@[simp] theorem freezeSourceHydrogenCounts_atomAt?_tetrahedral (mol : RawMolecule) (index : Nat) :
    ((freezeSourceHydrogenCounts mol).atomAt? index).map AtomSpec.tetrahedral? =
      (mol.atomAt? index).map AtomSpec.tetrahedral? := by
  rw [freezeSourceHydrogenCounts_atomAt?]
  cases mol.atomAt? index with
  | none => rfl
  | some atom => rfl

/-- The frozen hydrogen policy at every index is exactly the source hydrogen count. -/
@[simp] theorem freezeSourceHydrogenCounts_atomAt?_explicitHydrogens? (mol : RawMolecule)
    (index : Nat) :
    ((freezeSourceHydrogenCounts mol).atomAt? index).bind AtomSpec.explicitHydrogens? =
      (mol.atomAt? index).map (fun _ => mol.hydrogenCountAt index) := by
  rw [freezeSourceHydrogenCounts_atomAt?]
  cases mol.atomAt? index with
  | none => rfl
  | some atom => rfl

/-! ## Exact source hydrogen count -/

/-- An atom whose stored explicit policy is `some count` reports exactly `count` hydrogens. -/
theorem hydrogenCountAt_of_explicitHydrogens?_some (mol : RawMolecule) (index count : Nat)
    (atom : AtomSpec) (lookup : mol.atomAt? index = some atom)
    (explicit : atom.explicitHydrogens? = some count) :
    mol.hydrogenCountAt index = count := by
  simp [RawMolecule.hydrogenCountAt, lookup, explicit]

/-- An absent atom reports zero hydrogens. -/
@[simp] theorem hydrogenCountAt_of_atomAt?_eq_none (mol : RawMolecule) (index : Nat)
    (lookup : mol.atomAt? index = none) :
    mol.hydrogenCountAt index = 0 := by
  simp [RawMolecule.hydrogenCountAt, lookup]

/-- Freezing preserves the exact source hydrogen count at every index, including indices past the
end of the molecule (both sides are then zero). -/
theorem freezeSourceHydrogenCounts_hydrogenCountAt (mol : RawMolecule) (index : Nat) :
    (freezeSourceHydrogenCounts mol).hydrogenCountAt index = mol.hydrogenCountAt index := by
  cases lookup : mol.atomAt? index with
  | none =>
      have frozenLookup : (freezeSourceHydrogenCounts mol).atomAt? index = none := by
        rw [freezeSourceHydrogenCounts_atomAt?, lookup]
        rfl
      rw [hydrogenCountAt_of_atomAt?_eq_none _ index frozenLookup,
        hydrogenCountAt_of_atomAt?_eq_none mol index lookup]
  | some atom =>
      have frozenLookup : (freezeSourceHydrogenCounts mol).atomAt? index =
          some { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) } :=
        freezeSourceHydrogenCounts_atomAt?_spec mol index atom lookup
      rw [hydrogenCountAt_of_explicitHydrogens?_some _ index (mol.hydrogenCountAt index) _
        frozenLookup rfl]

/-! ## Bond, neighbour, and introduction invariants -/

@[simp] theorem freezeSourceHydrogenCounts_incidentBondOrderSum (mol : RawMolecule)
    (index : Nat) :
    (freezeSourceHydrogenCounts mol).incidentBondOrderSum index =
      mol.incidentBondOrderSum index := by
  simp [RawMolecule.incidentBondOrderSum]

@[simp] theorem freezeSourceHydrogenCounts_directedBondOrder (mol : RawMolecule) (u v : Nat) :
    (freezeSourceHydrogenCounts mol).directedBondOrder u v = mol.directedBondOrder u v := by
  simp [RawMolecule.directedBondOrder]

@[simp] theorem freezeSourceHydrogenCounts_bondOrder (mol : RawMolecule) (u v : Nat) :
    (freezeSourceHydrogenCounts mol).bondOrder u v = mol.bondOrder u v := by
  simp [RawMolecule.bondOrder]

/-- The written OpenSMILES neighbour order is unchanged at every atom. -/
@[simp] theorem freezeSourceHydrogenCounts_writtenNeighbors (mol : RawMolecule) (index : Nat) :
    (freezeSourceHydrogenCounts mol).writtenNeighbors index = mol.writtenNeighbors index := by
  simp [RawMolecule.writtenNeighbors]

@[simp] theorem freezeSourceHydrogenCounts_introductionPredecessorsValid? (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).introductionPredecessorsValid? =
      mol.introductionPredecessorsValid? := by
  simp [RawMolecule.introductionPredecessorsValid?]

@[simp] theorem freezeSourceHydrogenCounts_parserIntroductionValid? (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).parserIntroductionValid? =
      mol.parserIntroductionValid? := by
  simp [RawMolecule.parserIntroductionValid?]

/-! ## Structural admission -/

@[simp] theorem freezeSourceHydrogenCounts_bondEndpointsOK_iff (mol : RawMolecule)
    (bond : RawBond) :
    (freezeSourceHydrogenCounts mol).BondEndpointsOK bond ↔ mol.BondEndpointsOK bond := by
  simp [RawMolecule.BondEndpointsOK]

@[simp] theorem freezeSourceHydrogenCounts_admissible_iff (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).Admissible ↔ mol.Admissible := by
  simp [RawMolecule.Admissible, RawMolecule.WellFormed, RawMolecule.BondRecordsUnique]

/-- Freezing preserves `Admissible`. -/
theorem freezeSourceHydrogenCounts_admissible (mol : RawMolecule) (admissible : mol.Admissible) :
    (freezeSourceHydrogenCounts mol).Admissible :=
  (freezeSourceHydrogenCounts_admissible_iff mol).mpr admissible

@[simp] theorem freezeSourceHydrogenCounts_writtenNeighborExact? (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).writtenNeighborExact? = mol.writtenNeighborExact? := by
  unfold RawMolecule.writtenNeighborExact?
  simp only [freezeSourceHydrogenCounts_atomCount, freezeSourceHydrogenCounts_writtenNeighbors,
    freezeSourceHydrogenCounts_bondOrder]

@[simp] theorem freezeSourceHydrogenCounts_writtenNeighborExact_iff (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).WrittenNeighborExact ↔ mol.WrittenNeighborExact := by
  unfold RawMolecule.WrittenNeighborExact
  rw [freezeSourceHydrogenCounts_writtenNeighborExact?]

/-- Freezing preserves the exact written-neighbour view. -/
theorem freezeSourceHydrogenCounts_writtenNeighborExact (mol : RawMolecule)
    (exact : mol.WrittenNeighborExact) :
    (freezeSourceHydrogenCounts mol).WrittenNeighborExact :=
  (freezeSourceHydrogenCounts_writtenNeighborExact_iff mol).mpr exact

@[simp] theorem freezeSourceHydrogenCounts_stereochemicalAdmissible_iff (mol : RawMolecule) :
    (freezeSourceHydrogenCounts mol).StereochemicalAdmissible ↔
      mol.StereochemicalAdmissible := by
  unfold RawMolecule.StereochemicalAdmissible
  rw [freezeSourceHydrogenCounts_admissible_iff,
    freezeSourceHydrogenCounts_writtenNeighborExact_iff]

/-- Freezing preserves the combined stereochemical intake predicate. -/
theorem freezeSourceHydrogenCounts_stereochemicalAdmissible (mol : RawMolecule)
    (admissible : mol.StereochemicalAdmissible) :
    (freezeSourceHydrogenCounts mol).StereochemicalAdmissible :=
  (freezeSourceHydrogenCounts_stereochemicalAdmissible_iff mol).mpr admissible

/-! ## Valence is copied, not established -/

/-- The frozen valence demand at a real atom is exactly the frozen source hydrogen count plus the
unchanged source bond-order sum.  This is a copying equation, not a valence-validity claim. -/
theorem freezeSourceHydrogenCounts_usedValenceAt_eq (mol : RawMolecule) (index : Nat)
    (atom : AtomSpec) (lookup : mol.atomAt? index = some atom) :
    (freezeSourceHydrogenCounts mol).usedValenceAt index =
      mol.hydrogenCountAt index + mol.incidentBondOrderSum index := by
  have frozenLookup : (freezeSourceHydrogenCounts mol).atomAt? index =
      some { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) } :=
    freezeSourceHydrogenCounts_atomAt?_spec mol index atom lookup
  simp [RawMolecule.usedValenceAt, frozenLookup, AtomSpec.explicitHydrogens]

/-! ## Unspecified-bond normalization caveat

`hydrogenCountAt` counts a `ParsedBondKind.unspecified` bond through
`ParsedBondKind.order = 1`.  The repository's `normalizeUnspecifiedBonds` rewrites only the bond
kind and preserves that order, so it commutes with freezing at the level of hydrogen counts.  Any
normalization that *changes* bond orders does not, and must be applied after freezing if the
written source count is the intended datum. -/

@[simp] theorem normalizeUnspecifiedBonds_incidentBondOrderSum (mol : RawMolecule) (index : Nat) :
    mol.normalizeUnspecifiedBonds.incidentBondOrderSum index =
      mol.incidentBondOrderSum index := by
  simp only [RawMolecule.incidentBondOrderSum, RawMolecule.normalizeUnspecifiedBonds]
  rw [List.foldl_map]
  simp

/-- Unspecified-bond default normalization preserves the implied hydrogen count. -/
@[simp] theorem normalizeUnspecifiedBonds_hydrogenCountAt (mol : RawMolecule) (index : Nat) :
    mol.normalizeUnspecifiedBonds.hydrogenCountAt index = mol.hydrogenCountAt index := by
  simp [RawMolecule.hydrogenCountAt, RawMolecule.atomAt?]

/-- Freezing the default-normalized graph and freezing the source graph agree on every hydrogen
count. -/
theorem freezeSourceHydrogenCounts_normalizeUnspecifiedBonds_hydrogenCountAt
    (mol : RawMolecule) (index : Nat) :
    (freezeSourceHydrogenCounts mol.normalizeUnspecifiedBonds).hydrogenCountAt index =
      (freezeSourceHydrogenCounts mol).hydrogenCountAt index := by
  rw [freezeSourceHydrogenCounts_hydrogenCountAt, freezeSourceHydrogenCounts_hydrogenCountAt,
    normalizeUnspecifiedBonds_hydrogenCountAt]

/-! ## Kernel-authority guards -/

assert_kernel_only freezeSourceHydrogenCounts_atoms
assert_kernel_only freezeSourceHydrogenCounts_bonds
assert_kernel_only freezeSourceHydrogenCounts_neighborOrder
assert_kernel_only freezeSourceHydrogenCounts_introductionPredecessors
assert_kernel_only length_freezeSourceHydrogenCountsAux
assert_kernel_only freezeSourceHydrogenCounts_atomCount
assert_kernel_only listGet?_freezeSourceHydrogenCountsAux
assert_kernel_only freezeSourceHydrogenCounts_atomAt?
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_spec
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_element
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_isotope
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_charge
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_aromatic
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_tetrahedral
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_explicitHydrogens?
assert_kernel_only hydrogenCountAt_of_explicitHydrogens?_some
assert_kernel_only hydrogenCountAt_of_atomAt?_eq_none
assert_kernel_only freezeSourceHydrogenCounts_hydrogenCountAt
assert_kernel_only freezeSourceHydrogenCounts_incidentBondOrderSum
assert_kernel_only freezeSourceHydrogenCounts_directedBondOrder
assert_kernel_only freezeSourceHydrogenCounts_bondOrder
assert_kernel_only freezeSourceHydrogenCounts_writtenNeighbors
assert_kernel_only freezeSourceHydrogenCounts_introductionPredecessorsValid?
assert_kernel_only freezeSourceHydrogenCounts_parserIntroductionValid?
assert_kernel_only freezeSourceHydrogenCounts_bondEndpointsOK_iff
assert_kernel_only freezeSourceHydrogenCounts_admissible_iff
assert_kernel_only freezeSourceHydrogenCounts_admissible
assert_kernel_only freezeSourceHydrogenCounts_writtenNeighborExact?
assert_kernel_only freezeSourceHydrogenCounts_writtenNeighborExact_iff
assert_kernel_only freezeSourceHydrogenCounts_writtenNeighborExact
assert_kernel_only freezeSourceHydrogenCounts_stereochemicalAdmissible_iff
assert_kernel_only freezeSourceHydrogenCounts_stereochemicalAdmissible
assert_kernel_only freezeSourceHydrogenCounts_usedValenceAt_eq
assert_kernel_only normalizeUnspecifiedBonds_incidentBondOrderSum
assert_kernel_only normalizeUnspecifiedBonds_hydrogenCountAt
assert_kernel_only freezeSourceHydrogenCounts_normalizeUnspecifiedBonds_hydrogenCountAt

end RawMolecule
end OneCenter
end TetraStereo
