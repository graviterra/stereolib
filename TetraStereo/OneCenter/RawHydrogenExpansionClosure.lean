import TetraStereo.OneCenter.RawIntakeMaterializationFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TetraStereo
namespace OneCenter
namespace RawHydrogenExpansionClosure

open RawMolecule

/-!
# Closure of raw hydrogen expansion

`RawMolecule.HydrogenClosed` (defined in `RawIntakeMaterializationFidelity`) is the exact domain on
which `withExplicitHydrogens` inserts no atom.  That module proves the structural consequences of
closure but assumes the domain: its bridge theorems take `molecule.HydrogenClosed` as a hypothesis.

This module proves the missing source-to-output half for the actual production definition, with no
input-domain hypothesis, no validity/admissibility hypothesis and no output-readiness hypothesis:

`hydrogenClosed_withExplicitHydrogens : ∀ mol, mol.withExplicitHydrogens.HydrogenClosed`.

The proof tracks the real expansion fold, not an idealised description of it:

* at every original index the accumulator atom is `materializedAtomSpec spec`, whose inline count is
  `some 0`, so `hydrogenCountAt` is `0` (`hydrogenCountAt_withExplicitHydrogens_of_lt`);
* every index past the original atom count that exists in the accumulator was appended by some step,
  hence is `AtomSpec.aliphatic Element.H` (`fold_atomAt?_eq_hydrogen_of_le`);
* that step also emitted a single bond targeting the appended index, and splicing only permutes the
  bond list, so the appended hydrogen has positive incident bond order
  (`fold_fresh_atom_has_incident_bond`).  A hydrogen atom with positive incident order receives a
  fill count of zero, whether the used order is exactly one or already larger than hydrogen's only
  default valence (`hydrogenCountAt_eq_zero_of_aliphatic_hydrogen`).

No well-formedness is needed.  In particular `MaterializedValenceInvariant.freshAtom` — which asks
for incident order *exactly* one — is **not** available for arbitrary raw records: a malformed input
may carry a bond whose endpoint already names a future hydrogen index, giving that fresh hydrogen
incident order two.  Closure nevertheless holds, because any positive incident order yields count
zero.  The invariant's exact-one form is only needed where the existing `ValenceOK` preservation
theorem uses it.

For reviewers who require the guarded contract, `hydrogenClosed_withExplicitHydrogens_of_wellFormed`
states `(well : mol.WellFormed) → mol.withExplicitHydrogens.HydrogenClosed` and proves it through the
existing `fold_withExplicitHydrogensStep_preserves_materializedValenceInvariant`; the unconditional
theorem below is stronger and does not depend on that route.

## What this does and does not say

The second-expansion lemmas at the end read the closure result through the existing
`HydrogenClosed` API: applying `withExplicitHydrogens` a second time leaves the bond list and atom
count unchanged and leaves `toSemanticMolecule?` unchanged.

The raw *record* is nevertheless not idempotent.  The second expansion still materialises every
atom, so a fresh appended hydrogen (`explicitHydrogens? = none`) is rewritten to
`explicitHydrogens? = some 0`; `materializedAtomSpec_aliphatic_hydrogen_ne` records that this is a
genuine change.  Accordingly no raw-record equality is stated or used here: the second expansion's
atoms are the first expansion's atoms mapped by `materializedAtomSpec`.
-/

/-! ## Atom bookkeeping across one expansion step -/

/-- One step appends exactly `mol.hydrogenCountAt idx` atoms. -/
theorem withExplicitHydrogensStep_atomCount (mol : RawMolecule)
    (state : HydrogenExpansionState) (idx : ℕ) :
    (withExplicitHydrogensStep mol state idx).toRawMolecule.atomCount =
      state.toRawMolecule.atomCount + mol.hydrogenCountAt idx := by
  show (withExplicitHydrogensStep mol state idx).toRawMolecule.atoms.length =
    state.toRawMolecule.atoms.length + mol.hydrogenCountAt idx
  rw [RawIntakeMaterializationCounterexample.withExplicitHydrogensStep_atoms_eq]
  simp [List.length_append]

/-- A step leaves every index below the old atom count untouched. -/
theorem withExplicitHydrogensStep_atomAt?_of_lt (mol : RawMolecule)
    (state : HydrogenExpansionState) (idx atomIndex : ℕ)
    (bound : atomIndex < state.toRawMolecule.atomCount) :
    (withExplicitHydrogensStep mol state idx).toRawMolecule.atomAt? atomIndex =
      state.toRawMolecule.atomAt? atomIndex := by
  simp only [withExplicitHydrogensStep]
  split
  · rfl
  · dsimp only [HydrogenExpansionState.toRawMolecule, atomAt?]
    exact listGet?_append_left_of_lt state.1 _ atomIndex (by
      simpa [atomCount, HydrogenExpansionState.toRawMolecule] using bound)

/-- A fold of steps leaves every index below the current atom count untouched. -/
theorem fold_atomAt?_of_lt (mol : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState) :
    ∀ atomIndex, atomIndex < state.toRawMolecule.atomCount →
      (indices.foldl (withExplicitHydrogensStep mol) state).toRawMolecule.atomAt? atomIndex =
        state.toRawMolecule.atomAt? atomIndex := by
  induction indices generalizing state with
  | nil => intro atomIndex _bound; rfl
  | cons idx rest ih =>
      intro atomIndex bound
      rw [List.foldl_cons]
      rw [ih (withExplicitHydrogensStep mol state idx) atomIndex (by
        rw [withExplicitHydrogensStep_atomCount]
        omega)]
      exact withExplicitHydrogensStep_atomAt?_of_lt mol state idx atomIndex bound

/-- The initial accumulator starts from the materialised source atoms. -/
theorem initialHydrogenExpansionState_atomAt? (mol : RawMolecule) (atomIndex : ℕ) :
    (initialHydrogenExpansionState mol).toRawMolecule.atomAt? atomIndex =
      (mol.atomAt? atomIndex).map materializedAtomSpec := by
  simp [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule, atomAt?,
    listGet?_map]

/-- On an original atom, the actual expanded molecule holds the materialised source atom. -/
theorem withExplicitHydrogens_atomAt?_of_lt (mol : RawMolecule) (atomIndex : ℕ)
    (bound : atomIndex < mol.atomCount) :
    mol.withExplicitHydrogens.atomAt? atomIndex =
      (mol.atomAt? atomIndex).map materializedAtomSpec := by
  have foldBound : atomIndex < (initialHydrogenExpansionState mol).toRawMolecule.atomCount := by
    simpa using bound
  have expandedLookup :
      mol.withExplicitHydrogens.atomAt? atomIndex =
        ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
          (initialHydrogenExpansionState mol)).toRawMolecule.atomAt? atomIndex := by
    simp only [atomAt?]
    rw [withExplicitHydrogens_atoms_eq_fold]
  rw [expandedLookup,
    fold_atomAt?_of_lt mol (List.range mol.atomCount) (initialHydrogenExpansionState mol)
      atomIndex foldBound]
  exact initialHydrogenExpansionState_atomAt? mol atomIndex

/-- At an original index the expanded atom carries inline count `some 0`, so its hydrogen count is
zero irrespective of the bonding around it. -/
theorem hydrogenCountAt_withExplicitHydrogens_of_lt (mol : RawMolecule) (atomIndex : ℕ)
    (original : atomIndex < mol.atomCount) :
    mol.withExplicitHydrogens.hydrogenCountAt atomIndex = 0 := by
  obtain ⟨spec, specLookup⟩ := listGet?_exists_of_lt mol.atoms atomIndex original
  have sourceLookup : mol.atomAt? atomIndex = some spec := by
    simpa [atomAt?] using specLookup
  have expandedLookup : mol.withExplicitHydrogens.atomAt? atomIndex =
      some (materializedAtomSpec spec) := by
    rw [withExplicitHydrogens_atomAt?_of_lt mol atomIndex original, sourceLookup]
    rfl
  unfold RawMolecule.hydrogenCountAt
  rw [expandedLookup]
  simp [materializedAtomSpec]

/-! ## Fresh indices are hydrogens -/

/-- Every index at or beyond the current atom count that the fold can observe was appended by one
of the steps, and every appended atom is an ordinary aliphatic hydrogen. -/
theorem fold_atomAt?_eq_hydrogen_of_le (mol : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState) :
    ∀ atomIndex atom, state.toRawMolecule.atomCount ≤ atomIndex →
      (indices.foldl (withExplicitHydrogensStep mol) state).toRawMolecule.atomAt? atomIndex =
        some atom →
      atom = AtomSpec.aliphatic Element.H := by
  induction indices generalizing state with
  | nil =>
      intro atomIndex atom lower lookup
      have upper : atomIndex < state.toRawMolecule.atomCount :=
        listGet?_eq_some_implies_lt state.1 atomIndex atom (by
          simpa [atomAt?, HydrogenExpansionState.toRawMolecule] using lookup)
      exfalso
      omega
  | cons idx rest ih =>
      intro atomIndex atom lower lookup
      by_cases within :
          atomIndex < (withExplicitHydrogensStep mol state idx).toRawMolecule.atomCount
      · have foldEq :
            (rest.foldl (withExplicitHydrogensStep mol)
              (withExplicitHydrogensStep mol state idx)).toRawMolecule.atomAt? atomIndex =
              (withExplicitHydrogensStep mol state idx).toRawMolecule.atomAt? atomIndex :=
          fold_atomAt?_of_lt mol rest (withExplicitHydrogensStep mol state idx) atomIndex within
        have stepLookup :
            (withExplicitHydrogensStep mol state idx).toRawMolecule.atomAt? atomIndex =
              some atom := by
          rw [← foldEq]
          simpa only [List.foldl_cons] using lookup
        have atomsEq :=
          RawIntakeMaterializationCounterexample.withExplicitHydrogensStep_atoms_eq mol state idx
        have lowerBound : state.1.length ≤ atomIndex := by
          simpa [atomCount, HydrogenExpansionState.toRawMolecule] using lower
        have stepBound :
            atomIndex < (state.1 ++ List.replicate (mol.hydrogenCountAt idx)
              (AtomSpec.aliphatic Element.H)).length := by
          have observed := within
          change atomIndex <
            (withExplicitHydrogensStep mol state idx).toRawMolecule.atoms.length at observed
          rw [atomsEq] at observed
          simpa [HydrogenExpansionState.toRawMolecule] using observed
        have offsetBound : atomIndex - state.1.length < mol.hydrogenCountAt idx := by
          simp only [List.length_append, List.length_replicate] at stepBound
          omega
        have appendLookup :
            listGet? (state.1 ++ List.replicate (mol.hydrogenCountAt idx)
              (AtomSpec.aliphatic Element.H)) atomIndex = some atom := by
          have observed := stepLookup
          change listGet? (withExplicitHydrogensStep mol state idx).toRawMolecule.atoms
            atomIndex = some atom at observed
          rw [atomsEq] at observed
          simpa [HydrogenExpansionState.toRawMolecule] using observed
        rw [listGet?_append_right_of_length_le state.1 _ atomIndex lowerBound,
          listGet?_eq_getElem?, List.getElem?_replicate_of_lt offsetBound] at appendLookup
        exact (Option.some.inj appendLookup).symm
      · exact ih (withExplicitHydrogensStep mol state idx) atomIndex atom
          (Nat.le_of_not_gt within) (by simpa only [List.foldl_cons] using lookup)

/-! ## Fresh indices carry a generated bond -/

/-- An old bond survives one expansion step: splicing only permutes the old bond list. -/
theorem withExplicitHydrogensStep_old_bond_mem (mol : RawMolecule)
    (state : HydrogenExpansionState) (idx : ℕ) (bond : RawBond)
    (member : bond ∈ state.toRawMolecule.bonds) :
    bond ∈ (withExplicitHydrogensStep mol state idx).toRawMolecule.bonds := by
  simp only [withExplicitHydrogensStep]
  split
  · exact member
  · dsimp only [HydrogenExpansionState.toRawMolecule]
    let count := mol.hydrogenCountAt idx
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun target => base + target
    let newBonds := hydrogenIds.map fun target =>
      { source := idx, target := target, kind := ParsedBondKind.single : RawBond }
    have permuted :
        (spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[idx]?) state.2.1 idx
          newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    exact permuted.mem_iff.mpr (List.mem_append_left newBonds member)

/-- The single bond emitted for a fresh hydrogen is present after the step. -/
theorem withExplicitHydrogensStep_new_bond_mem (mol : RawMolecule)
    (state : HydrogenExpansionState) (idx offset : ℕ)
    (offsetBound : offset < mol.hydrogenCountAt idx) :
    (⟨idx, state.1.length + offset, ParsedBondKind.single⟩ : RawBond) ∈
      (withExplicitHydrogensStep mol state idx).toRawMolecule.bonds := by
  by_cases zero : mol.hydrogenCountAt idx == 0
  · have countZero : mol.hydrogenCountAt idx = 0 := by simpa using zero
    exfalso
    omega
  · let count := mol.hydrogenCountAt idx
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun target => base + target
    let newBonds := hydrogenIds.map fun target =>
      (⟨idx, target, ParsedBondKind.single⟩ : RawBond)
    have permuted :
        (spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[idx]?) state.2.1 idx
          newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    have hydrogenMember : base + offset ∈ hydrogenIds :=
      List.mem_map.mpr ⟨offset, List.mem_range.mpr (by simpa [count] using offsetBound), rfl⟩
    have newMember : (⟨idx, base + offset, ParsedBondKind.single⟩ : RawBond) ∈ newBonds :=
      List.mem_map.mpr ⟨base + offset, hydrogenMember, rfl⟩
    have spliced := permuted.mem_iff.mpr (List.mem_append_right state.2.1 newMember)
    simpa [withExplicitHydrogensStep, zero, count, base, hydrogenIds, newBonds] using spliced

/-- Old bonds survive a whole fold. -/
theorem fold_withExplicitHydrogensStep_bonds_mem (mol : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState) (bond : RawBond)
    (member : bond ∈ state.toRawMolecule.bonds) :
    bond ∈ (indices.foldl (withExplicitHydrogensStep mol) state).toRawMolecule.bonds := by
  induction indices generalizing state with
  | nil => exact member
  | cons idx rest ih =>
      rw [List.foldl_cons]
      exact ih (withExplicitHydrogensStep mol state idx)
        (withExplicitHydrogensStep_old_bond_mem mol state idx bond member)

/-- Every fresh index in the folded accumulator is the target of a bond whose order is at least
one.  No well-formedness is assumed: generated bonds alone supply the positive contribution, and a
malformed old bond can only add to it. -/
theorem fold_fresh_atom_has_incident_bond (mol : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState) :
    ∀ atomIndex, state.toRawMolecule.atomCount ≤ atomIndex →
      atomIndex < (indices.foldl (withExplicitHydrogensStep mol) state).toRawMolecule.atomCount →
      ∃ bond, bond ∈ (indices.foldl (withExplicitHydrogensStep mol) state).toRawMolecule.bonds ∧
        (bond.source = atomIndex ∨ bond.target = atomIndex) ∧ 1 ≤ bond.kind.order := by
  induction indices generalizing state with
  | nil =>
      intro atomIndex lower upper
      exfalso
      have upper' : atomIndex < state.toRawMolecule.atomCount := by simpa using upper
      omega
  | cons idx rest ih =>
      intro atomIndex lower upper
      by_cases within :
          atomIndex < (withExplicitHydrogensStep mol state idx).toRawMolecule.atomCount
      · let base := state.1.length
        let count := mol.hydrogenCountAt idx
        have lowerBase : base ≤ atomIndex := by
          simpa [base, atomCount, HydrogenExpansionState.toRawMolecule] using lower
        have stepCount :
            (withExplicitHydrogensStep mol state idx).toRawMolecule.atomCount = base + count := by
          rw [withExplicitHydrogensStep_atomCount]
          simp [base, count, atomCount, HydrogenExpansionState.toRawMolecule]
        have offsetBound : atomIndex - base < count := by omega
        let bond : RawBond := ⟨idx, base + (atomIndex - base), ParsedBondKind.single⟩
        have targetEq : bond.target = atomIndex := by
          dsimp only [bond]
          omega
        have bondMemStep :
            bond ∈ (withExplicitHydrogensStep mol state idx).toRawMolecule.bonds := by
          dsimp only [bond, base, count]
          exact withExplicitHydrogensStep_new_bond_mem mol state idx
            (atomIndex - state.1.length) offsetBound
        have bondMemFinal :
            bond ∈ (rest.foldl (withExplicitHydrogensStep mol)
              (withExplicitHydrogensStep mol state idx)).toRawMolecule.bonds :=
          fold_withExplicitHydrogensStep_bonds_mem mol rest
            (withExplicitHydrogensStep mol state idx) bond bondMemStep
        refine ⟨bond, ?_, Or.inr targetEq, ?_⟩
        · simpa only [List.foldl_cons] using bondMemFinal
        · dsimp only [bond]
          decide
      · rw [List.foldl_cons] at upper
        exact ih (withExplicitHydrogensStep mol state idx) atomIndex
          (Nat.le_of_not_gt within) upper

/-! ## Positive incident order forces a zero hydrogen count -/

/-- A plain aliphatic hydrogen with positive incident bond order has no implied hydrogens: the
default fill to valence one subtracts a used order of one, and a used order above one leaves no
admissible fill at all. -/
theorem hydrogenCountAt_eq_zero_of_aliphatic_hydrogen (mol : RawMolecule) (atomIndex : ℕ)
    (lookup : mol.atomAt? atomIndex = some (AtomSpec.aliphatic Element.H))
    (incident : 0 < mol.incidentBondOrderSum atomIndex) :
    mol.hydrogenCountAt atomIndex = 0 := by
  unfold RawMolecule.hydrogenCountAt
  rw [lookup]
  by_cases one : mol.incidentBondOrderSum atomIndex = 1
  · simp [AtomSpec.aliphatic, RawMolecule.defaultValences, RawMolecule.elementDefaultValences,
      one]
  · have notLe : ¬ mol.incidentBondOrderSum atomIndex ≤ 1 := by omega
    simp [AtomSpec.aliphatic, RawMolecule.defaultValences, RawMolecule.elementDefaultValences,
      notLe]

/-- A term of a mapped list sum is bounded by the whole sum. -/
theorem le_sum_map_of_mem {α : Type} (transform : α → ℕ) {values : List α} {value : α}
    (member : value ∈ values) :
    transform value ≤ (values.map transform).sum := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with equality | member
      · rw [equality]
        simp [List.map_cons, List.sum_cons]
      · simp only [List.map_cons, List.sum_cons]
        exact le_trans (inductionHypothesis member) (Nat.le_add_left _ _)

/-- A bond incident at an atom with positive order makes the incident bond-order sum positive. -/
theorem one_le_incidentBondOrderSum_of_mem (mol : RawMolecule) (atomIndex : ℕ) (bond : RawBond)
    (member : bond ∈ mol.bonds)
    (incident : bond.source = atomIndex ∨ bond.target = atomIndex)
    (order : 1 ≤ bond.kind.order) :
    1 ≤ mol.incidentBondOrderSum atomIndex := by
  rw [incidentBondOrderSum_eq_incidentContributionAt_sum]
  have contribution : 1 ≤ incidentContributionAt atomIndex bond := by
    unfold incidentContributionAt
    rcases incident with source | target
    · rw [source]
      simp [order]
    · rw [target]
      simp [order]
  exact le_trans contribution (le_sum_map_of_mem (incidentContributionAt atomIndex) member)

/-! ## The `WellFormed`-guarded contract form -/

/-- The existing materialized-valence invariant specialised to the complete expansion fold. -/
theorem withExplicitHydrogens_materializedValenceInvariant (mol : RawMolecule)
    (well : mol.WellFormed) :
    ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).MaterializedValenceInvariant mol := by
  have initialWell : (initialHydrogenExpansionState mol).toRawMolecule.WellFormed := by
    intro bond member
    simpa [BondEndpointsOK] using well bond member
  exact fold_withExplicitHydrogensStep_preserves_materializedValenceInvariant mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (by intro index member; exact List.mem_range.mp member)
    (initialHydrogenExpansionState_shapeInvariant mol) initialWell
    (initialHydrogenExpansionState_materializedValenceInvariant mol)

/-- **Closure under the well-formedness contract.**

On a well-formed raw graph the existing `MaterializedValenceInvariant` holds for the whole fold, so
each fresh atom has incident bond order exactly one and is an aliphatic hydrogen while original
atoms are materialised to `some 0`.  This is the contract form
`(well : mol.WellFormed) → mol.withExplicitHydrogens.HydrogenClosed`. -/
theorem hydrogenClosed_withExplicitHydrogens_of_wellFormed (mol : RawMolecule)
    (well : mol.WellFormed) :
    mol.withExplicitHydrogens.HydrogenClosed := by
  intro atomIndex bound
  by_cases original : atomIndex < mol.atomCount
  · exact hydrogenCountAt_withExplicitHydrogens_of_lt mol atomIndex original
  · have originalLe : mol.atomCount ≤ atomIndex := Nat.le_of_not_gt original
    have resultBound : atomIndex <
        ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
          (initialHydrogenExpansionState mol)).toRawMolecule.atomCount := by
      have bound' : atomIndex < mol.withExplicitHydrogens.atoms.length := by
        simpa [atomCount] using bound
      rw [withExplicitHydrogens_atoms_eq_fold] at bound'
      simpa [atomCount] using bound'
    obtain ⟨observed, observedLookup⟩ :=
      listGet?_exists_of_lt
        (((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
          (initialHydrogenExpansionState mol)).toRawMolecule.atoms) atomIndex
        (by simpa [atomCount] using resultBound)
    have resultLookup :
        ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
          (initialHydrogenExpansionState mol)).toRawMolecule.atomAt? atomIndex = some observed := by
      simpa [atomAt?] using observedLookup
    obtain ⟨observedIsHydrogen, incidentOne⟩ :=
      (withExplicitHydrogens_materializedValenceInvariant mol well).freshAtom
        atomIndex observed originalLe resultLookup
    have expandedLookup : mol.withExplicitHydrogens.atomAt? atomIndex = some observed := by
      simp only [atomAt?]
      rw [withExplicitHydrogens_atoms_eq_fold]
      exact resultLookup
    have incidentPositive : 0 < mol.withExplicitHydrogens.incidentBondOrderSum atomIndex := by
      have sumEq : mol.withExplicitHydrogens.incidentBondOrderSum atomIndex =
          ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
            (initialHydrogenExpansionState mol)).toRawMolecule.incidentBondOrderSum atomIndex := by
        simp only [RawMolecule.incidentBondOrderSum, withExplicitHydrogens_bonds_eq_fold]
      rw [sumEq, incidentOne]
      decide
    rw [observedIsHydrogen] at expandedLookup
    exact hydrogenCountAt_eq_zero_of_aliphatic_hydrogen mol.withExplicitHydrogens atomIndex
      expandedLookup incidentPositive

/-! ## Main closure theorem (no well-formedness hypothesis) -/

/-- **Hydrogen expansion always lands in its own closed domain.**

For an arbitrary parsed raw molecule — no admissibility, well-formedness or valence hypothesis —
`mol.withExplicitHydrogens` has zero implied/explicit hydrogens at every atom index it contains.
Original atoms are materialised to `explicitHydrogens? = some 0`; every appended atom is an
aliphatic hydrogen carrying its one generated single bond, which forces a zero fill count even if a
malformed old bond also touches the fresh index. -/
theorem hydrogenClosed_withExplicitHydrogens (mol : RawMolecule) :
    mol.withExplicitHydrogens.HydrogenClosed := by
  intro atomIndex bound
  by_cases original : atomIndex < mol.atomCount
  · exact hydrogenCountAt_withExplicitHydrogens_of_lt mol atomIndex original
  · have originalLe : mol.atomCount ≤ atomIndex := Nat.le_of_not_gt original
    have resultBound : atomIndex <
        ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
          (initialHydrogenExpansionState mol)).toRawMolecule.atomCount := by
      have bound' : atomIndex < mol.withExplicitHydrogens.atoms.length := by
        simpa [atomCount] using bound
      rw [withExplicitHydrogens_atoms_eq_fold] at bound'
      simpa [atomCount] using bound'
    obtain ⟨observed, observedLookup⟩ :=
      listGet?_exists_of_lt
        (((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
          (initialHydrogenExpansionState mol)).toRawMolecule.atoms) atomIndex
        (by simpa [atomCount] using resultBound)
    have resultLookup :
        ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
          (initialHydrogenExpansionState mol)).toRawMolecule.atomAt? atomIndex = some observed := by
      simpa [atomAt?] using observedLookup
    have observedIsHydrogen : observed = AtomSpec.aliphatic Element.H :=
      fold_atomAt?_eq_hydrogen_of_le mol (List.range mol.atomCount)
        (initialHydrogenExpansionState mol) atomIndex observed
        (by simpa using originalLe) resultLookup
    have expandedLookup : mol.withExplicitHydrogens.atomAt? atomIndex = some observed := by
      simp only [atomAt?]
      rw [withExplicitHydrogens_atoms_eq_fold]
      exact resultLookup
    obtain ⟨bond, bondMem, bondIncident, bondOrder⟩ :=
      fold_fresh_atom_has_incident_bond mol (List.range mol.atomCount)
        (initialHydrogenExpansionState mol) atomIndex
        (by simpa using originalLe) resultBound
    have bondMemExpanded : bond ∈ mol.withExplicitHydrogens.bonds := by
      rw [withExplicitHydrogens_bonds_eq_fold]
      exact bondMem
    have incidentPositive : 0 < mol.withExplicitHydrogens.incidentBondOrderSum atomIndex := by
      have positive :=
        one_le_incidentBondOrderSum_of_mem mol.withExplicitHydrogens atomIndex bond
          bondMemExpanded bondIncident bondOrder
      omega
    rw [observedIsHydrogen] at expandedLookup
    exact hydrogenCountAt_eq_zero_of_aliphatic_hydrogen mol.withExplicitHydrogens atomIndex
      expandedLookup incidentPositive

/-- Executable reflection of the closure theorem. -/
theorem hydrogenClosed?_withExplicitHydrogens (mol : RawMolecule) :
    mol.withExplicitHydrogens.hydrogenClosed? = true :=
  (RawMolecule.hydrogenClosed?_eq_true_iff mol.withExplicitHydrogens).mpr
    (hydrogenClosed_withExplicitHydrogens mol)

/-- Expansion is already closed, so closing it again changes nothing. -/
theorem hydrogenClosed_withExplicitHydrogens_secondExpansion (mol : RawMolecule) :
    mol.withExplicitHydrogens.withExplicitHydrogens.HydrogenClosed :=
  hydrogenClosed_withExplicitHydrogens mol.withExplicitHydrogens

/-! ## Second expansion adds no atoms or bonds -/

/-- A second expansion preserves the atom count. -/
theorem withExplicitHydrogens_secondExpansion_atomCount (mol : RawMolecule) :
    mol.withExplicitHydrogens.withExplicitHydrogens.atomCount =
      mol.withExplicitHydrogens.atomCount :=
  RawMolecule.withExplicitHydrogens_atomCount_of_hydrogenClosed mol.withExplicitHydrogens
    (hydrogenClosed_withExplicitHydrogens mol)

/-- A second expansion preserves the bond list exactly. -/
theorem withExplicitHydrogens_secondExpansion_bonds (mol : RawMolecule) :
    mol.withExplicitHydrogens.withExplicitHydrogens.bonds =
      mol.withExplicitHydrogens.bonds :=
  RawMolecule.withExplicitHydrogens_bonds_of_hydrogenClosed mol.withExplicitHydrogens
    (hydrogenClosed_withExplicitHydrogens mol)

/-- A second expansion preserves the semantic molecule produced by the raw conversion. -/
theorem withExplicitHydrogens_secondExpansion_toSemanticMolecule? (mol : RawMolecule) :
    mol.withExplicitHydrogens.withExplicitHydrogens.toSemanticMolecule? =
      mol.withExplicitHydrogens.toSemanticMolecule? :=
  RawMolecule.toSemanticMolecule?_withExplicitHydrogens_eq_of_hydrogenClosed
    mol.withExplicitHydrogens (hydrogenClosed_withExplicitHydrogens mol)

/-- The second expansion's atoms are the first expansion's atoms with the inline-count policy
consumed.  This is deliberately *not* an equality with the first expansion's raw atom list. -/
theorem withExplicitHydrogens_secondExpansion_atoms (mol : RawMolecule) :
    mol.withExplicitHydrogens.withExplicitHydrogens.atoms =
      mol.withExplicitHydrogens.atoms.map materializedAtomSpec :=
  RawMolecule.withExplicitHydrogens_atoms_of_hydrogenClosed mol.withExplicitHydrogens
    (hydrogenClosed_withExplicitHydrogens mol)

/-- A second expansion preserves admissibility of the first expansion. -/
theorem withExplicitHydrogens_secondExpansion_admissible (mol : RawMolecule)
    (admitted : mol.withExplicitHydrogens.Admissible) :
    mol.withExplicitHydrogens.withExplicitHydrogens.Admissible :=
  RawMolecule.withExplicitHydrogens_admissible_of_hydrogenClosed mol.withExplicitHydrogens
    admitted (hydrogenClosed_withExplicitHydrogens mol)

/-- A freshly appended aliphatic hydrogen *is* changed by materialisation: `none` is rewritten to
`some 0`.  This is why the raw record is not idempotent even though no atom is added on the second
expansion. -/
theorem materializedAtomSpec_aliphatic_hydrogen_ne :
    materializedAtomSpec (AtomSpec.aliphatic Element.H) ≠ AtomSpec.aliphatic Element.H := by
  intro equality
  have projected := congrArg AtomSpec.explicitHydrogens? equality
  simp [materializedAtomSpec, AtomSpec.aliphatic] at projected

/-! ## Kernel-authority certificates -/

assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogensStep_atomCount
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogensStep_atomAt?_of_lt
assert_kernel_only TetraStereo.OneCenter.RawHydrogenExpansionClosure.fold_atomAt?_of_lt
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.initialHydrogenExpansionState_atomAt?
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogens_atomAt?_of_lt
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.hydrogenCountAt_withExplicitHydrogens_of_lt
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.fold_atomAt?_eq_hydrogen_of_le
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogensStep_old_bond_mem
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogensStep_new_bond_mem
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.fold_withExplicitHydrogensStep_bonds_mem
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.fold_fresh_atom_has_incident_bond
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.hydrogenCountAt_eq_zero_of_aliphatic_hydrogen
assert_kernel_only TetraStereo.OneCenter.RawHydrogenExpansionClosure.le_sum_map_of_mem
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.one_le_incidentBondOrderSum_of_mem
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogens_materializedValenceInvariant
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.hydrogenClosed_withExplicitHydrogens_of_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.hydrogenClosed_withExplicitHydrogens
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.hydrogenClosed?_withExplicitHydrogens
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.hydrogenClosed_withExplicitHydrogens_secondExpansion
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogens_secondExpansion_atomCount
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogens_secondExpansion_bonds
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogens_secondExpansion_toSemanticMolecule?
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogens_secondExpansion_atoms
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.withExplicitHydrogens_secondExpansion_admissible
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpansionClosure.materializedAtomSpec_aliphatic_hydrogen_ne

end RawHydrogenExpansionClosure
end OneCenter
end TetraStereo
