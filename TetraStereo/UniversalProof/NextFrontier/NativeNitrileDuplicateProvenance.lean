import TetraStereo.UniversalProof.NextFrontier.NativeNitrileHydrogenAtoms
import TetraStereo.UniversalProof.NextFrontier.FramedAtomicDispatch
import TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

private theorem fold_order_ge_start (bonds : List RawBond) (left right start : Nat) :
    start ≤ bonds.foldl (fun order bond =>
      if bond.directedConnects left right then max order bond.kind.order else order) start := by
  induction bonds generalizing start with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      simp only [List.foldl_cons]
      split
      · exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
      · exact ih _

private theorem fold_order_ge_record (bonds : List RawBond) (left right start : Nat)
    (bond : RawBond) (retained : bond ∈ bonds)
    (directed : bond.directedConnects left right = true) :
    bond.kind.order ≤ bonds.foldl (fun order item =>
      if item.directedConnects left right then max order item.kind.order else order) start := by
  induction bonds generalizing start with
  | nil => simp at retained
  | cons head tail ih =>
      rcases List.mem_cons.mp retained with same | tailMember
      · subst head
        simp only [List.foldl_cons, directed, ↓reduceIte]
        exact Nat.le_trans (Nat.le_max_right _ _) (fold_order_ge_start tail left right _)
      · exact ih _ tailMember

theorem bond_record_order_lower_bound (mol : RawMolecule) (bond : RawBond)
    (retained : bond ∈ mol.bonds) (different : bond.source ≠ bond.target) :
    bond.kind.order ≤ mol.bondOrder bond.source bond.target := by
  have directed : bond.directedConnects bond.source bond.target = true := by
    simp [RawBond.directedConnects]
  have lower := fold_order_ge_record mol.bonds bond.source bond.target 0 bond retained directed
  unfold bondOrder
  rw [if_neg different]
  exact Nat.le_trans lower (Nat.le_max_left _ _)

private theorem retain_nonparent_copy (parent : Nat) (copy : Nat × Nat)
    (copies : List (Nat × Nat)) (different : copy.1 ≠ parent) (member : copy ∈ copies) :
    copy ∈ eraseCanonicalParentCopy parent copies := by
  induction copies with
  | nil => simp at member
  | cons head tail ih =>
      by_cases erased : (head.1 == parent && head.2 == 0) = true
      · simp only [eraseCanonicalParentCopy, erased, ↓reduceIte]
        rcases List.mem_cons.mp member with same | retained
        · subst head
          have both : copy.1 = parent ∧ copy.2 = 0 := by simpa using erased
          exact (different both.1).elim
        · exact retained
      · simp only [eraseCanonicalParentCopy, erased, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        rcases List.mem_cons.mp member with same | retained
        · exact Or.inl same
        · exact Or.inr (ih retained)

/-- An independently present ordinary nitrile bond creates the actual duplicate occurrence,
including its immutable construction history and `.multipleBondDuplicate` provenance. -/
def nitrileDuplicate : CanonicalBranchNode :=
  { atom := 3, parent := 2, history := [3, 2, 0], provenance := .multipleBondDuplicate 1 }

theorem actual_nitrile_duplicate_of_bond (mol : RawMolecule)
    (triple : ({ source := 2, target := 3, kind := .triple } : RawBond) ∈ mol.bonds) :
    nitrileDuplicate ∈ mol.canonicalChildren (canonicalRoot 0 2) := by
  have lower : 3 ≤ mol.bondOrder 2 3 :=
    bond_record_order_lower_bound mol _ triple (by decide)
  have enough : 1 < mol.canonicalBondOrder (canonicalRoot 0 2) 3 := by
    have positive : 1 < mol.bondOrder 2 3 := Nat.lt_of_lt_of_le (by decide : 1 < 3) lower
    simpa [canonicalBondOrder, canonicalRoot] using positive
  have seed : (3, 1) ∈ mol.canonicalChildCopies (canonicalRoot 0 2) := by
    unfold canonicalChildCopies
    apply retain_nonparent_copy
    · decide
    · apply List.mem_flatMap.mpr
      refine ⟨{ source := 2, target := 3, kind := .triple }, triple, ?_⟩
      simpa [canonicalRoot] using
        (List.mem_map.mpr ⟨1, List.mem_range.mpr enough, rfl⟩ :
          (3, 1) ∈ (List.range (mol.canonicalBondOrder (canonicalRoot 0 2) 3)).map
            (fun copy => (3, copy)))
  unfold canonicalChildren
  simp only [canonicalRoot, CanonicalBranchNode.forcedLeaf, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_map.mpr
  exact ⟨(3, 1), seed, by rfl⟩

theorem expanded_nitrile_duplicate (parity : TetrahedralInputParity) (n : Nat) :
    nitrileDuplicate ∈ (expanded parity n).canonicalChildren (canonicalRoot 0 2) :=
  actual_nitrile_duplicate_of_bond _
    (withExplicitHydrogens_retains_original_bonds (raw parity n) _ (raw_triple_present parity n))

theorem expanded_nitrile_root_generated (parity : TetrahedralInputParity) (n : Nat) :
    CanonicalCenterTreeNode (expanded parity n) 0 (canonicalRoot 0 2) := by
  have rawEdge : ({ source := 0, target := 2, kind := .single } : RawBond) ∈
      (raw parity n).bonds := by simp [raw, prefixBonds]
  have present := withExplicitHydrogens_retains_original_bonds (raw parity n) _ rawEdge
  have lower : 1 ≤ (expanded parity n).bondOrder 0 2 :=
    bond_record_order_lower_bound _ ⟨0, 2, .single⟩ present (by decide)
  have positive : 0 < (expanded parity n).canonicalBondOrder (canonicalCenterRoot 0) 2 :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1) lower
  have seed : (2, 0) ∈ (expanded parity n).canonicalChildCopies (canonicalCenterRoot 0) := by
    unfold canonicalChildCopies
    apply retain_nonparent_copy
    · decide
    · apply List.mem_flatMap.mpr
      refine ⟨⟨0, 2, .single⟩, present, ?_⟩
      simpa [canonicalCenterRoot] using
        (List.mem_map.mpr ⟨0, List.mem_range.mpr positive, rfl⟩ :
          (2, 0) ∈ (List.range
            ((expanded parity n).canonicalBondOrder (canonicalCenterRoot 0) 2)).map
            (fun copy => (2, copy)))
  apply CanonicalCenterTreeNode.child CanonicalCenterTreeNode.root
  unfold canonicalChildren
  simp only [canonicalCenterRoot, CanonicalBranchNode.forcedLeaf, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_map.mpr ⟨(2, 0), seed, rfl⟩

theorem expanded_duplicate_generated (parity : TetrahedralInputParity) (n : Nat) :
    CanonicalCenterTreeNode (expanded parity n) 0 nitrileDuplicate :=
  CanonicalCenterTreeNode.child (expanded_nitrile_root_generated parity n)
    (expanded_nitrile_duplicate parity n)

/-- The framed tree profile genuinely refuses every family member because the generated CIP
digraph contains a real multiple-bond duplicate. This is independent of a returned descriptor. -/
theorem expanded_profile_none (parity : TetrahedralInputParity) (n : Nat) :
    FrameRuntime.profile? (expanded parity n) (canonicalCenterRoot 0) = none := by
  cases profileEq : FrameRuntime.profile? (expanded parity n) (canonicalCenterRoot 0) with
  | none => rfl
  | some profile =>
      have real := (FramedAtomicDispatch.profile_generated CanonicalCenterTreeNode.root
        profile profileEq nitrileDuplicate (expanded_duplicate_generated parity n)).2
      cases real

theorem actual_fast_dispatch_legacy (parity : TetrahedralInputParity) (n fuel : Nat)
    (state : OccurrenceAuxState) :
    occurrenceFact? (expanded parity n) fuel state (canonicalCenterRoot 0) =
      legacyOccurrenceFact? (expanded parity n) fuel state (canonicalCenterRoot 0) :=
  occurrenceFact?_eq_legacy_of_profile_none _ _ _ _ (expanded_profile_none parity n)

theorem actual_authoritative_dispatch_legacy (parity : TetrahedralInputParity) (n fuel : Nat)
    (state : OccurrenceAuxState) :
    occurrenceFactAuthoritative? (expanded parity n) fuel state (canonicalCenterRoot 0) =
      legacyOccurrenceFactAuthoritative? (expanded parity n) fuel state (canonicalCenterRoot 0) :=
  occurrenceFactAuthoritative?_eq_legacy_of_profile_none _ _ _ _ (expanded_profile_none parity n)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
