import TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge
import TetraStereo.UniversalProof.SecondSphereFamilyGeneratedHistories

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereFamilyRuntimeInstantiation

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation







def familyRoles (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    GeneralSecondSphereRuntimeBridge.Roles (familyRaw ps) where
  backbone := ⟨1 + 12 * i.val, familyRaw_role_bound ps i 0 (by decide)⟩
  bridge := ⟨1 + 12 * i.val + 2, familyRaw_role_bound ps i 2 (by decide)⟩
  tag := ⟨1 + 12 * i.val + 5, familyRaw_role_bound ps i 5 (by decide)⟩
  methyl := ⟨1 + 12 * i.val + 8, familyRaw_role_bound ps i 8 (by decide)⟩
  bh1 := ⟨1 + 12 * i.val + 3, familyRaw_role_bound ps i 3 (by decide)⟩
  bh2 := ⟨1 + 12 * i.val + 4, familyRaw_role_bound ps i 4 (by decide)⟩
  mh1 := ⟨1 + 12 * i.val + 9, familyRaw_role_bound ps i 9 (by decide)⟩
  mh2 := ⟨1 + 12 * i.val + 10, familyRaw_role_bound ps i 10 (by decide)⟩
  mh3 := ⟨1 + 12 * i.val + 11, familyRaw_role_bound ps i 11 (by decide)⟩

def familyRoot (ps : List TetrahedralInputParity) : Fin (familyRaw ps).atomCount :=
  ⟨1, SecondSphereFamilyGeneratedHistories.familyRaw_root_bound ps⟩

def familyTail (i : Nat) : List Nat := SecondSphereFamilyGeneratedHistories.backboneTail i

theorem family_observed_carbon (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (member : offset ∈ [0, 2, 5, 8]) :
    GeneralSecondSphereRuntimeBridge.ObservedElement (familyRaw ps) (1 + 12 * i.val + offset) Element.C := by
  have bound : offset < 12 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  refine ⟨roleAtom (ps.get i) (roleOfOffset offset), familyRaw_role_atom ps i offset bound, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem family_observed_hydrogen (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (member : offset ∈ [3, 4, 9, 10, 11]) :
    GeneralSecondSphereRuntimeBridge.ObservedNaturalHydrogen (familyRaw ps) (1 + 12 * i.val + offset) := by
  have bound : offset < 12 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  refine ⟨roleAtom (ps.get i) (roleOfOffset offset), familyRaw_role_atom ps i offset bound, ?_, ?_⟩
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A block index supplies nonemptiness, so the actual first backbone is carbon at root 1. -/
theorem family_observed_root (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    GeneralSecondSphereRuntimeBridge.ObservedElement (familyRaw ps) (familyRoot ps).val Element.C := by
  have positive : 0 < ps.length := by have bound := i.isLt; omega
  exact family_observed_carbon ps ⟨0, positive⟩ 0 (by simp)

/-- Complete independent physical and generated-history domain, constructed internally. -/
def familyInteriorDomain (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    GeneralSecondSphereRuntimeBridge.InteriorDomain (familyRaw ps) (familyRoles ps i) (familyRoot ps) (familyTail i.val) where
  well := familyRaw_wellFormed ps
  rootAtom := family_observed_root ps i
  backboneAtom := family_observed_carbon ps i 0 (by simp)
  bridgeAtom := family_observed_carbon ps i 2 (by simp)
  methylAtom := family_observed_carbon ps i 8 (by simp)
  hydrogenAtoms := by
    intro h member
    change h ∈ [1 + 12 * i.val + 3, 1 + 12 * i.val + 4,
      1 + 12 * i.val + 9, 1 + 12 * i.val + 10, 1 + 12 * i.val + 11] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact family_observed_hydrogen ps i 3 (by simp)
    · exact family_observed_hydrogen ps i 4 (by simp)
    · exact family_observed_hydrogen ps i 9 (by simp)
    · exact family_observed_hydrogen ps i 10 (by simp)
    · exact family_observed_hydrogen ps i 11 (by simp)
  bridgeRow := familyRaw_bridge_records ps i
  methylRow := familyRaw_methyl_records ps i
  bridgeDistinct := by
    have distinct := (familyRaw_closed_rows_nodup ps i).1
    rw [familyRaw_bridge_records ps i] at distinct
    exact distinct
  methylDistinct := by
    have distinct := (familyRaw_closed_rows_nodup ps i).2.2
    rw [familyRaw_methyl_records ps i] at distinct
    exact distinct
  bridgeSingle := familyRaw_incident_order ps _
  methylSingle := familyRaw_incident_order ps _
  bh1Row := (familyRaw_comparison_leaf_records ps i).1
  bh2Row := (familyRaw_comparison_leaf_records ps i).2.1
  mh1Row := (familyRaw_comparison_leaf_records ps i).2.2.1
  mh2Row := (familyRaw_comparison_leaf_records ps i).2.2.2.1
  mh3Row := (familyRaw_comparison_leaf_records ps i).2.2.2.2
  generated := by
    simpa only [familyRoles, familyRoot, familyTail, GeneralSecondSphereRuntimeBridge.pathNode,
      SecondSphereFamilyGeneratedHistories.methylNode, SecondSphereFamilyGeneratedHistories.pathNode, SecondSphereFamilyGeneratedHistories.backboneIndex]
      using SecondSphereFamilyGeneratedHistories.familyRaw_methyl_generated ps i

def familyBridgeCursor (ps : List TetrahedralInputParity) (i : Fin ps.length) : CanonicalRerootCursor :=
  { node := SecondSphereFamilyGeneratedHistories.bridgeNode i.val, previous? := some (SecondSphereFamilyGeneratedHistories.tagNode i.val) }

def familyMethylCursor (ps : List TetrahedralInputParity) (i : Fin ps.length) : CanonicalRerootCursor :=
  { node := SecondSphereFamilyGeneratedHistories.methylNode i.val, previous? := some (SecondSphereFamilyGeneratedHistories.tagNode i.val) }

theorem generic_bridge_cursor_eq (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    GeneralSecondSphereRuntimeBridge.bridgeCursor (roles := familyRoles ps i) (tail := familyTail i.val) =
      familyBridgeCursor ps i := rfl

theorem generic_methyl_cursor_eq (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    GeneralSecondSphereRuntimeBridge.methylCursor (roles := familyRoles ps i) (tail := familyTail i.val) =
      familyMethylCursor ps i := rfl

theorem family_incoming_generated (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterRerootCursor (familyRaw ps) 1 (familyBridgeCursor ps i) :=
  SecondSphereFamilyGeneratedHistories.familyRaw_incoming_bridge_cursor ps i

theorem family_outgoing_generated (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterRerootCursor (familyRaw ps) 1 (familyMethylCursor ps i) :=
  SecondSphereFamilyGeneratedHistories.familyRaw_outgoing_methyl_cursor ps i

theorem family_fast_raw_both (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAt (familyRaw ps) (fuel + 1) stage
      (familyBridgeCursor ps i) (familyMethylCursor ps i) = some Ordering.gt ∧
    compareCursorBranchAt (familyRaw ps) (fuel + 1) stage
      (familyMethylCursor ps i) (familyBridgeCursor ps i) = some Ordering.lt := by
  simpa only [generic_bridge_cursor_eq, generic_methyl_cursor_eq]
    using GeneralSecondSphereRuntimeBridge.actual_fast_raw_both (familyInteriorDomain ps i) fuel stage

theorem family_authoritative_raw_both (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? (familyRaw ps) (fuel + 1) stage
      (familyBridgeCursor ps i) (familyMethylCursor ps i) = some Ordering.gt ∧
    compareCursorBranchAtAuthoritative? (familyRaw ps) (fuel + 1) stage
      (familyMethylCursor ps i) (familyBridgeCursor ps i) = some Ordering.lt := by
  simpa only [generic_bridge_cursor_eq, generic_methyl_cursor_eq]
    using GeneralSecondSphereRuntimeBridge.actual_authoritative_raw_both (familyInteriorDomain ps i) fuel stage

theorem family_certified_both (ps : List TetrahedralInputParity) (i : Fin ps.length) (fuel : Nat) :
    certifiedConstitutionalStage? (familyRaw ps) (fuel + 1)
      (familyBridgeCursor ps i) (familyMethylCursor ps i) = some Ordering.gt ∧
    certifiedConstitutionalStage? (familyRaw ps) (fuel + 1)
      (familyMethylCursor ps i) (familyBridgeCursor ps i) = some Ordering.lt := by
  simpa only [generic_bridge_cursor_eq, generic_methyl_cursor_eq]
    using GeneralSecondSphereRuntimeBridge.actual_certified_both (familyInteriorDomain ps i) fuel

theorem family_certified_authoritative_both (ps : List TetrahedralInputParity)
    (i : Fin ps.length) (fuel : Nat) :
    certifiedConstitutionalStageAuthoritative? (familyRaw ps) (fuel + 1)
      (familyBridgeCursor ps i) (familyMethylCursor ps i) = some Ordering.gt ∧
    certifiedConstitutionalStageAuthoritative? (familyRaw ps) (fuel + 1)
      (familyMethylCursor ps i) (familyBridgeCursor ps i) = some Ordering.lt := by
  simpa only [generic_bridge_cursor_eq, generic_methyl_cursor_eq]
    using GeneralSecondSphereRuntimeBridge.actual_certified_authoritative_both (familyInteriorDomain ps i) fuel

/-- Any auxiliary state is quantified in the conclusion; no successful state is an input. -/
theorem family_fast_protocol_both (ps : List TetrahedralInputParity) (i : Fin ps.length) (fuel : Nat) :
    ∀ state : OccurrenceAuxState,
    compareOccurrenceBranches? (familyRaw ps) state (fuel + 1)
      (familyBridgeCursor ps i) (familyMethylCursor ps i) =
        some { ordering := Ordering.gt, pseudo := false, rule4cCarrier? := none } ∧
    compareOccurrenceBranches? (familyRaw ps) state (fuel + 1)
      (familyMethylCursor ps i) (familyBridgeCursor ps i) =
        some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  intro state
  simpa only [generic_bridge_cursor_eq, generic_methyl_cursor_eq]
    using GeneralSecondSphereRuntimeBridge.actual_fast_protocol_both (familyInteriorDomain ps i) state fuel

theorem family_authoritative_protocol_both (ps : List TetrahedralInputParity)
    (i : Fin ps.length) (fuel : Nat) :
    ∀ state : OccurrenceAuxState,
    compareOccurrenceBranchesAuthoritative? (familyRaw ps) state (fuel + 1)
      (familyBridgeCursor ps i) (familyMethylCursor ps i) =
        some { ordering := Ordering.gt, pseudo := false, rule4cCarrier? := none } ∧
    compareOccurrenceBranchesAuthoritative? (familyRaw ps) state (fuel + 1)
      (familyMethylCursor ps i) (familyBridgeCursor ps i) =
        some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  intro state
  simpa only [generic_bridge_cursor_eq, generic_methyl_cursor_eq]
    using GeneralSecondSphereRuntimeBridge.actual_authoritative_protocol_both (familyInteriorDomain ps i) state fuel

theorem family_complete_protocol_both (ps : List TetrahedralInputParity)
    (i : Fin ps.length) (fuel : Nat) :
    ∀ state : OccurrenceAuxState,
    compareOccurrenceBranchesComplete? (familyRaw ps) state (fuel + 1)
      (familyBridgeCursor ps i) (familyMethylCursor ps i) =
        some { ordering := Ordering.gt, pseudo := false, rule4cCarrier? := none } ∧
    compareOccurrenceBranchesComplete? (familyRaw ps) state (fuel + 1)
      (familyMethylCursor ps i) (familyBridgeCursor ps i) =
        some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  intro state
  simpa only [generic_bridge_cursor_eq, generic_methyl_cursor_eq]
    using GeneralSecondSphereRuntimeBridge.actual_complete_protocol_both (familyInteriorDomain ps i) state fuel

/-- All natural comparison fuels at least one, with no assertion at zero. -/
theorem family_complete_protocol_positive (ps : List TetrahedralInputParity)
    (i : Fin ps.length) (fuel : Nat) (positive : 1 ≤ fuel) :
    ∀ state : OccurrenceAuxState,
    compareOccurrenceBranchesComplete? (familyRaw ps) state fuel
      (familyBridgeCursor ps i) (familyMethylCursor ps i) = some { ordering := Ordering.gt } ∧
    compareOccurrenceBranchesComplete? (familyRaw ps) state fuel
      (familyMethylCursor ps i) (familyBridgeCursor ps i) = some { ordering := Ordering.lt } := by
  intro state
  simpa only [generic_bridge_cursor_eq, generic_methyl_cursor_eq]
    using GeneralSecondSphereRuntimeBridge.actual_complete_protocol_positive (familyInteriorDomain ps i) state fuel positive

end TetraStereo.UniversalProof.SecondSphereFamilyRuntimeInstantiation
