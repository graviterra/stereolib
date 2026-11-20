import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-!
# A separately generated frozen-context recursive profile on the cage

Each node's auxiliary facts are independently regenerated with no inherited promotion reference.
At a promotion the same independently generated child map is reused. This is a chronology-only
ablation of the replacing-reference consensus evaluator, not a published-2018 fidelity claim.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage

open LocalizedGenericMarkedRecalculation
open LocalizedRecursiveAuxiliaryPhysicalCompletion
open LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedHiddenParityMarkedProbe hiding frameAtoms?
open LocalizedHiddenParityPromotedReadback hiding rankedAtoms?
open LocalizedHiddenParityPromotedReflection
open LocalizedGenericMarkedRecalculationCage

/-- Independent recursion: promotion references never enter the descendant query. The frozen
child map is still generated from the actual molecular expansion, not supplied as an input. -/
def frozenFacts (mol : RawMolecule) (fuel : Nat) :
    Nat → Geometry → OccurrenceAuxState → RawMolecule.CanonicalBranchNode → OccurrenceAuxState
  | 0, _, _, _ => []
  | depth + 1, geom, state, node =>
      (descriptorWith? mol fuel geom state none node
        (fun g s _ child => frozenFacts mol fuel depth g s child)).toList.map (factOf node) ++
      (mol.canonicalChildren node).flatMap (frozenFacts mol fuel depth geom state)

def frozenRaw? (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) : Option RS :=
  rawWith? mol fuel geom state none node
    (fun g s _ child => frozenFacts mol fuel depth g s child)

def frozenDescriptor? (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorWith? mol fuel geom state none node
    (fun g s _ child => frozenFacts mol fuel depth g s child)

def frozenAssignCenter? (mol : RawMolecule) (fuel : Nat) (geom : Geometry) (center : Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  frozenDescriptor? mol fuel (structuralDepth mol (canonicalCenterRoot center)) geom []
    (canonicalCenterRoot center)

/-- Same index enumeration as the original generic report, with the separately generated
frozen profile substituted at each final root. This is not the detected-center report API. -/
def frozenAssign (mol : RawMolecule) (fuel : Nat) (geom : Geometry) :
    List (Nat × LocalizedTetrahedralRSPseudoDescriptor) :=
  (List.range mol.atomCount).filterMap fun center =>
    (frozenAssignCenter? mol fuel geom center).map fun descriptor => (center, descriptor)


theorem frozenFacts_noFrame (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (frame : frameAtoms? mol node = none) :
    frozenFacts mol fuel (depth + 1) geom state node =
      (mol.canonicalChildren node).flatMap (frozenFacts mol fuel depth geom state) := by
  rw [frozenFacts, descriptorWith?_none_of_frame mol fuel geom state none node _ frame]
  rfl

theorem frozenFacts_forcedLeaf (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (leaf : node.forcedLeaf = true) : frozenFacts mol fuel depth geom state node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [frozenFacts_noFrame mol fuel depth geom state node
      (frameAtoms?_forcedLeaf mol node leaf), canonicalChildren_forcedLeaf mol node leaf]
    rfl

theorem frozenFacts_shallowNoFrame (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (frame : frameAtoms? mol node = none)
    (leaves : ∀ child ∈ mol.canonicalChildren node, child.forcedLeaf = true) :
    frozenFacts mol fuel depth geom state node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [frozenFacts_noFrame mol fuel depth geom state node frame]
    calc
      _ = (mol.canonicalChildren node).flatMap (fun _ => []) :=
        flatMap_congr_mem _ _ _ (fun child member =>
          frozenFacts_forcedLeaf mol fuel depth geom state child (leaves child member))
      _ = [] := flatMap_nil_fun _

/-- Structural extinction below the far layer works for either geometry and every depth. -/
theorem frozen_children_leafy (node : RawMolecule.CanonicalBranchNode)
    (leafy : ∀ child ∈ cageRaw.canonicalChildren node,
      frameAtoms? cageRaw child = none ∧
      ∀ next ∈ cageRaw.canonicalChildren child, next.forcedLeaf = true)
    (depth : Nat) (geom : Geometry) :
    (cageRaw.canonicalChildren node).flatMap (frozenFacts cageRaw 16 depth geom []) = [] := by
  calc
    _ = (cageRaw.canonicalChildren node).flatMap (fun _ => []) :=
      flatMap_congr_mem _ _ _ (fun child member =>
        frozenFacts_shallowNoFrame cageRaw 16 depth geom [] child
          (leafy child member).1 (leafy child member).2)
    _ = [] := flatMap_nil_fun _

/-- Promotion-local maps are constant in the frozen profile by construction. -/
theorem frozen_under_eq_children (depth : Nat) (geom : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (reference : Nat) :
    underWith cageRaw 16 geom [] node
      (fun g s _ child => frozenFacts cageRaw 16 depth g s child) reference =
      (tiedChildren cageRaw 16 [] node).flatMap (frozenFacts cageRaw 16 depth geom []) := rfl

/-- No auxiliary fact exists below a far promotion. -/
theorem frozen_under_leafy (node : RawMolecule.CanonicalBranchNode)
    (leafy : ∀ child ∈ cageRaw.canonicalChildren node,
      frameAtoms? cageRaw child = none ∧
      ∀ next ∈ cageRaw.canonicalChildren child, next.forcedLeaf = true)
    (depth : Nat) (geom : Geometry) (reference : Nat) :
    underWith cageRaw 16 geom [] node
      (fun g s _ child => frozenFacts cageRaw 16 depth g s child) reference = [] := by
  rw [frozen_under_eq_children]
  calc
    _ = (tiedChildren cageRaw 16 [] node).flatMap (fun _ => []) :=
      flatMap_congr_mem _ _ _ (fun child member =>
        frozenFacts_shallowNoFrame cageRaw 16 depth geom [] child
          (leafy child (mem_tiedChildren cageRaw 16 [] node child member)).1
          (leafy child (mem_tiedChildren cageRaw 16 [] node child member)).2)
    _ = [] := flatMap_nil_fun _

/-- An inherited atom outside the current frame selects the ordinary consensus branch. -/
theorem rawStep_none_eq_outside (geom : Geometry) (node : RawMolecule.CanonicalBranchNode)
    (atoms : List Nat) (reference : Nat) (under : Nat → OccurrenceAuxState)
    (frame : frameAtoms? cageRaw node = some atoms) (outside : atoms.contains reference = false) :
    rawStep? cageRaw 16 geom [] none node under =
      rawStep? cageRaw 16 geom [] (some reference) node under := by
  have absent : reference ∉ atoms := by
    intro member
    have present := List.contains_iff_mem.mpr member
    rw [outside] at present
    cases present
  simp [rawStep?, frame, absent]

/-- Remove all lower recursive work only after proving the actual expansion has no frames. -/
theorem frozenRaw_leafy (node : RawMolecule.CanonicalBranchNode)
    (leafy : ∀ child ∈ cageRaw.canonicalChildren node,
      frameAtoms? cageRaw child = none ∧
      ∀ next ∈ cageRaw.canonicalChildren child, next.forcedLeaf = true)
    (depth : Nat) (geom : Geometry) :
    frozenRaw? cageRaw 16 depth geom [] node =
      rawStep? cageRaw 16 geom [] none node (fun _ => []) := by
  unfold frozenRaw? rawWith?
  have equality : underWith cageRaw 16 geom [] node
      (fun g s _ child => frozenFacts cageRaw 16 depth g s child) = (fun _ => []) :=
    funext (frozen_under_leafy node leafy depth geom)
  rw [equality]

/-- Two focused actual ranking pins; no recursive state is evaluated here. -/
theorem root_empty_atoms3 : visitRankedAtoms? root0 3 = some [2,3,9,1] := by
  decide +kernel

theorem root_empty_atoms9 : visitRankedAtoms? root0 9 = some [2,9,3,1] := by
  decide +kernel


section Family
variable (P : List CartesianPoint3) (len : P.length = 15)

theorem frozenRaw_farA (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [5, 6, 7]) :
    frozenRaw? cageRaw 16 depth (geomOf P len) [] (farA o) = none := by
  rw [frozenRaw_leafy (farA o) (farA_leafy o member)]
  have actual := rawFarA_root P len nondeg 0 o 3 member (Or.inl rfl)
  unfold raw? rawWith? at actual
  have equality : underWith cageRaw 16 (geomOf P len) [] (farA o)
      (facts cageRaw 16 0) = (fun _ => []) :=
    funext (underFarA o member 0 (geomOf P len) [])
  rw [equality] at actual
  have choices : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using member
  rcases choices with rfl | rfl | rfl
  · exact (rawStep_none_eq_outside _ _ [5,4,6,7] 3 _
      (by rw [gFrame_eq]; exact farA5_frameAtoms) (by decide)).trans actual
  · exact (rawStep_none_eq_outside _ _ [6,4,5,7] 3 _
      (by rw [gFrame_eq]; exact farA6_frameAtoms) (by decide)).trans actual
  · exact (rawStep_none_eq_outside _ _ [7,4,5,6] 3 _
      (by rw [gFrame_eq]; exact farA7_frameAtoms) (by decide)).trans actual

theorem frozenRaw_farB (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [11, 12, 13]) :
    frozenRaw? cageRaw 16 depth (geomOf P len) [] (farB o) = none := by
  rw [frozenRaw_leafy (farB o) (farB_leafy o member)]
  have actual := rawFarB_root P len nondeg 0 o 3 member (Or.inl rfl)
  unfold raw? rawWith? at actual
  have equality : underWith cageRaw 16 (geomOf P len) [] (farB o)
      (facts cageRaw 16 0) = (fun _ => []) :=
    funext (underFarB o member 0 (geomOf P len) [])
  rw [equality] at actual
  have choices : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using member
  rcases choices with rfl | rfl | rfl
  · exact (rawStep_none_eq_outside _ _ [11,10,12,13] 3 _
      (by rw [gFrame_eq]; exact farB11_frameAtoms) (by decide)).trans actual
  · exact (rawStep_none_eq_outside _ _ [12,10,11,13] 3 _
      (by rw [gFrame_eq]; exact farB12_frameAtoms) (by decide)).trans actual
  · exact (rawStep_none_eq_outside _ _ [13,10,11,12] 3 _
      (by rw [gFrame_eq]; exact farB13_frameAtoms) (by decide)).trans actual

theorem frozenDescriptor_farA (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [5, 6, 7]) :
    frozenDescriptor? cageRaw 16 depth (geomOf P len) [] (farA o) = none := by
  change caseFromMirror? (frozenRaw? cageRaw 16 depth (geomOf P len) [] (farA o))
    (frozenRaw? cageRaw 16 depth (mirror (geomOf P len)) [] (farA o)) = none
  rw [frozenRaw_farA P len nondeg depth o member]
  rfl

theorem frozenDescriptor_farB (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [11, 12, 13]) :
    frozenDescriptor? cageRaw 16 depth (geomOf P len) [] (farB o) = none := by
  change caseFromMirror? (frozenRaw? cageRaw 16 depth (geomOf P len) [] (farB o))
    (frozenRaw? cageRaw 16 depth (mirror (geomOf P len)) [] (farB o)) = none
  rw [frozenRaw_farB P len nondeg depth o member]
  rfl

theorem frozenFacts_farA (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [5, 6, 7]) :
    frozenFacts cageRaw 16 depth (geomOf P len) [] (farA o) = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [frozenFacts, frozen_children_leafy (farA o) (farA_leafy o member)]
    change (frozenDescriptor? cageRaw 16 depth (geomOf P len) [] (farA o)).toList.map _ ++ [] = []
    rw [frozenDescriptor_farA P len nondeg depth o member]
    rfl

theorem frozenFacts_farB (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [11, 12, 13]) :
    frozenFacts cageRaw 16 depth (geomOf P len) [] (farB o) = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [frozenFacts, frozen_children_leafy (farB o) (farB_leafy o member)]
    change (frozenDescriptor? cageRaw 16 depth (geomOf P len) [] (farB o)).toList.map _ ++ [] = []
    rw [frozenDescriptor_farB P len nondeg depth o member]
    rfl

theorem frozenFacts_oxA (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [5, 6, 7]) :
    frozenFacts cageRaw 16 depth (geomOf P len) [] (oxA o) = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [frozenFacts_noFrame cageRaw 16 depth _ _ _ (oxA_noFrame o member), children_oxA o member]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact frozenFacts_farA P len nondeg depth o member

theorem frozenFacts_oxB (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [11, 12, 13]) :
    frozenFacts cageRaw 16 depth (geomOf P len) [] (oxB o) = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [frozenFacts_noFrame cageRaw 16 depth _ _ _ (oxB_noFrame o member), children_oxB o member]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact frozenFacts_farB P len nondeg depth o member

theorem frozen_under_nearA (nondeg : Nondegenerate P len) (depth reference : Nat) :
    underWith cageRaw 16 (geomOf P len) [] nearA
      (fun g s _ child => frozenFacts cageRaw 16 depth g s child) reference = [] := by
  rw [frozen_under_eq_children, tiedChildren_nearA]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [frozenFacts_oxA P len nondeg depth 5 (by decide),
    frozenFacts_oxA P len nondeg depth 6 (by decide),
    frozenFacts_oxA P len nondeg depth 7 (by decide)]
  rfl

theorem frozen_under_nearB (nondeg : Nondegenerate P len) (depth reference : Nat) :
    underWith cageRaw 16 (geomOf P len) [] nearB
      (fun g s _ child => frozenFacts cageRaw 16 depth g s child) reference = [] := by
  rw [frozen_under_eq_children, tiedChildren_nearB]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [frozenFacts_oxB P len nondeg depth 11 (by decide),
    frozenFacts_oxB P len nondeg depth 12 (by decide),
    frozenFacts_oxB P len nondeg depth 13 (by decide)]
  rfl

theorem frozenRaw_nearA (nondeg : Nondegenerate P len) (depth : Nat) :
    frozenRaw? cageRaw 16 depth (geomOf P len) [] nearA = none := by
  unfold frozenRaw? rawWith?
  rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] none nearA _ [0,5,6,7]
    [1,2,3,0] [some .eq,some .eq,some .gt]
    (by rw [gFrame_eq]; exact nearA_frameAtoms) nearA_ordinary
    (by decide) (by decide) (by decide) (fun r h => by cases h)]
  change consensus [_, _, _] = none
  simp only [frozen_under_nearA P len nondeg depth, appendFacts?_nil, Option.bind_some]
  rw [markedReadback_empty]
  have emptyRead : visitReadback? P len nearA 5 = none := by
    unfold visitReadback? visitRankedAtoms?
    rw [nearA_frameAtoms, near_mark5_tracked_output]
    rfl
  rw [emptyRead]
  rfl

theorem frozenRaw_nearB (nondeg : Nondegenerate P len) (depth : Nat) :
    frozenRaw? cageRaw 16 depth (geomOf P len) [] nearB = none := by
  unfold frozenRaw? rawWith?
  rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] none nearB _ [0,11,12,13]
    [1,2,3,0] [some .eq,some .eq,some .gt]
    (by rw [gFrame_eq]; exact nearB_frameAtoms) nearB_ordinary
    (by decide) (by decide) (by decide) (fun r h => by cases h)]
  change consensus [_, _, _] = none
  simp only [frozen_under_nearB P len nondeg depth, appendFacts?_nil, Option.bind_some]
  rw [markedReadback_empty]
  have emptyRead : visitReadback? P len nearB 11 = none := by
    unfold visitReadback? visitRankedAtoms?
    rw [nearB_frameAtoms, nearB_mark11_empty]
    rfl
  rw [emptyRead]
  rfl

theorem frozenFacts_nearA (nondeg : Nondegenerate P len) (depth : Nat) :
    frozenFacts cageRaw 16 depth (geomOf P len) [] nearA = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [frozenFacts, children_nearA]
    change (caseFromMirror? (frozenRaw? cageRaw 16 depth (geomOf P len) [] nearA)
      (frozenRaw? cageRaw 16 depth (mirror (geomOf P len)) [] nearA)).toList.map _ ++ _ = []
    rw [frozenRaw_nearA P len nondeg depth]
    simp only [caseFromMirror?, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [frozenFacts_oxA P len nondeg depth 5 (by decide),
      frozenFacts_oxA P len nondeg depth 6 (by decide),
      frozenFacts_oxA P len nondeg depth 7 (by decide)]
    rfl

theorem frozenFacts_nearB (nondeg : Nondegenerate P len) (depth : Nat) :
    frozenFacts cageRaw 16 depth (geomOf P len) [] nearB = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [frozenFacts, children_nearB]
    change (caseFromMirror? (frozenRaw? cageRaw 16 depth (geomOf P len) [] nearB)
      (frozenRaw? cageRaw 16 depth (mirror (geomOf P len)) [] nearB)).toList.map _ ++ _ = []
    rw [frozenRaw_nearB P len nondeg depth]
    simp only [caseFromMirror?, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [frozenFacts_oxB P len nondeg depth 11 (by decide),
      frozenFacts_oxB P len nondeg depth 12 (by decide),
      frozenFacts_oxB P len nondeg depth 13 (by decide)]
    rfl

theorem frozen_under_root (nondeg : Nondegenerate P len) (depth reference : Nat) :
    underWith cageRaw 16 (geomOf P len) [] root0
      (fun g s _ child => frozenFacts cageRaw 16 depth g s child) reference = [] := by
  rw [frozen_under_eq_children, tiedChildren_root]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [frozenFacts_nearA P len nondeg depth, frozenFacts_nearB P len nondeg depth]
  rfl


theorem emptyRoot_readback3 : visitReadback? P len root0 3 =
    readbackWith? P len (rootTemp RS.R RS.R false) root0 3 := by
  unfold visitReadback? readbackWith?
  rw [root_empty_atoms3, rootAtoms_RR_3]

theorem emptyRoot_readback9 : visitReadback? P len root0 9 =
    readbackWith? P len (rootTemp RS.R RS.R false) root0 9 := by
  unfold visitReadback? readbackWith?
  rw [root_empty_atoms9, rootAtoms_RR_9]

theorem frozenRaw_root (nondeg : Nondegenerate P len) (depth : Nat) :
    frozenRaw? cageRaw 16 depth (geomOf P len) [] root0 = none := by
  unfold frozenRaw? rawWith?
  rw [rawStep?_consensus cageRaw 16 (geomOf P len) [] none root0 _ [1,2,3,9]
    [1,2,3,0] [some .gt,some .eq,some .gt]
    (by rw [gFrame_eq]; exact root0_frameAtoms) root_ordinary
    (by decide) (by decide) (by decide) (fun r h => by cases h)]
  change consensus [_, _] = none
  simp only [frozen_under_root P len nondeg depth, appendFacts?_nil, Option.bind_some]
  rw [markedReadback_empty, markedReadback_empty, emptyRoot_readback3, emptyRoot_readback9,
    (rootReadback_equal P len RS.R false).1, (rootReadback_equal P len RS.R false).2,
    descriptorOfOrientedVolume?_of_ne (neg_ne_zero.mpr (nondeg k0)),
    descriptorOfOrientedVolume?_of_ne (nondeg k0), letterOfVolume_neg (nondeg k0)]
  generalize letterOfVolume (ligandVolumeWith P len k0) = raw
  cases raw <;> rfl

/-- The whole independently generated frozen profile refuses the final center0 descriptor.
All recursively produced child maps have been derived, rather than frozen from CURRENT. -/
theorem frozenAssign_root (nondeg : Nondegenerate P len) :
    frozenAssignCenter? cageRaw 16 (geomOf P len) 0 = none := by
  change caseFromMirror?
    (frozenRaw? cageRaw 16 (structuralDepth cageRaw root0) (geomOf P len) [] root0)
    (frozenRaw? cageRaw 16 (structuralDepth cageRaw root0) (mirror (geomOf P len)) [] root0) = none
  rw [frozenRaw_root P len nondeg]
  rfl

end Family

/-- Concrete final-output contrast on the same actual 15-atom input and certified geometry.
This compares two independent recursive profiles, both using consensus aggregation. -/
theorem independent_final_profiles_disagree :
    LocalizedGenericMarkedRecalculation.assignCenter? cageRaw (comparatorFuel cageRaw)
        (geomOf positions positions_length) 0 ≠
      frozenAssignCenter? cageRaw 16 (geomOf positions positions_length) 0 := by
  have distinct : jointLetterA positions positions_length ≠ jointLetterB positions positions_length := by
    simp [jointLetterA, jointLetterB, letterOfVolume, inCageA, not_lt.mpr inCageB.le]
  rw [assignCenter_eq_rootConsensus positions positions_length inNondegenerate,
    (rootConsensus_cases positions positions_length inNondegenerate false).1 distinct,
    frozenAssign_root positions positions_length inNondegenerate]
  simp



/-- The final generic index-enumerated reports differ, because the regenerated report has a
center0 entry and the independently generated frozen report cannot have one. No conclusions
about the other final centers are needed for this report contrast. -/
theorem independent_final_reports_disagree :
    LocalizedGenericMarkedRecalculation.assign cageRaw (geomOf positions positions_length) ≠
      frozenAssign cageRaw 16 (geomOf positions positions_length) := by
  have unequal := independent_final_profiles_disagree
  rw [frozenAssign_root positions positions_length inNondegenerate] at unequal
  cases result : LocalizedGenericMarkedRecalculation.assignCenter? cageRaw (comparatorFuel cageRaw)
      (geomOf positions positions_length) 0 with
  | none => exact False.elim (unequal result)
  | some descriptor =>
    have actualMember : (0, descriptor) ∈
        LocalizedGenericMarkedRecalculation.assign cageRaw (geomOf positions positions_length) := by
      unfold LocalizedGenericMarkedRecalculation.assign
      apply List.mem_filterMap.mpr
      exact ⟨0, by decide, by rw [result]; rfl⟩
    have absent : (0, descriptor) ∉ frozenAssign cageRaw 16 (geomOf positions positions_length) := by
      intro member
      unfold frozenAssign at member
      obtain ⟨center, _, returned⟩ := List.mem_filterMap.mp member
      cases value : frozenAssignCenter? cageRaw 16 (geomOf positions positions_length) center with
      | none => simp [value] at returned
      | some letter =>
        simp only [value, Option.map_some, Option.some.injEq, Prod.mk.injEq] at returned
        rcases returned with ⟨rfl, rfl⟩
        rw [frozenAssign_root positions positions_length inNondegenerate] at value
        cases value
    intro equality
    exact absent (equality ▸ actualMember)


end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenRaw?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenDescriptor?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenAssignCenter?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_noFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_forcedLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_shallowNoFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozen_children_leafy
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozen_under_eq_children
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozen_under_leafy

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.rawStep_none_eq_outside

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenRaw_leafy

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenRaw_farA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenRaw_farB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenDescriptor_farA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenDescriptor_farB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_farA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_farB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_oxA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_oxB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozen_under_nearA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozen_under_nearB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenRaw_nearA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenRaw_nearB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_nearA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenFacts_nearB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozen_under_root

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.root_empty_atoms3

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.root_empty_atoms9

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.emptyRoot_readback3

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.emptyRoot_readback9

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenRaw_root

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenAssign_root

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.independent_final_profiles_disagree

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.frozenAssign

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage.independent_final_reports_disagree
