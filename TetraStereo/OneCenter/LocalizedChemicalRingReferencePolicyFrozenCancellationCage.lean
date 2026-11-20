import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation
import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins
import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-! Independently recursive frozen cancellation, executed on every selected cage promotion.
No auxiliary map or desired descriptor is supplied. All completed refusals are some none;
operational failure remains outer none. This explicit single-current policy is neutral with
respect to journal source attribution. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage

open LocalizedGenericMarkedRecalculation hiding facts
open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedChemicalRingReferencePolicyFrozenCancellation
open LocalizedChemicalRingReferencePolicyFrozenCancellationPins
open LocalizedRecursiveAuxiliaryPhysicalCompletion
open LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedHiddenParityMarkedProbe hiding frameAtoms?
open LocalizedHiddenParityPromotedReadback hiding rankedAtoms?
open LocalizedHiddenParityPromotedReflection
open LocalizedGenericMarkedRecalculationCage
open LocalizedChemicalRingReferencePolicyFrozenCage (emptyRoot_readback3 emptyRoot_readback9)

theorem children_leafy (node : RawMolecule.CanonicalBranchNode)
    (leafy : ∀ child ∈ cageRaw.canonicalChildren node,
      frameAtoms? cageRaw child = none ∧
      ∀ next ∈ cageRaw.canonicalChildren child, next.forcedLeaf = true)
    (depth : Nat) (geom : Geometry) :
    collect (facts cageRaw 16 depth geom []) (cageRaw.canonicalChildren node) = some [] := by
  exact collect_empty _ _ (fun child member =>
    facts_shallowNoFrame cageRaw 16 depth geom [] child
      (leafy child member).1 (leafy child member).2)

theorem selected_leafy (node : RawMolecule.CanonicalBranchNode)
    (leafy : ∀ child ∈ cageRaw.canonicalChildren node,
      frameAtoms? cageRaw child = none ∧
      ∀ next ∈ cageRaw.canonicalChildren child, next.forcedLeaf = true)
    (depth : Nat) (geom : Geometry) :
    collect (facts cageRaw 16 depth geom []) (tiedChildren cageRaw 16 [] node) = some [] := by
  exact collect_empty _ _ (fun child member =>
    facts_shallowNoFrame cageRaw 16 depth geom [] child
      (leafy child (mem_tiedChildren cageRaw 16 [] node child member)).1
      (leafy child (mem_tiedChildren cageRaw 16 [] node child member)).2)

section Family
variable (P : List CartesianPoint3) (len : P.length = 15)

theorem raw_farA (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [5,6,7]) :
    raw cageRaw 16 depth (geomOf P len) [] (farA o) = some none := by
  obtain ⟨h65, h75, h56, h76, h57, h67⟩ := farReadbackA_letters P len nondeg
  have choices : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using member
  unfold raw
  rcases choices with rfl | rfl | rfl
  · rw [rawWith_partition cageRaw 16 (geomOf P len) [] (farA 5) _
      [5,4,6,7] [0,2,3,1] [some .gt,some .eq,some .gt]
      (by rw [gFrame_eq]; exact farA5_frameAtoms) (farA_ordinary 5 (by decide))
      (by decide) (by decide) (by decide)
      (selected_leafy (farA 5) (farA_leafy 5 (by decide)) depth (geomOf P len))]
    change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] (farA 5) 6,
      promotionOutcome cageRaw 16 (geomOf P len) [] (farA 5) 7] = some none
    rw [promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farA 5) 6 _
      ((markedReadback_empty P len (farA 5) 6).trans h56),
      promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farA 5) 7 _
      ((markedReadback_empty P len (farA 5) 7).trans h57)]
    generalize farLetterA P len = letter
    cases letter <;> decide
  · rw [rawWith_partition cageRaw 16 (geomOf P len) [] (farA 6) _
      [6,4,5,7] [0,2,3,1] [some .gt,some .eq,some .gt]
      (by rw [gFrame_eq]; exact farA6_frameAtoms) (farA_ordinary 6 (by decide))
      (by decide) (by decide) (by decide)
      (selected_leafy (farA 6) (farA_leafy 6 (by decide)) depth (geomOf P len))]
    change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] (farA 6) 5,
      promotionOutcome cageRaw 16 (geomOf P len) [] (farA 6) 7] = some none
    rw [promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farA 6) 5 _
      ((markedReadback_empty P len (farA 6) 5).trans h65),
      promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farA 6) 7 _
      ((markedReadback_empty P len (farA 6) 7).trans h67)]
    generalize farLetterA P len = letter
    cases letter <;> decide
  · rw [rawWith_partition cageRaw 16 (geomOf P len) [] (farA 7) _
      [7,4,5,6] [0,2,3,1] [some .gt,some .eq,some .gt]
      (by rw [gFrame_eq]; exact farA7_frameAtoms) (farA_ordinary 7 (by decide))
      (by decide) (by decide) (by decide)
      (selected_leafy (farA 7) (farA_leafy 7 (by decide)) depth (geomOf P len))]
    change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] (farA 7) 5,
      promotionOutcome cageRaw 16 (geomOf P len) [] (farA 7) 6] = some none
    rw [promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farA 7) 5 _
      ((markedReadback_empty P len (farA 7) 5).trans h75),
      promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farA 7) 6 _
      ((markedReadback_empty P len (farA 7) 6).trans h76)]
    generalize farLetterA P len = letter
    cases letter <;> decide

theorem descriptor_farA (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [5,6,7]) :
    descriptor cageRaw 16 depth (geomOf P len) [] (farA o) = some none := by
  change (do
    let first ← raw cageRaw 16 depth (geomOf P len) [] (farA o)
    let second ← raw cageRaw 16 depth (mirror (geomOf P len)) [] (farA o)
    pure (caseFromMirror? first second)) = some none
  rw [raw_farA P len nondeg depth o member, geomOf_mirror,
    raw_farA _ _ (nondegenerate_mirror P len nondeg) depth o member]
  rfl

theorem facts_farA (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [5,6,7]) :
    facts cageRaw 16 depth (geomOf P len) [] (farA o) = some [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [facts, children_leafy (farA o) (farA_leafy o member)]
    change (do
      let outcome ← descriptor cageRaw 16 depth (geomOf P len) [] (farA o)
      let descendants ← some ([] : OccurrenceAuxState)
      pure (outcome.toList.map (factOf (farA o)) ++ descendants)) = some []
    rw [descriptor_farA P len nondeg depth o member]
    rfl

theorem facts_oxA (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [5,6,7]) :
    facts cageRaw 16 depth (geomOf P len) [] (oxA o) = some [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [facts_noFrame cageRaw 16 depth _ _ _ (oxA_noFrame o member), children_oxA o member]
    rw [collect, facts_farA P len nondeg depth o member]
    rfl

theorem raw_farB (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [11,12,13]) :
    raw cageRaw 16 depth (geomOf P len) [] (farB o) = some none := by
  obtain ⟨h1211, h1311, h1112, h1312, h1113, h1213⟩ := farReadbackB_letters P len nondeg
  have choices : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using member
  unfold raw
  rcases choices with rfl | rfl | rfl
  · rw [rawWith_partition cageRaw 16 (geomOf P len) [] (farB 11) _
      [11,10,12,13] [0,2,3,1] [some .gt,some .eq,some .gt]
      (by rw [gFrame_eq]; exact farB11_frameAtoms) (farB_ordinary 11 (by decide))
      (by decide) (by decide) (by decide)
      (selected_leafy (farB 11) (farB_leafy 11 (by decide)) depth (geomOf P len))]
    change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] (farB 11) 12,
      promotionOutcome cageRaw 16 (geomOf P len) [] (farB 11) 13] = some none
    rw [promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farB 11) 12 _
      ((markedReadback_empty P len (farB 11) 12).trans h1112),
      promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farB 11) 13 _
      ((markedReadback_empty P len (farB 11) 13).trans h1113)]
    generalize farLetterB P len = letter
    cases letter <;> decide
  · rw [rawWith_partition cageRaw 16 (geomOf P len) [] (farB 12) _
      [12,10,11,13] [0,2,3,1] [some .gt,some .eq,some .gt]
      (by rw [gFrame_eq]; exact farB12_frameAtoms) (farB_ordinary 12 (by decide))
      (by decide) (by decide) (by decide)
      (selected_leafy (farB 12) (farB_leafy 12 (by decide)) depth (geomOf P len))]
    change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] (farB 12) 11,
      promotionOutcome cageRaw 16 (geomOf P len) [] (farB 12) 13] = some none
    rw [promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farB 12) 11 _
      ((markedReadback_empty P len (farB 12) 11).trans h1211),
      promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farB 12) 13 _
      ((markedReadback_empty P len (farB 12) 13).trans h1213)]
    generalize farLetterB P len = letter
    cases letter <;> decide
  · rw [rawWith_partition cageRaw 16 (geomOf P len) [] (farB 13) _
      [13,10,11,12] [0,2,3,1] [some .gt,some .eq,some .gt]
      (by rw [gFrame_eq]; exact farB13_frameAtoms) (farB_ordinary 13 (by decide))
      (by decide) (by decide) (by decide)
      (selected_leafy (farB 13) (farB_leafy 13 (by decide)) depth (geomOf P len))]
    change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] (farB 13) 11,
      promotionOutcome cageRaw 16 (geomOf P len) [] (farB 13) 12] = some none
    rw [promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farB 13) 11 _
      ((markedReadback_empty P len (farB 13) 11).trans h1311),
      promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] (farB 13) 12 _
      ((markedReadback_empty P len (farB 13) 12).trans h1312)]
    generalize farLetterB P len = letter
    cases letter <;> decide

theorem descriptor_farB (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [11,12,13]) :
    descriptor cageRaw 16 depth (geomOf P len) [] (farB o) = some none := by
  change (do
    let first ← raw cageRaw 16 depth (geomOf P len) [] (farB o)
    let second ← raw cageRaw 16 depth (mirror (geomOf P len)) [] (farB o)
    pure (caseFromMirror? first second)) = some none
  rw [raw_farB P len nondeg depth o member, geomOf_mirror,
    raw_farB _ _ (nondegenerate_mirror P len nondeg) depth o member]
  rfl

theorem facts_farB (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [11,12,13]) :
    facts cageRaw 16 depth (geomOf P len) [] (farB o) = some [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [facts, children_leafy (farB o) (farB_leafy o member)]
    change (do
      let outcome ← descriptor cageRaw 16 depth (geomOf P len) [] (farB o)
      let descendants ← some ([] : OccurrenceAuxState)
      pure (outcome.toList.map (factOf (farB o)) ++ descendants)) = some []
    rw [descriptor_farB P len nondeg depth o member]
    rfl

theorem facts_oxB (nondeg : Nondegenerate P len) (depth o : Nat)
    (member : o ∈ [11,12,13]) :
    facts cageRaw 16 depth (geomOf P len) [] (oxB o) = some [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [facts_noFrame cageRaw 16 depth _ _ _ (oxB_noFrame o member), children_oxB o member]
    rw [collect, facts_farB P len nondeg depth o member]
    rfl

theorem selected_nearA (nondeg : Nondegenerate P len) (depth : Nat) :
    collect (facts cageRaw 16 depth (geomOf P len) [])
      (tiedChildren cageRaw 16 [] nearA) = some [] := by
  rw [tiedChildren_nearA]
  rw [collect, facts_oxA P len nondeg depth 5 (by decide),
    collect, facts_oxA P len nondeg depth 6 (by decide),
    collect, facts_oxA P len nondeg depth 7 (by decide)]
  rfl

theorem raw_nearA (nondeg : Nondegenerate P len) (depth : Nat) :
    raw cageRaw 16 depth (geomOf P len) [] nearA = some none := by
  unfold raw
  rw [rawWith_partition cageRaw 16 (geomOf P len) [] nearA _ [0,5,6,7]
    [1,2,3,0] [some .eq,some .eq,some .gt]
    (by rw [gFrame_eq]; exact nearA_frameAtoms) nearA_ordinary
    (by decide) (by decide) (by decide) (selected_nearA P len nondeg depth)]
  change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] nearA 5,
    promotionOutcome cageRaw 16 (geomOf P len) [] nearA 6,
    promotionOutcome cageRaw 16 (geomOf P len) [] nearA 7] = some none
  rw [promotionOutcome_unresolved cageRaw 16 (geomOf P len) [] nearA 5
    (nearA_all_nonunique 5 (by decide)),
    promotionOutcome_unresolved cageRaw 16 (geomOf P len) [] nearA 6
    (nearA_all_nonunique 6 (by decide)),
    promotionOutcome_unresolved cageRaw 16 (geomOf P len) [] nearA 7
    (nearA_all_nonunique 7 (by decide))]
  decide

theorem descriptor_nearA (nondeg : Nondegenerate P len) (depth : Nat) :
    descriptor cageRaw 16 depth (geomOf P len) [] nearA = some none := by
  change (do
    let first ← raw cageRaw 16 depth (geomOf P len) [] nearA
    let second ← raw cageRaw 16 depth (mirror (geomOf P len)) [] nearA
    pure (caseFromMirror? first second)) = some none
  rw [raw_nearA P len nondeg depth, geomOf_mirror,
    raw_nearA _ _ (nondegenerate_mirror P len nondeg) depth]
  rfl

theorem facts_nearA (nondeg : Nondegenerate P len) (depth : Nat) :
    facts cageRaw 16 depth (geomOf P len) [] nearA = some [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [facts, children_nearA]
    change (do
      let outcome ← descriptor cageRaw 16 depth (geomOf P len) [] nearA
      let descendants ← collect (facts cageRaw 16 depth (geomOf P len) [])
        [oxA 5, oxA 6, oxA 7]
      pure (outcome.toList.map (factOf nearA) ++ descendants)) = some []
    rw [descriptor_nearA P len nondeg depth,
      collect, facts_oxA P len nondeg depth 5 (by decide),
      collect, facts_oxA P len nondeg depth 6 (by decide),
      collect, facts_oxA P len nondeg depth 7 (by decide)]
    rfl

theorem selected_nearB (nondeg : Nondegenerate P len) (depth : Nat) :
    collect (facts cageRaw 16 depth (geomOf P len) [])
      (tiedChildren cageRaw 16 [] nearB) = some [] := by
  rw [tiedChildren_nearB]
  rw [collect, facts_oxB P len nondeg depth 11 (by decide),
    collect, facts_oxB P len nondeg depth 12 (by decide),
    collect, facts_oxB P len nondeg depth 13 (by decide)]
  rfl

theorem raw_nearB (nondeg : Nondegenerate P len) (depth : Nat) :
    raw cageRaw 16 depth (geomOf P len) [] nearB = some none := by
  unfold raw
  rw [rawWith_partition cageRaw 16 (geomOf P len) [] nearB _ [0,11,12,13]
    [1,2,3,0] [some .eq,some .eq,some .gt]
    (by rw [gFrame_eq]; exact nearB_frameAtoms) nearB_ordinary
    (by decide) (by decide) (by decide) (selected_nearB P len nondeg depth)]
  change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] nearB 11,
    promotionOutcome cageRaw 16 (geomOf P len) [] nearB 12,
    promotionOutcome cageRaw 16 (geomOf P len) [] nearB 13] = some none
  rw [promotionOutcome_unresolved cageRaw 16 (geomOf P len) [] nearB 11
    (nearB_all_nonunique 11 (by decide)),
    promotionOutcome_unresolved cageRaw 16 (geomOf P len) [] nearB 12
    (nearB_all_nonunique 12 (by decide)),
    promotionOutcome_unresolved cageRaw 16 (geomOf P len) [] nearB 13
    (nearB_all_nonunique 13 (by decide))]
  decide

theorem descriptor_nearB (nondeg : Nondegenerate P len) (depth : Nat) :
    descriptor cageRaw 16 depth (geomOf P len) [] nearB = some none := by
  change (do
    let first ← raw cageRaw 16 depth (geomOf P len) [] nearB
    let second ← raw cageRaw 16 depth (mirror (geomOf P len)) [] nearB
    pure (caseFromMirror? first second)) = some none
  rw [raw_nearB P len nondeg depth, geomOf_mirror,
    raw_nearB _ _ (nondegenerate_mirror P len nondeg) depth]
  rfl

theorem facts_nearB (nondeg : Nondegenerate P len) (depth : Nat) :
    facts cageRaw 16 depth (geomOf P len) [] nearB = some [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [facts, children_nearB]
    change (do
      let outcome ← descriptor cageRaw 16 depth (geomOf P len) [] nearB
      let descendants ← collect (facts cageRaw 16 depth (geomOf P len) [])
        [oxB 11, oxB 12, oxB 13]
      pure (outcome.toList.map (factOf nearB) ++ descendants)) = some []
    rw [descriptor_nearB P len nondeg depth,
      collect, facts_oxB P len nondeg depth 11 (by decide),
      collect, facts_oxB P len nondeg depth 12 (by decide),
      collect, facts_oxB P len nondeg depth 13 (by decide)]
    rfl

theorem selected_root (nondeg : Nondegenerate P len) (depth : Nat) :
    collect (facts cageRaw 16 depth (geomOf P len) [])
      (tiedChildren cageRaw 16 [] root0) = some [] := by
  rw [tiedChildren_root, collect, facts_nearA P len nondeg depth,
    collect, facts_nearB P len nondeg depth]
  rfl

/-- Both selected final promotions complete with opposite letters and cancel. -/
theorem raw_root (nondeg : Nondegenerate P len) (depth : Nat) :
    raw cageRaw 16 depth (geomOf P len) [] root0 = some none := by
  unfold raw
  rw [rawWith_partition cageRaw 16 (geomOf P len) [] root0 _ [1,2,3,9]
    [1,2,3,0] [some .gt,some .eq,some .gt]
    (by rw [gFrame_eq]; exact root0_frameAtoms) root_ordinary
    (by decide) (by decide) (by decide) (selected_root P len nondeg depth)]
  change promotionAggregate [promotionOutcome cageRaw 16 (geomOf P len) [] root0 3,
    promotionOutcome cageRaw 16 (geomOf P len) [] root0 9] = some none
  have first : markedReadback? cageRaw 16 (geomOf P len) [] root0 3 =
      some (letterOfVolume (ligandVolumeWith P len k0)).swap := by
    rw [markedReadback_empty, emptyRoot_readback3, (rootReadback_equal P len RS.R false).1,
      descriptorOfOrientedVolume?_of_ne (neg_ne_zero.mpr (nondeg k0)),
      letterOfVolume_neg (nondeg k0)]
  have second : markedReadback? cageRaw 16 (geomOf P len) [] root0 9 =
      some (letterOfVolume (ligandVolumeWith P len k0)) := by
    rw [markedReadback_empty, emptyRoot_readback9, (rootReadback_equal P len RS.R false).2,
      descriptorOfOrientedVolume?_of_ne (nondeg k0)]
  rw [promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] root0 3 _ first,
    promotionOutcome_descriptor cageRaw 16 (geomOf P len) [] root0 9 _ second]
  generalize letterOfVolume (ligandVolumeWith P len k0) = letter
  cases letter <;> decide

theorem descriptor_root (nondeg : Nondegenerate P len) (depth : Nat) :
    descriptor cageRaw 16 depth (geomOf P len) [] root0 = some none := by
  change (do
    let first ← raw cageRaw 16 depth (geomOf P len) [] root0
    let second ← raw cageRaw 16 depth (mirror (geomOf P len)) [] root0
    pure (caseFromMirror? first second)) = some none
  rw [raw_root P len nondeg depth, geomOf_mirror,
    raw_root _ _ (nondegenerate_mirror P len nondeg) depth]
  rfl

/-- Independent final cancellation profile: completed refusal, not operational failure. -/
theorem assignCenter_root (nondeg : Nondegenerate P len) :
    assignCenter cageRaw 16 (geomOf P len) 0 = some none :=
  descriptor_root P len nondeg (structuralDepth cageRaw root0)

end Family
end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.children_leafy

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.selected_leafy

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.raw_farA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.descriptor_farA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.facts_farA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.facts_oxA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.raw_farB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.descriptor_farB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.facts_farB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.facts_oxB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.selected_nearA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.raw_nearA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.descriptor_nearA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.facts_nearA

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.selected_nearB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.raw_nearB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.descriptor_nearB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.facts_nearB

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.selected_root

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.raw_root

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.descriptor_root

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage.assignCenter_root
