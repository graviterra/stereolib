import TetraStereo.OneCenter.LocalizedChemicalRingDescriptorSpatialMirror
import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked
import TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport
import TetraStereo.OneCenter.DeclarativeCIPRetainedWindowIndependence
import TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation
import TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
**Exact generated-label behavior under spatial mirror**, for every step and molecule.

Reflecting the geometry reflects the generated fact list entrywise: uppercase facts swap and
lowercase facts are unchanged, at the same occurrence keys. Hence the raw-state descriptor map of
the reflected state is the reflected map, and at one target the actual retained keys of the two
states have the same prior keys; a pair of slots changes order exactly when it is prior-tied.
With injective prior keys the two actual rankings are the same permutation.

No comparison outcome, label value, success or physical sign is assumed. Frames, trees and windows
of the two states are compiled independently and related by accepted isomorphism and window lemmas.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedRetainedDescriptorTransport (retainedPairCompare_reflect)
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingDescriptorSpatialMirror
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedStateReader
open LocalizedMarkedOperationEvaluator (Operations underWith)
open LocalizedGenericMarkedRecalculation (Geometry mirror factOf flatMap_congr_mem)
open LocalizedChemicalRingCompletenessMarked (slotPerm keyOrder_eq_slots)

noncomputable section
open scoped Classical

/-- A generated fact under spatial reflection. -/
def mirrorFact (fact : OccurrenceAuxFact) : OccurrenceAuxFact :=
  if fact.uppercase then { fact with descriptor := fact.descriptor.swap } else fact

theorem mirrorFact_key (fact : OccurrenceAuxFact) : (mirrorFact fact).key = fact.key := by
  unfold mirrorFact
  split <;> rfl

theorem factOf_spatialMirror (node : RawMolecule.CanonicalBranchNode)
    (label : LocalizedTetrahedralRSPseudoDescriptor) :
    factOf node (spatialMirror label) = mirrorFact (factOf node label) := by
  rcases label with raw | raw
  · rfl
  · cases raw <;> rfl

/-- **Reflecting the geometry reflects the generated facts entrywise.** -/
theorem factsWith_mirror (step : Step) (mol : RawMolecule) (ops : Operations) :
    ∀ (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
      (node : RawMolecule.CanonicalBranchNode),
      factsWith step mol ops depth (mirror geom) state ctx node =
        (factsWith step mol ops depth geom state ctx node).map mirrorFact := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro geom state ctx node
      rw [factsWith_succ, factsWith_succ, descriptorWith_spatialMirror, List.map_append,
        List.map_flatMap]
      congr 1
      · cases descriptorWith step mol ops depth geom state ctx node with
        | none => rfl
        | some label => simp [factOf_spatialMirror]
      · apply flatMap_congr_mem
        intro child _
        exact ih geom state ctx child

theorem underWith_mirror (step : Step) (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (mark : Nat) :
    underWith mol ops (mirror geom) state node (factsWith step mol ops depth) mark =
      (underWith mol ops geom state node (factsWith step mol ops depth) mark).map mirrorFact := by
  unfold underWith
  rw [List.map_flatMap]
  apply flatMap_congr_mem
  intro child _
  exact factsWith_mirror step mol ops depth geom state _ child

private theorem factDescriptor_mirror (fact : OccurrenceAuxFact) :
    factDescriptor (mirrorFact fact) = (factDescriptor fact).reflect := by
  rcases fact with ⟨key, atom, descriptor, uppercase, positions⟩
  cases uppercase <;> cases descriptor <;> rfl

/-- The raw-state descriptor map of a reflected state is the reflected map. -/
theorem rawStateDescriptorMap_mirror (input : CertifiedLocalizedCIPInput) (state : OccurrenceAuxState) :
    rawStateDescriptorMap input (state.map mirrorFact) =
      (rawStateDescriptorMap input state).reflect := by
  funext unit
  unfold rawStateDescriptorMap DescriptorMap.reflect rawStateFact?
  rw [List.find?_map]
  have predicate : ((fun fact : OccurrenceAuxFact => fact.key == rawOccurrenceKey unit.1) ∘ mirrorFact) =
      fun fact => fact.key == rawOccurrenceKey unit.1 := by
    funext fact
    simp only [Function.comp, mirrorFact_key]
  rw [predicate]
  dsimp only
  cases state.find? (fun fact => fact.key == rawOccurrenceKey unit.1) with
  | none => rfl
  | some fact => exact congrArg some (factDescriptor_mirror fact)

/-! ## The order of keys -/

section Keys

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom]

private theorem compare_eq_of_agrees {a b c d : CompleteLigandRule5Key}
    (agrees : OrderAgrees a b c d) : compare a b = compare c d := by
  have less : compare a b = .lt ↔ compare c d = .lt :=
    (completeLigandRule5Key_compare_lt_iff a b).trans
      (agrees.1.trans (completeLigandRule5Key_compare_lt_iff c d).symm)
  have same : compare a b = .eq ↔ compare c d = .eq :=
    (completeLigandRule5Key_compare_eq_iff a b).trans
      (agrees.2.trans (completeLigandRule5Key_compare_eq_iff c d).symm)
  cases first : compare a b <;> cases second : compare c d <;> simp_all

/-- Keys of reflected-map graphs at their own window against keys of isomorphic source graphs at
another window. -/
theorem compare_reflect_across (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) {left right left' right' : RootedDigraph Atom}
    (isoL : RootedDigraph.Iso left left') (isoR : RootedDigraph.Iso right right')
    {W D W' D' : Nat} (coverL : WindowCovers left W D) (coverR : WindowCovers right W D)
    (coverL' : WindowCovers left' W' D') (coverR' : WindowCovers right' W' D') :
    compare (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit left' W' D')
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit right' W' D') =
      if (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)).1 =
          (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)).1 then
        (compare (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)
          (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)).swap
      else compare (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) := by
  have boundW : W ≤ max W W' := Nat.le_max_left _ _
  have boundD : D ≤ max D D' := Nat.le_max_left _ _
  have boundW' : W' ≤ max W W' := Nat.le_max_right _ _
  have boundD' : D' ≤ max D D' := Nat.le_max_right _ _
  have imageWindow := retainedCompleteLigandRule5KeyAt_orderAgrees_window molecule
    descriptorMap.reflect unit coverL' (windowCovers_mono coverL' boundW' boundD') coverR'
    (windowCovers_mono coverR' boundW' boundD')
  have sourceWindow := retainedCompleteLigandRule5KeyAt_orderAgrees_window molecule
    descriptorMap unit coverL (windowCovers_mono coverL boundW boundD) coverR
    (windowCovers_mono coverR boundW boundD)
  rw [compare_eq_of_agrees imageWindow.1,
    retainedCompleteLigandRule5KeyAt_iso molecule descriptorMap.reflect unit isoL,
    retainedCompleteLigandRule5KeyAt_iso molecule descriptorMap.reflect unit isoR,
    retainedPairCompare_reflect molecule descriptorMap unit left right,
    compare_eq_of_agrees sourceWindow.1]
  have priors : (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)).1 =
      (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)).1 ↔
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left (max W W') (max D D') =
        retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right (max W W') (max D D') :=
    sourceWindow.2.2
  by_cases tied : (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)).1 =
      (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)).1
  · rw [if_pos tied, if_pos (priors.mp tied)]
  · rw [if_neg tied, if_neg (fun same => tied (priors.mpr same))]

end Keys

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

private theorem frames_same (first second : OccurrenceAuxState) :
    (rawStateFrames input single first target real unit targetUnit).frame =
      (rawStateFrames input single second target real unit targetUnit).frame :=
  Option.some.inj ((rawStateFrames input single first target real unit targetUnit).frameComputed.symm.trans
    (rawStateFrames input single second target real unit targetUnit).frameComputed)

private theorem slot_iso (first second : OccurrenceAuxState) (slot : Fin 4) :
    Nonempty (RootedDigraph.Iso
      (ruleMajorTreeGraph ((rawStateFrames input single first target real unit targetUnit).stages slot).a.tree)
      (ruleMajorTreeGraph ((rawStateFrames input single second target real unit targetUnit).stages slot).a.tree)) := by
  apply LocalizedMarkedRetainedFuelSaturation.graphIso_of_sameSource_crossFuel input _ _ _ _ _ _
    ((rawStateFrames input single first target real unit targetUnit).stages slot).a.trace
    ((rawStateFrames input single second target real unit targetUnit).stages slot).a.trace
  rw [((rawStateFrames input single first target real unit targetUnit).stages slot).a.sourceEq,
    ((rawStateFrames input single second target real unit targetUnit).stages slot).a.sourceEq,
    frames_same input single target real unit targetUnit first second]

private theorem slot_cover (first : OccurrenceAuxState) (slot : Fin 4) :
    WindowCovers
      (ruleMajorTreeGraph ((rawStateFrames input single first target real unit targetUnit).stages slot).a.tree)
      (rawStateFrames input single first target real unit targetUnit).W
      (rawStateFrames input single first target real unit targetUnit).D :=
  ⟨(((rawStateFrames input single first target real unit targetUnit).stages slot).a_width_le).trans
      ((rawStateFrames input single first target real unit targetUnit).widthBound slot),
    (((rawStateFrames input single first target real unit targetUnit).stages slot).a_depth_le).trans
      ((rawStateFrames input single first target real unit targetUnit).depthBound slot)⟩

/-- **The order of actual keys under spatial reflection.** A pair of slots keeps its order unless
its prior keys tie, and then the order is reversed. -/
theorem rawStateKeys_mirror_compare (left right : Fin 4) :
    compare (rawStateKeys input single (state.map mirrorFact) target real unit targetUnit left)
        (rawStateKeys input single (state.map mirrorFact) target real unit targetUnit right) =
      if (ofLex (rawStateKeys input single state target real unit targetUnit left)).1 =
          (ofLex (rawStateKeys input single state target real unit targetUnit right)).1 then
        (compare (rawStateKeys input single state target real unit targetUnit left)
          (rawStateKeys input single state target real unit targetUnit right)).swap
      else compare (rawStateKeys input single state target real unit targetUnit left)
        (rawStateKeys input single state target real unit targetUnit right) := by
  obtain ⟨isoL⟩ := slot_iso input single target real unit targetUnit state (state.map mirrorFact) left
  obtain ⟨isoR⟩ := slot_iso input single target real unit targetUnit state (state.map mirrorFact) right
  have across := compare_reflect_across input.moleculeGraph (rawStateDescriptorMap input state) unit
    isoL isoR (slot_cover input single target real unit targetUnit state left)
    (slot_cover input single target real unit targetUnit state right)
    (slot_cover input single target real unit targetUnit (state.map mirrorFact) left)
    (slot_cover input single target real unit targetUnit (state.map mirrorFact) right)
  rw [← rawStateDescriptorMap_mirror] at across
  exact across

/-- With injective prior keys the two states order the slots identically. -/
theorem rawStateKeys_mirror_compare_of_prior_injective
    (injective : Function.Injective fun slot =>
      (ofLex (rawStateKeys input single state target real unit targetUnit slot)).1)
    (left right : Fin 4) :
    compare (rawStateKeys input single (state.map mirrorFact) target real unit targetUnit left)
        (rawStateKeys input single (state.map mirrorFact) target real unit targetUnit right) =
      compare (rawStateKeys input single state target real unit targetUnit left)
        (rawStateKeys input single state target real unit targetUnit right) := by
  rw [rawStateKeys_mirror_compare]
  by_cases same : left = right
  · subst same
    rw [if_pos rfl, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl]
    rfl
  · rw [if_neg (fun tied => same (injective tied))]

/-- Equal key comparisons with injective keys give the same sorted slot permutation. -/
theorem slotPerm_eq_of_compare {K K' : Fin 4 → CompleteLigandRule5Key}
    (injective : Function.Injective K)
    (same : ∀ left right, compare (K' left) (K' right) = compare (K left) (K right)) :
    slotPerm K' = slotPerm K := by
  have le_iff (a b : Fin 4) : K' a ≤ K' b ↔ K a ≤ K b := by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq, ← completeLigandRule5Key_compare_lt_iff,
      ← completeLigandRule5Key_compare_lt_iff, ← completeLigandRule5Key_compare_eq_iff,
      ← completeLigandRule5Key_compare_eq_iff, same]
  have order : keyOrder K' (List.finRange 4) = keyOrder K (List.finRange 4) := by
    have first : (keyOrder K' (List.finRange 4)).Pairwise (fun a b => K b ≤ K a) :=
      (keyOrder_pairwise K' _).imp (fun le => (le_iff _ _).mp le)
    have perm := (keyOrder_perm K' (List.finRange 4)).trans (keyOrder_perm K (List.finRange 4)).symm
    exact perm.eq_of_pairwise (fun a b _ _ ab ba => injective (le_antisymm ba ab)) first
      (keyOrder_pairwise K _)
  rw [keyOrder_eq_slots, keyOrder_eq_slots] at order
  simp only [List.cons.injEq, and_true] at order
  apply Equiv.ext
  intro i
  fin_cases i
  · exact order.1
  · exact order.2.1
  · exact order.2.2.1
  · exact order.2.2.2

/-- **Injective prior keys: reflection leaves the actual sorted slot permutation unchanged.** -/
theorem slotPerm_mirror_of_prior_injective
    (injective : Function.Injective fun slot =>
      (ofLex (rawStateKeys input single state target real unit targetUnit slot)).1) :
    slotPerm (rawStateKeys input single (state.map mirrorFact) target real unit targetUnit) =
      slotPerm (rawStateKeys input single state target real unit targetUnit) :=
  slotPerm_eq_of_compare
    (fun _ _ tied => injective (congrArg (fun key => (ofLex key).1) tied))
    (rawStateKeys_mirror_compare_of_prior_injective input single state target real unit targetUnit
      injective)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection.factsWith_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection.underWith_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection.rawStateDescriptorMap_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection.compare_reflect_across
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection.rawStateKeys_mirror_compare
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection.slotPerm_mirror_of_prior_injective
