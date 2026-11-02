import TetraStereo.UniversalProof.NativeSourcePhysicalCoordinates
import TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
import TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceReadiness
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment














-- converted_atomic_number is re-exported from NativeSourcePhysicalCoordinates.


section ActualFrame

variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
variable (center : source.AromaticCanonicalTetrahedralCenter)
variable (domain : SingleLeafDomain raw center.1.val)
variable (four : (recordNeighbors raw center.1.val).length = 4)

include converted domain four

noncomputable def actualFrame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel where
  roots := finalOccurrenceRoots source carrierFuel center
  rootsLength := (actual_returned_four_roots raw source converted carrierFuel center domain four).2

noncomputable def slotAtomID (slot : Fin 4) : Nat :=
  (cursorAtomID source
    ((actualFrame raw source converted carrierFuel center domain four).cursorAt slot)).getD 0

theorem actual_slot_endpoint (slot : Fin 4) :
    ∃ atom : source.AromaticCanonicalAtom, atom.val ∈ recordNeighbors raw center.1.val ∧
      ((actualFrame raw source converted carrierFuel center domain four).cursorAt slot).occurrence.1.node.current? = some atom ∧
      ((actualFrame raw source converted carrierFuel center domain four).cursorAt slot).occurrence.1.node.provenance = .realAtom ∧
      slotAtomID raw source converted carrierFuel center domain four slot = atom.val := by
  have present : (actualFrame raw source converted carrierFuel center domain four).cursorAt slot ∈
      finalOccurrenceRoots source carrierFuel center := List.get_mem _ _
  obtain ⟨atom, member, node⟩ := converted_final_cursor_real_root
    raw source converted carrierFuel center domain _ present
  refine ⟨atom, member, ?_, ?_, ?_⟩
  · simp [node, OfficialCIPNode.rootFromEdge]
  · simp [node, OfficialCIPNode.rootFromEdge]
  · simp [slotAtomID, cursorAtomID, node, OfficialCIPNode.rootFromEdge]

theorem actual_roots_real : OccurrenceRootsReal source
    (actualFrame raw source converted carrierFuel center domain four) := by
  intro slot
  obtain ⟨atom, _, current, provenance, _⟩ :=
    actual_slot_endpoint raw source converted carrierFuel center domain four slot
  exact ⟨atom, current, provenance⟩

theorem actual_slot_member (slot : Fin 4) :
    slotAtomID raw source converted carrierFuel center domain four slot ∈
      recordNeighbors raw center.1.val := by
  obtain ⟨atom, member, _, _, equal⟩ :=
    actual_slot_endpoint raw source converted carrierFuel center domain four slot
  simpa only [equal] using member

theorem actual_priority_eq_raw_Z (slot : Fin 4) :
    occurrenceAtomicPriority source (actualFrame raw source converted carrierFuel center domain four) slot =
      raw.atomZAt (slotAtomID raw source converted carrierFuel center domain four slot) := by
  obtain ⟨atom, _, current, _, equal⟩ :=
    actual_slot_endpoint raw source converted carrierFuel center domain four slot
  simp only [occurrenceAtomicPriority, cursorAtomicPriority, current, Option.map_some, Option.getD_some]
  rw [converted_atomic_number raw source converted atom, equal]

theorem slot_ids_eq_returned_ids :
    (List.finRange 4).map (slotAtomID raw source converted carrierFuel center domain four) =
      (finalOccurrenceRootIDs source carrierFuel center).map (fun id => id.getD 0) := by
  let frame := actualFrame raw source converted carrierFuel center domain four
  let read := fun cursor : source.AromaticCanonicalRerootCursor carrierFuel =>
    (cursorAtomID source cursor).getD 0
  have casted := List.ofFn_congr frame.rootsLength (fun i => read (frame.roots.get i))
  have enumerated := List.ofFn_comp' frame.roots.get read
  have allRoots := congrArg (List.map read) (List.ofFn_get frame.roots)
  exact (by simpa only [List.finRange, List.map_ofFn, slotAtomID,
    AromaticCanonicalOccurrenceFourLigandFrame.cursorAt, finalOccurrenceRootIDs,
    List.map_map, frame, read] using casted.symm.trans (enumerated.trans allRoots))

theorem actual_slot_ids_perm :
    ((List.finRange 4).map (slotAtomID raw source converted carrierFuel center domain four)).Perm
      (recordNeighbors raw center.1.val) := by
  rw [slot_ids_eq_returned_ids raw source converted carrierFuel center domain four]
  have transported := (converted_final_root_ids_perm raw source converted carrierFuel center domain).map
    (fun id => id.getD 0)
  simpa only [List.map_map, Function.comp_def, Option.getD_some, List.map_id'] using transported

theorem actual_slot_ids_injective :
    Function.Injective (slotAtomID raw source converted carrierFuel center domain four) := by
  have distinct := (actual_slot_ids_perm raw source converted carrierFuel center domain four).nodup_iff.mpr
    domain.leaf.neighbors_nodup
  have onSlots := (List.nodup_map_iff_inj_on (List.nodup_finRange 4)).mp distinct
  intro left right equal
  exact onSlots left (List.mem_finRange left) right (List.mem_finRange right) equal

theorem actual_priority_injective : Function.Injective
    (occurrenceAtomicPriority source (actualFrame raw source converted carrierFuel center domain four)) := by
  intro left right equal
  rw [actual_priority_eq_raw_Z raw source converted carrierFuel center domain four left,
    actual_priority_eq_raw_Z raw source converted carrierFuel center domain four right] at equal
  have idsEqual := domain.leaf.rank_injective
    (actual_slot_member raw source converted carrierFuel center domain four left)
    (actual_slot_member raw source converted carrierFuel center domain four right) equal
  exact actual_slot_ids_injective raw source converted carrierFuel center domain four idsEqual

/-- A source slot maps into the ACTUAL generated runtime cursor carrier, including previous root. -/
noncomputable def runtimeCursorAt (slot : Fin 4) : CanonicalRerootCursor :=
  { node := canonicalRoot center.1.val (slotAtomID raw source converted carrierFuel center domain four slot),
    previous? := some (canonicalCenterRoot center.1.val) }

theorem runtimeCursorAt_mem (slot : Fin 4) :
    runtimeCursorAt raw source converted carrierFuel center domain four slot ∈
      generatedRuntimeRoots raw center.1.val := by
  rw [generatedRuntimeRoots_eq raw center.1.val domain.leaf]
  exact List.mem_map.mpr ⟨slotAtomID raw source converted carrierFuel center domain four slot,
    actual_slot_member raw source converted carrierFuel center domain four slot, rfl⟩

theorem runtimeCursorAt_injective :
    Function.Injective (runtimeCursorAt raw source converted carrierFuel center domain four) := by
  intro left right equal
  apply actual_slot_ids_injective raw source converted carrierFuel center domain four
  exact congrArg (fun cursor : CanonicalRerootCursor => cursor.node.atom) equal

/-- The actual compiled constitutional head observes the raw atom at the recovered source slot. -/
theorem actual_key_head_raw_Z
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (actualFrame raw source converted carrierFuel center domain four).roots = some keys)
    (slot : Fin 4) :
    (ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
      (keys.keyAt slot).rule3.constitutional.sourceNodes).head? =
      some [([], DeclarativeCIP.ExactAtomicNumber.ofNat
        (raw.atomZAt (slotAtomID raw source converted carrierFuel center domain four slot)))] := by
  have head := occurrence_keyFrame_exact_atomic_head source
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
    (actualFrame raw source converted carrierFuel center domain four)
    (actual_roots_real raw source converted carrierFuel center domain four) keys computed slot
  rw [actual_priority_eq_raw_Z raw source converted carrierFuel center domain four slot] at head
  exact head

/-- Both actual comparator protocols give the same ordering and pseudo flag on distinct slots. -/
theorem actual_callbacks_agree
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (actualFrame raw source converted carrierFuel center domain four).roots = some keys)
    (state : OccurrenceAuxState) (runtimeFuel : Nat) (left right : Fin 4) (different : left ≠ right) :
    (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys left right).map
        (fun result => (result.ordering, result.pseudo)) =
      (compareOccurrenceBranchesComplete? raw state runtimeFuel
        (runtimeCursorAt raw source converted carrierFuel center domain four left)
        (runtimeCursorAt raw source converted carrierFuel center domain four right)).map
          (fun result => (result.ordering, result.pseudo)) := by
  have sourceCompared := occurrence_callback_eq_strictRank_of_ne source
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
    (actualFrame raw source converted carrierFuel center domain four)
    (actual_roots_real raw source converted carrierFuel center domain four)
    (actual_priority_injective raw source converted carrierFuel center domain four)
    keys computed left right different
  obtain ⟨leftSpec, rightSpec, leftLookup, rightLookup, runtimeCompared⟩ :=
    generated_compare_complete raw center.1.val runtimeFuel domain.leaf state
      (runtimeCursorAt raw source converted carrierFuel center domain four left)
      (runtimeCursorAt raw source converted carrierFuel center domain four right)
      (runtimeCursorAt_mem raw source converted carrierFuel center domain four left)
      (runtimeCursorAt_mem raw source converted carrierFuel center domain four right)
      (fun equal => different
        (runtimeCursorAt_injective raw source converted carrierFuel center domain four equal))
  have leftZ := TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.atomZAt_eq_of_atomAt?
    raw _ leftSpec leftLookup
  have rightZ := TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.atomZAt_eq_of_atomAt?
    raw _ rightSpec rightLookup
  have leftZ' : raw.atomZAt (slotAtomID raw source converted carrierFuel center domain four left) =
      leftSpec.element.atomicNumber := leftZ
  have rightZ' : raw.atomZAt (slotAtomID raw source converted carrierFuel center domain four right) =
      rightSpec.element.atomicNumber := rightZ
  rw [sourceCompared, runtimeCompared]
  simp only [strictRankComparison, Option.map_some,
    actual_priority_eq_raw_Z raw source converted carrierFuel center domain four left,
    actual_priority_eq_raw_Z raw source converted carrierFuel center domain four right]
  change some (compare (raw.atomZAt _) (raw.atomZAt _), false) =
    some (compare leftSpec.element.atomicNumber rightSpec.element.atomicNumber, false)
  rw [leftZ', rightZ']

end ActualFrame

/-- Strictly sorted actual atom-ID permutations have one order. This is a list uniqueness law,
not a supplied comparator or a replacement runtime sorter. -/
theorem atom_id_order_unique (raw : RawMolecule) (left right : List Nat)
    (leftSorted : left.Pairwise (fun a b => raw.atomZAt b < raw.atomZAt a))
    (rightSorted : right.Pairwise (fun a b => raw.atomZAt b < raw.atomZAt a))
    (sameAtoms : left.Perm right) : left = right := by
  apply List.Perm.eq_of_pairwise (le := fun a b => raw.atomZAt b < raw.atomZAt a)
    _ leftSorted rightSorted sameAtoms
  intro a b _ _ forward backward
  exact False.elim ((Nat.lt_asymm forward) backward)

/-- Internally construct both actual sorting pipelines and identify their actual sorted atom IDs.
The source uses rule fuel 2*(carrierFuel+1); runtime fuel/state and source auxiliary view are free.
Whole-source noDouble is an independent restriction of the old source-key backend. -/
theorem actual_runtime_source_priority_alignment (raw : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ keys tracked runtimeResult,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1))
        (actualFrame raw source converted carrierFuel center domain four).roots = some keys ∧
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
        (generatedRuntimeRoots raw center.1.val) = some runtimeResult ∧
      tracked.highestFirst.map (slotAtomID raw source converted carrierFuel center domain four) =
        runtimeResult.1.map (fun cursor => cursor.node.atom) ∧
      tracked.pseudoComparisons = 0 ∧ runtimeResult.2 = 0 := by
  let frame := actualFrame raw source converted carrierFuel center domain four
  obtain ⟨keys, tracked, keyComputed, safeComputed, sourcePerm, sourceSorted, sourceZero⟩ :=
    exists_occurrence_production_keys_and_safe_order source
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view frame
      (finalOccurrenceRoots_are_returned source carrierFuel center)
      (actual_roots_real raw source converted carrierFuel center domain four)
      (actual_priority_injective raw source converted carrierFuel center domain four) noDouble
  obtain ⟨runtimeResult, runtimeComputed, runtimePerm, runtimeSorted, runtimeZero⟩ :=
    generated_runtime_sort raw center.1.val runtimeFuel domain.leaf state
  have sourceIDs : (tracked.highestFirst.map
      (slotAtomID raw source converted carrierFuel center domain four)).Perm
        (recordNeighbors raw center.1.val) :=
    (sourcePerm.map (slotAtomID raw source converted carrierFuel center domain four)).trans
      (actual_slot_ids_perm raw source converted carrierFuel center domain four)
  have runtimeIDs : (runtimeResult.1.map (fun cursor => cursor.node.atom)).Perm
      (recordNeighbors raw center.1.val) := by
    have transported := runtimePerm.map (fun cursor => cursor.node.atom)
    rw [generatedRuntimeRoots_eq raw center.1.val domain.leaf] at transported
    simpa only [List.map_map, Function.comp_def, canonicalRoot, List.map_id'] using transported
  have sourceIDsorted : (tracked.highestFirst.map
      (slotAtomID raw source converted carrierFuel center domain four)).Pairwise
        (fun a b => raw.atomZAt b < raw.atomZAt a) := by
    apply List.pairwise_map.mpr
    apply sourceSorted.imp
    intro left right higher
    simpa only [frame,
      actual_priority_eq_raw_Z raw source converted carrierFuel center domain four left,
      actual_priority_eq_raw_Z raw source converted carrierFuel center domain four right] using higher
  have runtimeIDsorted : (runtimeResult.1.map (fun cursor => cursor.node.atom)).Pairwise
      (fun a b => raw.atomZAt b < raw.atomZAt a) :=
    List.pairwise_map.mpr runtimeSorted
  exact ⟨keys, tracked, runtimeResult, keyComputed, safeComputed, runtimeComputed,
    atom_id_order_unique raw _ _ sourceIDsorted runtimeIDsorted (sourceIDs.trans runtimeIDs.symm),
    sourceZero, runtimeZero⟩

namespace ClosedCF

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness

abbrev raw : RawMolecule := annotatedRawCF
abbrev source : AuthoritativeChemicalInput := parserSource
abbrev center : source.AromaticCanonicalTetrahedralCenter := parserCenter

theorem actual_conversion : raw.toSemanticMolecule? = some source.molecule := parserSource_agreement.1

theorem actual_domain : SingleLeafDomain raw center.1.val := by
  constructor
  · constructor
    · rw [wellFormed_iff_all_bondEndpointsOK]
      decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · intro bond member _
    change bond ∈ [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩] at member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem actual_four : (recordNeighbors raw center.1.val).length = 4 := by decide +kernel

theorem actual_noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : source.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

/-- Both actual pipelines succeed and agree on this already converted annotated parser source.
No emitted descriptor or annotation/parity transport is asserted by a priority agreement. -/
theorem actual_priority_alignment
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ keys tracked runtimeResult,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2
        (actualFrame raw source actual_conversion 0 center actual_domain actual_four).roots = some keys ∧
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
        (generatedRuntimeRoots raw center.1.val) = some runtimeResult ∧
      tracked.highestFirst.map (slotAtomID raw source actual_conversion 0 center actual_domain actual_four) =
        runtimeResult.1.map (fun cursor => cursor.node.atom) ∧
      tracked.pseudoComparisons = 0 ∧ runtimeResult.2 = 0 :=
  actual_runtime_source_priority_alignment raw source actual_conversion 0 center actual_domain actual_four
    actual_noDouble view state runtimeFuel

end ClosedCF

end TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
