import TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
import TetraStereo.UniversalProof.NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.OneCenter.CIPAuthoritativeRule6UnannotatedChemicalCompleteness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge

















structure SourceAtomicDomain (raw : RawMolecule) (center : Nat) : Prop where
  atomic : NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.AtomicCenterDomain raw center
  incidentKinds : ∀ bond ∈ raw.bonds,
    bond.source = center ∨ bond.target = center → bond.kind = .single

def SourceAtomicDomain.incidence {raw : RawMolecule} {center : Nat}
    (domain : SourceAtomicDomain raw center) :
    NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.SingleIncidentDomain raw center :=
  ⟨domain.atomic.wellFormed, domain.incidentKinds⟩

theorem SourceAtomicDomain.rank_injective {raw : RawMolecule} {center : Nat}
    (domain : SourceAtomicDomain raw center) {left right : Nat}
    (leftMember : left ∈ recordNeighbors raw center)
    (rightMember : right ∈ recordNeighbors raw center)
    (equal : raw.atomZAt left = raw.atomZAt right) : left = right :=
  (List.nodup_map_iff_inj_on domain.atomic.neighbors_nodup).mp domain.atomic.distinctRanks
    left leftMember right rightMember equal

section Converted
variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule)
variable (center : source.AromaticCanonicalAtom)
variable (domain : SourceAtomicDomain raw center.val)
include converted domain

theorem converted_neighbor_bound (neighbor : Nat)
    (member : neighbor ∈ recordNeighbors raw center.val) :
    neighbor < source.molecule.atomCount ∧ neighbor ≠ center.val :=
  NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_neighbor_bound
    raw source converted center domain.incidence neighbor member

theorem converted_no_mancude_representative :
    source.molecule.aromaticCanonicalMancudeRepresentativeAt? source.molecule.atomCount center = none :=
  NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_no_mancude_representative
    raw source converted center domain.incidence

theorem converted_ordinary_copies :
    source.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt source.molecule.atomCount center =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ recordNeighbors raw center.val))).map
        (fun neighbor => (neighbor, 0)) :=
  NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_ordinary_copies
    raw source converted center domain.incidence

/-- Official enumeration uses source atom indices, not raw bond record order. -/
theorem converted_official_children :
    source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
        (OfficialCIPNode.root center) =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ recordNeighbors raw center.val))).map
        (fun neighbor => (OfficialCIPNode.root center).extend neighbor 0) := by
  simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
    OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf,
    SemanticMolecule.aromaticCanonicalChildCopiesAt, OfficialCIPNode.parent?,
    converted_no_mancude_representative raw source converted center domain,
    converted_ordinary_copies raw source converted center domain, List.map_map]

theorem converted_official_root_ids :
    officialRootIDs source center =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ recordNeighbors raw center.val))).map
        (fun neighbor => some neighbor.val) := by
  unfold officialRootIDs
  rw [converted_official_children raw source converted center domain]
  simp only [List.map_map]
  apply List.map_congr_left
  intro neighbor _
  rfl

theorem converted_official_root_ids_perm :
    (officialRootIDs source center).Perm ((recordNeighbors raw center.val).map some) := by
  rw [converted_official_root_ids raw source converted center domain]
  apply List.perm_of_nodup_nodup_toFinset_eq
  · apply List.Nodup.map
    · intro left right equal
      exact Fin.ext (Option.some.inj equal)
    · exact (List.nodup_finRange _).filter _
  · exact domain.atomic.neighbors_nodup.map (Option.some_injective Nat)
  · apply Finset.ext
    intro atomID
    cases atomID with
    | none => simp
    | some neighbor =>
        have bounded (present : neighbor ∈ recordNeighbors raw center.val) :
            neighbor < source.molecule.atomCount :=
          (converted_neighbor_bound raw source converted center domain neighbor present).1
        simp only [List.mem_toFinset, List.mem_map, List.mem_filter,
          List.mem_finRange, true_and, decide_eq_true_eq, Option.some.injEq]
        constructor
        · rintro ⟨atom, present, rfl⟩
          exact ⟨atom.val, present, rfl⟩
        · rintro ⟨value, present, equality⟩
          subst value
          exact ⟨⟨neighbor, bounded present⟩, present, rfl⟩

end Converted

theorem converted_final_root_ids_perm (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceAtomicDomain raw center.1.val) :
    (finalOccurrenceRootIDs source fuel center).Perm ((recordNeighbors raw center.1.val).map some) :=
  (finalOccurrenceRootIDs_perm_officialRootIDs source fuel center).trans
    (converted_official_root_ids_perm raw source converted center.1 domain)

theorem actual_returned_four_roots (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceAtomicDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4) :
    source.aromaticCanonicalOccurrenceLigandFrame?
      (source.aromaticCanonicalFinalOccurrence fuel center) =
        some (finalOccurrenceRoots source fuel center) ∧
      (finalOccurrenceRoots source fuel center).length = 4 := by
  refine ⟨finalOccurrenceRoots_are_returned source fuel center, ?_⟩
  have count := (converted_final_root_ids_perm raw source converted fuel center domain).length_eq
  simpa only [finalOccurrenceRootIDs, List.length_map, four] using count

/-- A returned canonical root has the SAME real endpoint and center-edge history. -/
theorem converted_final_cursor_real_root (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceAtomicDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    ∃ neighbor : source.AromaticCanonicalAtom, neighbor.val ∈ recordNeighbors raw center.1.val ∧
      cursor.occurrence.1.node = OfficialCIPNode.rootFromEdge center.1 neighbor := by
  have nodesPerm := (finalOccurrenceRoots_frames_perm source fuel center).map (fun frame => frame.node)
  have officialNodes : (aromaticCanonicalFinalDirectChildFrames source fuel center).map
      (fun frame => frame.node) = source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount (OfficialCIPNode.root center.1) := by
    unfold aromaticCanonicalFinalDirectChildFrames
    rw [List.map_map]
    change (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      (OfficialCIPNode.root center.1)).zipIdx.map Prod.fst = _
    exact List.zipIdx_map_fst 0 _
  have inActual : cursor.occurrence.1.node ∈
      ((finalOccurrenceRoots source fuel center).map (fun child => child.occurrence.1)).map
        (fun frame => frame.node) := by
    simp only [List.mem_map]
    exact ⟨cursor.occurrence.1, ⟨cursor, present, rfl⟩, rfl⟩
  have inOfficial := nodesPerm.mem_iff.mp inActual
  rw [officialNodes, converted_official_children raw source converted center.1 domain] at inOfficial
  obtain ⟨neighbor, retained, nodeEq⟩ := List.mem_map.mp inOfficial
  have endpointPresent : neighbor.val ∈ recordNeighbors raw center.1.val :=
    of_decide_eq_true (List.mem_filter.mp retained).2
  have neighborDifferent : neighbor ≠ center.1 := by
    intro same
    exact (converted_neighbor_bound raw source converted center.1 domain neighbor.val endpointPresent).2
      (congrArg Fin.val same)
  refine ⟨neighbor, endpointPresent, nodeEq.symm.trans ?_⟩
  simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
    OfficialCIPNode.root, OfficialCIPNode.rootFromEdge, neighborDifferent]

/-- Actual finite matching is derived from physical count and raw written-neighbor exactness. -/
theorem converted_written_alignment_exists (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceAtomicDomain raw center.1.val)
    (written : raw.WrittenNeighborExact) (four : (recordNeighbors raw center.1.val).length = 4) :
    ∃ positions, findSlotAlignment? (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source fuel center) = some positions := by
  have writtenPerm : (raw.writtenNeighbors center.1.val).Perm (recordNeighbors raw center.1.val) := by
    exact NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_written_permutation raw center.1.val domain.atomic written
  apply findSlotAlignment?_exists_of_perm
  · exact writtenPerm.length_eq.trans four
  · exact writtenPerm.nodup_iff.mpr domain.atomic.neighbors_nodup
  · exact (converted_final_root_ids_perm raw source converted fuel center domain).trans
      (writtenPerm.map some).symm

section ActualFrame

variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
variable (center : source.AromaticCanonicalTetrahedralCenter)
variable (domain : SourceAtomicDomain raw center.1.val)
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
  rw [RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.converted_atomic_number raw source converted atom, equal]

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
    domain.atomic.neighbors_nodup
  have onSlots := (List.nodup_map_iff_inj_on (List.nodup_finRange 4)).mp distinct
  intro left right equal
  exact onSlots left (List.mem_finRange left) right (List.mem_finRange right) equal

theorem actual_priority_injective : Function.Injective
    (occurrenceAtomicPriority source (actualFrame raw source converted carrierFuel center domain four)) := by
  intro left right equal
  rw [actual_priority_eq_raw_Z raw source converted carrierFuel center domain four left,
    actual_priority_eq_raw_Z raw source converted carrierFuel center domain four right] at equal
  have idsEqual := domain.rank_injective
    (actual_slot_member raw source converted carrierFuel center domain four left)
    (actual_slot_member raw source converted carrierFuel center domain four right) equal
  exact actual_slot_ids_injective raw source converted carrierFuel center domain four idsEqual

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


end ActualFrame

/-- Internally construct both actual sorting pipelines and identify their actual sorted atom IDs.
The source uses rule fuel 2*(carrierFuel+1); runtime fuel/state and source auxiliary view are free.
Whole-source noDouble is an independent restriction of the old source-key backend. -/
theorem actual_runtime_source_priority_alignment (raw : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceAtomicDomain raw center.1.val)
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
    NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_generated_sort raw center.1.val domain.atomic state runtimeFuel
  have sourceIDs : (tracked.highestFirst.map
      (slotAtomID raw source converted carrierFuel center domain four)).Perm
        (recordNeighbors raw center.1.val) :=
    (sourcePerm.map (slotAtomID raw source converted carrierFuel center domain four)).trans
      (actual_slot_ids_perm raw source converted carrierFuel center domain four)
  have runtimeIDs : (runtimeResult.1.map (fun cursor => cursor.node.atom)).Perm
      (recordNeighbors raw center.1.val) := by
    have transported := runtimePerm.map (fun cursor => cursor.node.atom)
    rw [NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.generatedRuntimeRoots_eq raw center.1.val domain.atomic] at transported
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
    RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.atom_id_order_unique raw _ _ sourceIDsorted runtimeIDsorted (sourceIDs.trans runtimeIDs.symm),
    sourceZero, runtimeZero⟩

section Aligned

variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
variable (center : source.AromaticCanonicalTetrahedralCenter)
variable (domain : SourceAtomicDomain raw center.1.val)
variable (four : (recordNeighbors raw center.1.val).length = 4)

include converted domain four

theorem actual_returned_id_at (slot : Fin 4) :
    (finalOccurrenceRootIDs source carrierFuel center)[slot.val]? =
      some (some (slotAtomID raw source converted carrierFuel center domain four slot)) := by
  let frame := actualFrame raw source converted carrierFuel center domain four
  have bound : slot.val < frame.roots.length := by rw [frame.rootsLength]; exact slot.isLt
  change (frame.roots.map (cursorAtomID source))[slot.val]? = _
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  obtain ⟨atom, _, current, _, equal⟩ :=
    actual_slot_endpoint raw source converted carrierFuel center domain four slot
  change some (cursorAtomID source (frame.cursorAt slot)) = _
  change (frame.cursorAt slot).occurrence.1.node.current? = some atom at current
  rw [equal]
  unfold cursorAtomID
  rw [current]
  rfl

theorem actual_aligned_written_lookup (slots : List Nat)
    (matching : ExactSlotAlignment (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source carrierFuel center) slots) (slot : Fin 4) :
    (raw.writtenNeighbors center.1.val)[slots.getD slot.val 0]? =
      some (slotAtomID raw source converted carrierFuel center domain four slot) := by
  have length : slots.length = 4 := matching.2.2.1.length_eq.trans (List.length_range (n := 4))
  have bound : slot.val < slots.length := by rw [length]; exact slot.isLt
  have slotObserved : slots[slot.val]? = some (slots.getD slot.val 0) := by
    rw [List.getElem?_eq_getElem bound]
    exact congrArg some (List.getElem_eq_getD 0)
  have indexed := congrArg (fun ids : List (Option Nat) => ids[slot.val]?) matching.2.2.2
  simp only [List.getElem?_map, slotObserved, Option.map_some] at indexed
  rw [actual_returned_id_at raw source converted carrierFuel center domain four slot] at indexed
  exact Option.some.inj indexed

theorem actual_written_slot_recovered (slots : List Nat)
    (matching : ExactSlotAlignment (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source carrierFuel center) slots) (slot : Fin 4) :
    writtenSlot? (raw.writtenNeighbors center.1.val)
      (slotAtomID raw source converted carrierFuel center domain four slot) =
        some (slots.getD slot.val 0) :=
  writtenSlot?_eq_some _ matching.2.1 _ _
    (actual_aligned_written_lookup raw source converted carrierFuel center domain four slots matching slot)

/-- Actual position lookup succeeds for every canonical slot order, including the derived sorter.
No identity slot alignment is used. -/
theorem actual_priority_positions (slots : List Nat)
    (matching : ExactSlotAlignment (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source carrierFuel center) slots) (order : List (Fin 4)) :
    (order.map (slotAtomID raw source converted carrierFuel center domain four)).mapM
      (writtenSlot? (raw.writtenNeighbors center.1.val)) =
        some (order.map fun slot => slots.getD slot.val 0) := by
  induction order with
  | nil => rfl
  | cons slot remaining inductionHypothesis =>
      simp only [List.map_cons, List.mapM_cons,
        actual_written_slot_recovered raw source converted carrierFuel center domain four slots matching slot,
        inductionHypothesis]
      rfl

/-- This is the exact algebra used by the runtime consumer after its actual lookup has returned.
It applies to arbitrary genuine nonidentity slot alignments. -/
theorem actual_parity_transport (parity : TetrahedralInputParity) (slots : List Nat)
    (matching : ExactSlotAlignment (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source carrierFuel center) slots)
    (order : List (Fin 4)) :
    ((order.map (slotAtomID raw source converted carrierFuel center domain four)).mapM
      (writtenSlot? (raw.writtenNeighbors center.1.val))).map
        (fun positions => RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions)) =
      some (writtenFramePriorityDescriptor parity slots order) := by
  rw [actual_priority_positions raw source converted carrierFuel center domain four slots matching order]
  rfl

end Aligned

/-- GENERAL actual formal assignment / actual runtime lookup algebra agreement. The parity is
the actual input record, not a desired output. Runtime auxiliary discovery, adjacent refusal and
the public normalized wrapper are deliberately not inferred from the lookup fragment. -/
theorem actual_runtime_formal_descriptor_transport (raw : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement raw source)
    (written : raw.WrittenNeighborExact) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceAtomicDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ runtimeResult positions descriptor,
      occurrenceLigandFrame? raw (canonicalCenterRoot center.1.val) =
        some (generatedRuntimeRoots raw center.1.val) ∧
      sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
        (generatedRuntimeRoots raw center.1.val) = some runtimeResult ∧
      runtimePriorityPositions? raw center.1.val runtimeResult.1 = some positions ∧
      descriptor = RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions) ∧
      constitutionParserRichDescriptor? raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) (.chiral descriptor) ∧ runtimeResult.2 = 0 := by
  classical
  obtain ⟨keys, tracked, runtimeResult, keyComputed, safeComputed, runtimeComputed, sameIDs,
      sourceZero, runtimeZero⟩ :=
    actual_runtime_source_priority_alignment raw source agreement.1 carrierFuel center domain four
      noDouble view state runtimeFuel
  obtain ⟨slots, slotsComputed⟩ :=
    converted_written_alignment_exists raw source agreement.1 carrierFuel center domain written four
  have matching := findSlotAlignment?_sound _ _ _ slotsComputed
  let positions := tracked.highestFirst.map (fun slot => slots.getD slot.val 0)
  let descriptor := writtenFramePriorityDescriptor parity slots tracked.highestFirst
  have writtenFour := (NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_written_permutation raw center.1.val domain.atomic written).length_eq.trans four
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center.1.val writtenFour
  have positionsComputed : runtimePriorityPositions? raw center.1.val runtimeResult.1 = some positions := by
    unfold runtimePriorityPositions?
    rw [ligands]
    change runtimeResult.1.mapM
      ((writtenSlot? (raw.writtenNeighbors center.1.val)) ∘ (fun cursor => cursor.node.atom)) = _
    rw [← List.mapM_map, ← sameIDs]
    exact actual_priority_positions raw source agreement.1 carrierFuel center domain four
      slots matching tracked.highestFirst
  change source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
    (2 * (carrierFuel + 1)) (finalOccurrenceRoots source carrierFuel center) = some keys at keyComputed
  let evidence : ParserRichPriorityEvidence source carrierFuel :=
    { slots := slots, keys := keys, tracked := tracked, writtenParity := parity, raw := descriptor }
  have evidenceComputed : constitutionParserRichPriorityEvidence? raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some evidence := by
    have slotsForRoots : findSlotAlignment? (raw.writtenNeighbors center.1.val)
        ((finalOccurrenceRoots source carrierFuel center).map (cursorAtomID source)) = some slots :=
      slotsComputed
    simp [constitutionParserRichPriorityEvidence?, occurrenceTetrahedralCenter?_final,
      parserIndexViaConversion_val, rawWrittenLigandFrame, atomObserved, parityObserved,
      finalOccurrenceRoots_are_returned, occurrenceRootIDs,
      slotsForRoots, keyComputed, safeComputed, evidence]
    rfl
  have descriptorComputed : constitutionParserRichDescriptor? raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some (.chiral descriptor) := by
    simp [constitutionParserRichDescriptor?, evidenceComputed, evidence, sourceZero,
      classifyTetrahedralRSPseudo]
  exact ⟨runtimeResult, positions, descriptor,
    NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_four_frame raw center.1.val domain.atomic written four, runtimeComputed, positionsComputed, rfl,
    descriptorComputed, constitutionParserRichDescriptor?_sound raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (.chiral descriptor) descriptorComputed, runtimeZero⟩


/-- Actual PUBLIC occurrence consumer and the SAME-source independent rich parser meaning.
Only-center annotation and sufficient collector fuel are independent original-record conditions. -/
theorem actual_public_formal_alignment (raw : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement raw source)
    (written : raw.WrittenNeighborExact) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceAtomicDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (only : RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.OnlyCenterTagged raw center.1.val)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (runtimeFuel : Nat) (enough : raw.atomCount + 1 ≤ runtimeFuel) :
    ∃ positions descriptor,
      tetrahedralOccurrenceFact? raw runtimeFuel center.1.val =
        some (RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.recoveredPublicFact
          center.1.val positions descriptor) ∧
      constitutionParserRichDescriptor? raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) (.chiral descriptor) ∧
      descriptor = RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions) := by
  obtain ⟨result, positions, descriptor, frameComputed, sortComputed, positionsComputed,
    formula, parserComputed, meaning, _⟩ := actual_runtime_formal_descriptor_transport
      raw source agreement written carrierFuel center domain four noDouble spec atomObserved
      parity parityObserved view [] runtimeFuel
  obtain ⟨actual, actualComputed, permutation, sorted, _⟩ :=
    NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_generated_sort
      raw center.1.val domain.atomic [] runtimeFuel
  have equal : actual = result := Option.some.inj (actualComputed.symm.trans sortComputed)
  subst actual
  obtain ⟨decisions, decisionsComputed, strict, pseudo, _⟩ :=
    NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_observed_adjacent raw [] runtimeFuel result.1
      (fun cursor member => NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_root_observed
        raw center.1.val domain.atomic cursor (permutation.mem_iff.mp member)) sorted
  have localComputed := RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery.actual_fact_of_program_bindings
    raw center.1.val runtimeFuel [] spec parity atomObserved parityObserved result positions
    decisions descriptor frameComputed sortComputed positionsComputed decisionsComputed strict pseudo formula
    (NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_root_observed raw center.1.val domain.atomic)
    (NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_root_distinct_ranks raw center.1.val domain.atomic)
  exact ⟨positions, descriptor,
    RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.public_fact_of_actual_local_fact
      raw runtimeFuel center.1.val only
      (FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery.prefixTree raw center.1.val 0 runtimeFuel)
      (FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery.actual_collector_complete
        raw center.1.val runtimeFuel domain.atomic.wellFormed domain.atomic.centerBound enough)
      positions descriptor localComputed, parserComputed, meaning, formula⟩

namespace CyclicSource

abbrev raw : RawMolecule := NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.raw

/-- The source is obtained from THIS actual tagged cyclic input; no foreign molecule/view cast. -/
def source : AuthoritativeChemicalInput :=
  raw.toAuthoritativeChemicalInput?.getD { molecule := { atoms := [], interactions := [] } }

def atom (index : Fin 9) : source.AromaticCanonicalAtom :=
  ⟨index.val, by change index.val < 9; exact index.isLt⟩

def center : source.AromaticCanonicalTetrahedralCenter :=
  ⟨atom 0, (mem_aromaticCanonicalTetrahedralCenterSet_iff _ _).mpr ⟨by
    unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
    decide +kernel, by
      have neighbors : source.aromaticCanonicalNeighborFinset (atom 0) =
          {atom 1, atom 4, atom 7, atom 8} := by
        ext neighbor
        rw [mem_aromaticCanonicalNeighborFinset_iff]
        change Fin 9 at neighbor
        fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel
      rw [neighbors]
      decide +kernel⟩⟩

theorem actual_conversion : raw.toSemanticMolecule? = some source.molecule := by decide +kernel

theorem actual_annotation_agreement : RawAnnotationAgreement raw source := by
  apply (rawAnnotationAgreement_iff raw source).mpr
  exact ⟨actual_conversion, by decide +kernel⟩

theorem actual_domain : SourceAtomicDomain raw center.1.val := by
  refine ⟨NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_domain, ?_⟩
  intro bond member _
  change bond ∈ [⟨0, 1, .single⟩, ⟨0, 4, .single⟩, ⟨0, 7, .single⟩, ⟨0, 8, .single⟩,
    ⟨1, 2, .single⟩, ⟨2, 3, .single⟩, ⟨3, 1, .single⟩,
    ⟨4, 5, .single⟩, ⟨5, 6, .single⟩, ⟨6, 4, .single⟩] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem actual_no_double : source.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : source.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    change Fin 9 at left right
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

/-- The nominal OWN source really contains both cycles used by the raw runtime witness. -/
theorem actual_source_cycles :
    source.AromaticCanonicalAdjacent (atom 1) (atom 2) ∧
    source.AromaticCanonicalAdjacent (atom 2) (atom 3) ∧
    source.AromaticCanonicalAdjacent (atom 3) (atom 1) ∧
    source.AromaticCanonicalAdjacent (atom 4) (atom 5) ∧
    source.AromaticCanonicalAdjacent (atom 5) (atom 6) ∧
    source.AromaticCanonicalAdjacent (atom 6) (atom 4) := by
  unfold AromaticCanonicalAdjacent
  decide +kernel

/-- At EVERY own-source carrier/view the real cyclic/nonleaf parser emits S with independent
meaning. The label is derived from actual runtime positions [3,1,2,0] and actual clockwise input. -/
theorem actual_parser_S (carrierFuel : Nat)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    constitutionParserRichDescriptor? raw source actual_annotation_agreement
      NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_admissible.2
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some (.chiral .S) ∧
    ConstitutionParserRichDescriptorMeaning raw source actual_annotation_agreement
      NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_admissible.2
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (.chiral .S) := by
  obtain ⟨result, positions, descriptor, _, sortComputed, positionsComputed, formula,
    parserComputed, meaning, _⟩ := actual_runtime_formal_descriptor_transport raw source
      actual_annotation_agreement NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_admissible.2
      carrierFuel center actual_domain NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_four
      actual_no_double { AtomSpec.aliphatic .C with tetrahedral? := some .clockwise }
      rfl .clockwise rfl view [] 0
  have sortedEqual : result =
      ([NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.root 8,
        NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.root 4,
        NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.root 7,
        NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.root 1], 0) :=
    Option.some.inj (sortComputed.symm.trans
      (NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_sort [] 0))
  subst result
  have positionsEqual : positions = [3, 1, 2, 0] :=
    Option.some.inj (positionsComputed.symm.trans
      NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_positions)
  rw [positionsEqual] at formula
  have descriptorEqual : descriptor = .S := formula.trans (by decide +kernel)
  subst descriptor
  exact ⟨parserComputed, meaning⟩

/-- Closed cyclic/nonleaf SAME-input public runtime and OWN-source parser agreement, retaining
the independently established parser meaning and actual finite-graph collector fuel. -/
theorem actual_public_and_parser_S (carrierFuel runtimeFuel : Nat)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) (enough : 10 ≤ runtimeFuel) :
    tetrahedralOccurrenceFact? raw runtimeFuel 0 =
      some (RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.recoveredPublicFact 0 [3, 1, 2, 0] .S) ∧
    constitutionParserRichDescriptor? raw source actual_annotation_agreement
      NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_admissible.2
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some (.chiral .S) ∧
    ConstitutionParserRichDescriptorMeaning raw source actual_annotation_agreement
      NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_admissible.2
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (.chiral .S) :=
  ⟨NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.CyclicTagged.actual_public_S runtimeFuel enough,
    actual_parser_S carrierFuel view⟩

end CyclicSource

end TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
