import TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
import TetraStereo.UniversalProof.NativeOrdinarySourceInput
import TetraStereo.UniversalProof.NativeSourcePhysicalCoordinates
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceReadiness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation









abbrev ExactLayer := List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber)

def carbonRootLayer : ExactLayer := [([], .ofNat 6)]
def bridgeChildLayer : ExactLayer := [([0], .ofNat 6), ([1], .ofNat 1), ([2], .ofNat 1)]
def methylChildLayer : ExactLayer := [([0], .ofNat 1), ([1], .ofNat 1), ([2], .ofNat 1)]

/-- The actual exact-rational sparse-layer comparator observes a tied carbon root then the
first child slot. Arbitrary later constitutional layers cannot reverse either direction. -/
theorem second_sphere_sparse_both (bridgeTail methylTail : List ExactLayer) :
    OfficialRuleMajorKey.compareSparseLayers ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (carbonRootLayer :: bridgeChildLayer :: bridgeTail)
      (carbonRootLayer :: methylChildLayer :: methylTail) = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (carbonRootLayer :: methylChildLayer :: methylTail)
      (carbonRootLayer :: bridgeChildLayer :: bridgeTail) = Ordering.lt := by
  have carbonTie : ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (.ofNat 6) (.ofNat 6) = Ordering.eq := by decide +kernel
  have carbonAbove := ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat_gt
    (left := 6) (right := 1) (by decide)
  have hydrogenBelow := ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat_lt
    (left := 1) (right := 6) (by decide)
  constructor <;>
    simp [OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
      OfficialRuleMajorKey.compareSparseEntry, OfficialRuleMajorKey.compareNat,
      carbonRootLayer, bridgeChildLayer, methylChildLayer, List.compareLex, compareLex,
      Ordering.byKey, flip, carbonTie, carbonAbove, hydrogenBelow]

/-- Transport the physical two-layer exact projection through the actual Rules-1a--5 key
comparator. This is a coordinate lemma, not an assertion that returned family keys have those
coordinates. That separate production construction remains explicit and OPEN below. -/
theorem second_sphere_source_keys_both (source : AuthoritativeChemicalInput)
    (bridge methyl : source.AromaticCanonicalOccurrenceRule3Through5Key)
    (bridgeTail methylTail : List ExactLayer)
    (bridgeProjection : ExactOfficialRuleMajorKey.exactRule1aLayers
      source.molecule.toLocalizedMoleculeGraph bridge.rule3.constitutional.sourceNodes =
      carbonRootLayer :: bridgeChildLayer :: bridgeTail)
    (methylProjection : ExactOfficialRuleMajorKey.exactRule1aLayers
      source.molecule.toLocalizedMoleculeGraph methyl.rule3.constitutional.sourceNodes =
      carbonRootLayer :: methylChildLayer :: methylTail) :
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys bridge methyl = Ordering.gt ∧
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys methyl bridge = Ordering.lt := by
  have strict := second_sphere_sparse_both bridgeTail methylTail
  constructor <;>
    simp [compareAromaticCanonicalOccurrenceRule3Through5Keys,
      compareAromaticCanonicalUncancelledRule3SpatialKeys,
      ExactOfficialRuleMajorKey.compare, ExactOfficialRuleMajorKey.compareAddressedSources,
      Ordering.byKey, compareLex, bridgeProjection, methylProjection, strict.1, strict.2]

/-- Independent source geometry domain, admitting the repeated C/C first sphere. -/
structure SourceRecordDomain (raw : RawMolecule) (center : Nat) : Prop where
  well : raw.WellFormed
  rowDistinct : (recordNeighbors raw center).Nodup
  incidentSingle : ∀ bond ∈ raw.bonds,
    bond.source = center ∨ bond.target = center → bond.kind = .single

def SourceRecordDomain.incidence {raw : RawMolecule} {center : Nat}
    (domain : SourceRecordDomain raw center) :
    NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.SingleIncidentDomain raw center :=
  ⟨domain.well, domain.incidentSingle⟩

section Converted
variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule)
variable (center : source.AromaticCanonicalAtom)
variable (domain : SourceRecordDomain raw center.val)
include converted domain

theorem converted_neighbor_bound (neighbor : Nat)
    (member : neighbor ∈ recordNeighbors raw center.val) :
    neighbor < source.molecule.atomCount ∧ neighbor ≠ center.val :=
  NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_neighbor_bound
    raw source converted center domain.incidence neighbor member

/-- The actual converted ordinary root children, without any rank injectivity condition. -/
theorem converted_official_children :
    source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
        (OfficialCIPNode.root center) =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ recordNeighbors raw center.val))).map
        (fun neighbor => OfficialCIPNode.extend (OfficialCIPNode.root center) neighbor 0) := by
  have noMancude := NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_no_mancude_representative
    raw source converted center domain.incidence
  have copies := NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_ordinary_copies
    raw source converted center domain.incidence
  simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
    OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf,
    SemanticMolecule.aromaticCanonicalChildCopiesAt, OfficialCIPNode.parent?,
    noMancude, copies, List.map_map]

/-- Single physical records below a root edge remove the real parent once and create ordinary
official children. This theorem observes the converted source topology, not raw surrogate keys. -/
theorem converted_official_edge_children (parent : source.AromaticCanonicalAtom) :
    source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
        (OfficialCIPNode.rootFromEdge parent center) =
      (((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ recordNeighbors raw center.val))).filter
        (fun neighbor => !(neighbor == parent))).map
        (fun neighbor => OfficialCIPNode.extend (OfficialCIPNode.rootFromEdge parent center) neighbor 0) := by
  have noMancude := NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_no_mancude_representative
    raw source converted center domain.incidence
  have copies := NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_ordinary_copies
    raw source converted center domain.incidence
  simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
    OfficialCIPNode.rootFromEdge, OfficialCIPNode.isDuplicateLeaf,
    SemanticMolecule.aromaticCanonicalChildCopiesAt, OfficialCIPNode.parent?,
    noMancude, copies, List.filter_map, List.map_map]

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
  · exact domain.rowDistinct.map (Option.some_injective Nat)
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

/-- Physical endpoint permutation of the actual source edge children. Parent removal is
derived by filtering the already-proved root permutation; no atomic-rank premise appears. -/
theorem converted_official_edge_ids_perm (parent : source.AromaticCanonicalAtom) :
    ((source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      (OfficialCIPNode.rootFromEdge parent center)).map
        (fun node => node.current?.map Fin.val)).Perm
      (((recordNeighbors raw center.val).filter (fun atom => !(atom == parent.val))).map some) := by
  have permutation := converted_official_root_ids_perm raw source converted center domain
  rw [converted_official_root_ids raw source converted center domain] at permutation
  have filtered := permutation.filter (fun id => id != some parent.val)
  have finComparison (neighbor : source.AromaticCanonicalAtom) :
      (neighbor.val == parent.val) = (neighbor == parent) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Fin.ext_iff]
  rw [converted_official_edge_children raw source converted center domain parent]
  simpa [List.filter_map, List.map_map, Function.comp_def,
    OfficialCIPNode.extend_current?, bne, finComparison] using filtered

end Converted

theorem converted_final_root_ids_perm (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceRecordDomain raw center.1.val) :
    (finalOccurrenceRootIDs source fuel center).Perm ((recordNeighbors raw center.1.val).map some) :=
  (finalOccurrenceRootIDs_perm_officialRootIDs source fuel center).trans
    (converted_official_root_ids_perm raw source converted center.1 domain)

theorem actual_returned_four_roots (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceRecordDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4) :
    source.aromaticCanonicalOccurrenceLigandFrame?
      (source.aromaticCanonicalFinalOccurrence fuel center) =
        some (finalOccurrenceRoots source fuel center) ∧
      (finalOccurrenceRoots source fuel center).length = 4 := by
  refine ⟨finalOccurrenceRoots_are_returned source fuel center, ?_⟩
  have count := (converted_final_root_ids_perm raw source converted fuel center domain).length_eq
  simpa only [finalOccurrenceRootIDs, List.length_map, four] using count

/-- A production returned direct ligand has exactly the requested carrier remainder and one
address slot. This is a carrier-coordinate result, independent of chemical ranking. -/
theorem returned_direct_coordinates (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center) :
    cursor.occurrence.1.remaining = carrierFuel ∧ cursor.occurrence.1.address.length = 1 ∧
      cursor.previous? = some (source.aromaticCanonicalFinalOccurrence carrierFuel center) := by
  have frames := finalOccurrenceRoots_frames_perm source carrierFuel center
  have here : cursor.occurrence.1 ∈
      (finalOccurrenceRoots source carrierFuel center).map (fun child => child.occurrence.1) :=
    List.mem_map.mpr ⟨cursor, present, rfl⟩
  have official := frames.mem_iff.mp here
  unfold aromaticCanonicalFinalDirectChildFrames at official
  obtain ⟨indexed, _, frameEq⟩ := List.mem_map.mp official
  refine ⟨?_, ?_, ?_⟩
  · exact (congrArg AromaticCanonicalOccurrenceFrame.remaining frameEq).symm
  · rw [← frameEq]; rfl
  · exact (source.aromaticCanonicalRerootChildren_sound
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none }).2 cursor present

/-- Carrier remaining zero admits no outward coordinate: the exact grading proves exclusion.
No unproved adequacy assumption for positive carrier fuel is hidden in this result. -/
theorem carrier_outward_empty_at_zero (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence carrierFuel)
    (zero : occurrence.1.remaining = 0) :
    source.aromaticCanonicalCarrierOutwardChildFrames (fuel := carrierFuel) occurrence.1 = [] := by
  have rootGrade := source.aromaticCanonicalOccurrence_depthGrade occurrence
  rw [zero] at rootGrade
  unfold aromaticCanonicalCarrierOutwardChildFrames
  apply List.filter_eq_nil_iff.mpr
  intro candidate member
  have candidateGrade := source.aromaticCanonicalOccurrence_depthGrade
    (fuel := carrierFuel) ⟨candidate, member⟩
  change candidate.address.length + candidate.remaining = carrierFuel + 1 at candidateGrade
  have different : candidate.address.length ≠ occurrence.1.address.length + 1 := by omega
  simp [different]

/-- Zero-fuel returned ligands have no outward sphere under the actual production carrier. -/
theorem returned_zero_no_outward (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 0)
    (present : cursor ∈ finalOccurrenceRoots source 0 center) :
    source.aromaticCanonicalCarrierOutwardChildFrames (fuel := 0) cursor.occurrence.1 = [] :=
  carrier_outward_empty_at_zero source cursor.occurrence
    (returned_direct_coordinates source 0 center cursor present).1

/-- Returned roots retain the source rootFromEdge node, derived from actual carrier geometry. -/
theorem converted_final_cursor_real_root (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceRecordDomain raw center.1.val)
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

section ActualFrame
variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
variable (center : source.AromaticCanonicalTetrahedralCenter)
variable (domain : SourceRecordDomain raw center.1.val)
variable (four : (recordNeighbors raw center.1.val).length = 4)
include converted domain four

noncomputable def actualFrame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel where
  roots := finalOccurrenceRoots source carrierFuel center
  rootsLength := (actual_returned_four_roots raw source converted carrierFuel center domain four).2

/-- Expose finite slot membership before specializing to a large converted graph. This avoids
unfolding the source conversion while elaborating an inferred list index. -/
theorem actual_frame_cursor_mem (slot : Fin 4) :
    (actualFrame raw source converted carrierFuel center domain four).cursorAt slot ∈
      finalOccurrenceRoots source carrierFuel center := List.get_mem _ _

noncomputable def slotAtomID (slot : Fin 4) : Nat :=
  (cursorAtomID source ((actualFrame raw source converted carrierFuel center domain four).cursorAt slot)).getD 0

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

/-- Recover a returned slot's exact root node from its physical atom identity before
specializing the source conversion to a concrete family. -/
theorem actual_slot_root_node (slot : Fin 4) (atom : source.AromaticCanonicalAtom)
    (identity : slotAtomID raw source converted carrierFuel center domain four slot = atom.val) :
    ((actualFrame raw source converted carrierFuel center domain four).cursorAt slot).occurrence.1.node =
      OfficialCIPNode.rootFromEdge center.1 atom := by
  obtain ⟨neighbor, _, nodeEq⟩ := converted_final_cursor_real_root raw source converted
    carrierFuel center domain _ (actual_frame_cursor_mem raw source converted carrierFuel center domain four slot)
  have observedId : slotAtomID raw source converted carrierFuel center domain four slot = neighbor.val := by
    simp only [slotAtomID, cursorAtomID, nodeEq, OfficialCIPNode.rootFromEdge,
      Option.map_some, Option.getD_some]
  have equal : neighbor = atom := Fin.ext (observedId.symm.trans identity)
  exact equal ▸ nodeEq

theorem actual_roots_real : OccurrenceRootsReal source
    (actualFrame raw source converted carrierFuel center domain four) := by
  intro slot
  obtain ⟨atom, _, current, provenance, _⟩ :=
    actual_slot_endpoint raw source converted carrierFuel center domain four slot
  exact ⟨atom, current, provenance⟩

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

/-- Slot identity is injective even when atomic priority is not. -/
theorem actual_slot_ids_injective :
    Function.Injective (slotAtomID raw source converted carrierFuel center domain four) := by
  have distinct := (actual_slot_ids_perm raw source converted carrierFuel center domain four).nodup_iff.mpr
    domain.rowDistinct
  have onSlots := (List.nodup_map_iff_inj_on (List.nodup_finRange 4)).mp distinct
  intro left right equal
  exact onSlots left (List.mem_finRange left) right (List.mem_finRange right) equal

/-- The generic source-key existence theorem is reused, with no distinct-Z premise. -/
theorem actual_source_key_frame_exists
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1))
      (actualFrame raw source converted carrierFuel center domain four).roots = some keys := by
  apply exists_occurrence_production_keyFrame_of_returned_noDouble source
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
    (actualFrame raw source converted carrierFuel center domain four)
  · exact (actual_returned_four_roots raw source converted carrierFuel center domain four).1
  · exact noDouble

end ActualFrame

/-- Actual physical input to the existing ordinary parser-to-source converter. -/
def familyInput (ps : List TetrahedralInputParity) : OrdinarySourceInput (familyRaw ps) :=
  ⟨familyRaw_wellFormed ps, familyRaw_writtenNeighborExact ps,
    familyRaw_known_elements ps, familyRaw_all_single ps⟩

def familySource (ps : List TetrahedralInputParity) : AuthoritativeChemicalInput := ownSource (familyRaw ps)

theorem family_source_conversion (ps : List TetrahedralInputParity) :
    (familyRaw ps).toAuthoritativeChemicalInput? = some (familySource ps) :=
  actual_source_conversion (familyRaw ps) (familyInput ps)

theorem family_annotation_agreement (ps : List TetrahedralInputParity) :
    SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement.RawAnnotationAgreement (familyRaw ps) (familySource ps) :=
  actual_annotation_agreement (familyRaw ps) (familyInput ps)

/-- Role atoms are constructed through THIS input's actual source conversion. -/
def familyAtom (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (bound : offset < 12) : (familySource ps).AromaticCanonicalAtom :=
  (familyRaw ps).convertedAtomIndex (familySource ps) (family_annotation_agreement ps).1
    ⟨1 + 12 * i.val + offset, familyRaw_role_bound ps i offset bound⟩

@[simp] theorem family_atom_index (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (bound : offset < 12) :
    (familyAtom ps i offset bound).val = 1 + 12 * i.val + offset := rfl

theorem family_source_role_Z (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (bound : offset < 12) :
    (familySource ps).molecule.toLocalizedMoleculeGraph.atomZ (familyAtom ps i offset bound) =
      (roleAtom (ps.get i) (roleOfOffset offset)).element.atomicNumber := by
  rw [converted_atomic_number (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1,
    family_atom_index]
  exact familyRaw_role_Z ps i offset bound

/-- All actual graph-generated first outward children are real when the physical role is
distinct from the ligand and the tag. Their inherited histories have exactly three atoms. -/
theorem family_source_child_real (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (parent offset : Nat) (parentBound : parent < 12) (bound : offset < 12)
    (different : offset ≠ parent) (notTag : offset ≠ 5) :
    (OfficialCIPNode.extend
      (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i parent parentBound)) (familyAtom ps i offset bound) 0).provenance = .realAtom ∧
    (OfficialCIPNode.extend
      (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i parent parentBound)) (familyAtom ps i offset bound) 0).history.length = 3 := by
  have parentDifferent : familyAtom ps i offset bound ≠ familyAtom ps i parent parentBound := by
    intro equal
    have indices := congrArg Fin.val equal
    simp only [family_atom_index] at indices
    omega
  have tagDifferent : familyAtom ps i offset bound ≠ familyAtom ps i 5 (by decide) := by
    intro equal
    have indices := congrArg Fin.val equal
    simp only [family_atom_index] at indices
    omega
  simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
    OfficialCIPNode.rootFromEdge, parentDifferent, tagDifferent]

/-- Exact Rule-1a observation of the generated physical source child, independent of its
own deeper descendants and any auxiliary descriptor state. -/
theorem family_source_child_observation (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (parent offset : Nat) (parentBound : parent < 12) (bound : offset < 12)
    (different : offset ≠ parent) (notTag : offset ≠ 5) :
    (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (OfficialCIPNode.extend
        (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
          (familyAtom ps i parent parentBound)) (familyAtom ps i offset bound) 0) =
      .ofNat ((roleAtom (ps.get i) (roleOfOffset offset)).element.atomicNumber) := by
  have real := (family_source_child_real ps i parent offset parentBound bound different notTag).1
  simp only [MoleculeGraph.exactOfficialRule1aObservation, OfficialCIPNode.extend_current?, real]
  rw [family_source_role_Z]

theorem family_source_no_double (ps : List TetrahedralInputParity) :
    (familySource ps).NoAromaticCanonicalOrdinaryDoubleBond :=
  actual_source_no_double (familyRaw ps) (familyInput ps)

/-- Actual source bridge children retain the backbone carbon and both physical hydrogens,
after removing the tag edge. This is independent of source carrier truncation and key sorting. -/
theorem family_source_bridge_child_ids (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (((familySource ps).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (familySource ps).molecule.atomCount
      (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i 2 (by decide)))).map (fun node => node.current?.map Fin.val)).Perm
      [some (1 + 12 * i.val), some (1 + 12 * i.val + 3), some (1 + 12 * i.val + 4)] := by
  have domain : SourceRecordDomain (familyRaw ps) (familyAtom ps i 2 (by decide)).val :=
    ⟨familyRaw_wellFormed ps, (familyRaw_closed_rows_nodup ps i).1,
      fun bond member _ => familyRaw_all_single ps bond member⟩
  have permutation := converted_official_edge_ids_perm (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 (familyAtom ps i 2 (by decide)) domain
    (familyAtom ps i 5 (by decide))
  simp only [family_atom_index] at permutation
  rw [familyRaw_bridge_records ps i] at permutation
  have exclude0 : (1 + 12 * i.val == 1 + 12 * i.val + 5) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  have exclude3 : (1 + 12 * i.val + 3 == 1 + 12 * i.val + 5) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  have exclude4 : (1 + 12 * i.val + 4 == 1 + 12 * i.val + 5) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  simpa only [List.filter_cons, List.filter_nil, exclude0, exclude3, exclude4,
    beq_self_eq_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, List.map_cons, List.map_nil] using permutation

theorem family_source_methyl_child_ids (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (((familySource ps).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (familySource ps).molecule.atomCount
      (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i 8 (by decide)))).map (fun node => node.current?.map Fin.val)).Perm
      [some (1 + 12 * i.val + 9), some (1 + 12 * i.val + 10), some (1 + 12 * i.val + 11)] := by
  have domain : SourceRecordDomain (familyRaw ps) (familyAtom ps i 8 (by decide)).val :=
    ⟨familyRaw_wellFormed ps, (familyRaw_closed_rows_nodup ps i).2.2,
      fun bond member _ => familyRaw_all_single ps bond member⟩
  have permutation := converted_official_edge_ids_perm (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 (familyAtom ps i 8 (by decide)) domain
    (familyAtom ps i 5 (by decide))
  simp only [family_atom_index] at permutation
  rw [familyRaw_methyl_records ps i] at permutation
  have exclude9 : (1 + 12 * i.val + 9 == 1 + 12 * i.val + 5) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  have exclude10 : (1 + 12 * i.val + 10 == 1 + 12 * i.val + 5) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  have exclude11 : (1 + 12 * i.val + 11 == 1 + 12 * i.val + 5) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  simpa only [List.filter_cons, List.filter_nil, exclude9, exclude10, exclude11,
    beq_self_eq_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, List.map_cons, List.map_nil] using permutation

def familyCenter (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familySource ps).AromaticCanonicalTetrahedralCenter :=
  actualCenter (familyRaw ps) (familyInput ps)
    ⟨1 + 12 * i.val + 5, familyRaw_role_bound ps i 5 (by decide)⟩
    (roleAtom (ps.get i) .tagCarbon)
    (familyRaw_role_atom ps i 5 (by decide))
    (by trivial)
    (by rw [familyRaw_tag_written ps i]; rfl)

@[simp] theorem family_center_index (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyCenter ps i).1.val = 1 + 12 * i.val + 5 := rfl

def familyRecordDomain (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    SourceRecordDomain (familyRaw ps) (familyCenter ps i).1.val :=
  ⟨familyRaw_wellFormed ps, (familyRaw_closed_rows_nodup ps i).2.1,
    fun bond member _ => familyRaw_all_single ps bond member⟩

theorem family_four_records (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (recordNeighbors (familyRaw ps) (familyCenter ps i).1.val).length = 4 := by
  rw [family_center_index, familyRaw_tag_records ps i]
  rfl

noncomputable def familyFrame (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) : (familySource ps).AromaticCanonicalOccurrenceFourLigandFrame carrierFuel :=
  actualFrame (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
    carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i)

theorem family_returned_frame (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) :
    (familySource ps).aromaticCanonicalOccurrenceLigandFrame?
      ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i)) =
        some (familyFrame ps i carrierFuel).roots :=
  (actual_returned_four_roots (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
    carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i)).1

/-- Returned source root IDs are precisely the physical written role IDs as a permutation. -/
theorem family_returned_root_ids (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) :
    ((familyFrame ps i carrierFuel).roots.map (cursorAtomID (familySource ps))).Perm
      [some (1 + 12 * i.val + 2), some (1 + 12 * i.val + 6),
       some (1 + 12 * i.val + 7), some (1 + 12 * i.val + 8)] := by
  have permutation := converted_final_root_ids_perm (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 carrierFuel (familyCenter ps i) (familyRecordDomain ps i)
  rw [family_center_index, familyRaw_tag_records ps i] at permutation
  exact permutation

theorem family_roots_real (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) : OccurrenceRootsReal (familySource ps) (familyFrame ps i carrierFuel) :=
  actual_roots_real (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
    carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i)

/-- An internally defined dependency view for the independent constitutional ordering target.
This is not identified with the scheduled model's final view. -/
def constitutionalView (ps : List TetrahedralInputParity) (i : Fin ps.length) (carrierFuel : Nat) :
    (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i)) :=
  fun _ _ => none

/-- Actual key construction from returned roots, reused generic readiness and independently
derived no-double admission. Holds even at zero carrier: readiness does not imply ranking. -/
theorem family_key_frame_exists (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) :
    ∃ keys, (familySource ps).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i))
      (constitutionalView ps i carrierFuel) (2 * (carrierFuel + 1))
      (familyFrame ps i carrierFuel).roots = some keys := by
  exact actual_source_key_frame_exists (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 carrierFuel (familyCenter ps i)
    (familyRecordDomain ps i) (family_four_records ps i) (constitutionalView ps i carrierFuel)
    (family_source_no_double ps)

noncomputable def familyKeys (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) : (familySource ps).AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel :=
  Classical.choose (family_key_frame_exists ps i carrierFuel)

theorem family_keys_computed (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) :
    (familySource ps).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i))
      (constitutionalView ps i carrierFuel) (2 * (carrierFuel + 1))
      (familyFrame ps i carrierFuel).roots = some (familyKeys ps i carrierFuel) :=
  Classical.choose_spec (family_key_frame_exists ps i carrierFuel)

/-- Every physical written role has an actual returned source slot, without an injective-Z
domain or a supplied frame/slot/output. The slot is recovered from the derived permutation. -/
theorem family_role_slot_exists (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel offset : Nat) (member : offset ∈ [2, 6, 7, 8]) :
    ∃ slot : Fin 4, slotAtomID (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
      carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i) slot =
        1 + 12 * i.val + offset := by
  have permutation := actual_slot_ids_perm (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 carrierFuel (familyCenter ps i)
    (familyRecordDomain ps i) (family_four_records ps i)
  have physical : 1 + 12 * i.val + offset ∈ recordNeighbors (familyRaw ps) (familyCenter ps i).1.val := by
    rw [family_center_index, familyRaw_tag_records ps i]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp
  have present := permutation.mem_iff.mpr physical
  obtain ⟨slot, _, equal⟩ := List.mem_map.mp present
  exact ⟨slot, equal⟩

noncomputable def familyRoleSlot (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel offset : Nat) (member : offset ∈ [2, 6, 7, 8]) : Fin 4 :=
  Classical.choose (family_role_slot_exists ps i carrierFuel offset member)

theorem family_role_slot_index (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel offset : Nat) (member : offset ∈ [2, 6, 7, 8]) :
    slotAtomID (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
      carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i)
      (familyRoleSlot ps i carrierFuel offset member) = 1 + 12 * i.val + offset :=
  Classical.choose_spec (family_role_slot_exists ps i carrierFuel offset member)

/-- Head-only physical priorities of the four roles. Repeated carbon is deliberately retained. -/
def roleAtomicPriority : Nat → Nat
  | 2 | 8 => 6
  | 6 => 1
  | 7 => 9
  | _ => 0

theorem family_role_priority (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel offset : Nat) (member : offset ∈ [2, 6, 7, 8]) :
    occurrenceAtomicPriority (familySource ps) (familyFrame ps i carrierFuel)
      (familyRoleSlot ps i carrierFuel offset member) = roleAtomicPriority offset := by
  change occurrenceAtomicPriority (familySource ps)
    (actualFrame (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
      carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i))
        (familyRoleSlot ps i carrierFuel offset member) = _
  rw [actual_priority_eq_raw_Z (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
    carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i),
    family_role_slot_index]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact (familyRaw_interior_carbon_Z ps i).2.1
  · exact (familyRaw_terminal_Z ps i).2.2.2.1
  · exact (familyRaw_terminal_Z ps i).2.2.2.2.1
  · exact (familyRaw_interior_carbon_Z ps i).2.2.2

/-- Exact heads of actual production returned keys, including both carbon roles. This theorem
does not supply their second layer or assume a comparator result. -/
theorem family_role_key_atomic_head (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel offset : Nat) (member : offset ∈ [2, 6, 7, 8]) :
    (ExactOfficialRuleMajorKey.exactRule1aLayers (familySource ps).molecule.toLocalizedMoleculeGraph
      ((familyKeys ps i carrierFuel).keyAt (familyRoleSlot ps i carrierFuel offset member)).rule3.constitutional.sourceNodes).head? =
      some [([], .ofNat (roleAtomicPriority offset))] := by
  have head := occurrence_keyFrame_exact_atomic_head (familySource ps)
    ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i))
    (constitutionalView ps i carrierFuel) (2 * (carrierFuel + 1)) (familyFrame ps i carrierFuel)
    (family_roots_real ps i carrierFuel) (familyKeys ps i carrierFuel)
    (family_keys_computed ps i carrierFuel) (familyRoleSlot ps i carrierFuel offset member)
  rw [family_role_priority] at head
  exact head

/-- All actual unequal-Z source comparisons are internally derived. The repeated-carbon pair
is excluded from this head-only helper and is derived separately from production second layers below. -/
theorem family_source_unequal_role_comparison (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel left right : Nat) (leftMember : left ∈ [2, 6, 7, 8])
    (rightMember : right ∈ [2, 6, 7, 8])
    (different : roleAtomicPriority left ≠ roleAtomicPriority right) :
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyKeys ps i carrierFuel)
      (familyRoleSlot ps i carrierFuel left leftMember)
      (familyRoleSlot ps i carrierFuel right rightMember) =
      some { ordering := (compare (roleAtomicPriority left) (roleAtomicPriority right)), decisiveRule? := none, pseudo := false } := by
  rcases Nat.lt_or_gt_of_ne different with lower | higher
  · have priorities : occurrenceAtomicPriority (familySource ps) (familyFrame ps i carrierFuel)
        (familyRoleSlot ps i carrierFuel left leftMember) <
      occurrenceAtomicPriority (familySource ps) (familyFrame ps i carrierFuel)
        (familyRoleSlot ps i carrierFuel right rightMember) := by
        rw [family_role_priority, family_role_priority]
        exact lower
    have compared := occurrence_comparison_lt_of_atomic_priority (familySource ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i))
      (constitutionalView ps i carrierFuel) (2 * (carrierFuel + 1)) (familyFrame ps i carrierFuel)
      (family_roots_real ps i carrierFuel) (familyKeys ps i carrierFuel) (family_keys_computed ps i carrierFuel)
      (familyRoleSlot ps i carrierFuel left leftMember) (familyRoleSlot ps i carrierFuel right rightMember) priorities
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      compared, Nat.compare_eq_lt.mpr lower]
  · have priorities : occurrenceAtomicPriority (familySource ps) (familyFrame ps i carrierFuel)
        (familyRoleSlot ps i carrierFuel right rightMember) <
      occurrenceAtomicPriority (familySource ps) (familyFrame ps i carrierFuel)
        (familyRoleSlot ps i carrierFuel left leftMember) := by
        rw [family_role_priority, family_role_priority]
        exact higher
    have compared := occurrence_comparison_gt_of_atomic_priority (familySource ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i))
      (constitutionalView ps i carrierFuel) (2 * (carrierFuel + 1)) (familyFrame ps i carrierFuel)
      (family_roots_real ps i carrierFuel) (familyKeys ps i carrierFuel) (family_keys_computed ps i carrierFuel)
      (familyRoleSlot ps i carrierFuel left leftMember) (familyRoleSlot ps i carrierFuel right rightMember) priorities
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      compared, Nat.compare_eq_gt.mpr higher]

/-- Extend an independently derived occurrence along an actual official edge when its own
remaining depth is positive. The proof follows the preserved reachability derivation. -/
private theorem carrier_subtree_extend (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    ∀ (depth : Nat) (child : OfficialCIPNode source.AromaticCanonicalAtom) (slot : Nat),
      occurrence.remaining = depth + 1 →
      (child, slot) ∈ (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount occurrence.node).zipIdx →
      source.DeclarativeAromaticCanonicalOccurrenceSubtree root path fuel node
        { root := occurrence.root
          address := occurrence.address ++ [slot]
          node := child
          remaining := depth } := by
  induction derived with
  | subtreeRoot path fuel node =>
      intro depth child slot remaining edge
      change fuel = depth + 1 at remaining
      subst fuel
      exact .subtreeDescendant edge (.subtreeRoot (path ++ [slot]) depth child)
  | subtreeDescendant edge below ih =>
      intro depth child slot remaining nextEdge
      exact .subtreeDescendant edge (ih depth child slot remaining nextEdge)

/-- Every actual official child is present in the exact outward carrier when the parent has
positive remaining depth. This is a proved carrier sufficiency statement, independent of key
construction, key sorting and descriptor views. -/
theorem carrier_positive_official_child (source : AuthoritativeChemicalInput)
    {carrierFuel depth : Nat} (occurrence : source.AromaticCanonicalOccurrence carrierFuel)
    (child : OfficialCIPNode source.AromaticCanonicalAtom) (slot : Nat)
    (remaining : occurrence.1.remaining = depth + 1)
    (edge : (child, slot) ∈ (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
      source.molecule.atomCount occurrence.1.node).zipIdx) :
    { root := occurrence.1.root
      address := occurrence.1.address ++ [slot]
      node := child
      remaining := depth } ∈ source.aromaticCanonicalCarrierOutwardChildFrames
        (fuel := carrierFuel) occurrence.1 := by
  have original := (source.mem_aromaticCanonicalOccurrences_iff carrierFuel occurrence.1).mp
    occurrence.2
  have extended := carrier_subtree_extend source original depth child slot remaining edge
  have admitted := (source.mem_aromaticCanonicalOccurrences_iff carrierFuel
    { root := occurrence.1.root, address := occurrence.1.address ++ [slot],
      node := child, remaining := depth }).mpr extended
  rw [aromaticCanonicalCarrierOutwardChildFrames, List.mem_filter]
  refine ⟨admitted, ?_⟩
  simp

/-- Positive remaining depth cannot truncate all outward coordinates of a physically
nonterminal official node. No successful key or desired source comparison is assumed. -/
theorem carrier_positive_has_outward (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (occurrence : source.AromaticCanonicalOccurrence carrierFuel)
    (positive : 0 < occurrence.1.remaining)
    (nonterminal : source.molecule.aromaticCanonicalOfficialCIPChildrenAt
      source.molecule.atomCount occurrence.1.node ≠ []) :
    source.aromaticCanonicalCarrierOutwardChildFrames (fuel := carrierFuel) occurrence.1 ≠ [] := by
  cases remaining : occurrence.1.remaining with
  | zero => omega
  | succ depth =>
      obtain ⟨child, member⟩ := List.exists_mem_of_ne_nil _ nonterminal
      have indexedMember : child ∈ (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount occurrence.1.node).zipIdx.map Prod.fst := by
        rw [List.zipIdx_map_fst 0 _]
        exact member
      obtain ⟨indexed, edge, _⟩ := List.mem_map.mp indexedMember
      have outward := carrier_positive_official_child source occurrence indexed.1 indexed.2
        remaining edge
      intro empty
      rw [empty] at outward
      exact List.not_mem_nil outward

/-- Actual internally selected role cursor retains its tag-rooted official node, including
both repeated-carbon branches. This is an identity result, not a source-key premise. -/
theorem family_role_root_node (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel offset : Nat) (member : offset ∈ [2, 6, 7, 8]) (bound : offset < 12) :
    ((familyFrame ps i carrierFuel).cursorAt
      (familyRoleSlot ps i carrierFuel offset member)).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i offset bound) := by
  let cursor := (familyFrame ps i carrierFuel).cursorAt
    (familyRoleSlot ps i carrierFuel offset member)
  have present : cursor ∈ finalOccurrenceRoots (familySource ps) carrierFuel (familyCenter ps i) :=
    List.get_mem _ _
  obtain ⟨neighbor, _, nodeEq⟩ := converted_final_cursor_real_root (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 carrierFuel (familyCenter ps i)
    (familyRecordDomain ps i) cursor present
  have observedId : slotAtomID (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
      carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i)
      (familyRoleSlot ps i carrierFuel offset member) = neighbor.val := by
    change (cursorAtomID (familySource ps) cursor).getD 0 = neighbor.val
    simp [cursorAtomID, nodeEq, OfficialCIPNode.rootFromEdge]
  have sameIndex := observedId.symm.trans (family_role_slot_index ps i carrierFuel offset member)
  have neighborEq : neighbor = familyAtom ps i offset bound := Fin.ext sameIndex
  have centerEq : (familyCenter ps i).1 = familyAtom ps i 5 (by decide) :=
    Fin.ext (family_center_index ps i)
  simpa only [neighborEq, centerEq] using nodeEq

noncomputable def familyBridgeCursor (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) : (familySource ps).AromaticCanonicalRerootCursor carrierFuel :=
  (familyFrame ps i carrierFuel).cursorAt (familyRoleSlot ps i carrierFuel 2 (by simp))

noncomputable def familyMethylCursor (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) : (familySource ps).AromaticCanonicalRerootCursor carrierFuel :=
  (familyFrame ps i carrierFuel).cursorAt (familyRoleSlot ps i carrierFuel 8 (by simp))

/-- At every independently positive carrier depth the actual selected carbon ligands both
retain an outward sphere. This proves adequacy against total second-layer carrier truncation;
it does not yet identify exact sorted source-key projections or descriptor-model output. -/
theorem family_positive_carbon_outward (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) (adequate : 1 ≤ carrierFuel) :
    (familySource ps).aromaticCanonicalCarrierOutwardChildFrames
      (fuel := carrierFuel) (familyBridgeCursor ps i carrierFuel).occurrence.1 ≠ [] ∧
    (familySource ps).aromaticCanonicalCarrierOutwardChildFrames
      (fuel := carrierFuel) (familyMethylCursor ps i carrierFuel).occurrence.1 ≠ [] := by
  have bridgePresent : familyBridgeCursor ps i carrierFuel ∈
      finalOccurrenceRoots (familySource ps) carrierFuel (familyCenter ps i) := List.get_mem _ _
  have methylPresent : familyMethylCursor ps i carrierFuel ∈
      finalOccurrenceRoots (familySource ps) carrierFuel (familyCenter ps i) := List.get_mem _ _
  have bridgeCoordinates := returned_direct_coordinates (familySource ps) carrierFuel
    (familyCenter ps i) (familyBridgeCursor ps i carrierFuel) bridgePresent
  have methylCoordinates := returned_direct_coordinates (familySource ps) carrierFuel
    (familyCenter ps i) (familyMethylCursor ps i carrierFuel) methylPresent
  have bridgeNode : (familyBridgeCursor ps i carrierFuel).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i 2 (by decide)) :=
    family_role_root_node ps i carrierFuel 2 (by simp) (by decide)
  have methylNode : (familyMethylCursor ps i carrierFuel).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i 8 (by decide)) :=
    family_role_root_node ps i carrierFuel 8 (by simp) (by decide)
  constructor
  · apply carrier_positive_has_outward (familySource ps) (familyBridgeCursor ps i carrierFuel).occurrence
    · rw [bridgeCoordinates.1]
      omega
    · rw [bridgeNode]
      intro empty
      have length := (family_source_bridge_child_ids ps i).length_eq
      rw [empty] at length
      simp at length
  · apply carrier_positive_has_outward (familySource ps) (familyMethylCursor ps i carrierFuel).occurrence
    · rw [methylCoordinates.1]
      omega
    · rw [methylNode]
      intro empty
      have length := (family_source_methyl_child_ids ps i).length_eq
      rw [empty] at length
      simp at length

/-- A real returned direct ligand's outward carrier coordinates survive the actual incoming
cut. Parent erasure uses addresses, and an outward address cannot equal the final root address. -/
theorem returned_outward_is_intended (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center)
    (real : cursor.occurrence.1.node.provenance = .realAtom)
    (candidate : source.AromaticCanonicalOccurrenceFrame)
    (outward : candidate ∈ source.aromaticCanonicalCarrierOutwardChildFrames
      (fuel := carrierFuel) cursor.occurrence.1) :
    candidate ∈ source.intendedAromaticCanonicalRerootChildFrames cursor := by
  have coordinates := returned_direct_coordinates source carrierFuel center cursor present
  have conditions := (List.mem_filter.mp outward).2
  simp only [Bool.and_eq_true, beq_iff_eq] at conditions
  have length : candidate.address.length = 2 := by omega
  have different : candidate.address ≠
      (source.aromaticCanonicalFinalOccurrence carrierFuel center).1.address := by
    intro same
    have lengths := congrArg List.length same
    change candidate.address.length = 0 at lengths
    omega
  have nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, real, OfficialCIPNodeProvenance.isDuplicateLeaf]
  unfold intendedAromaticCanonicalRerootChildFrames
  rw [nonduplicate, coordinates.2.2]
  simp only [Bool.false_eq_true, ↓reduceIte, List.mem_filter, bne_iff_ne]
  refine ⟨?_, different⟩
  rw [aromaticCanonicalRerootNeighborFrames, List.mem_append]
  exact Or.inr outward

/-- Nonempty physical outward carrier geometry forces nonempty production reroot children for
real returned direct roots. No executable-success equation is a caller input. -/
theorem returned_outward_has_reroot_children (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center)
    (real : cursor.occurrence.1.node.provenance = .realAtom)
    (outwardNonempty : source.aromaticCanonicalCarrierOutwardChildFrames
      (fuel := carrierFuel) cursor.occurrence.1 ≠ []) :
    source.aromaticCanonicalRerootChildren cursor ≠ [] := by
  obtain ⟨candidate, outward⟩ := List.exists_mem_of_ne_nil _ outwardNonempty
  have intended := returned_outward_is_intended source carrierFuel center cursor present
    real candidate outward
  have frames := (source.aromaticCanonicalRerootChildren_sound cursor).1
  intro empty
  rw [empty] at frames
  have none : source.intendedAromaticCanonicalRerootChildFrames cursor = [] := frames.symm
  rw [none] at intended
  exact List.not_mem_nil intended

/-- The actual selected carbon roles have nonempty source reroot children at positive carrier
fuel. This is the production topology consumed by key construction. -/
theorem family_positive_carbon_reroot (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) (adequate : 1 ≤ carrierFuel) :
    (familySource ps).aromaticCanonicalRerootChildren (familyBridgeCursor ps i carrierFuel) ≠ [] ∧
    (familySource ps).aromaticCanonicalRerootChildren (familyMethylCursor ps i carrierFuel) ≠ [] := by
  have outward := family_positive_carbon_outward ps i carrierFuel adequate
  have bridgeNode := family_role_root_node ps i carrierFuel 2 (by simp) (by decide)
  have methylNode := family_role_root_node ps i carrierFuel 8 (by simp) (by decide)
  constructor
  · apply returned_outward_has_reroot_children (familySource ps) carrierFuel (familyCenter ps i)
      (familyBridgeCursor ps i carrierFuel) (List.get_mem _ _) _ outward.1
    change ((familyFrame ps i carrierFuel).cursorAt
      (familyRoleSlot ps i carrierFuel 2 (by simp))).occurrence.1.node.provenance = .realAtom
    rw [bridgeNode]
    rfl
  · apply returned_outward_has_reroot_children (familySource ps) carrierFuel (familyCenter ps i)
      (familyMethylCursor ps i carrierFuel) (List.get_mem _ _) _ outward.2
    change ((familyFrame ps i carrierFuel).cursorAt
      (familyRoleSlot ps i carrierFuel 8 (by simp))).occurrence.1.node.provenance = .realAtom
    rw [methylNode]
    rfl

/-- Actual recursive branch meaning retained from the production key derivation. The child
keys, their physical cursor derivations, permutation and descending proof are witnesses,
not caller-supplied keys or ordering outcomes. -/
def SourceKeyBranch (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) (ruleFuel : Nat)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) : Prop :=
  ∃ (depth : Nat) (children : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (childKeys sorted : List source.AromaticCanonicalUncancelledRule3SpatialKey),
    ruleFuel = depth + 1 ∧
    source.DeclarativeAromaticCanonicalRerootChildren cursor children ∧ children ≠ [] ∧
    source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList excluded depth children childKeys ∧
    sorted.Perm childKeys ∧
    AromaticCanonicalUncancelledRule3SpatialKeysDescending
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys sorted ∧
    key.constitutional.sourceNodes = [[([], cursor.occurrence.1.node)]] ++
      OfficialRuleMajorKey.mergeAddressedChildren
        (sorted.map fun child => child.constitutional.sourceNodes)

private theorem source_key_branch_of_nonterminal (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel cursor key)
    (nonterminal : source.aromaticCanonicalRerootChildren cursor ≠ []) :
    SourceKeyBranch source excluded ruleFuel cursor key := by
  cases derived with
  | zeroLeaf frame terminal observed =>
      have computed := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
      have actual := computed
      simp only [aromaticCanonicalRerootChildren?, Option.some.injEq] at actual
      exact False.elim (nonterminal (actual.trans terminal))
  | successorLeaf frame terminal observed =>
      have computed := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
      have actual := computed
      simp only [aromaticCanonicalRerootChildren?, Option.some.injEq] at actual
      exact False.elim (nonterminal (actual.trans terminal))
  | successorBranch frame nonterminal observed childrenDerived permutation descending =>
      refine ⟨_, _, _, _, rfl, frame, nonterminal, childrenDerived, permutation, descending, ?_⟩
      simp only [ExactOfficialRuleMajorKey.assemble,
        MoleculeGraph.exactOfficialRuleMajorRootKey, List.map_map, Function.comp_def]

private theorem exceptList_pointwise {source : AuthoritativeChemicalInput}
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded ruleFuel cursors keys) :
    List.Forall₂ (source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel)
      cursors keys :=
  match derived with
  | .nil _ => .nil
  | .cons head tail => .cons head (exceptList_pointwise tail)

/-- Exact branch assembly of an actual production key at a nonterminal returned slot. This
general helper exposes the production proof; final family use computes the keys internally. -/
theorem production_keyFrame_branch (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view ruleFuel frame.roots = some keys) (slot : Fin 4)
    (nonterminal : source.aromaticCanonicalRerootChildren (frame.cursorAt slot) ≠ []) :
    SourceKeyBranch source keys.rule3Frame.excluded ruleFuel (frame.cursorAt slot)
      (keys.keyAt slot).rule3 := by
  have meaning := source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
    target view ruleFuel frame.roots keys computed
  have pointwise := exceptList_pointwise meaning.1.2.2.2
  have derived := pointwise.get (i := slot.val)
    (by rw [frame.rootsLength]; exact slot.isLt)
    (by rw [keys.rule3Length]; exact slot.isLt)
  exact source_key_branch_of_nonterminal source derived nonterminal

/-- Actual internally constructed bridge and methyl production keys retain their complete
nonleaf assembly relation at positive carrier depth. Exact numeric second-layer projection,
strict repeated-carbon comparison and scheduled descriptor/model remain OPEN. -/
theorem family_positive_carbon_key_branches (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel : Nat) (adequate : 1 ≤ carrierFuel) :
    SourceKeyBranch (familySource ps) (familyKeys ps i carrierFuel).rule3Frame.excluded
      (2 * (carrierFuel + 1)) (familyBridgeCursor ps i carrierFuel)
      ((familyKeys ps i carrierFuel).keyAt (familyRoleSlot ps i carrierFuel 2 (by simp))).rule3 ∧
    SourceKeyBranch (familySource ps) (familyKeys ps i carrierFuel).rule3Frame.excluded
      (2 * (carrierFuel + 1)) (familyMethylCursor ps i carrierFuel)
      ((familyKeys ps i carrierFuel).keyAt (familyRoleSlot ps i carrierFuel 8 (by simp))).rule3 := by
  have nonterminal := family_positive_carbon_reroot ps i carrierFuel adequate
  constructor
  · exact production_keyFrame_branch (familySource ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i))
      (constitutionalView ps i carrierFuel) (2 * (carrierFuel + 1)) (familyFrame ps i carrierFuel)
      (familyKeys ps i carrierFuel) (family_keys_computed ps i carrierFuel)
      (familyRoleSlot ps i carrierFuel 2 (by simp)) nonterminal.1
  · exact production_keyFrame_branch (familySource ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence carrierFuel (familyCenter ps i))
      (constitutionalView ps i carrierFuel) (2 * (carrierFuel + 1)) (familyFrame ps i carrierFuel)
      (familyKeys ps i carrierFuel) (family_keys_computed ps i carrierFuel)
      (familyRoleSlot ps i carrierFuel 8 (by simp)) nonterminal.2

/-- Exact second-layer carrier membership at the internally minimal depth one. Reachability
has precisely two official edges here, so there are neither missing nor extra outward nodes. -/
theorem one_carrier_outward_iff (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (child : OfficialCIPNode source.AromaticCanonicalAtom) (rootSlot : Nat)
    (rootEdge : (child, rootSlot) ∈ (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
      source.molecule.atomCount (OfficialCIPNode.root center.1)).zipIdx)
    (candidate : source.AromaticCanonicalOccurrenceFrame) :
    candidate ∈ source.aromaticCanonicalCarrierOutwardChildFrames (fuel := 1)
      { root := center.1, address := [rootSlot], node := child, remaining := 1 } ↔
      ∃ grandchild slot,
        (grandchild, slot) ∈ (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount child).zipIdx ∧
        candidate = { root := center.1, address := [rootSlot, slot], node := grandchild, remaining := 0 } := by
  constructor
  · intro outward
    rw [aromaticCanonicalCarrierOutwardChildFrames, List.mem_filter] at outward
    obtain ⟨global, conditions⟩ := outward
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    have rootEq := conditions.1.1
    have addressLength : candidate.address.length = 2 := by simpa using conditions.1.2
    have derived := (source.mem_aromaticCanonicalOccurrences_iff 1 candidate).mp global
    have atCenter : source.DeclarativeAromaticCanonicalOccurrenceSubtree
        center.1 [] 2 (OfficialCIPNode.root center.1) candidate := by
      simpa [DeclarativeAromaticCanonicalOccurrence,
        DeclarativeAromaticCanonicalOccurrenceAtAtom, rootEq] using derived
    cases atCenter with
    | subtreeRoot => simp at addressLength
    | @subtreeDescendant _ _ _ direct firstSlot candidate firstEdge below =>
        cases below with
        | subtreeRoot => simp at addressLength
        | @subtreeDescendant _ _ _ grandchild slot candidate edge last =>
            cases last with
            | subtreeRoot =>
                have sameSlot : firstSlot = rootSlot := by simpa using conditions.2
                subst firstSlot
                have firstLookup := List.mk_mem_zipIdx_iff_getElem?.mp firstEdge
                have rootLookup := List.mk_mem_zipIdx_iff_getElem?.mp rootEdge
                have sameChild : direct = child := Option.some.inj (firstLookup.symm.trans rootLookup)
                subst direct
                exact ⟨grandchild, slot, edge, rfl⟩
  · rintro ⟨grandchild, slot, edge, rfl⟩
    rw [aromaticCanonicalCarrierOutwardChildFrames, List.mem_filter]
    constructor
    · apply (source.mem_aromaticCanonicalOccurrences_iff 1 _).mpr
      change source.DeclarativeAromaticCanonicalOccurrenceSubtree
        center.1 [] 2 (OfficialCIPNode.root center.1)
          { root := center.1, address := [rootSlot, slot], node := grandchild, remaining := 0 }
      exact .subtreeDescendant rootEdge (.subtreeDescendant edge
        (.subtreeRoot [rootSlot, slot] 0 grandchild))
    · simp

theorem returned_direct_official_coordinate (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center) :
    ∃ child slot,
      (child, slot) ∈ (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount (OfficialCIPNode.root center.1)).zipIdx ∧
      cursor.occurrence.1 = { root := center.1, address := [slot], node := child, remaining := carrierFuel } := by
  have here : cursor.occurrence.1 ∈
      (finalOccurrenceRoots source carrierFuel center).map (fun child => child.occurrence.1) :=
    List.mem_map.mpr ⟨cursor, present, rfl⟩
  have official := (finalOccurrenceRoots_frames_perm source carrierFuel center).mem_iff.mp here
  exact (mem_aromaticCanonicalFinalDirectChildFrames_iff source carrierFuel center _).mp official

/-- Fixed-depth exact outward meaning for actual returned source roots. -/
theorem returned_one_outward_iff (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 1)
    (present : cursor ∈ finalOccurrenceRoots source 1 center)
    (candidate : source.AromaticCanonicalOccurrenceFrame) :
    candidate ∈ source.aromaticCanonicalCarrierOutwardChildFrames (fuel := 1) cursor.occurrence.1 ↔
      ∃ child slot,
        (child, slot) ∈ (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount cursor.occurrence.1.node).zipIdx ∧
        candidate = { root := cursor.occurrence.1.root, address := cursor.occurrence.1.address ++ [slot], node := child, remaining := 0 } := by
  obtain ⟨child, rootSlot, edge, coordinate⟩ :=
    returned_direct_official_coordinate source 1 center cursor present
  rw [coordinate]
  simpa using one_carrier_outward_iff source center child rootSlot edge candidate

noncomputable def directSecondFrames (source : AuthoritativeChemicalInput)
    (cursor : source.AromaticCanonicalRerootCursor 1) : List source.AromaticCanonicalOccurrenceFrame :=
  (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
    source.molecule.atomCount cursor.occurrence.1.node).zipIdx.map fun child =>
      { root := cursor.occurrence.1.root
        address := cursor.occurrence.1.address ++ [child.2]
        node := child.1
        remaining := 0 }

private theorem directSecondFrames_nodup (source : AuthoritativeChemicalInput)
    (cursor : source.AromaticCanonicalRerootCursor 1) : (directSecondFrames source cursor).Nodup := by
  let children := source.molecule.aromaticCanonicalOfficialCIPChildrenAt
    source.molecule.atomCount cursor.occurrence.1.node
  have slotNodup : (children.zipIdx.map Prod.snd).Nodup := by simp [List.nodup_range']
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at slotNodup
  unfold directSecondFrames
  change (children.zipIdx.map _).Nodup
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact slotNodup.imp (by
    intro left right different equal
    apply different
    have addresses := congrArg (fun frame : source.AromaticCanonicalOccurrenceFrame => frame.address) equal
    have tails := List.append_cancel_left addresses
    simpa using tails)

theorem returned_one_outward_frames_perm (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 1)
    (present : cursor ∈ finalOccurrenceRoots source 1 center) :
    (source.aromaticCanonicalCarrierOutwardChildFrames (fuel := 1) cursor.occurrence.1).Perm
      (directSecondFrames source cursor) := by
  apply (List.perm_ext_iff_of_nodup ((source.aromaticCanonicalOccurrences_nodup 1).filter _)
    (directSecondFrames_nodup source cursor)).mpr
  intro candidate
  change candidate ∈ source.aromaticCanonicalCarrierOutwardChildFrames (fuel := 1) cursor.occurrence.1 ↔ _
  rw [returned_one_outward_iff source center cursor present candidate]
  unfold directSecondFrames
  rw [List.mem_map]
  constructor
  · rintro ⟨child, slot, edge, rfl⟩
    exact ⟨(child, slot), edge, rfl⟩
  · rintro ⟨⟨child, slot⟩, edge, rfl⟩
    exact ⟨child, slot, edge, rfl⟩

/-- The real direct-root cut selects precisely its outward carrier set. -/
theorem returned_intended_outward_perm (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center)
    (real : cursor.occurrence.1.node.provenance = .realAtom) :
    (source.intendedAromaticCanonicalRerootChildFrames cursor).Perm
      (source.aromaticCanonicalCarrierOutwardChildFrames (fuel := carrierFuel) cursor.occurrence.1) := by
  apply (List.perm_ext_iff_of_nodup (source.intendedAromaticCanonicalRerootChildFrames_nodup cursor)
    ((source.aromaticCanonicalOccurrences_nodup carrierFuel).filter _)).mpr
  intro candidate
  constructor
  · intro intended
    have coordinates := returned_direct_coordinates source carrierFuel center cursor present
    have neighbor := source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended cursor candidate intended
    have cut := source.address_ne_previous_of_mem_aromaticCanonicalIntended cursor
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) coordinates.2.2 candidate intended
    rw [aromaticCanonicalRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parent | outward
    · have conditions := (List.mem_filter.mp parent).2
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have one := coordinates.2.1
      have zero : candidate.address.length = 0 := by omega
      have same : candidate.address =
          (source.aromaticCanonicalFinalOccurrence carrierFuel center).1.address := by
        change candidate.address = []
        exact List.eq_nil_of_length_eq_zero zero
      exact False.elim (cut same)
    · exact outward
  · exact returned_outward_is_intended source carrierFuel center cursor present real candidate

/-- Actual fixed-depth source reroot children are a permutation of the official physical child
nodes. This joins production cursor topology to the source graph, beyond key existence. -/
theorem returned_one_reroot_nodes_perm (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 1)
    (present : cursor ∈ finalOccurrenceRoots source 1 center)
    (real : cursor.occurrence.1.node.provenance = .realAtom) :
    ((source.aromaticCanonicalRerootChildren cursor).map (fun child => child.occurrence.1.node)).Perm
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount cursor.occurrence.1.node) := by
  have permutation := (returned_intended_outward_perm source 1 center cursor present real).trans
    (returned_one_outward_frames_perm source center cursor present)
  have nodes := permutation.map (fun frame => frame.node)
  rw [← (source.aromaticCanonicalRerootChildren_sound cursor).1, List.map_map] at nodes
  have official : (directSecondFrames source cursor).map (fun frame => frame.node) =
      source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount cursor.occurrence.1.node := by
    unfold directSecondFrames
    rw [List.map_map]
    change (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
      source.molecule.atomCount cursor.occurrence.1.node).zipIdx.map Prod.fst = _
    exact List.zipIdx_map_fst 0 _
  rw [official] at nodes
  exact nodes

theorem official_zero_copy_observation {V : Type*} [Fintype V] [DecidableEq V]
    (graph : MoleculeGraph V) (node : OfficialCIPNode V) (neighbor : V) :
    graph.exactOfficialRule1aObservation (OfficialCIPNode.extend node neighbor 0) =
      .ofNat (graph.atomZ neighbor) := by
  by_cases visited : neighbor ∈ node.history <;>
    simp [MoleculeGraph.exactOfficialRule1aObservation, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, visited]

def atomIDObservation (raw : RawMolecule) (atomID : Option Nat) : DeclarativeCIP.ExactAtomicNumber :=
  .ofNat (raw.atomZAt (atomID.getD raw.atomCount))

/-- Actual source observations below a unit-bond edge are read from the converted physical
atom identities. No distinct-Z condition or source-key projection is a premise. -/
theorem converted_edge_observation_ids (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalAtom) (domain : SourceRecordDomain raw center.val)
    (parent : source.AromaticCanonicalAtom) :
    (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      (OfficialCIPNode.rootFromEdge parent center)).map
        source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation =
    ((source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      (OfficialCIPNode.rootFromEdge parent center)).map
        (fun node => node.current?.map Fin.val)).map (atomIDObservation raw) := by
  rw [converted_official_edge_children raw source converted center domain parent]
  simp only [List.map_map]
  apply List.map_congr_left
  intro neighbor _
  dsimp only [Function.comp_def]
  rw [official_zero_copy_observation, converted_atomic_number raw source converted neighbor]
  rfl

theorem family_source_bridge_observations (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (((familySource ps).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (familySource ps).molecule.atomCount
      (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i 2 (by decide)))).map
      (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation).Perm
        [DeclarativeCIP.ExactAtomicNumber.ofNat 6, .ofNat 1, .ofNat 1] := by
  have domain : SourceRecordDomain (familyRaw ps) (familyAtom ps i 2 (by decide)).val :=
    ⟨familyRaw_wellFormed ps, (familyRaw_closed_rows_nodup ps i).1,
      fun bond member _ => familyRaw_all_single ps bond member⟩
  have permutation := (family_source_bridge_child_ids ps i).map (atomIDObservation (familyRaw ps))
  rw [← converted_edge_observation_ids (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 (familyAtom ps i 2 (by decide)) domain
    (familyAtom ps i 5 (by decide))] at permutation
  have z0 : (familyRaw ps).atomZAt (1 + 12 * i.val) = 6 := (familyRaw_interior_carbon_Z ps i).1
  have z3 : (familyRaw ps).atomZAt (1 + 12 * i.val + 3) = 1 := familyRaw_role_Z ps i 3 (by decide)
  have z4 : (familyRaw ps).atomZAt (1 + 12 * i.val + 4) = 1 := familyRaw_role_Z ps i 4 (by decide)
  simpa only [List.map_cons, List.map_nil, atomIDObservation, Option.getD_some, z0, z3, z4]
    using permutation

theorem family_source_methyl_observations (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (((familySource ps).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (familySource ps).molecule.atomCount
      (OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide))
        (familyAtom ps i 8 (by decide)))).map
      (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation).Perm
        [DeclarativeCIP.ExactAtomicNumber.ofNat 1, .ofNat 1, .ofNat 1] := by
  have domain : SourceRecordDomain (familyRaw ps) (familyAtom ps i 8 (by decide)).val :=
    ⟨familyRaw_wellFormed ps, (familyRaw_closed_rows_nodup ps i).2.2,
      fun bond member _ => familyRaw_all_single ps bond member⟩
  have permutation := (family_source_methyl_child_ids ps i).map (atomIDObservation (familyRaw ps))
  rw [← converted_edge_observation_ids (familyRaw ps) (familySource ps)
    (family_annotation_agreement ps).1 (familyAtom ps i 8 (by decide)) domain
    (familyAtom ps i 5 (by decide))] at permutation
  have z9 : (familyRaw ps).atomZAt (1 + 12 * i.val + 9) = 1 := familyRaw_role_Z ps i 9 (by decide)
  have z10 : (familyRaw ps).atomZAt (1 + 12 * i.val + 10) = 1 := familyRaw_role_Z ps i 10 (by decide)
  have z11 : (familyRaw ps).atomZAt (1 + 12 * i.val + 11) = 1 := familyRaw_role_Z ps i 11 (by decide)
  simpa only [List.map_cons, List.map_nil, atomIDObservation, Option.getD_some, z9, z10, z11]
    using permutation

/-- Exact physical observation multisets of the actual production source children at the
internally chosen adequate carrier depth one. This is a family theorem with only ps and i. -/
theorem family_one_child_observations (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (((familySource ps).aromaticCanonicalRerootChildren (familyBridgeCursor ps i 1)).map
      (fun child => (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm
          [DeclarativeCIP.ExactAtomicNumber.ofNat 6, .ofNat 1, .ofNat 1] ∧
    (((familySource ps).aromaticCanonicalRerootChildren (familyMethylCursor ps i 1)).map
      (fun child => (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm
          [DeclarativeCIP.ExactAtomicNumber.ofNat 1, .ofNat 1, .ofNat 1] := by
  have bridgeNode : (familyBridgeCursor ps i 1).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide)) (familyAtom ps i 2 (by decide)) :=
    family_role_root_node ps i 1 2 (by simp) (by decide)
  have methylNode : (familyMethylCursor ps i 1).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide)) (familyAtom ps i 8 (by decide)) :=
    family_role_root_node ps i 1 8 (by simp) (by decide)
  have bridge := returned_one_reroot_nodes_perm (familySource ps) (familyCenter ps i)
    (familyBridgeCursor ps i 1) (List.get_mem _ _)
    (by rw [bridgeNode]; rfl)
  have methyl := returned_one_reroot_nodes_perm (familySource ps) (familyCenter ps i)
    (familyMethylCursor ps i 1) (List.get_mem _ _)
    (by rw [methylNode]; rfl)
  rw [bridgeNode] at bridge
  rw [methylNode] at methyl
  have bridgeObservations := bridge.map
    (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
  have methylObservations := methyl.map
    (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
  simp only [List.map_map] at bridgeObservations methylObservations
  exact ⟨bridgeObservations.trans (family_source_bridge_observations ps i),
    methylObservations.trans (family_source_methyl_observations ps i)⟩

private theorem zero_descending_reroot_empty (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (previous : source.AromaticCanonicalOccurrence carrierFuel)
    (zero : cursor.occurrence.1.remaining = 0)
    (incoming : cursor.previous? = some previous)
    (drop : cursor.occurrence.1.address.dropLast = previous.1.address) :
    source.aromaticCanonicalRerootChildren cursor = [] := by
  have outward := carrier_outward_empty_at_zero source cursor.occurrence zero
  have intended : source.intendedAromaticCanonicalRerootChildFrames cursor = [] := by
    unfold intendedAromaticCanonicalRerootChildFrames
    split
    · rfl
    · rw [incoming, aromaticCanonicalRerootNeighborFrames, outward, List.append_nil]
      apply List.filter_eq_nil_iff.mpr
      intro candidate member
      have conditions := (List.mem_filter.mp member).2
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      simp [conditions.2, drop]
  have frames := (source.aromaticCanonicalRerootChildren_sound cursor).1
  rw [intended] at frames
  exact List.map_eq_nil_iff.mp frames

/-- Every production child of a real returned root at carrier depth one is terminal after the
actual cut. This is a carrier fact, not an isotope, key, comparison or callback premise. -/
theorem returned_one_child_terminal (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 1)
    (present : cursor ∈ finalOccurrenceRoots source 1 center)
    (real : cursor.occurrence.1.node.provenance = .realAtom)
    (child : source.AromaticCanonicalRerootCursor 1)
    (member : child ∈ source.aromaticCanonicalRerootChildren cursor) :
    source.aromaticCanonicalRerootChildren child = [] := by
  have relation := source.aromaticCanonicalRerootChildren_sound cursor
  have intended : child.occurrence.1 ∈ source.intendedAromaticCanonicalRerootChildFrames cursor := by
    rw [← relation.1]
    exact List.mem_map.mpr ⟨child, member, rfl⟩
  have outward := (returned_intended_outward_perm source 1 center cursor present real).mem_iff.mp intended
  obtain ⟨node, slot, _, coordinate⟩ :=
    (returned_one_outward_iff source center cursor present _).mp outward
  apply zero_descending_reroot_empty source child cursor.occurrence
  · rewrite [coordinate]
    rfl
  · exact relation.2 child member
  · rw [coordinate]
    simp

private theorem source_key_singleton_of_terminal (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel cursor key)
    (terminal : source.aromaticCanonicalRerootChildren cursor = []) :
    key.constitutional.sourceNodes = [[([], cursor.occurrence.1.node)]] := by
  cases derived with
  | zeroLeaf => rfl
  | successorLeaf => rfl
  | successorBranch frame nonterminal observed childrenDerived permutation descending =>
      have actual := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
      simp only [aromaticCanonicalRerootChildren?, Option.some.injEq] at actual
      exact False.elim (nonterminal (actual.symm.trans terminal))

noncomputable def keyAtomicNat (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) : Nat :=
  ((((ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
    key.constitutional.sourceNodes).head?.getD []).head?.getD ([], .zero)).2).numerator

private theorem source_key_head (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel cursor key) :
    key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] := by
  cases derived <;> rfl

private theorem source_key_atomicNat (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel cursor key) :
    keyAtomicNat source key =
      (source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        cursor.occurrence.1.node).numerator := by
  have head := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph key.constitutional.sourceNodes cursor.occurrence.1.node
    (source_key_head source derived)
  simp [keyAtomicNat, head]

private theorem exceptList_atomicNats (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded ruleFuel cursors keys) :
    keys.map (keyAtomicNat source) = cursors.map (fun cursor =>
      (source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        cursor.occurrence.1.node).numerator) := by
  have pointwise := exceptList_pointwise derived
  clear derived
  induction pointwise with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, source_key_atomicNat source head, ih]

private theorem exceptList_natural_heads (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded ruleFuel cursors keys)
    (natural : ∀ cursor ∈ cursors,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation cursor.occurrence.1.node =
        .ofNat ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          cursor.occurrence.1.node).numerator)) :
    ∀ key ∈ keys, (ExactOfficialRuleMajorKey.exactRule1aLayers
      source.molecule.toLocalizedMoleculeGraph key.constitutional.sourceNodes).head? =
        some [([], .ofNat (keyAtomicNat source key))] := by
  have pointwise := exceptList_pointwise derived
  clear derived
  revert natural
  induction pointwise with
  | nil => intro natural; simp
  | @cons cursor key cursors keys head tail ih =>
      intro natural selected member
      rcases List.mem_cons.mp member with rfl | retained
      · have projected := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
          source.molecule.toLocalizedMoleculeGraph selected.constitutional.sourceNodes cursor.occurrence.1.node
          (source_key_head source head)
        rw [source_key_atomicNat source head]
        rw [natural cursor List.mem_cons_self] at projected
        exact projected
      · exact ih (fun cursor member => natural cursor (List.mem_cons_of_mem _ member)) selected retained

private theorem exceptList_terminal_nodes (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded ruleFuel cursors keys)
    (terminal : ∀ cursor ∈ cursors, source.aromaticCanonicalRerootChildren cursor = [])
    (natural : ∀ cursor ∈ cursors,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation cursor.occurrence.1.node =
        .ofNat ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          cursor.occurrence.1.node).numerator)) :
    ∀ key ∈ keys, ∃ node,
      key.constitutional.sourceNodes = [[([], node)]] ∧
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation node =
        .ofNat (keyAtomicNat source key) := by
  have pointwise := exceptList_pointwise derived
  clear derived
  revert terminal natural
  induction pointwise with
  | nil => intro terminal natural; simp
  | @cons cursor key cursors keys head tail ih =>
      intro terminal natural selected member
      rcases List.mem_cons.mp member with rfl | retained
      · refine ⟨cursor.occurrence.1.node,
          source_key_singleton_of_terminal source head (terminal cursor List.mem_cons_self), ?_⟩
        rw [source_key_atomicNat source head]
        exact natural cursor List.mem_cons_self
      · exact ih (fun cursor member => terminal cursor (List.mem_cons_of_mem _ member))
          (fun cursor member => natural cursor (List.mem_cons_of_mem _ member)) selected retained

/-- Descending actual source keys have descending atomic heads whenever the physical heads
are natural-valued singleton roots. A strictly lower head would force the actual key comparator
lower before any isotope or descriptor-dependent rule. -/
theorem descending_keys_atomicNats (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (heads : ∀ key ∈ keys, (ExactOfficialRuleMajorKey.exactRule1aLayers
      source.molecule.toLocalizedMoleculeGraph key.constitutional.sourceNodes).head? =
        some [([], .ofNat (keyAtomicNat source key))])
    (descending : AromaticCanonicalUncancelledRule3SpatialKeysDescending
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys keys) :
    (keys.map (keyAtomicNat source)).Pairwise (fun left right => right ≤ left) := by
  rw [List.pairwise_map]
  change keys.Pairwise (fun left right =>
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right ≠ Ordering.lt) at descending
  apply descending.imp_of_mem
  intro left right leftMember rightMember ordered
  by_contra reversed
  have lower : keyAtomicNat source left < keyAtomicNat source right := Nat.lt_of_not_ge reversed
  have atomic := ExactOfficialRuleMajorKey.compareSparseExactRule1a_lt_of_heads_lt
    (heads left leftMember) (heads right rightMember) lower
  have strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right = .lt := by
    simp [compareAromaticCanonicalUncancelledRule3SpatialKeys,
      ExactOfficialRuleMajorKey.compare, ExactOfficialRuleMajorKey.compareAddressedSources,
      Ordering.byKey, compareLex, atomic]
  exact ordered strict

/-- A physical three-child minimal-carrier branch is projected from its actual production
key derivation. Sorting follows the derived key comparator and natural atomic heads; no sorted
key list or desired comparison is supplied. Final family use derives every premise below. -/
theorem source_three_leaf_projection (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 1)
    (present : cursor ∈ finalOccurrenceRoots source 1 center)
    (real : cursor.occurrence.1.node.provenance = .realAtom)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) (ruleFuel : Nat)
    (branch : SourceKeyBranch source excluded ruleFuel cursor key)
    (rootZ z0 z1 z2 : Nat)
    (rootObservation : source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      cursor.occurrence.1.node = .ofNat rootZ)
    (observations : ((source.aromaticCanonicalRerootChildren cursor).map (fun child =>
      (source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node).numerator)).Perm [z0, z1, z2])
    (natural : ∀ child ∈ source.aromaticCanonicalRerootChildren cursor,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation child.occurrence.1.node =
        .ofNat ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator))
    (orderedNumbers : [z0, z1, z2].Pairwise (fun left right => right ≤ left)) :
    ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
      key.constitutional.sourceNodes =
      [[([], .ofNat rootZ)], [([0], .ofNat z0), ([1], .ofNat z1), ([2], .ofNat z2)]] := by
  obtain ⟨depth, children, rawKeys, sorted, _, frame, _, derived, permutation, descending, assembly⟩ := branch
  have actual : source.aromaticCanonicalRerootChildren cursor = children := by
    have computed := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
    simpa only [aromaticCanonicalRerootChildren?, Option.some.injEq] using computed
  have childNatural : ∀ child ∈ children,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation child.occurrence.1.node =
        .ofNat ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator) := by
    intro child member
    exact natural child (by rw [actual]; exact member)
  have childTerminal : ∀ child ∈ children, source.aromaticCanonicalRerootChildren child = [] := by
    intro child member
    exact returned_one_child_terminal source center cursor present real child (by rw [actual]; exact member)
  have rawHeads := exceptList_natural_heads source derived childNatural
  have sortedHeads : ∀ key ∈ sorted,
      (ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
        key.constitutional.sourceNodes).head? = some [([], .ofNat (keyAtomicNat source key))] := by
    intro selected member
    exact rawHeads selected (permutation.mem_iff.mp member)
  have values := permutation.map (keyAtomicNat source)
  rw [exceptList_atomicNats source derived] at values
  have physical := observations
  rw [actual] at physical
  have valuesPerm := values.trans physical
  have sortedValues := descending_keys_atomicNats source sorted sortedHeads descending
  have valueOrder : sorted.map (keyAtomicNat source) = [z0, z1, z2] :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ first second => Nat.le_antisymm second first)
      sortedValues orderedNumbers valuesPerm
  have leafNodes := exceptList_terminal_nodes source derived childTerminal childNatural
  have sortedNodes : ∀ key ∈ sorted, ∃ node,
      key.constitutional.sourceNodes = [[([], node)]] ∧
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation node =
        .ofNat (keyAtomicNat source key) := by
    intro selected member
    exact leafNodes selected (permutation.mem_iff.mp member)
  have length : sorted.length = 3 := by
    have lengths := congrArg List.length valueOrder
    simpa only [List.length_map, List.length_cons, List.length_nil] using lengths
  obtain ⟨k0, k1, k2, sortedEq⟩ := List.length_eq_three.mp length
  subst sorted
  obtain ⟨n0, s0, o0⟩ := sortedNodes k0 (by simp)
  obtain ⟨n1, s1, o1⟩ := sortedNodes k1 (by simp)
  obtain ⟨n2, s2, o2⟩ := sortedNodes k2 (by simp)
  have v0 : keyAtomicNat source k0 = z0 := by
    simpa using congrArg (fun numbers : List Nat => numbers.getD 0 0) valueOrder
  have v1 : keyAtomicNat source k1 = z1 := by
    simpa using congrArg (fun numbers : List Nat => numbers.getD 1 0) valueOrder
  have v2 : keyAtomicNat source k2 = z2 := by
    simpa using congrArg (fun numbers : List Nat => numbers.getD 2 0) valueOrder
  rw [assembly]
  simp [ExactOfficialRuleMajorKey.exactRule1aLayers, OfficialRuleMajorKey.mapSourceLayers,
    OfficialRuleMajorKey.mergeAddressedChildren, OfficialRuleMajorKey.addressedChildLayerCount,
    OfficialRuleMajorKey.prefixLayer, OfficialRuleMajorKey.mapObservation,
    s0, s1, s2, rootObservation, o0, o1, o2, v0, v1, v2, List.range_succ]

/-- Exact two-layer Rule-1a projections of the actual internally computed production keys.
The carrier depth is internally fixed to one and evaluation fuel to four. All child geometry,
natural observations, terminality and sorting are derived from physical/source construction. -/
theorem family_one_production_projections (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ExactOfficialRuleMajorKey.exactRule1aLayers (familySource ps).molecule.toLocalizedMoleculeGraph
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 2 (by simp))).rule3.constitutional.sourceNodes =
        [carbonRootLayer, bridgeChildLayer] ∧
    ExactOfficialRuleMajorKey.exactRule1aLayers (familySource ps).molecule.toLocalizedMoleculeGraph
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 8 (by simp))).rule3.constitutional.sourceNodes =
        [carbonRootLayer, methylChildLayer] := by
  have branches := family_positive_carbon_key_branches ps i 1 (by decide)
  have observed := family_one_child_observations ps i
  have bridgeNode : (familyBridgeCursor ps i 1).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide)) (familyAtom ps i 2 (by decide)) :=
    family_role_root_node ps i 1 2 (by simp) (by decide)
  have methylNode : (familyMethylCursor ps i 1).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (familyAtom ps i 5 (by decide)) (familyAtom ps i 8 (by decide)) :=
    family_role_root_node ps i 1 8 (by simp) (by decide)
  have bridgeRoot : (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (familyBridgeCursor ps i 1).occurrence.1.node = .ofNat 6 := by
    rw [bridgeNode, MoleculeGraph.exactOfficialRule1aObservation_rootFromEdge, family_source_role_Z]
    rfl
  have methylRoot : (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (familyMethylCursor ps i 1).occurrence.1.node = .ofNat 6 := by
    rw [methylNode, MoleculeGraph.exactOfficialRule1aObservation_rootFromEdge, family_source_role_Z]
    rfl
  have bridgeNumbers := observed.1.map DeclarativeCIP.ExactAtomicNumber.numerator
  have methylNumbers := observed.2.map DeclarativeCIP.ExactAtomicNumber.numerator
  simp only [List.map_map, List.map_cons, List.map_nil, DeclarativeCIP.ExactAtomicNumber.ofNat]
    at bridgeNumbers methylNumbers
  have bridgeNatural : ∀ child ∈ (familySource ps).aromaticCanonicalRerootChildren
      (familyBridgeCursor ps i 1),
      (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation child.occurrence.1.node =
        .ofNat (((familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator) := by
    intro child member
    have natural := observed.1.mem_iff.mp (List.mem_map.mpr ⟨child, member, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at natural
    rcases natural with first | second | third
    · rw [first]
      rfl
    · rw [second]
      rfl
    · rw [third]
      rfl
  have methylNatural : ∀ child ∈ (familySource ps).aromaticCanonicalRerootChildren
      (familyMethylCursor ps i 1),
      (familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation child.occurrence.1.node =
        .ofNat (((familySource ps).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator) := by
    intro child member
    have natural := observed.2.mem_iff.mp (List.mem_map.mpr ⟨child, member, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at natural
    rcases natural with first | second | third
    · rw [first]
      rfl
    · rw [second]
      rfl
    · rw [third]
      rfl
  have bridge := source_three_leaf_projection (familySource ps) (familyCenter ps i)
    (familyBridgeCursor ps i 1) (List.get_mem _ _) (by rw [bridgeNode]; rfl)
    ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 2 (by simp))).rule3
    (familyKeys ps i 1).rule3Frame.excluded 4 branches.1 6 6 1 1 bridgeRoot
    bridgeNumbers bridgeNatural (by decide)
  have methyl := source_three_leaf_projection (familySource ps) (familyCenter ps i)
    (familyMethylCursor ps i 1) (List.get_mem _ _) (by rw [methylNode]; rfl)
    ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 8 (by simp))).rule3
    (familyKeys ps i 1).rule3Frame.excluded 4 branches.2 6 1 1 1 methylRoot
    methylNumbers methylNatural (by decide)
  exact ⟨bridge, methyl⟩

/-- Strict comparison of the actual chosen production Rule-3 keys in both directions. Later
Rules 1b--5, masses, auxiliary descriptors and dependency views cannot override Rule 1a here. -/
theorem family_one_rule3_keys_both (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familySource ps).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 2 (by simp))).rule3
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 8 (by simp))).rule3 = .gt ∧
    (familySource ps).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 8 (by simp))).rule3
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 2 (by simp))).rule3 = .lt := by
  have projections := family_one_production_projections ps i
  have atomic := second_sphere_sparse_both [] []
  constructor <;>
    simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, ExactOfficialRuleMajorKey.compare,
      ExactOfficialRuleMajorKey.compareAddressedSources, Ordering.byKey, compareLex,
      projections.1, projections.2, atomic.1, atomic.2]

theorem family_one_production_keys_both (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5Keys
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 2 (by simp)))
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 8 (by simp))) = .gt ∧
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5Keys
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 8 (by simp)))
      ((familyKeys ps i 1).keyAt (familyRoleSlot ps i 1 2 (by simp))) = .lt := by
  have strict := family_one_rule3_keys_both ps i
  constructor <;>
    simp [compareAromaticCanonicalOccurrenceRule3Through5Keys, Ordering.byKey, compareLex,
      strict.1, strict.2]

/-- Actual production source comparison callback, preserving its non-pseudo metadata. -/
theorem family_one_source_callback_both (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyKeys ps i 1)
      (familyRoleSlot ps i 1 2 (by simp)) (familyRoleSlot ps i 1 8 (by simp)) =
        some { ordering := .gt, decisiveRule? := none, pseudo := false } ∧
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyKeys ps i 1)
      (familyRoleSlot ps i 1 8 (by simp)) (familyRoleSlot ps i 1 2 (by simp)) =
        some { ordering := .lt, decisiveRule? := none, pseudo := false } := by
  have strict := family_one_rule3_keys_both ps i
  constructor <;>
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      compareAromaticCanonicalOccurrenceRule3Through5At, strict.1, strict.2]

theorem family_role_slots_ne (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (carrierFuel left right : Nat) (leftMember : left ∈ [2, 6, 7, 8])
    (rightMember : right ∈ [2, 6, 7, 8]) (different : left ≠ right) :
    familyRoleSlot ps i carrierFuel left leftMember ≠ familyRoleSlot ps i carrierFuel right rightMember := by
  intro same
  have indices := congrArg (slotAtomID (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
    carrierFuel (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i)) same
  rw [family_role_slot_index, family_role_slot_index] at indices
  exact different (by omega)

theorem family_role_slots_nodup (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    [familyRoleSlot ps i 1 2 (by simp), familyRoleSlot ps i 1 6 (by simp),
      familyRoleSlot ps i 1 7 (by simp), familyRoleSlot ps i 1 8 (by simp)].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true]
  repeat' constructor
  all_goals exact family_role_slots_ne ps i 1 _ _ (by simp) (by simp) (by decide)

private theorem four_distinct_fin4_cover : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    ∀ slot : Fin 4, slot = a ∨ slot = b ∨ slot = c ∨ slot = d := by decide +kernel

theorem family_role_slots_cover (ps : List TetrahedralInputParity) (i : Fin ps.length) (slot : Fin 4) :
    slot = familyRoleSlot ps i 1 2 (by simp) ∨ slot = familyRoleSlot ps i 1 6 (by simp) ∨
    slot = familyRoleSlot ps i 1 7 (by simp) ∨ slot = familyRoleSlot ps i 1 8 (by simp) :=
  four_distinct_fin4_cover _ _ _ _ (family_role_slots_nodup ps i) slot

noncomputable def familyPriorityRank (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (slot : Fin 4) : Nat :=
  if slot = familyRoleSlot ps i 1 7 (by simp) then 4
  else if slot = familyRoleSlot ps i 1 2 (by simp) then 3
  else if slot = familyRoleSlot ps i 1 8 (by simp) then 2 else 1

theorem family_priority_rank_roles (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    familyPriorityRank ps i (familyRoleSlot ps i 1 2 (by simp)) = 3 ∧
    familyPriorityRank ps i (familyRoleSlot ps i 1 6 (by simp)) = 1 ∧
    familyPriorityRank ps i (familyRoleSlot ps i 1 7 (by simp)) = 4 ∧
    familyPriorityRank ps i (familyRoleSlot ps i 1 8 (by simp)) = 2 := by
  have bF := family_role_slots_ne ps i 1 2 7 (by simp) (by simp) (by decide)
  have hF := family_role_slots_ne ps i 1 6 7 (by simp) (by simp) (by decide)
  have hB := family_role_slots_ne ps i 1 6 2 (by simp) (by simp) (by decide)
  have hM := family_role_slots_ne ps i 1 6 8 (by simp) (by simp) (by decide)
  have mF := family_role_slots_ne ps i 1 8 7 (by simp) (by simp) (by decide)
  have mB := family_role_slots_ne ps i 1 8 2 (by simp) (by simp) (by decide)
  simp [familyPriorityRank, bF, hF, hB, hM, mF, mB]

theorem family_priority_rank_injective (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    Function.Injective (familyPriorityRank ps i) := by
  intro left right same
  have ranks := family_priority_rank_roles ps i
  rcases family_role_slots_cover ps i left with rfl | rfl | rfl | rfl <;>
    rcases family_role_slots_cover ps i right with rfl | rfl | rfl | rfl
  all_goals simp_all [ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2]

/-- Every off-diagonal production source callback agrees with the internally derived strict
role rank F > bridge > methyl > H. Both repeated-carbon cases use the actual second layer. -/
theorem family_one_callback_strictRank (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (left right : Fin 4) (different : left ≠ right) :
    (familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyKeys ps i 1) left right =
      strictRankComparison (familyPriorityRank ps i) left right := by
  have ranks := family_priority_rank_roles ps i
  have carbon := family_one_source_callback_both ps i
  rcases family_role_slots_cover ps i left with rfl | rfl | rfl | rfl <;>
    rcases family_role_slots_cover ps i right with rfl | rfl | rfl | rfl
  all_goals simp only [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2]
  all_goals first
    | exact False.elim (different rfl)
    | exact carbon.1
    | exact carbon.2
    | (apply family_source_unequal_role_comparison ps i 1; decide)

noncomputable def familyPrioritySlots (ps : List TetrahedralInputParity) (i : Fin ps.length) : List (Fin 4) :=
  [familyRoleSlot ps i 1 7 (by simp), familyRoleSlot ps i 1 2 (by simp),
    familyRoleSlot ps i 1 8 (by simp), familyRoleSlot ps i 1 6 (by simp)]

theorem family_priority_slots_perm (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyPrioritySlots ps i).Perm (List.finRange 4) := by
  have distinct : (familyPrioritySlots ps i).Nodup := by
    unfold familyPrioritySlots
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    repeat' constructor
    all_goals exact family_role_slots_ne ps i 1 _ _ (by simp) (by simp) (by decide)
  apply (List.perm_ext_iff_of_nodup distinct (List.nodup_finRange 4)).mpr
  intro slot
  simp only [List.mem_finRange, iff_true]
  rcases family_role_slots_cover ps i slot with rfl | rfl | rfl | rfl <;> simp [familyPrioritySlots]

theorem family_priority_slots_descending (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyPrioritySlots ps i).Pairwise (fun left right => familyPriorityRank ps i right < familyPriorityRank ps i left) := by
  have ranks := family_priority_rank_roles ps i
  simp [familyPrioritySlots, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2]

/-- The actual production safe tracked source order is constructed internally and coherent.
This is the constitutional dependency view; scheduled-model identification remains separate. -/
theorem family_one_safe_tracked_order (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ∃ tracked,
      (familySource ps).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? (familyKeys ps i 1) = some tracked ∧
      tracked.highestFirst = familyPrioritySlots ps i ∧ tracked.pseudoComparisons = 0 ∧
      (familySource ps).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
        (familyKeys ps i 1) tracked.highestFirst = true := by
  obtain ⟨tracked, computed, permutation, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne (familyPriorityRank ps i)
      (family_priority_rank_injective ps i)
      ((familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At? (familyKeys ps i 1))
      (family_one_callback_strictRank ps i)
  have higherOrdering : ∀ left right, familyPriorityRank ps i right < familyPriorityRank ps i left →
      ((familySource ps).compareAromaticCanonicalOccurrenceRule3Through5At
        (familyKeys ps i 1) left right).ordering = .gt := by
    intro left right higher
    have different : left ≠ right := by intro same; subst right; exact Nat.lt_irrefl _ higher
    have callback := family_one_callback_strictRank ps i left right different
    have ordering := congrArg (fun result => result.map (fun comparison => comparison.ordering)) callback
    simpa [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      strictRankComparison, Nat.compare_eq_gt.mpr higher] using ordering
  have coherent := ((familySource ps).aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
    (familyKeys ps i 1) tracked.highestFirst).mpr (descending.imp (fun {left right} higher => higherOrdering left right higher))
  have safe : (familySource ps).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? (familyKeys ps i 1) =
      some tracked := by
    simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?, computed, coherent]
  have exactOrder : tracked.highestFirst = familyPrioritySlots ps i :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ first second => False.elim (Nat.lt_asymm first second))
      descending (family_priority_slots_descending ps i)
      (permutation.trans (family_priority_slots_perm ps i).symm)
  exact ⟨tracked, safe, exactOrder, zero, coherent⟩

noncomputable def familyTracked (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    TrackedLocalizedLigandOrder := Classical.choose (family_one_safe_tracked_order ps i)

theorem family_tracked_properties (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familySource ps).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? (familyKeys ps i 1) =
      some (familyTracked ps i) ∧
    (familyTracked ps i).highestFirst = familyPrioritySlots ps i ∧
    (familyTracked ps i).pseudoComparisons = 0 ∧
    (familySource ps).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      (familyKeys ps i 1) (familyTracked ps i).highestFirst = true :=
  Classical.choose_spec (family_one_safe_tracked_order ps i)

/-- The actual internally computed safe source tracked order maps to the physical written
positions [2,0,3,1], without identity source-slot alignment or caller-provided sorted roots. -/
theorem family_tracked_written_positions (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (((familyTracked ps i).highestFirst.map
      (slotAtomID (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
        1 (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i))).mapM
          (NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.writtenSlot?
            ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)))) = some [2, 0, 3, 1] := by
  have written := familyRaw_tag_written ps i
  have distinct : ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)).Nodup := by
    rw [written]
    simp (disch := omega) [List.nodup_cons]
  have p0 := NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.writtenSlot?_eq_some
    ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)) distinct 0 (1 + 12 * i.val + 2)
    (by rw [written]; rfl)
  have p1 := NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.writtenSlot?_eq_some
    ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)) distinct 1 (1 + 12 * i.val + 6)
    (by rw [written]; rfl)
  have p2 := NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.writtenSlot?_eq_some
    ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)) distinct 2 (1 + 12 * i.val + 7)
    (by rw [written]; rfl)
  have p3 := NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.writtenSlot?_eq_some
    ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)) distinct 3 (1 + 12 * i.val + 8)
    (by rw [written]; rfl)
  rw [(family_tracked_properties ps i).2.1]
  simp only [familyPrioritySlots, List.map_cons, List.map_nil, family_role_slot_index]
  simp [List.mapM_cons, p0, p1, p2, p3]

/-- Written-frame parity transport from the actual safe source order. This is the annotation
algebra; scheduled descriptor-model evaluation is a separate, still-open integration theorem. -/
theorem family_written_parity_transport (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ((((familyTracked ps i).highestFirst.map
      (slotAtomID (familyRaw ps) (familySource ps) (family_annotation_agreement ps).1
        1 (familyCenter ps i) (familyRecordDomain ps i) (family_four_records ps i))).mapM
          (NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.writtenSlot?
            ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)))).map
              (fun positions => descriptorOfParity (ps.get i) (permutationIsEven positions))) =
        some (descriptorOfParity (ps.get i) false) := by
  have odd : permutationIsEven [2, 0, 3, 1] = false := by decide +kernel
  rw [family_tracked_written_positions]
  simp only [Option.map_some, odd]

end TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
