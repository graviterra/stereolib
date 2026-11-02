import TetraStereo.UniversalProof.NativeSourceSingleIncidence
import TetraStereo.UniversalProof.LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery
import TetraStereo.UniversalProof.RuntimeSourceGenericPublicPipelineRecoveryProofs.RuntimeSourceGenericPublicPipelineRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge


















-- SingleIncidentDomain is re-exported from NativeSourceSingleIncidence.


namespace Incidence

section Converted
variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule)
variable (center : source.AromaticCanonicalAtom)
variable (domain : SingleIncidentDomain raw center.val)
include converted domain

-- converted_neighbor_bound is re-exported from NativeSourceSingleIncidence.



-- converted_center_incidents is re-exported from NativeSourceSingleIncidence.


-- converted_neighbor_record is re-exported from NativeSourceSingleIncidence.


-- converted_matching_record is re-exported from NativeSourceSingleIncidence.


-- converted_localized_keys_iff is re-exported from NativeSourceSingleIncidence.


omit converted domain in
private theorem lookup_single (records : List ((Nat × Nat) × Nat)) (key : Nat × Nat)
    (single : ∀ record ∈ records, record.1 = key → record.2 = 1) :
    SemanticMolecule.localizedBondOrderAtKey records key =
      if key ∈ records.map Prod.fst then 1 else 0 := by
  induction records with
  | nil => simp [SemanticMolecule.localizedBondOrderAtKey]
  | cons record records inductionHypothesis =>
      by_cases same : record.1 = key
      · simp [SemanticMolecule.localizedBondOrderAtKey, same,
          single record (by simp) same]
      · have tailSingle : ∀ item ∈ records, item.1 = key → item.2 = 1 := by
          intro item retained matched
          exact single item (List.mem_cons_of_mem _ retained) matched
        rw [SemanticMolecule.localizedBondOrderAtKey, if_neg same,
          inductionHypothesis tailSingle]
        simp only [List.map_cons, List.mem_cons, Ne.symm same, false_or]

-- converted_localized_bond_order is re-exported from NativeSourceSingleIncidence.


-- converted_no_incident_aromatic is re-exported from NativeSourceSingleIncidence.


-- converted_canonical_bond_order is re-exported from NativeSourceSingleIncidence.


-- converted_no_mancude_representative is re-exported from NativeSourceSingleIncidence.


-- converted_ordinary_copies is re-exported from NativeSourceSingleIncidence.



end Converted
end Incidence

/-- A ligand's actual incident records are single because its only neighbor is the center;
the center's degree need not be one. -/
theorem actual_leaf_incidence_domain (raw : RawMolecule) (center atom : Nat)
    (domain : SingleLeafDomain raw center) (member : atom ∈ recordNeighbors raw center) :
    SingleIncidentDomain raw atom := by
  have row := RuntimeSourceGenericPublicPipelineRecoveryProofs.RuntimeSourceGenericPublicPipelineRecovery.actual_leaf_record_row
    raw center atom domain.leaf member
  refine ⟨domain.leaf.wellFormed, ?_⟩
  intro bond retained incident
  rcases incident with sourceEqual | targetEqual
  · have observed : recordNeighbor? atom bond = some bond.target := by
      simp [recordNeighbor?, sourceEqual]
    have targetMember : bond.target ∈ recordNeighbors raw atom :=
      List.mem_filterMap.mpr ⟨bond, retained, observed⟩
    rw [row] at targetMember
    exact domain.incidentKinds bond retained (Or.inr (List.mem_singleton.mp targetMember))
  · have sourceDifferent : bond.source ≠ atom := by
      intro same
      exact (domain.leaf.wellFormed bond retained).2.2 (same.trans targetEqual.symm)
    have observed : recordNeighbor? atom bond = some bond.source := by
      simp [recordNeighbor?, sourceDifferent, targetEqual]
    have sourceMember : bond.source ∈ recordNeighbors raw atom :=
      List.mem_filterMap.mpr ⟨bond, retained, observed⟩
    rw [row] at sourceMember
    exact domain.incidentKinds bond retained (Or.inl (List.mem_singleton.mp sourceMember))

/-- Actual OLD canonical parent-copy removal: every ordinary copy is the single real parent. -/
theorem actual_formal_leaf_child_copies_nil (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center atom : source.AromaticCanonicalAtom) (domain : SingleLeafDomain raw center.val)
    (member : atom.val ∈ recordNeighbors raw center.val) :
    source.molecule.aromaticCanonicalChildCopiesAt source.molecule.atomCount
      (OfficialCIPNode.rootFromEdge center atom) = [] := by
  have narrow := actual_leaf_incidence_domain raw center.val atom.val domain member
  have row := RuntimeSourceGenericPublicPipelineRecoveryProofs.RuntimeSourceGenericPublicPipelineRecovery.actual_leaf_record_row
    raw center.val atom.val domain.leaf member
  change (source.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt source.molecule.atomCount atom).filter
    (fun copy => !(copy.1 == center && copy.2 == 0)) = []
  rw [Incidence.converted_ordinary_copies raw source converted atom narrow]
  apply List.filter_eq_nil_iff.mpr
  intro copy present
  obtain ⟨neighbor, retained, rfl⟩ := List.mem_map.mp present
  have neighborMember : neighbor.val ∈ recordNeighbors raw atom.val :=
    of_decide_eq_true (List.mem_filter.mp retained).2
  rw [row] at neighborMember
  have same : neighbor = center := Fin.ext (List.mem_singleton.mp neighborMember)
  simp [same]

/-- No ordinary outward copy OR aromatic virtual representative survives at the actual leaf. -/
theorem actual_formal_leaf_children_nil (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center atom : source.AromaticCanonicalAtom) (domain : SingleLeafDomain raw center.val)
    (member : atom.val ∈ recordNeighbors raw center.val) :
    source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      (OfficialCIPNode.rootFromEdge center atom) = [] := by
  have narrow := actual_leaf_incidence_domain raw center.val atom.val domain member
  have copies := actual_formal_leaf_child_copies_nil raw source converted center atom domain member
  simp only [OfficialCIPNode.rootFromEdge] at copies
  have noVirtual := Incidence.converted_no_mancude_representative raw source converted atom narrow
  simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, copies,
    OfficialCIPNode.rootFromEdge, OfficialCIPNode.isDuplicateLeaf, noVirtual]

/-- All actual official children of the source center are genuine terminal physical ligands. -/
theorem actual_formal_root_children_terminal (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalAtom) (domain : SingleLeafDomain raw center.val)
    (child : OfficialCIPNode source.AromaticCanonicalAtom)
    (present : child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      (OfficialCIPNode.root center)) :
    source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount child = [] := by
  rw [converted_official_children raw source converted center domain] at present
  obtain ⟨neighbor, retained, rfl⟩ := List.mem_map.mp present
  have member : neighbor.val ∈ recordNeighbors raw center.val :=
    of_decide_eq_true (List.mem_filter.mp retained).2
  have different : neighbor ≠ center := by
    intro equal
    exact (converted_neighbor_bound raw source converted center domain neighbor.val member).2
      (congrArg Fin.val equal)
  have nodeEq : (OfficialCIPNode.root center).extend neighbor 0 =
      OfficialCIPNode.rootFromEdge center neighbor := by
    simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
      OfficialCIPNode.root, OfficialCIPNode.rootFromEdge, different]
  rw [nodeEq]
  exact actual_formal_leaf_children_nil raw source converted center neighbor domain member

/-- Generic exact ORIGINAL subtree law for an actual terminal official node. -/
theorem actual_terminal_subtree (source : AuthoritativeChemicalInput)
    (root : source.AromaticCanonicalAtom) (fuel : Nat) (path : List Nat)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (terminal : source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount node = []) :
    source.aromaticCanonicalOccurrenceSubtree root fuel path node =
      [{ root := root, address := path, node := node, remaining := fuel }] := by
  cases fuel <;> simp [aromaticCanonicalOccurrenceSubtree, terminal]

/-- Every ORIGINAL carrier frame under the center is at depth zero or one, at ANY carrier fuel. -/
theorem actual_center_carrier_depth_le_one (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalAtom) (domain : SingleLeafDomain raw center.val)
    (fuel : Nat) (frame : source.AromaticCanonicalOccurrenceFrame)
    (present : frame ∈ source.aromaticCanonicalOccurrencesAtAtom fuel center) :
    frame.address.length ≤ 1 := by
  rw [aromaticCanonicalOccurrencesAtAtom, aromaticCanonicalOccurrenceSubtree, List.mem_cons] at present
  rcases present with here | below
  · subst frame
    simp
  · obtain ⟨child, childPresent, below⟩ := List.mem_flatMap.mp below
    have inChildren : child.1 ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount (OfficialCIPNode.root center) := by
      have inMap : child.1 ∈
          (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
            (OfficialCIPNode.root center)).zipIdx.map Prod.fst :=
        List.mem_map.mpr ⟨child, childPresent, rfl⟩
      rw [List.zipIdx_map_fst] at inMap
      exact inMap
    have terminal := actual_formal_root_children_terminal raw source converted center domain child.1 inChildren
    rw [actual_terminal_subtree source center fuel ([] ++ [child.2]) child.1 terminal] at below
    have equal := List.mem_singleton.mp below
    subst frame
    simp

/-- The molecule-wide original carrier retains that local depth bound; other components are free. -/
theorem actual_occurrence_depth_le_one (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalAtom) (domain : SingleLeafDomain raw center.val)
    (fuel : Nat) (occurrence : source.AromaticCanonicalOccurrence fuel)
    (sameRoot : occurrence.1.root = center) : occurrence.1.address.length ≤ 1 := by
  have derived := (source.mem_aromaticCanonicalOccurrences_iff fuel occurrence.1).mp occurrence.2
  have retained := (source.mem_aromaticCanonicalOccurrencesAtAtom_iff
    fuel occurrence.1.root occurrence.1).mpr derived
  rw [sameRoot] at retained
  exact actual_center_carrier_depth_le_one raw source converted center domain fuel occurrence.1 retained

/-- The actual final ligand zipper has no children at ANY carrier depth: the incoming center is
cut, while any purported outward child contradicts original-carrier local terminality. -/
theorem actual_final_cursor_children_nil (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    source.aromaticCanonicalRerootChildren cursor = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro child childPresent
  obtain ⟨_remaining, cursorLength, previous⟩ := final_cursor_grade_and_previous source fuel center cursor present
  have cursorRoot : cursor.occurrence.1.root = center.1 :=
    source.aromaticCanonicalRerootChildren_root_eq
      { occurrence := source.aromaticCanonicalFinalOccurrence fuel center, previous? := none } cursor present
  have childRoot : child.occurrence.1.root = center.1 :=
    (source.aromaticCanonicalRerootChildren_root_eq cursor child childPresent).trans cursorRoot
  have childBound := actual_occurrence_depth_le_one raw source converted center.1 domain fuel child.occurrence childRoot
  have intended : child.occurrence.1 ∈ source.intendedAromaticCanonicalRerootChildFrames cursor := by
    rw [← (source.aromaticCanonicalRerootChildren_sound cursor).1]
    exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
  have adjacent := ((source.mem_aromaticCanonicalRerootNeighborFrames_iff
    cursor.occurrence.1 child.occurrence.1).mp
      (source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended cursor child.occurrence.1 intended)).2
  rcases adjacent with ⟨_root, parent | outward⟩
  · have emptyAddress : child.occurrence.1.address = [] := List.length_eq_zero_iff.mp (by omega)
    exact source.address_ne_previous_of_mem_aromaticCanonicalIntended cursor
      (source.aromaticCanonicalFinalOccurrence fuel center) previous child.occurrence.1 intended emptyAddress
  · omega


/-- The actual structural leaf key at its ORIGINAL carrier coordinate. -/
def localLeafRule3Key (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.AromaticCanonicalUncancelledRule3SpatialKey :=
  { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey cursor.occurrence.1.node true
    observations := [], rule3 := [] }

theorem local_raw_key (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center) (ruleFuel : Nat) :
    source.buildAromaticCanonicalUncancelledRule3SpatialKey? ruleFuel cursor =
      some (localLeafRule3Key source cursor) := by
  have children := actual_final_cursor_children_nil raw source converted carrierFuel center domain cursor present
  have observed := local_final_cursor_structural_outcome raw source converted carrierFuel center domain cursor present
  cases ruleFuel <;> simp [buildAromaticCanonicalUncancelledRule3SpatialKey?, children,
    observed, localLeafRule3Key, aromaticCanonicalRule3RootObservations,
    aromaticCanonicalRule3RootPriorities]

theorem local_except_key (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) (ruleFuel : Nat) :
    source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded ruleFuel cursor =
      some (localLeafRule3Key source cursor) := by
  have children := actual_final_cursor_children_nil raw source converted carrierFuel center domain cursor present
  have observed := local_final_cursor_structural_outcome raw source converted carrierFuel center domain cursor present
  have exceptObserved : source.aromaticCanonicalRule3SpatialNodeExcept?
      excluded cursor.occurrence.1.node = some none := by
    simp [aromaticCanonicalRule3SpatialNodeExcept?, observed]
  cases ruleFuel <;> simp [buildAromaticCanonicalRule3SpatialKeyExcept?, children,
    exceptObserved, localLeafRule3Key, aromaticCanonicalRule3RootObservations,
    aromaticCanonicalRule3RootPriorities]

private theorem mapM_eq_some_map_of_member_eq
    {Input Output : Type} (f : Input → Option Output) (g : Input → Output) :
    ∀ inputs : List Input, (∀ input ∈ inputs, f input = some (g input)) →
      inputs.mapM f = some (inputs.map g)
  | [], _ => rfl
  | input :: inputs, computed => by
      have head := computed input (by simp)
      have tail := mapM_eq_some_map_of_member_eq f g inputs
        (fun value retained => computed value (List.mem_cons_of_mem input retained))
      simp [List.mapM_cons, head, tail]

noncomputable def localRule3Keys (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    List source.AromaticCanonicalUncancelledRule3SpatialKey :=
  (finalOccurrenceRoots source carrierFuel center).map (localLeafRule3Key source)

theorem local_rule3_frame_units_nil (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalRule3FramePhysicalUnits (localRule3Keys source carrierFuel center) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro unit retained
  rcases (source.mem_aromaticCanonicalRule3FramePhysicalUnits_iff _ unit).mp retained with
    ⟨key, keyPresent, layer, layerPresent, _entry, _entryPresent, _identity⟩
  rcases List.mem_map.mp keyPresent with ⟨cursor, _cursorPresent, rfl⟩
  simp [localLeafRule3Key] at layerPresent

theorem local_rule3_coupled_pairs_nil (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalRule3CoupledUnitPairs (localRule3Keys source carrierFuel center) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro pair retained
  have unitPresent := ((source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff _ pair).mp retained).1
  rw [local_rule3_frame_units_nil source carrierFuel center] at unitPresent
  simp at unitPresent

noncomputable def localRule3Frame (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalRule3CanonicalKeyFrame :=
  { rawKeys := localRule3Keys source carrierFuel center
    resolution := .ordinary, excluded := [], keys := localRule3Keys source carrierFuel center }

theorem local_rule3_frame (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (ruleFuel : Nat) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some (localRule3Frame source carrierFuel center) := by
  have rawComputed : (finalOccurrenceRoots source carrierFuel center).mapM
      (source.buildAromaticCanonicalUncancelledRule3SpatialKey? ruleFuel) =
      some (localRule3Keys source carrierFuel center) :=
    mapM_eq_some_map_of_member_eq _ _ _ (fun cursor present =>
      local_raw_key raw source converted carrierFuel center domain cursor present ruleFuel)
  have exceptComputed : (finalOccurrenceRoots source carrierFuel center).mapM
      (source.buildAromaticCanonicalRule3SpatialKeyExcept? [] ruleFuel) =
      some (localRule3Keys source carrierFuel center) :=
    mapM_eq_some_map_of_member_eq _ _ _ (fun cursor present =>
      local_except_key raw source converted carrierFuel center domain cursor present [] ruleFuel)
  have resolutionComputed : source.aromaticCanonicalRule3PhysicalTopologyResolution?
      (localRule3Keys source carrierFuel center) = some .ordinary := by
    simp [aromaticCanonicalRule3PhysicalTopologyResolution?, local_rule3_coupled_pairs_nil]
  have excludedEmpty : source.aromaticCanonicalRule3ExcludedPhysicalUnits
      (localRule3Keys source carrierFuel center) .ordinary = [] := by
    simp [aromaticCanonicalRule3ExcludedPhysicalUnits, aromaticCanonicalRule3SharedPhysicalUnits,
      local_rule3_frame_units_nil]
  simp [buildAromaticCanonicalRule3CanonicalKeyFrame?, rawComputed, resolutionComputed,
    excludedEmpty, exceptComputed, localRule3Frame]

private theorem exists_mapM_compound45_of_valid
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45Key? target view (2 * (carrierFuel + 1))) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ := source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
        target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ := exists_mapM_compound45_of_valid source target view cursors
        (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [List.mapM_cons, keyComputed, keysComputed]⟩

theorem exists_local_keyFrame (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
      (finalOccurrenceRoots source carrierFuel center) = some keys := by
  let rule3Frame := localRule3Frame source carrierFuel center
  have rule3Computed := local_rule3_frame raw source converted carrierFuel center domain (2 * (carrierFuel + 1))
  have rootLength := (actual_returned_four_roots raw source converted carrierFuel center domain four).2
  have rule3Length : rule3Frame.keys.length = 4 := by
    simpa [rule3Frame, localRule3Frame, localRule3Keys] using rootLength
  obtain ⟨rule45Keys, rule45Computed⟩ := exists_mapM_compound45_of_valid source
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (finalOccurrenceRoots source carrierFuel center)
    (finalOccurrenceRoots_valid source carrierFuel center)
  have rule45Length : rule45Keys.length = 4 :=
    (mapM_length_eq_of_eq_some (source.buildAromaticCanonicalRerootCompoundRule45Key?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)))
      (finalOccurrenceRoots source carrierFuel center) rule45Keys rule45Computed).trans rootLength
  refine ⟨{ rule3Frame, rule3Length, rule45Keys, rule45Length }, ?_⟩
  simp [buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?, rule3Frame,
    rule3Computed, rule3Length, rule45Computed, rule45Length]

theorem exists_local_safe_order (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ∃ keys tracked,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
        (actualFrame raw source converted carrierFuel center domain four).roots = some keys ∧
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        occurrenceAtomicPriority source (actualFrame raw source converted carrierFuel center domain four) right <
        occurrenceAtomicPriority source (actualFrame raw source converted carrierFuel center domain four) left) ∧
      tracked.pseudoComparisons = 0 := by
  let frame := actualFrame raw source converted carrierFuel center domain four
  have real := actual_roots_real raw source converted carrierFuel center domain four
  have injective := actual_priority_injective raw source converted carrierFuel center domain four
  obtain ⟨keys, keysComputed⟩ := exists_local_keyFrame raw source converted carrierFuel center domain four view
  obtain ⟨tracked, rawComputed, perm, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
      (occurrenceAtomicPriority source frame) injective
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys)
      (occurrence_callback_eq_strictRank_of_ne source (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        view (2 * (carrierFuel + 1)) frame real injective keys keysComputed)
  have coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keys tracked.highestFirst = true :=
    (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff keys tracked.highestFirst).mpr
      (descending.imp (by
        intro left right higher
        rw [occurrence_comparison_gt_of_atomic_priority source (source.aromaticCanonicalFinalOccurrence carrierFuel center)
          view (2 * (carrierFuel + 1)) frame real keys keysComputed left right higher]))
  have safeComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked := by
    simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawComputed, coherent]
  exact ⟨keys, tracked, keysComputed, safeComputed, perm, descending, zero⟩


theorem actual_local_priority_alignment (raw : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
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
    exists_local_safe_order raw source converted carrierFuel center domain four view
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

theorem actual_local_descriptor_transport (raw : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement raw source)
    (written : raw.WrittenNeighborExact) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
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
    actual_local_priority_alignment raw source agreement.1 carrierFuel center domain four
      view state runtimeFuel
  obtain ⟨slots, slotsComputed⟩ :=
    converted_written_alignment_exists raw source agreement.1 carrierFuel center domain written four
  have matching := findSlotAlignment?_sound _ _ _ slotsComputed
  let positions := tracked.highestFirst.map (fun slot => slots.getD slot.val 0)
  let descriptor := writtenFramePriorityDescriptor parity slots tracked.highestFirst
  have writtenFour := actual_written_four raw center.1.val domain written four
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
    actual_runtime_frame raw center.1.val domain written four, runtimeComputed, positionsComputed, rfl,
    descriptorComputed, constitutionParserRichDescriptor?_sound raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (.chiral descriptor) descriptorComputed, runtimeZero⟩

namespace DisconnectedAlkene

abbrev raw := LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.raw
abbrev source := LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.source
abbrev center := LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.center

/-- The SAME actual converted seven-atom source retains its genuine ordinary disconnected C=C. -/
theorem actual_not_global_noDouble : ¬ source.NoAromaticCanonicalOrdinaryDoubleBond :=
  LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_not_global_noDouble

/-- Closed local keyframe construction at ANY carrier depth and ANY own auxiliary view. -/
theorem actual_local_keyFrame (carrierFuel : Nat)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
      (finalOccurrenceRoots source carrierFuel center) = some keys :=
  exists_local_keyFrame raw source
    LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_conversion carrierFuel center
    LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_domain
    LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_four view

theorem actual_parser_R (carrierFuel : Nat)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    constitutionParserRichDescriptor? raw source LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_annotation_agreement LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_written_exact
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) = some (.chiral RS.R) ∧
    ConstitutionParserRichDescriptorMeaning raw source LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_annotation_agreement LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_written_exact
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) (.chiral RS.R) := by
  obtain ⟨runtimeResult, positions, descriptor, _frame, runtimeComputed, positionsComputed,
      formula, parserComputed, parserMeaning, _zero⟩ :=
    actual_local_descriptor_transport raw source LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_annotation_agreement LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_written_exact
      carrierFuel center LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_domain LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_four
      { AtomSpec.aliphatic .C with tetrahedral? := some .clockwise }
      (by rfl) .clockwise (by rfl) view [] 0
  have runtimeEqual : runtimeResult = (LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actualSorted, 0) :=
    Option.some.inj (runtimeComputed.symm.trans LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_runtime_sort)
  subst runtimeResult
  have positionsEqual : positions = [3, 2, 1, 0] :=
    Option.some.inj (positionsComputed.symm.trans LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery.DisconnectedAlkene.actual_runtime_positions)
  subst positions
  have descriptorEqual : descriptor = RS.R := formula.trans (by decide +kernel)
  subst descriptor
  exact ⟨parserComputed, parserMeaning⟩


end DisconnectedAlkene

end TetraStereo.UniversalProof.NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery
