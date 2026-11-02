import TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
import TetraStereo.OneCenter.AuthoritativeSingleWedgeZeroCarrierReadiness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge

















theorem local_final_cursor_not_rule3_edge (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center) :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge cursor.occurrence.1.node := by
  obtain ⟨neighbor, member, nodeEq⟩ :=
    converted_final_cursor_real_root raw source converted carrierFuel center domain cursor present
  rintro ⟨_real, current, parent, currentEq, parentEq, ordinary⟩
  have currentSame : current = neighbor := by
    simpa [nodeEq, OfficialCIPNode.rootFromEdge] using currentEq.symm
  have parentSame : parent = center.1 := by
    simpa [nodeEq, OfficialCIPNode.parent?, OfficialCIPNode.rootFromEdge] using parentEq.symm
  subst current
  subst parent
  have orderTwo := ordinary.2
  rw [converted_canonical_bond_order raw source converted center.1 domain neighbor.val,
    if_pos member] at orderTwo
  omega

theorem local_final_cursor_structural_outcome (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ finalOccurrenceRoots source carrierFuel center) :
    source.aromaticCanonicalRule3SpatialNode? cursor.occurrence.1.node = some none :=
  source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge _
    (local_final_cursor_not_rule3_edge raw source converted carrierFuel center domain cursor present)

theorem local_zero_raw_key (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor 0)
    (present : cursor ∈ finalOccurrenceRoots source 0 center) (ruleFuel : Nat) :
    source.buildAromaticCanonicalUncancelledRule3SpatialKey? ruleFuel cursor =
      some (zeroCarrierLeafRule3Key source cursor) := by
  have children := zero_carrier_final_cursor_children_nil source center cursor present
  have observed := local_final_cursor_structural_outcome raw source converted 0 center domain cursor present
  cases ruleFuel <;> simp [buildAromaticCanonicalUncancelledRule3SpatialKey?, children,
    observed, zeroCarrierLeafRule3Key, aromaticCanonicalRule3RootObservations,
    aromaticCanonicalRule3RootPriorities]

theorem local_zero_except_key (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor 0)
    (present : cursor ∈ finalOccurrenceRoots source 0 center)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) (ruleFuel : Nat) :
    source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded ruleFuel cursor =
      some (zeroCarrierLeafRule3Key source cursor) := by
  have children := zero_carrier_final_cursor_children_nil source center cursor present
  have observed := local_final_cursor_structural_outcome raw source converted 0 center domain cursor present
  have exceptObserved : source.aromaticCanonicalRule3SpatialNodeExcept?
      excluded cursor.occurrence.1.node = some none := by
    simp [aromaticCanonicalRule3SpatialNodeExcept?, observed]
  cases ruleFuel <;> simp [buildAromaticCanonicalRule3SpatialKeyExcept?, children,
    exceptObserved, zeroCarrierLeafRule3Key, aromaticCanonicalRule3RootObservations,
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

theorem local_zero_rule3_frame (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (ruleFuel : Nat) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? ruleFuel
      (finalOccurrenceRoots source 0 center) = some (zeroCarrierRule3Frame source center) := by
  have rawComputed : (finalOccurrenceRoots source 0 center).mapM
      (source.buildAromaticCanonicalUncancelledRule3SpatialKey? ruleFuel) =
      some (zeroCarrierRule3Keys source center) :=
    mapM_eq_some_map_of_member_eq _ _ _ (fun cursor present =>
      local_zero_raw_key raw source converted center domain cursor present ruleFuel)
  have exceptComputed : (finalOccurrenceRoots source 0 center).mapM
      (source.buildAromaticCanonicalRule3SpatialKeyExcept? [] ruleFuel) =
      some (zeroCarrierRule3Keys source center) :=
    mapM_eq_some_map_of_member_eq _ _ _ (fun cursor present =>
      local_zero_except_key raw source converted center domain cursor present [] ruleFuel)
  have resolutionComputed : source.aromaticCanonicalRule3PhysicalTopologyResolution?
      (zeroCarrierRule3Keys source center) = some .ordinary := by
    simp [aromaticCanonicalRule3PhysicalTopologyResolution?, zero_carrier_rule3_coupled_pairs_nil]
  have excludedEmpty : source.aromaticCanonicalRule3ExcludedPhysicalUnits
      (zeroCarrierRule3Keys source center) .ordinary = [] := by
    simp [aromaticCanonicalRule3ExcludedPhysicalUnits, aromaticCanonicalRule3SharedPhysicalUnits,
      zero_carrier_rule3_frame_units_nil]
  simp [buildAromaticCanonicalRule3CanonicalKeyFrame?, rawComputed, resolutionComputed,
    excludedEmpty, exceptComputed, zeroCarrierRule3Frame]

private theorem exists_zero_mapM_compound45_of_valid
    (source : AuthoritativeChemicalInput) (target : source.AromaticCanonicalOccurrence 0)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor 0),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45Key? target view 2) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ := source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
        target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ := exists_zero_mapM_compound45_of_valid source target view cursors
        (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [List.mapM_cons, keyComputed, keysComputed]⟩

theorem exists_local_zero_keyFrame (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2
      (finalOccurrenceRoots source 0 center) = some keys := by
  let rule3Frame := zeroCarrierRule3Frame source center
  have rule3Computed := local_zero_rule3_frame raw source converted center domain 2
  have rootLength := (actual_returned_four_roots raw source converted 0 center domain four).2
  have rule3Length : rule3Frame.keys.length = 4 := by
    simpa [rule3Frame, zeroCarrierRule3Frame, zeroCarrierRule3Keys] using rootLength
  obtain ⟨rule45Keys, rule45Computed⟩ := exists_zero_mapM_compound45_of_valid source
    (source.aromaticCanonicalFinalOccurrence 0 center) view (finalOccurrenceRoots source 0 center)
    (finalOccurrenceRoots_valid source 0 center)
  have rule45Length : rule45Keys.length = 4 :=
    (mapM_length_eq_of_eq_some (source.buildAromaticCanonicalRerootCompoundRule45Key?
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2)
      (finalOccurrenceRoots source 0 center) rule45Keys rule45Computed).trans rootLength
  refine ⟨{ rule3Frame, rule3Length, rule45Keys, rule45Length }, ?_⟩
  simp [buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?, rule3Frame,
    rule3Computed, rule3Length, rule45Computed, rule45Length]

theorem exists_local_zero_safe_order (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ∃ keys tracked,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2
        (actualFrame raw source converted 0 center domain four).roots = some keys ∧
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        occurrenceAtomicPriority source (actualFrame raw source converted 0 center domain four) right <
        occurrenceAtomicPriority source (actualFrame raw source converted 0 center domain four) left) ∧
      tracked.pseudoComparisons = 0 := by
  let frame := actualFrame raw source converted 0 center domain four
  have real := actual_roots_real raw source converted 0 center domain four
  have injective := actual_priority_injective raw source converted 0 center domain four
  obtain ⟨keys, keysComputed⟩ := exists_local_zero_keyFrame raw source converted center domain four view
  obtain ⟨tracked, rawComputed, perm, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
      (occurrenceAtomicPriority source frame) injective
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys)
      (occurrence_callback_eq_strictRank_of_ne source (source.aromaticCanonicalFinalOccurrence 0 center)
        view 2 frame real injective keys keysComputed)
  have coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keys tracked.highestFirst = true :=
    (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff keys tracked.highestFirst).mpr
      (descending.imp (by
        intro left right higher
        rw [occurrence_comparison_gt_of_atomic_priority source (source.aromaticCanonicalFinalOccurrence 0 center)
          view 2 frame real keys keysComputed left right higher]))
  have safeComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked := by
    simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawComputed, coherent]
  exact ⟨keys, tracked, keysComputed, safeComputed, perm, descending, zero⟩

/-! Actual runtime/source sorted-ID and parser parity transport, with the new locally derived
old production frame. Only carrier zero is claimed; every actual auxiliary view remains free. -/

theorem actual_local_zero_priority_alignment (raw : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ keys tracked runtimeResult,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (source.aromaticCanonicalFinalOccurrence 0 center) view
        2
        (actualFrame raw source converted 0 center domain four).roots = some keys ∧
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
        (generatedRuntimeRoots raw center.1.val) = some runtimeResult ∧
      tracked.highestFirst.map (slotAtomID raw source converted 0 center domain four) =
        runtimeResult.1.map (fun cursor => cursor.node.atom) ∧
      tracked.pseudoComparisons = 0 ∧ runtimeResult.2 = 0 := by
  let frame := actualFrame raw source converted 0 center domain four
  obtain ⟨keys, tracked, keyComputed, safeComputed, sourcePerm, sourceSorted, sourceZero⟩ :=
    exists_local_zero_safe_order raw source converted center domain four view
  obtain ⟨runtimeResult, runtimeComputed, runtimePerm, runtimeSorted, runtimeZero⟩ :=
    generated_runtime_sort raw center.1.val runtimeFuel domain.leaf state
  have sourceIDs : (tracked.highestFirst.map
      (slotAtomID raw source converted 0 center domain four)).Perm
        (recordNeighbors raw center.1.val) :=
    (sourcePerm.map (slotAtomID raw source converted 0 center domain four)).trans
      (actual_slot_ids_perm raw source converted 0 center domain four)
  have runtimeIDs : (runtimeResult.1.map (fun cursor => cursor.node.atom)).Perm
      (recordNeighbors raw center.1.val) := by
    have transported := runtimePerm.map (fun cursor => cursor.node.atom)
    rw [generatedRuntimeRoots_eq raw center.1.val domain.leaf] at transported
    simpa only [List.map_map, Function.comp_def, canonicalRoot, List.map_id'] using transported
  have sourceIDsorted : (tracked.highestFirst.map
      (slotAtomID raw source converted 0 center domain four)).Pairwise
        (fun a b => raw.atomZAt b < raw.atomZAt a) := by
    apply List.pairwise_map.mpr
    apply sourceSorted.imp
    intro left right higher
    simpa only [frame,
      actual_priority_eq_raw_Z raw source converted 0 center domain four left,
      actual_priority_eq_raw_Z raw source converted 0 center domain four right] using higher
  have runtimeIDsorted : (runtimeResult.1.map (fun cursor => cursor.node.atom)).Pairwise
      (fun a b => raw.atomZAt b < raw.atomZAt a) :=
    List.pairwise_map.mpr runtimeSorted
  exact ⟨keys, tracked, runtimeResult, keyComputed, safeComputed, runtimeComputed,
    atom_id_order_unique raw _ _ sourceIDsorted runtimeIDsorted (sourceIDs.trans runtimeIDs.symm),
    sourceZero, runtimeZero⟩

theorem actual_local_zero_descriptor_transport (raw : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement raw source)
    (written : raw.WrittenNeighborExact)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ runtimeResult positions descriptor,
      occurrenceLigandFrame? raw (canonicalCenterRoot center.1.val) =
        some (generatedRuntimeRoots raw center.1.val) ∧
      sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
        (generatedRuntimeRoots raw center.1.val) = some runtimeResult ∧
      runtimePriorityPositions? raw center.1.val runtimeResult.1 = some positions ∧
      descriptor = RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions) ∧
      constitutionParserRichDescriptor? raw source agreement written
        (source.aromaticCanonicalFinalOccurrence 0 center) view
        2 = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement written
        (source.aromaticCanonicalFinalOccurrence 0 center) view
        2 (.chiral descriptor) ∧ runtimeResult.2 = 0 := by
  classical
  obtain ⟨keys, tracked, runtimeResult, keyComputed, safeComputed, runtimeComputed, sameIDs,
      sourceZero, runtimeZero⟩ :=
    actual_local_zero_priority_alignment raw source agreement.1 center domain four
      view state runtimeFuel
  obtain ⟨slots, slotsComputed⟩ :=
    converted_written_alignment_exists raw source agreement.1 0 center domain written four
  have matching := findSlotAlignment?_sound _ _ _ slotsComputed
  let positions := tracked.highestFirst.map (fun slot => slots.getD slot.val 0)
  let descriptor := SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.writtenFramePriorityDescriptor
    parity slots tracked.highestFirst
  have writtenFour := actual_written_four raw center.1.val domain written four
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center.1.val writtenFour
  have positionsComputed : runtimePriorityPositions? raw center.1.val runtimeResult.1 = some positions := by
    unfold runtimePriorityPositions?
    rw [ligands]
    change runtimeResult.1.mapM
      ((writtenSlot? (raw.writtenNeighbors center.1.val)) ∘ (fun cursor => cursor.node.atom)) = _
    rw [← List.mapM_map, ← sameIDs]
    exact actual_priority_positions raw source agreement.1 0 center domain four
      slots matching tracked.highestFirst
  change source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    (source.aromaticCanonicalFinalOccurrence 0 center) view
    2 (finalOccurrenceRoots source 0 center) = some keys at keyComputed
  let evidence : ParserRichPriorityEvidence source 0 :=
    { slots := slots, keys := keys, tracked := tracked, writtenParity := parity, raw := descriptor }
  have evidenceComputed : constitutionParserRichPriorityEvidence? raw source agreement written
      (source.aromaticCanonicalFinalOccurrence 0 center) view
      2 = some evidence := by
    have slotsForRoots : findSlotAlignment? (raw.writtenNeighbors center.1.val)
        ((finalOccurrenceRoots source 0 center).map (cursorAtomID source)) = some slots :=
      slotsComputed
    simp [constitutionParserRichPriorityEvidence?, occurrenceTetrahedralCenter?_final,
      parserIndexViaConversion_val, rawWrittenLigandFrame, atomObserved, parityObserved,
      finalOccurrenceRoots_are_returned, occurrenceRootIDs,
      slotsForRoots, keyComputed, safeComputed, evidence]
    rfl
  have descriptorComputed : constitutionParserRichDescriptor? raw source agreement written
      (source.aromaticCanonicalFinalOccurrence 0 center) view
      2 = some (.chiral descriptor) := by
    simp [constitutionParserRichDescriptor?, evidenceComputed, evidence, sourceZero,
      classifyTetrahedralRSPseudo]
  exact ⟨runtimeResult, positions, descriptor,
    actual_runtime_frame raw center.1.val domain written four, runtimeComputed, positionsComputed, rfl,
    descriptorComputed, constitutionParserRichDescriptor?_sound raw source agreement written
      (source.aromaticCanonicalFinalOccurrence 0 center) view
      2 (.chiral descriptor) descriptorComputed, runtimeZero⟩

namespace DisconnectedAlkene

/-- Independent actual raw records: a tagged four-distinct-Z star and a separate ordinary C=C. -/
def raw : RawMolecule :=
  { atoms := [{ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise },
      AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .Br,
      AtomSpec.aliphatic .I, AtomSpec.aliphatic .C, AtomSpec.aliphatic .C]
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩,
      ⟨0, 4, .single⟩, ⟨5, 6, .double⟩] }

def source : AuthoritativeChemicalInput :=
  raw.toAuthoritativeChemicalInput?.getD { molecule := { atoms := [], interactions := [] } }

def centerAtom : source.AromaticCanonicalAtom := ⟨0, by decide +kernel⟩

def center : source.AromaticCanonicalTetrahedralCenter :=
  ⟨centerAtom, (mem_aromaticCanonicalTetrahedralCenterSet_iff _ _).mpr ⟨by
    unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
    decide +kernel, by
      have neighbors : source.aromaticCanonicalNeighborFinset centerAtom =
          {⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩,
           ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩} := by
        ext neighbor
        rw [mem_aromaticCanonicalNeighborFinset_iff]
        fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel
      rw [neighbors]
      decide +kernel⟩⟩

def alkeneLeft : source.AromaticCanonicalAtom := ⟨5, by decide +kernel⟩
def alkeneRight : source.AromaticCanonicalAtom := ⟨6, by decide +kernel⟩

theorem actual_well_formed : raw.WellFormed := by
  rw [wellFormed_iff_all_bondEndpointsOK]
  decide +kernel

theorem actual_conversion : raw.toSemanticMolecule? = some source.molecule := by
  decide +kernel

theorem actual_annotation_agreement : RawAnnotationAgreement raw source := by
  apply (rawAnnotationAgreement_iff raw source).mpr
  exact ⟨actual_conversion, by decide +kernel⟩

theorem actual_written_exact : raw.WrittenNeighborExact :=
  raw.writtenNeighborExact?_eq_true_iff.mp (by decide +kernel)

theorem actual_domain : SingleLeafDomain raw center.1.val := by
  constructor
  · exact ⟨actual_well_formed, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · intro bond retained incident
    change bond ∈ [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩,
      ⟨0, 4, .single⟩, ⟨5, 6, .double⟩] at retained
    simp at retained
    rcases retained with rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · change 5 = 0 ∨ 6 = 0 at incident
      omega

theorem actual_four : (recordNeighbors raw center.1.val).length = 4 := by
  decide +kernel

theorem actual_ordinary_double : source.AromaticCanonicalOrdinaryDoubleBond alkeneLeft alkeneRight := by
  unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
  decide +kernel

/-- This source genuinely fails the restriction in Automateds156/157; no policy substitution occurs. -/
theorem actual_not_global_noDouble : ¬ source.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro absent
  exact absent alkeneLeft alkeneRight actual_ordinary_double

theorem actual_local_keyFrame
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2
      (finalOccurrenceRoots source 0 center) = some keys :=
  exists_local_zero_keyFrame raw source actual_conversion center actual_domain actual_four view

/-- Actual authoritative runtime cursor order, including the original previous-root pointer. -/
def actualSorted : List CanonicalRerootCursor :=
  [4, 3, 2, 1].map fun atom =>
    { node := canonicalRoot 0 atom, previous? := some (canonicalCenterRoot 0) }

theorem actual_runtime_sort : sortOccurrencesTrackedAuthoritative? raw [] 0
    (generatedRuntimeRoots raw 0) = some (actualSorted, 0) := by
  rw [generatedRuntimeRoots_eq raw 0 actual_domain.leaf]
  decide +kernel

theorem actual_runtime_positions : runtimePriorityPositions? raw 0 actualSorted = some [3, 2, 1, 0] := by
  decide +kernel

/-- Actual old parser assignment and its OWN independent meaning on a source with ordinary C=C.
Its R label is derived from the actual runtime order and the raw clockwise written annotation. -/
theorem actual_parser_R
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    constitutionParserRichDescriptor? raw source actual_annotation_agreement actual_written_exact
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2 = some (.chiral RS.R) ∧
    ConstitutionParserRichDescriptorMeaning raw source actual_annotation_agreement actual_written_exact
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2 (.chiral RS.R) := by
  obtain ⟨runtimeResult, positions, descriptor, _frame, runtimeComputed, positionsComputed,
      formula, parserComputed, parserMeaning, _zero⟩ :=
    actual_local_zero_descriptor_transport raw source actual_annotation_agreement actual_written_exact
      center actual_domain actual_four
      { AtomSpec.aliphatic .C with tetrahedral? := some .clockwise }
      (by rfl) .clockwise (by rfl) view [] 0
  have runtimeEqual : runtimeResult = (actualSorted, 0) :=
    Option.some.inj (runtimeComputed.symm.trans actual_runtime_sort)
  subst runtimeResult
  have positionsEqual : positions = [3, 2, 1, 0] :=
    Option.some.inj (positionsComputed.symm.trans actual_runtime_positions)
  subst positions
  have descriptorEqual : descriptor = RS.R := formula.trans (by decide +kernel)
  subst descriptor
  exact ⟨parserComputed, parserMeaning⟩

end DisconnectedAlkene

end TetraStereo.UniversalProof.LocalSourceRule3DomainRecoveryProofs.LocalSourceRule3DomainRecovery
