import TetraStereo.UniversalProof.SourceNativePlanarTetrahedralKeyFrameProofs.SourceNativePlanarTetrahedralKeyFrame
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-!
# Observation conservation in actual returned planar keys

The generic recursive compiler retains positive root results and positive child results through
its actual child compilation, sorting and observation merge.  Addresses may be prefixed, but the
node result and hence its physical identity are preserved.  The closed NEW72 source consequently
has four actually compiled raw keys: the first retains the real C5 `seqcis` result, while the three
halogen keys have no observations or physical unit identities.  No desired key or successful
execution is supplied to this closed witness.

TECHNICAL_PROOF_REQUIRED: physical-topology readiness and the closed excluded second-pass frame.
HUMAN_REVIEW_REQUIRED: the planar convention and scientific interpretation of this fixture.
EXTERNAL_EVIDENCE_REQUIRED: scientific source adoption.  This unit proves uncancelled raw-key
conservation, not complete production or adoption.
-/

namespace TetraStereo.UniversalProof.SourceNativePlanarKeyObservationConservationProofs.SourceNativePlanarKeyObservationConservation

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralKeyFrameProofs.SourceNativePlanarTetrahedralKeyFrame
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource
  (firstCursor roots actual_carbon_child_seqcis cisNodeResult)

/-- Address-independent occurrence of an actual node result in a returned key. -/
def HasObservation (input : AuthoritativeChemicalInput)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (result : input.AromaticCanonicalRule3SpatialNodeResult) : Prop :=
  ∃ layer ∈ key.observations, ∃ address, (address, result) ∈ layer

theorem observation_physical_id_mem (input : AuthoritativeChemicalInput)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (result : input.AromaticCanonicalRule3SpatialNodeResult)
    (observed : HasObservation input key result) :
    result.physicalUnitId ∈ input.aromaticCanonicalRule3PhysicalUnitIds key := by
  obtain ⟨layer, present, address, entry⟩ := observed
  exact (input.mem_aromaticCanonicalRule3PhysicalUnitIds_iff key result.physicalUnitId).mpr
    ⟨layer, present, (address, result), entry, rfl⟩

private theorem fold_max_ge_initial (input : AuthoritativeChemicalInput)
    (keys : List input.AromaticCanonicalUncancelledRule3SpatialKey) (initial : Nat) :
    initial ≤ keys.foldl (fun n key => max n key.observations.length) initial := by
  induction keys generalizing initial with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      exact (Nat.le_max_left _ _).trans (ih _)

theorem observation_length_le_child_count (input : AuthoritativeChemicalInput)
    (keys : List input.AromaticCanonicalUncancelledRule3SpatialKey)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey) (present : key ∈ keys) :
    key.observations.length ≤ aromaticCanonicalRule3ObservationChildLayerCount keys := by
  have bound : ∀ (values : List input.AromaticCanonicalUncancelledRule3SpatialKey)
      (initial : Nat) (entry : input.AromaticCanonicalUncancelledRule3SpatialKey),
      entry ∈ values → entry.observations.length ≤
        values.foldl (fun n child => max n child.observations.length) initial := by
    intro values
    induction values with
    | nil => intro initial entry absent; simp at absent
    | cons head tail ih =>
        intro initial entry present
        rcases List.mem_cons.mp present with same | rest
        · subst entry
          exact (Nat.le_max_right _ _).trans (fold_max_ge_initial input tail _)
        · exact ih _ _ rest
  exact bound keys 0 key present

/-- Merging prefixed child layers preserves the node result, independently of its address. -/
theorem merge_preserves_observation (input : AuthoritativeChemicalInput)
    (keys : List input.AromaticCanonicalUncancelledRule3SpatialKey)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (result : input.AromaticCanonicalRule3SpatialNodeResult)
    (present : key ∈ keys) (observed : HasObservation input key result) :
    ∃ layer ∈ mergeAromaticCanonicalRule3ObservationChildren keys,
      ∃ address, (address, result) ∈ layer := by
  obtain ⟨layer, layerMem, address, entryMem⟩ := observed
  obtain ⟨depth, depthLt, layerEq⟩ := List.mem_iff_getElem.mp layerMem
  obtain ⟨index, indexLt, keyEq⟩ := List.mem_iff_getElem.mp present
  have depthCount : depth < aromaticCanonicalRule3ObservationChildLayerCount keys :=
    depthLt.trans_le (observation_length_le_child_count input keys key present)
  have zipped : (key, index) ∈ keys.zipIdx := by
    apply List.mem_iff_getElem.mpr
    refine ⟨index, by simpa using indexLt, ?_⟩
    simp [List.getElem_zipIdx, keyEq]
  have getLayer : key.observations.getD depth [] = layer := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem depthLt]
    exact layerEq
  refine ⟨_, List.mem_map.mpr ⟨depth, List.mem_range.mpr depthCount, rfl⟩,
    index :: address, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(key, index), zipped, ?_⟩
  change (index :: address, result) ∈
    OfficialRuleMajorKey.prefixLayer index (key.observations.getD depth [])
  rw [getLayer]
  exact List.mem_map.mpr ⟨(address, result), entryMem, rfl⟩

private theorem child_derivation (input : AuthoritativeChemicalInput)
    {carrierFuel fuel : Nat}
    {meaning : OfficialCIPNode input.AromaticCanonicalAtom →
      Option input.AromaticCanonicalRule3SpatialNodeResult → Prop}
    {cursors : List (input.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List input.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : input.CanonicalAromaticCanonicalRule3SpatialKeyWithList meaning fuel cursors keys)
    (cursor : input.AromaticCanonicalRerootCursor carrierFuel) (present : cursor ∈ cursors) :
    ∃ key ∈ keys, input.CanonicalAromaticCanonicalRule3SpatialKeyWith meaning fuel cursor key :=
  match derived with
  | .nil _ => by simp at present
  | .cons headDerived tailDerived => by
      rcases List.mem_cons.mp present with same | rest
      · subst cursor
        exact ⟨_, List.mem_cons_self, headDerived⟩
      · obtain ⟨found, foundMem, foundDerived⟩ := child_derivation input tailDerived cursor rest
        exact ⟨found, List.mem_cons_of_mem _ foundMem, foundDerived⟩

/-- A positive root reading is retained by every successful generic raw key. -/
theorem root_positive_conserved (input : AuthoritativeChemicalInput)
    {carrierFuel fuel : Nat}
    (observe : OfficialCIPNode input.AromaticCanonicalAtom →
      Option (Option input.AromaticCanonicalRule3SpatialNodeResult))
    (cursor : input.AromaticCanonicalRerootCursor carrierFuel)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (result : input.AromaticCanonicalRule3SpatialNodeResult)
    (computed : input.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel cursor = some key)
    (positive : observe cursor.occurrence.1.node = some (some result)) :
    HasObservation input key result := by
  have derived := (input.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    observe (fun node outcome => observe node = some outcome) (fun _ _ => Iff.rfl)
    fuel cursor key).mp computed
  cases derived with
  | terminal frame empty observed =>
      have same := Option.some.inj (observed.symm.trans positive)
      cases same
      exact ⟨[([], result)], by simp [aromaticCanonicalRule3RootObservations], [], by simp⟩
  | branch frame nonempty observed childDerivations ranking =>
      have same := Option.some.inj (observed.symm.trans positive)
      cases same
      exact ⟨[([], result)], by simp [aromaticCanonicalRule3RootObservations], [], by simp⟩

theorem root_positive_physical_id_conserved (input : AuthoritativeChemicalInput)
    {carrierFuel fuel : Nat}
    (observe : OfficialCIPNode input.AromaticCanonicalAtom →
      Option (Option input.AromaticCanonicalRule3SpatialNodeResult))
    (cursor : input.AromaticCanonicalRerootCursor carrierFuel)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (result : input.AromaticCanonicalRule3SpatialNodeResult)
    (computed : input.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel cursor = some key)
    (positive : observe cursor.occurrence.1.node = some (some result)) :
    result.physicalUnitId ∈ input.aromaticCanonicalRule3PhysicalUnitIds key :=
  observation_physical_id_mem input key result
    (root_positive_conserved input observe cursor key result computed positive)

/-- An actually compiled positive child survives the actual child sorting and merge. -/
theorem child_positive_conserved (input : AuthoritativeChemicalInput)
    {carrierFuel fuel : Nat}
    (observe : OfficialCIPNode input.AromaticCanonicalAtom →
      Option (Option input.AromaticCanonicalRule3SpatialNodeResult))
    (cursor child : input.AromaticCanonicalRerootCursor carrierFuel)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (result : input.AromaticCanonicalRule3SpatialNodeResult)
    (computed : input.buildAromaticCanonicalRule3SpatialKeyWith? observe (fuel + 1) cursor = some key)
    (present : child ∈ input.aromaticCanonicalRerootChildren cursor)
    (positive : observe child.occurrence.1.node = some (some result)) :
    HasObservation input key result := by
  have derived := (input.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    observe (fun node outcome => observe node = some outcome) (fun _ _ => Iff.rfl)
    (fuel + 1) cursor key).mp computed
  cases derived with
  | @terminal _ _ children observation frame empty observed =>
      have childrenEq : input.aromaticCanonicalRerootChildren cursor = children := by
        simpa [aromaticCanonicalRerootChildren?] using
          (input.aromaticCanonicalRerootChildren?_eq_some_iff cursor children).mpr frame
      rw [childrenEq, empty] at present
      simp at present
  | @branch _ _ children observation childKeys sorted frame nonempty observed derivations ranking =>
      have childrenEq : input.aromaticCanonicalRerootChildren cursor = children := by
        simpa [aromaticCanonicalRerootChildren?] using
          (input.aromaticCanonicalRerootChildren?_eq_some_iff cursor children).mpr frame
      rw [childrenEq] at present
      obtain ⟨childKey, childKeyMem, childDerived⟩ :=
        child_derivation input derivations child present
      have childComputed := (input.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
        observe (fun node outcome => observe node = some outcome) (fun _ _ => Iff.rfl)
        _ child childKey).mpr childDerived
      have sortedEq := (input.sortAromaticCanonicalUncancelledRule3SpatialKeys_eq_iff_canonical
        childKeys sorted).mpr ranking
      have sortedMem : childKey ∈ sorted := by
        rw [← sortedEq]
        exact (sortAromaticCanonicalUncancelledRule3SpatialKeys_perm
          input.compareAromaticCanonicalUncancelledRule3SpatialKeys childKeys).mem_iff.mpr childKeyMem
      obtain ⟨layer, layerMem, address, entry⟩ := merge_preserves_observation input sorted childKey
        result sortedMem (root_positive_conserved input observe child childKey result childComputed positive)
      exact ⟨layer, List.mem_append_right _ layerMem, address, entry⟩

theorem child_positive_physical_id_conserved (input : AuthoritativeChemicalInput)
    {carrierFuel fuel : Nat}
    (observe : OfficialCIPNode input.AromaticCanonicalAtom →
      Option (Option input.AromaticCanonicalRule3SpatialNodeResult))
    (cursor child : input.AromaticCanonicalRerootCursor carrierFuel)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (result : input.AromaticCanonicalRule3SpatialNodeResult)
    (computed : input.buildAromaticCanonicalRule3SpatialKeyWith? observe (fuel + 1) cursor = some key)
    (present : child ∈ input.aromaticCanonicalRerootChildren cursor)
    (positive : observe child.occurrence.1.node = some (some result)) :
    result.physicalUnitId ∈ input.aromaticCanonicalRule3PhysicalUnitIds key :=
  observation_physical_id_mem input key result
    (child_positive_conserved input observe cursor child key result computed present positive)

theorem terminal_negative_key_neutral (input : AuthoritativeChemicalInput)
    {carrierFuel fuel : Nat}
    (observe : OfficialCIPNode input.AromaticCanonicalAtom →
      Option (Option input.AromaticCanonicalRule3SpatialNodeResult))
    (cursor : input.AromaticCanonicalRerootCursor carrierFuel)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : input.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel cursor = some key)
    (terminal : input.aromaticCanonicalRerootChildren cursor = [])
    (negative : observe cursor.occurrence.1.node = some none) :
    key.observations = [] ∧ input.aromaticCanonicalRule3PhysicalUnitIds key = [] := by
  cases fuel <;>
    simp [buildAromaticCanonicalRule3SpatialKeyWith?, terminal, negative] at computed <;>
    subst key <;>
    simp [aromaticCanonicalRule3RootObservations, aromaticCanonicalRule3PhysicalUnitIds]

theorem no_observations_no_physical_ids (input : AuthoritativeChemicalInput)
    (key : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (empty : key.observations = []) : input.aromaticCanonicalRule3PhysicalUnitIds key = [] := by
  simp [aromaticCanonicalRule3PhysicalUnitIds, empty]

abbrev source := TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.source
local instance : NeZero source.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

theorem actual_halogen_children_empty :
    source.aromaticCanonicalRerootChildren (firstCursor 1) = [] ∧
    source.aromaticCanonicalRerootChildren (firstCursor 2) = [] ∧
    source.aromaticCanonicalRerootChildren (firstCursor 3) = [] := by
  have empty (slot : Fin 4) (notCarbon : slot ≠ 0) :
      source.aromaticCanonicalRerootChildren (firstCursor slot) = [] := by
    apply List.eq_nil_of_map_eq_nil
      (f := fun cursor : source.AromaticCanonicalRerootCursor 1 => cursor.occurrence.1)
    rw [(source.aromaticCanonicalRerootChildren_sound (firstCursor slot)).1]
    fin_cases slot <;> first | contradiction | decide +kernel
  exact ⟨empty 1 (by decide), empty 2 (by decide), empty 3 (by decide)⟩

theorem actual_c1_key_observation
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : source.buildAromaticCanonicalRule3SpatialKeyWith? planarObserver.observe 4
      (firstCursor 0) = some key) :
    HasObservation source key cisNodeResult := by
  obtain ⟨child, present, _, _, resolved⟩ := actual_carbon_child_seqcis
  exact child_positive_conserved source planarObserver.observe (firstCursor 0) child key
    cisNodeResult computed present resolved

theorem actual_c1_key_physical_id
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : source.buildAromaticCanonicalRule3SpatialKeyWith? planarObserver.observe 4
      (firstCursor 0) = some key) :
    source.aromaticCanonicalRule3PhysicalUnitId 1 5 ∈
      source.aromaticCanonicalRule3PhysicalUnitIds key :=
  observation_physical_id_mem source key cisNodeResult (actual_c1_key_observation key computed)

/-- Closed actual four-key execution with retained `seqcis` and three neutral halogen keys. -/
theorem actual_four_raw_keys_conserve_seqcis :
    ∃ carbon fluorine bromine iodine : source.AromaticCanonicalUncancelledRule3SpatialKey,
      roots.mapM (source.buildAromaticCanonicalRule3SpatialKeyWith? planarObserver.observe 4) =
        some [carbon, fluorine, bromine, iodine] ∧
      HasObservation source carbon cisNodeResult ∧
      source.aromaticCanonicalRule3PhysicalUnitId 1 5 ∈
        source.aromaticCanonicalRule3PhysicalUnitIds carbon ∧
      fluorine.observations = [] ∧ bromine.observations = [] ∧ iodine.observations = [] ∧
      source.aromaticCanonicalRule3PhysicalUnitIds fluorine = [] ∧
      source.aromaticCanonicalRule3PhysicalUnitIds bromine = [] ∧
      source.aromaticCanonicalRule3PhysicalUnitIds iodine = [] := by
  obtain ⟨keys, computed, meaning, _⟩ := actual_four_planar_raw_keys
  change source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
    (CanonicalAromaticCanonicalPlanarRule3NodeOutcome source) 4
    [firstCursor 0, firstCursor 1, firstCursor 2, firstCursor 3] keys at meaning
  cases meaning with
  | cons carbonMeaning tail => cases tail with
    | cons fluorineMeaning tail => cases tail with
      | cons bromineMeaning tail => cases tail with
        | cons iodineMeaning tail => cases tail with
          | nil =>
            have toComputed {cursor : source.AromaticCanonicalRerootCursor 1}
                {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
                (derived : source.CanonicalAromaticCanonicalRule3SpatialKeyWith
                  (CanonicalAromaticCanonicalPlanarRule3NodeOutcome source) 4 cursor key) :=
              (source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                planarObserver.observe (CanonicalAromaticCanonicalPlanarRule3NodeOutcome source)
                planarObserver.nodeExact 4 cursor key).mpr derived
            have carbonComputed := toComputed carbonMeaning
            have fluorineNeutral := terminal_negative_key_neutral source planarObserver.observe
              (firstCursor 1) _ (toComputed fluorineMeaning) actual_halogen_children_empty.1
              terminal_root_readers.1
            have bromineNeutral := terminal_negative_key_neutral source planarObserver.observe
              (firstCursor 2) _ (toComputed bromineMeaning) actual_halogen_children_empty.2.1
              terminal_root_readers.2.1
            have iodineNeutral := terminal_negative_key_neutral source planarObserver.observe
              (firstCursor 3) _ (toComputed iodineMeaning) actual_halogen_children_empty.2.2
              terminal_root_readers.2.2
            exact ⟨_, _, _, _, computed, actual_c1_key_observation _ carbonComputed,
              actual_c1_key_physical_id _ carbonComputed, fluorineNeutral.1, bromineNeutral.1,
              iodineNeutral.1, fluorineNeutral.2, bromineNeutral.2, iodineNeutral.2⟩

/-- A real returned key contains an actual `seqcis` entry, with no guessed layer or address. -/
theorem actual_returned_seqcis_entry :
    ∃ keys : List source.AromaticCanonicalUncancelledRule3SpatialKey,
      roots.mapM (source.buildAromaticCanonicalRule3SpatialKeyWith? planarObserver.observe 4) =
        some keys ∧ ∃ key ∈ keys, ∃ layer ∈ key.observations, ∃ entry ∈ layer,
          entry.2.unit.geometry = .seqcis ∧
          entry.2.physicalUnitId = source.aromaticCanonicalRule3PhysicalUnitId 1 5 := by
  obtain ⟨carbon, fluorine, bromine, iodine, computed, observed, _⟩ :=
    actual_four_raw_keys_conserve_seqcis
  obtain ⟨layer, layerMem, address, entryMem⟩ := observed
  exact ⟨[carbon, fluorine, bromine, iodine], computed, carbon, List.mem_cons_self,
    layer, layerMem, (address, cisNodeResult), entryMem, rfl, rfl⟩

end TetraStereo.UniversalProof.SourceNativePlanarKeyObservationConservationProofs.SourceNativePlanarKeyObservationConservation
