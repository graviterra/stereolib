import TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarFrameClosureProofs.SourceNativeAnnotatedPlanarFrameClosure

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry
open TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison
  (buildAromaticCanonicalPlanarRule3Frame? CanonicalAromaticCanonicalPlanarRule3Frame)
open TetraStereo.UniversalProof.SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness (pt)
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFuelCompletenessProofs.SourceNativeRule3ObserverFuelCompleteness
open TetraStereo.UniversalProof.SourceNativePlanarKeyObservationConservationProofs.SourceNativePlanarKeyObservationConservation
  (HasObservation child_positive_conserved observation_physical_id_mem terminal_negative_key_neutral)
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralTwoPassClosureProofs.SourceNativePlanarTetrahedralTwoPassClosure
  (physical_count_le_one_of_three_neutral ordinary_topology_of_unit_counts_le_one
   ordinary_excluded_nil_of_unit_counts_le_one observeExcept_nil_eq_observe)
open TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness
  (roots firstCursor rootNode cisUnit actual_planar_seqcis_unit own_left_senior own_right_senior
   actual_roots_valid actual_four_real_roots)




















abbrev source := SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.source
abbrev Atom := source.AromaticCanonicalAtom
local instance : NeZero source.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

def reverseCisUnit : source.AromaticCanonicalRule3SpatialUnitResult := ⟨8, 6, .seqcis⟩

theorem own_reverse_unit_canonical :
    CanonicalAromaticCanonicalPlanarRule3Unit source 5 1 reverseCisUnit := by
  refine ⟨?_, own_right_senior, own_left_senior,
    pt 2 0, pt 0 0, pt 3 1, pt (-1) 1, ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
    decide +kernel
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 5 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 1 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 8 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 6 _).mp (by decide +kernel)
  · norm_num [SameSide, planarDirectedArea, pt]

theorem actual_reverse_seqcis_unit :
    aromaticCanonicalPlanarRule3Unit? source 5 1 = some reverseCisUnit :=
  (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source 5 1 reverseCisUnit).mpr
    own_reverse_unit_canonical

theorem ordinary_double_bond_pairs : ∀ parent current : Atom,
    source.AromaticCanonicalOrdinaryDoubleBond parent current ↔
      (parent = 1 ∧ current = 5) ∨ (parent = 5 ∧ current = 1) := by
  unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
  decide +kernel

noncomputable def observer : Rule3Observer source :=
  SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison.planarObserver source

theorem actual_observer_total : ObserverTotal observer := by
  classical
  intro node
  change ∃ outcome, aromaticCanonicalPlanarRule3Node? source node = some outcome
  by_cases edge : source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node
  · rcases edge with ⟨real, current, parent, currentEq, parentEq, ordinary⟩
    have resolved : ∃ unit, aromaticCanonicalPlanarRule3Unit? source parent current = some unit := by
      rcases (ordinary_double_bond_pairs parent current).mp ordinary with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨cisUnit, actual_planar_seqcis_unit⟩
      · exact ⟨reverseCisUnit, actual_reverse_seqcis_unit⟩
    obtain ⟨unit, unitComputed⟩ := resolved
    refine ⟨some { left := parent, right := current, unit := unit }, ?_⟩
    exact (aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical source node
      { left := parent, right := current, unit := unit }).mpr
      ⟨real, currentEq, parentEq, ordinary,
        (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source parent current unit).mp
          unitComputed⟩
  · exact ⟨none, aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source node edge⟩

theorem actual_four_raw_keys :
    ∃ keys : List source.AromaticCanonicalUncancelledRule3SpatialKey,
      roots.mapM (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe 4) = some keys ∧
      source.CanonicalAromaticCanonicalRule3SpatialKeyWithList observer.NodeOutcome 4 roots keys ∧
      keys.length = 4 := by
  obtain ⟨keys, computed, meaning⟩ := exists_observer_key_list_at_or_above_twice
    (carrierFuel := 1) (evaluationFuel := 4) observer actual_observer_total roots
    actual_roots_valid (by decide)
  exact ⟨keys, computed, meaning,
    (mapM_length_eq_of_eq_some
      (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe 4)
      roots keys computed).trans actual_four_real_roots.1⟩

def carbonNode : OfficialCIPNode Atom := rootNode.extend 1 0
def realC5Node : OfficialCIPNode Atom := carbonNode.extend 5 0
def cisNodeResult : source.AromaticCanonicalRule3SpatialNodeResult := ⟨1, 5, cisUnit⟩

theorem actual_real_C5_reader :
    aromaticCanonicalPlanarRule3Node? source realC5Node = some (some cisNodeResult) := by
  apply (aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical source realC5Node
    cisNodeResult).mpr
  refine ⟨rfl, rfl, rfl, ?_, SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness.own_unit_canonical⟩
  unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
  decide +kernel

def carbonChildFrames : List source.AromaticCanonicalOccurrenceFrame :=
  [ { root := 0, address := [0, 0], node := realC5Node, remaining := 0 }
  , { root := 0, address := [0, 1], node := carbonNode.extend 5 1, remaining := 0 }
  , { root := 0, address := [0, 2], node := carbonNode.extend 6 0, remaining := 0 } ]

theorem actual_carbon_child_frames :
    (source.aromaticCanonicalRerootChildren (firstCursor 0)).map
      (fun cursor => cursor.occurrence.1) = carbonChildFrames := by
  rw [(source.aromaticCanonicalRerootChildren_sound (firstCursor 0)).1]
  decide +kernel

theorem actual_carbon_child_seqcis :
    ∃ child ∈ source.aromaticCanonicalRerootChildren (firstCursor 0),
      child.occurrence.1.node.history = [5, 1, 0] ∧
      child.previous? = some (firstCursor 0).occurrence ∧
      observer.observe child.occurrence.1.node = some (some cisNodeResult) := by
  have present : carbonChildFrames.head (by decide) ∈
      (source.aromaticCanonicalRerootChildren (firstCursor 0)).map
        (fun cursor => cursor.occurrence.1) := by
    rw [actual_carbon_child_frames]
    simp [carbonChildFrames]
  rcases List.mem_map.mp present with ⟨child, childPresent, frameEq⟩
  have nodeEq : child.occurrence.1.node = realC5Node := congrArg (fun frame => frame.node) frameEq
  refine ⟨child, childPresent, ?_,
    (source.aromaticCanonicalRerootChildren_sound (firstCursor 0)).2 child childPresent, ?_⟩
  · rw [nodeEq]; rfl
  · rw [nodeEq]; exact actual_real_C5_reader

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

theorem actual_halogen_readers_negative :
    observer.observe (firstCursor 1).occurrence.1.node = some none ∧
    observer.observe (firstCursor 2).occurrence.1.node = some none ∧
    observer.observe (firstCursor 3).occurrence.1.node = some none := by
  have negative (slot : Fin 4) (notCarbon : slot ≠ 0) :
      observer.observe (firstCursor slot).occurrence.1.node = some none := by
    change aromaticCanonicalPlanarRule3Node? source (firstCursor slot).occurrence.1.node = some none
    apply aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source
    unfold AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge
      AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
    fin_cases slot <;> first | contradiction | decide +kernel
  exact ⟨negative 1 (by decide), negative 2 (by decide), negative 3 (by decide)⟩

theorem actual_carbon_key_observation
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe 4
      (firstCursor 0) = some key) : HasObservation source key cisNodeResult := by
  obtain ⟨child, present, _, _, positive⟩ := actual_carbon_child_seqcis
  exact child_positive_conserved source observer.observe (firstCursor 0) child key
    cisNodeResult computed present positive

theorem actual_four_raw_keys_conserve_seqcis :
    ∃ carbon fluorine bromine iodine : source.AromaticCanonicalUncancelledRule3SpatialKey,
      roots.mapM (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe 4) =
        some [carbon, fluorine, bromine, iodine] ∧
      HasObservation source carbon cisNodeResult ∧
      fluorine.observations = [] ∧ bromine.observations = [] ∧ iodine.observations = [] ∧
      source.aromaticCanonicalRule3PhysicalUnitIds fluorine = [] ∧
      source.aromaticCanonicalRule3PhysicalUnitIds bromine = [] ∧
      source.aromaticCanonicalRule3PhysicalUnitIds iodine = [] := by
  obtain ⟨keys, computed, meaning, _⟩ := actual_four_raw_keys
  change source.CanonicalAromaticCanonicalRule3SpatialKeyWithList observer.NodeOutcome 4
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
                  observer.NodeOutcome 4 cursor key) :=
              (source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                observer.observe observer.NodeOutcome observer.nodeExact 4 cursor key).mpr derived
            have fluorineNeutral := terminal_negative_key_neutral source observer.observe
              (firstCursor 1) _ (toComputed fluorineMeaning) actual_halogen_children_empty.1
              actual_halogen_readers_negative.1
            have bromineNeutral := terminal_negative_key_neutral source observer.observe
              (firstCursor 2) _ (toComputed bromineMeaning) actual_halogen_children_empty.2.1
              actual_halogen_readers_negative.2.1
            have iodineNeutral := terminal_negative_key_neutral source observer.observe
              (firstCursor 3) _ (toComputed iodineMeaning) actual_halogen_children_empty.2.2
              actual_halogen_readers_negative.2.2
            exact ⟨_, _, _, _, computed, actual_carbon_key_observation _ (toComputed carbonMeaning),
              fluorineNeutral.1, bromineNeutral.1, iodineNeutral.1,
              fluorineNeutral.2, bromineNeutral.2, iodineNeutral.2⟩

theorem actual_raw_topology_and_exclusion
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : roots.mapM
      (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe 4) = some keys) :
    source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = some .ordinary ∧
      source.aromaticCanonicalRule3ExcludedPhysicalUnits keys .ordinary = [] := by
  obtain ⟨carbon, fluorine, bromine, iodine, rawComputed, _, _, _, _,
    fluorineNeutral, bromineNeutral, iodineNeutral⟩ := actual_four_raw_keys_conserve_seqcis
  have same : keys = [carbon, fluorine, bromine, iodine] :=
    Option.some.inj (computed.symm.trans rawComputed)
  subst keys
  have bound := physical_count_le_one_of_three_neutral source carbon fluorine bromine iodine
    fluorineNeutral bromineNeutral iodineNeutral
  exact ⟨ordinary_topology_of_unit_counts_le_one source _ bound,
    ordinary_excluded_nil_of_unit_counts_le_one source _ bound⟩

theorem actual_own_twoPass_frame_closed :
    ∃ frame : source.AromaticCanonicalRule3CanonicalKeyFrame,
      buildAromaticCanonicalPlanarRule3Frame? source 4 roots = some frame ∧
      CanonicalAromaticCanonicalPlanarRule3Frame source 4 roots frame ∧
      frame.resolution = .ordinary ∧ frame.excluded = [] ∧ frame.keys = frame.rawKeys ∧
      ∃ key ∈ frame.keys, HasObservation source key cisNodeResult := by
  obtain ⟨carbon, fluorine, bromine, iodine, rawComputed, observed, _⟩ :=
    actual_four_raw_keys_conserve_seqcis
  let keys := [carbon, fluorine, bromine, iodine]
  have facts := actual_raw_topology_and_exclusion keys rawComputed
  dsimp only [keys] at facts
  let frame : source.AromaticCanonicalRule3CanonicalKeyFrame :=
    { rawKeys := keys, resolution := .ordinary, excluded := [], keys := keys }
  have computed : buildRule3ObserverFrame? observer 4 roots = some frame := by
    simp [buildRule3ObserverFrame?, frame, keys, facts.1, facts.2,
      observeExcept_nil_eq_observe, rawComputed]
  exact ⟨frame, computed, buildRule3ObserverFrame?_sound observer 4 roots frame computed,
    rfl, rfl, rfl, carbon, List.mem_cons_self, observed⟩

theorem actual_own_second_pass_seqcis_entry :
    ∃ frame : source.AromaticCanonicalRule3CanonicalKeyFrame,
      buildAromaticCanonicalPlanarRule3Frame? source 4 roots = some frame ∧
      ∃ key ∈ frame.keys, ∃ layer ∈ key.observations, ∃ entry ∈ layer,
        entry.2.unit.geometry = .seqcis ∧
        entry.2.physicalUnitId = source.aromaticCanonicalRule3PhysicalUnitId 1 5 := by
  obtain ⟨frame, computed, _, _, _, _, key, keyMem, layer, layerMem, address, entryMem⟩ :=
    actual_own_twoPass_frame_closed
  exact ⟨frame, computed, key, keyMem, layer, layerMem,
    (address, cisNodeResult), entryMem, rfl, rfl⟩

end TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarFrameClosureProofs.SourceNativeAnnotatedPlanarFrameClosure
