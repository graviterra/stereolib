import TetraStereo.UniversalProof.SourceNativePlanarKeyObservationConservationProofs.SourceNativePlanarKeyObservationConservation
import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativePlanarTetrahedralTwoPassClosureProofs.SourceNativePlanarTetrahedralTwoPassClosure

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralKeyFrameProofs.SourceNativePlanarTetrahedralKeyFrame
  (planarObserver)
open TetraStereo.UniversalProof.SourceNativePlanarKeyObservationConservationProofs.SourceNativePlanarKeyObservationConservation
  (HasObservation actual_four_raw_keys_conserve_seqcis)
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource
  (roots cisNodeResult)


















abbrev source := TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.source
local instance : NeZero source.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

/-- Three neutral ligand keys leave each physical unit present in at most one key. -/
theorem physical_count_le_one_of_three_neutral
    (input : AuthoritativeChemicalInput)
    (carbon fluorine bromine iodine : input.AromaticCanonicalUncancelledRule3SpatialKey)
    (fluorineNeutral : input.aromaticCanonicalRule3PhysicalUnitIds fluorine = [])
    (bromineNeutral : input.aromaticCanonicalRule3PhysicalUnitIds bromine = [])
    (iodineNeutral : input.aromaticCanonicalRule3PhysicalUnitIds iodine = [])
    (unit : input.AromaticCanonicalRule3PhysicalUnitId) :
    input.aromaticCanonicalRule3PhysicalUnitKeyCount [carbon, fluorine, bromine, iodine] unit ≤
      1 := by
  by_cases present : unit ∈ input.aromaticCanonicalRule3PhysicalUnitIds carbon
  · simp [aromaticCanonicalRule3PhysicalUnitKeyCount,
      fluorineNeutral, bromineNeutral,
      iodineNeutral, present]
  · simp [aromaticCanonicalRule3PhysicalUnitKeyCount,
      fluorineNeutral, bromineNeutral,
      iodineNeutral, present]

theorem no_coupled_pair_of_unit_counts_le_one (input : AuthoritativeChemicalInput)
    (keys : List input.AromaticCanonicalUncancelledRule3SpatialKey)
    (bound : ∀ unit, input.aromaticCanonicalRule3PhysicalUnitKeyCount keys unit ≤ 1)
    (pair : input.AromaticCanonicalRule3CoupledUnitPair) :
    ¬ input.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair := by
  rintro ⟨_, _, _, _, _, firstCount, _⟩
  have small := bound pair.firstUnit
  omega

theorem ordinary_topology_of_unit_counts_le_one (input : AuthoritativeChemicalInput)
    (keys : List input.AromaticCanonicalUncancelledRule3SpatialKey)
    (bound : ∀ unit, input.aromaticCanonicalRule3PhysicalUnitKeyCount keys unit ≤ 1) :
    input.aromaticCanonicalRule3PhysicalTopologyResolution? keys = some .ordinary := by
  have pairsEmpty : input.aromaticCanonicalRule3CoupledUnitPairs keys = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro pair present
    exact no_coupled_pair_of_unit_counts_le_one input keys bound pair
      ((input.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys pair).mp present)
  simp [aromaticCanonicalRule3PhysicalTopologyResolution?, pairsEmpty]

theorem ordinary_excluded_nil_of_unit_counts_le_one (input : AuthoritativeChemicalInput)
    (keys : List input.AromaticCanonicalUncancelledRule3SpatialKey)
    (bound : ∀ unit, input.aromaticCanonicalRule3PhysicalUnitKeyCount keys unit ≤ 1) :
    input.aromaticCanonicalRule3ExcludedPhysicalUnits keys .ordinary = [] := by
  change input.aromaticCanonicalRule3SharedPhysicalUnits keys = []
  rw [List.eq_nil_iff_forall_not_mem]
  intro unit present
  have shared := ((input.mem_aromaticCanonicalRule3SharedPhysicalUnits_iff keys unit).mp present).2
  have small := bound unit
  omega

theorem observeExcept_nil_eq_observe {input : AuthoritativeChemicalInput}
    (observer : Rule3Observer input) : observeExcept observer [] = observer.observe := by
  funext node
  cases computed : observer.observe node with
  | none => simp [observeExcept, computed]
  | some outcome => cases outcome <;> simp [observeExcept, computed]

/-- Topology and exclusion are derived for ANY actual returned raw list, not supplied as readiness. -/
theorem actual_raw_topology_and_exclusion
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : roots.mapM
      (source.buildAromaticCanonicalRule3SpatialKeyWith? planarObserver.observe 4) = some keys) :
    source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = some .ordinary ∧
      source.aromaticCanonicalRule3ExcludedPhysicalUnits keys .ordinary = [] := by
  obtain ⟨carbon, fluorine, bromine, iodine, rawComputed, _, _, _, _, _,
    fluorineNeutral, bromineNeutral, iodineNeutral⟩ := actual_four_raw_keys_conserve_seqcis
  have same : keys = [carbon, fluorine, bromine, iodine] :=
    Option.some.inj (computed.symm.trans rawComputed)
  subst keys
  have bound := physical_count_le_one_of_three_neutral source carbon fluorine bromine iodine
    fluorineNeutral bromineNeutral iodineNeutral
  exact ⟨ordinary_topology_of_unit_counts_le_one source _ bound,
    ordinary_excluded_nil_of_unit_counts_le_one source _ bound⟩

/-- The concrete 1--5 unit occurs in exactly one returned ligand key. -/
theorem actual_cis_unit_key_count_one :
    ∃ keys : List source.AromaticCanonicalUncancelledRule3SpatialKey,
      roots.mapM (source.buildAromaticCanonicalRule3SpatialKeyWith? planarObserver.observe 4) =
        some keys ∧
      source.aromaticCanonicalRule3PhysicalUnitKeyCount keys
        (source.aromaticCanonicalRule3PhysicalUnitId 1 5) = 1 := by
  obtain ⟨carbon, fluorine, bromine, iodine, computed, _, carbonPresent, _, _, _,
    fluorineNeutral, bromineNeutral, iodineNeutral⟩ := actual_four_raw_keys_conserve_seqcis
  refine ⟨[carbon, fluorine, bromine, iodine], computed, ?_⟩
  simp [aromaticCanonicalRule3PhysicalUnitKeyCount,
    fluorineNeutral, bromineNeutral, iodineNeutral, carbonPresent]

/-- Both actual passes succeed, with the independently judged ordinary topology, empty common
exclusion, identical second-pass keys and actual retained 1--5 seqcis observation. -/
theorem actual_twoPass_frame_closed :
    ∃ frame : source.AromaticCanonicalRule3CanonicalKeyFrame,
      buildRule3ObserverFrame? planarObserver 4 roots = some frame ∧
      CanonicalRule3ObserverFrame planarObserver 4 roots frame ∧
      frame.resolution = .ordinary ∧ frame.excluded = [] ∧ frame.keys = frame.rawKeys ∧
      ∃ key ∈ frame.keys, HasObservation source key cisNodeResult := by
  obtain ⟨carbon, fluorine, bromine, iodine, rawComputed, observed, _⟩ :=
    actual_four_raw_keys_conserve_seqcis
  let keys := [carbon, fluorine, bromine, iodine]
  have facts := actual_raw_topology_and_exclusion keys rawComputed
  dsimp only [keys] at facts
  let frame : source.AromaticCanonicalRule3CanonicalKeyFrame :=
    { rawKeys := keys, resolution := .ordinary, excluded := [], keys := keys }
  have computed : buildRule3ObserverFrame? planarObserver 4 roots = some frame := by
    simp [buildRule3ObserverFrame?, frame, keys, facts.1, facts.2,
      observeExcept_nil_eq_observe, rawComputed]
  exact ⟨frame, computed, buildRule3ObserverFrame?_sound planarObserver 4 roots frame computed,
    rfl, rfl, rfl, carbon, List.mem_cons_self, observed⟩

/-- The actual exported NEW planar frame builder succeeds with its own planar canonical meaning. -/
theorem actual_planar_twoPass_frame_closed :
    ∃ frame : source.AromaticCanonicalRule3CanonicalKeyFrame,
      SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison.buildAromaticCanonicalPlanarRule3Frame?
        source 4 roots = some frame ∧
      SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison.CanonicalAromaticCanonicalPlanarRule3Frame
        source 4 roots frame ∧
      frame.resolution = .ordinary ∧ frame.excluded = [] ∧ frame.keys = frame.rawKeys ∧
      ∃ key ∈ frame.keys, HasObservation source key cisNodeResult := by
  obtain ⟨frame, computed, meaning, ordinary, excluded, same, observed⟩ := actual_twoPass_frame_closed
  exact ⟨frame, computed, meaning, ordinary, excluded, same, observed⟩

/-- A returned SECOND-pass key retains an actual seqcis entry with physical identity 1--5. -/
theorem actual_second_pass_seqcis_entry :
    ∃ frame : source.AromaticCanonicalRule3CanonicalKeyFrame,
      buildRule3ObserverFrame? planarObserver 4 roots = some frame ∧
      ∃ key ∈ frame.keys, ∃ layer ∈ key.observations, ∃ entry ∈ layer,
        entry.2.unit.geometry = .seqcis ∧
        entry.2.physicalUnitId = source.aromaticCanonicalRule3PhysicalUnitId 1 5 := by
  obtain ⟨frame, computed, _, _, _, _, key, keyMem, layer, layerMem, address, entryMem⟩ :=
    actual_twoPass_frame_closed
  exact ⟨frame, computed, key, keyMem, layer, layerMem,
    (address, cisNodeResult), entryMem, rfl, rfl⟩

/-- The earlier explicit closed-frame technical obligation is now inhabited. -/
theorem actual_twoPass_obligation_closed :
    SourceNativePlanarTetrahedralKeyFrameProofs.SourceNativePlanarTetrahedralKeyFrame.PlanarTetrahedralTwoPassFrameObligation := by
  obtain ⟨frame, computed, meaning, _⟩ := actual_twoPass_frame_closed
  exact ⟨frame, computed, meaning⟩

end TetraStereo.UniversalProof.SourceNativePlanarTetrahedralTwoPassClosureProofs.SourceNativePlanarTetrahedralTwoPassClosure
