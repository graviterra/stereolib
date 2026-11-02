import TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
import TetraStereo.UniversalProof.NextFrontier.ParsedParityCumulativeLeafDescriptors

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Actual same-model compound Rules4a--5 fields for the parsed family. Every key is extracted
from the internally computed central key frame. Actual scheduled arm labels and actual unlabeled
terminal descendants determine complete descriptor arrays and every pre-Rule5 tie. -/

namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule45

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCumulativeLeafDescriptors

private theorem canonical_ranked_head (source : AuthoritativeChemicalInput)
    {carrierFuel fuel : Nat} (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalCumulativeRule45Key)
    (derived : source.CanonicalAromaticCanonicalCumulativeRule45Key
      stage target view fuel cursor key) :
    key.rankedLabels.head? = some [([], source.aromaticCanonicalDependencyLabel target view cursor)] := by
  cases derived with
  | terminal frame empty observed =>
      rw [(source.aromaticCanonicalDependencyLabel_eq_iff target view cursor _).mpr observed]
      rfl
  | branch frame nonempty observed childDerivations ranking =>
      rw [(source.aromaticCanonicalDependencyLabel_eq_iff target view cursor _).mpr observed]
      rfl

private theorem actual_compound_references_of_chiral_label
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key) (reference : RS)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45Key?
      target view fuel cursor = some key)
    (label : source.aromaticCanonicalDependencyLabel target view cursor = some (.chiral reference)) :
    key.prior.references = [reference] := by
  have canonical := (source.buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
    target view fuel cursor key).mp computed
  have rankedHead := canonical_ranked_head source .rule4a target view cursor
    key.prior.rule4aKey canonical.1.1
  rw [label] at rankedHead
  have refsComputed := (localizedRule4bReferencesFromRankedLabels_eq_iff
    key.prior.rule4aKey.rankedLabels key.prior.references).mpr canonical.1.2.1
  cases layersEq : key.prior.rule4aKey.rankedLabels with
  | nil => simp [layersEq] at rankedHead
  | cons first tail =>
      have firstEq : first = [([], some (.chiral reference))] := by
        simpa [layersEq] using rankedHead
      rw [layersEq, firstEq] at refsComputed
      cases reference <;>
        simpa [localizedRule4bReferencesFromRankedLabels, localizedFirstChiralRankPopulation,
          localizedFirstChiralRankPopulationInLayer, localizedChiralDescriptorsAtRank,
          localizedRule4bReferencesFromPopulation] using refsComputed.symm

private theorem mapM_actual_outputs {α β : Type*} (f : α → Option β) :
    ∀ inputs outputs, inputs.mapM f = some outputs →
      List.Forall₂ (fun input output => f input = some output) inputs outputs
  | [], outputs, computed => by
      simp at computed
      subst outputs
      exact .nil
  | input :: inputs, outputs, computed => by
      rw [List.mapM_cons] at computed
      cases first : f input with
      | none => simp [first] at computed
      | some output =>
          cases rest : inputs.mapM f with
          | none => simp [first, rest] at computed
          | some tail =>
              simp [first, rest] at computed
              subst outputs
              exact .cons first (mapM_actual_outputs f inputs tail rest)

private theorem keyFrame_actual_outputs (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel roots = some frame) :
    List.Forall₂ (fun cursor key => source.buildAromaticCanonicalRerootCompoundRule45Key?
      target view fuel cursor = some key) roots frame.rule45Keys := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? at computed
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel roots with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases length3 : rule3Frame.keys.length = 4
      · cases keysComputed : roots.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) with
        | none => simp [rule3Computed, keysComputed] at computed
        | some keys =>
            by_cases length45 : keys.length = 4
            · simp [rule3Computed, length3, keysComputed, length45] at computed
              subst frame
              exact mapM_actual_outputs _ roots keys keysComputed
            · simp [rule3Computed, keysComputed, length45] at computed
      · simp [rule3Computed, length3] at computed

private theorem keyFrame_slot_computed (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel frame.roots = some keys) (slot : Fin 4) :
    source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel (frame.cursorAt slot) =
      some (keys.keyAt slot).rule45 := by
  have outputs := keyFrame_actual_outputs source target view fuel frame.roots keys computed
  exact outputs.get (i := slot.val)
    (by rw [frame.rootsLength]; exact slot.isLt)
    (by rw [keys.rule45Length]; exact slot.isLt)

/-- Every compound key field comes from the genuine central compiler invocation. -/
theorem central_rule45_computed (c l r : TetrahedralInputParity) (slot : Fin 4) :
    (ownSource (raw c l r)).buildAromaticCanonicalRerootCompoundRule45Key?
      (centralTarget c l r) (centralView c l r) 4 ((sourceFrame c l r).cursorAt slot) =
      some ((centralKeys c l r).keyAt slot).rule45 :=
  keyFrame_slot_computed (ownSource (raw c l r)) (centralTarget c l r) (centralView c l r)
    4 (sourceFrame c l r) (centralKeys c l r) (central_keys_computed c l r) slot

def armReference (l r : TetrahedralInputParity) (left : Bool) : RS :=
  descriptorOfParity (armParity l r left) false

theorem arm_actual_label (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).aromaticCanonicalDependencyLabel (centralTarget c l r)
      (centralView c l r) (armCursor c l r left) = some (.chiral (armReference l r left)) :=
  central_scheduled_arm_label c l r left

/-- Complete descriptor projection for any stage: actual root label, then three absent labels. -/
def armDescriptorLayers (stage : LocalizedCumulativeRule45Stage) (reference : RS) :
    List (List (OfficialSparseEntry (List Nat))) :=
  [[([], localizedCumulativeRule45Priority stage (some (.chiral reference)))],
   [([0], localizedCumulativeRule45Priority stage none),
    ([1], localizedCumulativeRule45Priority stage none),
    ([2], localizedCumulativeRule45Priority stage none)]]

theorem arm_cumulative_descriptor (c l r : TetrahedralInputParity) (left : Bool)
    (stage : LocalizedCumulativeRule45Stage)
    (key : (ownSource (raw c l r)).AromaticCanonicalCumulativeRule45Key)
    (derived : (ownSource (raw c l r)).CanonicalAromaticCanonicalCumulativeRule45Key
      stage (centralTarget c l r) (centralView c l r) 4 (armCursor c l r left) key) :
    key.descriptor = armDescriptorLayers stage (armReference l r left) := by
  have projected := canonical_three_leaf_descriptor (ownSource (raw c l r)) stage
    (centralTarget c l r) (centralView c l r) (armCursor c l r left) key derived
    (arm_children_length c l r left) (arm_child_terminal c l r left)
    (arm_child_dependency_none c l r left)
  simpa only [arm_actual_label, armDescriptorLayers] using projected

theorem arm_references (c l r : TetrahedralInputParity) (left : Bool) :
    ((centralKeys c l r).keyAt (armSlot c l r left)).rule45.prior.references =
      [armReference l r left] :=
  actual_compound_references_of_chiral_label (ownSource (raw c l r))
    (centralTarget c l r) (centralView c l r) 4 (armCursor c l r left)
    ((centralKeys c l r).keyAt (armSlot c l r left)).rule45 (armReference l r left)
    (central_rule45_computed c l r (armSlot c l r left)) (arm_actual_label c l r left)

private theorem singleton_reading_meaning (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) (reference : RS)
    (readings : List source.AromaticCanonicalRerootRule4bcReading)
    (derived : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      target view fuel cursor [some reference] readings) :
    ∃ reading, readings = [reading] ∧ reading.reference? = some reference ∧
      source.CanonicalAromaticCanonicalCumulativeRule45Key (.rule4b reference)
        target view fuel cursor reading.rule4bKey ∧
      source.CanonicalAromaticCanonicalCumulativeRule45Key (.rule4c reference)
        target view fuel cursor reading.rule4cKey := by
  cases derived with
  | cons first rest =>
      cases rest
      cases first with
      | reference rule4b rule4c => exact ⟨_, rfl, rfl, rule4b, rule4c⟩

theorem arm_prior_shape (c l r : TetrahedralInputParity) (left : Bool) :
    ((centralKeys c l r).keyAt (armSlot c l r left)).rule45.prior.referenceCountPriority = 2 ∧
    ∃ reading : (ownSource (raw c l r)).AromaticCanonicalRerootRule4bcReading,
      ((centralKeys c l r).keyAt (armSlot c l r left)).rule45.prior.readings = [reading] ∧
      reading.reference? = some (armReference l r left) ∧
      reading.rule4bKey.descriptor = armDescriptorLayers (.rule4b (armReference l r left))
        (armReference l r left) ∧
      reading.rule4cKey.descriptor = armDescriptorLayers (.rule4c (armReference l r left))
        (armReference l r left) := by
  have canonical := ((ownSource (raw c l r)).buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
    (centralTarget c l r) (centralView c l r) 4 (armCursor c l r left)
    ((centralKeys c l r).keyAt (armSlot c l r left)).rule45).mp
      (central_rule45_computed c l r (armSlot c l r left))
  have count := canonical.1.2.2.1
  rw [arm_references] at count
  have readings := canonical.1.2.2.2
  rw [arm_references] at readings
  have normalized : aromaticCanonicalRule4bcReferenceAlternatives [armReference l r left] =
      [some (armReference l r left)] := rfl
  rw [normalized] at readings
  obtain ⟨reading, singleton, reference, rule4b, rule4c⟩ := singleton_reading_meaning
    (ownSource (raw c l r)) (centralTarget c l r) (centralView c l r)
    (armCursor c l r left) (armReference l r left) _ readings
  exact ⟨count, reading, singleton, reference,
    arm_cumulative_descriptor c l r left _ _ rule4b,
    arm_cumulative_descriptor c l r left _ _ rule4c⟩

/-- Every complete Rule4 prior ties between the two chemically corresponding arms,
including equal-label members; references and complete descriptors are derived above. -/
theorem arm_prior_comparison (c l r : TetrahedralInputParity) (first second : Bool) :
    (ownSource (raw c l r)).compareAromaticCanonicalRerootCompoundRule4bcKeys
      ((centralKeys c l r).keyAt (armSlot c l r first)).rule45.prior
      ((centralKeys c l r).keyAt (armSlot c l r second)).rule45.prior = .eq := by
  obtain ⟨count1, reading1, list1, _, b1, c1⟩ := arm_prior_shape c l r first
  obtain ⟨count2, reading2, list2, _, b2, c2⟩ := arm_prior_shape c l r second
  unfold compareAromaticCanonicalRerootCompoundRule4bcKeys
    compareAromaticCanonicalRerootCompoundRule4bReadings
    compareAromaticCanonicalRerootRule4bcReadingsByRule4b
    compareAromaticCanonicalRerootCompoundRule4cReadings
  simp only [compareLex, Ordering.byKey, count1, count2, list1, list2]
  simp only [List.compareLex, Ordering.byKey, b1, b2, c1, c2]
  generalize armReference l r first = ref1
  generalize armReference l r second = ref2
  cases ref1 <;> cases ref2 <;> decide +kernel

private theorem singleton_rule5_meaning (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (readings : List source.AromaticCanonicalRerootRule5Reading)
    (derived : source.CanonicalAromaticCanonicalRerootRule5Readings
      target view fuel cursor [prior] readings) :
    ∃ reading, readings = [reading] ∧
      source.CanonicalAromaticCanonicalRerootRule5Reading target view fuel cursor prior reading := by
  cases derived with
  | cons first rest => cases rest; exact ⟨_, rfl, first⟩

theorem arm_rule5_shape (c l r : TetrahedralInputParity) (left : Bool) :
    ∃ reading : (ownSource (raw c l r)).AromaticCanonicalRerootRule5Reading,
      ((centralKeys c l r).keyAt (armSlot c l r left)).rule45.rule5Readings = [reading] ∧
      reading.commonR.descriptor =
        armDescriptorLayers (.rule5 (armReference l r left) .R) (armReference l r left) ∧
      reading.commonS.descriptor =
        armDescriptorLayers (.rule5 (armReference l r left) .S) (armReference l r left) := by
  have canonical := ((ownSource (raw c l r)).buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
    (centralTarget c l r) (centralView c l r) 4 (armCursor c l r left)
    ((centralKeys c l r).keyAt (armSlot c l r left)).rule45).mp
      (central_rule45_computed c l r (armSlot c l r left))
  obtain ⟨_, prior, singleton, reference, _, _⟩ := arm_prior_shape c l r left
  have derived := canonical.2
  rw [singleton] at derived
  obtain ⟨reading, readings, meaning⟩ := singleton_rule5_meaning (ownSource (raw c l r))
    (centralTarget c l r) (centralView c l r) (armCursor c l r left) prior _ derived
  have commonR := meaning.2.1
  have commonS := meaning.2.2
  rw [reference] at commonR commonS
  exact ⟨reading, readings,
    arm_cumulative_descriptor c l r left _ _ commonR,
    arm_cumulative_descriptor c l r left _ _ commonS⟩

/-- Numeric form of the actual common-reference Rule5 choice. -/
def referenceComparison (common first second : RS) : Ordering :=
  compare (if first = common then (1 : Nat) else 0) (if second = common then (1 : Nat) else 0)

theorem arm_rule5_comparison (c l r : TetrahedralInputParity) (first second : Bool) (common : RS) :
    (ownSource (raw c l r)).compareAromaticCanonicalRerootCompoundRule5Readings common
      ((centralKeys c l r).keyAt (armSlot c l r first)).rule45.rule5Readings
      ((centralKeys c l r).keyAt (armSlot c l r second)).rule45.rule5Readings =
      referenceComparison common (armReference l r first) (armReference l r second) := by
  obtain ⟨reading1, list1, r1, s1⟩ := arm_rule5_shape c l r first
  obtain ⟨reading2, list2, r2, s2⟩ := arm_rule5_shape c l r second
  rw [list1, list2]
  cases common <;>
    simp only [compareAromaticCanonicalRerootCompoundRule5Readings,
      aromaticCanonicalRerootRule5Descriptor, Ordering.byKey, List.compareLex, r1, r2, s1, s2]
  all_goals
    generalize armReference l r first = ref1
    generalize armReference l r second = ref2
    cases ref1 <;> cases ref2 <;> decide +kernel

/-- Opposite actual R/S labels produce the Rule5 pseudo signal; equal actual labels tie. -/
theorem arm_compound_comparison (c l r : TetrahedralInputParity) (first second : Bool) :
    (ownSource (raw c l r)).compareAromaticCanonicalRerootCompoundThroughRule5
      ((centralKeys c l r).keyAt (armSlot c l r first)).rule45
      ((centralKeys c l r).keyAt (armSlot c l r second)).rule45 =
      { ordering := referenceComparison .R (armReference l r first) (armReference l r second)
        pseudo := decide (armReference l r first ≠ armReference l r second) } := by
  unfold compareAromaticCanonicalRerootCompoundThroughRule5
  rw [arm_prior_comparison, arm_rule5_comparison, arm_rule5_comparison]
  generalize armReference l r first = ref1
  generalize armReference l r second = ref2
  cases ref1 <;> cases ref2 <;> decide +kernel

end TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule45
