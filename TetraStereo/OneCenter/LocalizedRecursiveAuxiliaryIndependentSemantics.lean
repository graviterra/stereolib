import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
import TetraStereo.OneCenter.LocalizedRetainedContextAllOccurrences
import TetraStereo.OneCenter.DeclarativeCIPRetainedContextDescriptor
import TetraStereo.OneCenter.LocalizedRuleMajorReportCorrectness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# The generated auxiliary states uniquely solve the fixed retained equations

`all_carrier_occurrences_retained_on_cut_arms` (accepted) proves that at every real detected
carrier occurrence the generated state equals the retained judgment on the canonical predecessor
cuts. That judgment reads auxiliary labels through `descriptorMap input`, i.e. through the
**generated states themselves**. This module instead quantifies over arbitrary candidate states
and proves uniqueness for the equations on the fixed compiled carrier.

`IndependentRetainedModel S` says, for an arbitrary candidate state `S`:

* non-real occurrences and real non-centers carry `none`;
* at every real detected occurrence, `S` is the retained outcome on that occurrence's canonical
  cuts, reading auxiliary labels from **`S` itself** (`stateMap S`).

The cuts are graph objects (`cutRetainedArm` named by the compiled cursors) and the window `W, D`
and coordinates are those of the occurrence's frame compilation. Candidate reads use only `S`,
but the compilation-selected windows still depend on the generated stage trees. This is not yet
an evaluator-free molecular specification; independence of sufficiently large windows remains
a separate obligation.

* `referenceState_independentRetainedModel`: the generated state is a model.
* `independentRetainedModel_unique`: every model is the generated state. Proof by strong
  induction on the remaining path length: a retained read at a unit with an ancestor-step path
  exists only when that unit's path is strictly longer (`contextOccurrence`). Real carrier
  occurrences have nodup histories, so their path length is at most the number of atoms.

Hence the actual recursively generated auxiliary states at **all** retained occurrences (every
depth, rings, duplicates, refusals and lowercase labels) are the unique solution of these fixed
retained ordinary-rule equations. The report corollary reads that same model at every detected
center. Physical completeness and chemical fidelity of the retained equations are separate claims.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open LocalizedRecursiveAuxiliaryPhysicalDomain
open scoped Classical

noncomputable section

variable {input : Input}

/-- The descriptor map induced by a candidate state, through the carrier occurrence of a unit. -/
def stateMap (input : Input) (state : Occurrence input → Option LocalizedAuxiliaryLabel) :
    DescriptorMap (DetectedOccurrence input.certified.moleculeGraph) :=
  fun unit => (actualReferenceOccurrenceOf input unit.1).bind fun occurrence =>
    (state occurrence).map localizedAuxiliaryDescriptor

theorem stateMap_referenceState (input : Input) :
    stateMap input (referenceState input) = descriptorMap input := rfl

/-- **Independent retained model.** The candidate state is the retained ordinary-rule outcome at
every real detected carrier occurrence, with auxiliary labels read from the candidate itself. -/
def IndependentRetainedModel (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (state : Occurrence input → Option LocalizedAuxiliaryLabel) : Prop :=
  ∀ target : Occurrence input,
    (target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom → state target = none) ∧
    (∀ _real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom,
      ¬ IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit target.1).atom → state target = none) ∧
    (∀ (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
      (detected : IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit target.1).atom),
      let unit : DetectedOccurrence input.certified.moleculeGraph :=
        ⟨input.certified.molecularFrameUnit target.1, detected⟩
      let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
      RetainedContextualOutcomeAt input.certified.moleculeGraph (stateMap input state) unit
        (frames.canonicalCutGraphs singleBonded) frames.W frames.D frames.actualCoordinates
        (state target))

/-! ## Generic facts about retained outcomes -/

theorem retainedContextualOutcomeAt_unique {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    {molecule : MoleculeGraph Atom} {map : DescriptorMap (DetectedOccurrence molecule)}
    {unit : DetectedOccurrence molecule} {graphs : Fin 4 → RootedDigraph Atom} {W D : ℕ}
    {coordinates : Fin 4 → Option CartesianPoint3} {first second : Option LocalizedAuxiliaryLabel}
    (hfirst : RetainedContextualOutcomeAt molecule map unit graphs W D coordinates first)
    (hsecond : RetainedContextualOutcomeAt molecule map unit graphs W D coordinates second) :
    first = second := by
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some descriptor =>
          simp only [RetainedContextualOutcomeAt] at hfirst hsecond
          exact (hfirst ⟨descriptor, hsecond⟩).elim
  | some descriptor =>
      cases second with
      | none =>
          simp only [RetainedContextualOutcomeAt] at hfirst hsecond
          exact (hsecond ⟨descriptor, hfirst⟩).elim
      | some other =>
          simp only [RetainedContextualOutcomeAt] at hfirst hsecond
          obtain ⟨points, available, judgment⟩ := hfirst
          obtain ⟨points', available', judgment'⟩ := hsecond
          have same : points = points' := funext fun slot =>
            Option.some.inj ((available slot).symm.trans (available' slot))
          subst same
          exact congrArg some (completeRootDescriptorJudgment_unique judgment judgment')

theorem retainedContextualOutcomeAt_congr_keys {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    {molecule : MoleculeGraph Atom} {first second : DescriptorMap (DetectedOccurrence molecule)}
    {unit : DetectedOccurrence molecule} {graphs : Fin 4 → RootedDigraph Atom} {W D : ℕ}
    {coordinates : Fin 4 → Option CartesianPoint3} {outcome : Option LocalizedAuxiliaryLabel}
    (keys : retainedContextualFrameKeysAt molecule first unit graphs W D =
      retainedContextualFrameKeysAt molecule second unit graphs W D)
    (holds : RetainedContextualOutcomeAt molecule first unit graphs W D coordinates outcome) :
    RetainedContextualOutcomeAt molecule second unit graphs W D coordinates outcome := by
  cases outcome with
  | none =>
      simp only [RetainedContextualOutcomeAt, RetainedContextualDescriptorJudgmentAt] at holds ⊢
      rw [← keys]
      exact holds
  | some descriptor =>
      simp only [RetainedContextualOutcomeAt, RetainedContextualDescriptorJudgmentAt] at holds ⊢
      rw [← keys]
      exact holds

/-- A context read exists only at a unit with a strictly longer path. -/
theorem contextOccurrence_path_lt {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    {molecule : MoleculeGraph Atom} {unit occ : DetectedOccurrence molecule} {steps : List Atom}
    (read : contextOccurrence molecule unit steps = some occ) :
    unit.1.path.length < occ.1.path.length := by
  unfold contextOccurrence at read
  dsimp only at read
  split at read
  · rename_i h
    cases read
    exact h.1
  · cases read

/-- The path of a real carrier occurrence is at most the number of atoms long. -/
theorem realUnitPath_length_le (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    (input.certified.molecularFrameUnit target.1).path.length ≤
      Fintype.card input.certified.Atom := by
  have nodup := (LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    input.certified target real).1
  have bound := nodup.length_le_card
  show (target.1.node.history.reverse.tail).length ≤ _
  rw [List.length_tail, List.length_reverse]
  omega

/-! ## Existence and uniqueness -/

/-- The generated reference state is an independent retained model. -/
theorem referenceState_independentRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    IndependentRetainedModel input singleBonded (referenceState input) := by
  intro target
  obtain ⟨notReal, notDetected, detectedFacts⟩ :=
    all_carrier_occurrences_retained_on_cut_arms singleBonded target
  refine ⟨notReal, notDetected, ?_⟩
  intro real detected
  obtain ⟨_roots, _previous, _cuts, someIff, noneIff⟩ := detectedFacts real detected
  cases state : referenceState input target with
  | none => exact noneIff.mp state
  | some descriptor => exact (someIff descriptor).mp state

/-- **Uniqueness of the independent retained model.** Any state obeying the retained
ordinary-rule equations with its own auxiliary reads is the generated reference state. -/
theorem independentRetainedModel_unique
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {state : Occurrence input → Option LocalizedAuxiliaryLabel}
    (model : IndependentRetainedModel input singleBonded state) :
    state = referenceState input := by
  have main : ∀ n, ∀ target : Occurrence input,
      target.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      Fintype.card input.certified.Atom -
          (input.certified.molecularFrameUnit target.1).path.length = n →
        state target = referenceState input target := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro target real measure
      by_cases detected : IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit target.1).atom
      swap
      · rw [(model target).2.1 real detected,
          referenceState_none_of_real_not_detected singleBonded target real detected]
      let unit : DetectedOccurrence input.certified.moleculeGraph :=
        ⟨input.certified.molecularFrameUnit target.1, detected⟩
      let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
      have candidate := (model target).2.2 real detected
      have generated := (referenceState_independentRetainedModel singleBonded target).2.2 real
        detected
      have keys : retainedContextualFrameKeysAt input.certified.moleculeGraph
          (stateMap input state) unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D =
          retainedContextualFrameKeysAt input.certified.moleculeGraph
            (stateMap input (referenceState input)) unit
            (frames.canonicalCutGraphs singleBonded) frames.W frames.D := by
        funext slot
        apply cut_retainedCompleteLigandRule5KeyAt_congr
        intro node steps occ _nodeReal _ancestors read
        have longer := contextOccurrence_path_lt read
        show (actualReferenceOccurrenceOf input occ.1).bind (fun occurrence =>
            (state occurrence).map localizedAuxiliaryDescriptor) =
          (actualReferenceOccurrenceOf input occ.1).bind (fun occurrence =>
            (referenceState input occurrence).map localizedAuxiliaryDescriptor)
        cases chosen : actualReferenceOccurrenceOf input occ.1 with
        | none => rfl
        | some source =>
            simp only [Option.bind_some]
            have unitEq := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input
              singleBonded occ.1 source).mp chosen
            by_cases sourceReal : source.1.node.provenance = OfficialCIPNodeProvenance.realAtom
            · have bound := realUnitPath_length_le source sourceReal
              have lengths : (input.certified.molecularFrameUnit target.1).path.length <
                  (input.certified.molecularFrameUnit source.1).path.length := by
                rw [unitEq]
                exact longer
              rw [ih _ (by omega) source sourceReal rfl]
            · rw [(model source).1 sourceReal, referenceState_none_of_not_real input source
                sourceReal]
      exact retainedContextualOutcomeAt_unique candidate
        (retainedContextualOutcomeAt_congr_keys keys.symm generated)
  funext target
  by_cases real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · exact main _ target real rfl
  · rw [(model target).1 real, referenceState_none_of_not_real input target real]

/-- **Existence and uniqueness.** -/
theorem existsUnique_independentRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    ∃! state : Occurrence input → Option LocalizedAuxiliaryLabel,
      IndependentRetainedModel input singleBonded state :=
  ⟨referenceState input, referenceState_independentRetainedModel singleBonded,
    fun _ model => independentRetainedModel_unique singleBonded model⟩

/-- The entire actual detected-center report reads the unique model of the fixed retained
equations. This includes refused outcomes; it does not assert physical completeness. -/
theorem mem_analyze_iff_independentRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {state : Occurrence input → Option LocalizedAuxiliaryLabel}
    (model : IndependentRetainedModel input singleBonded state)
    (atom : Nat) (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ analyze input ↔
      ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
        state (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
          outcome := by
  rw [independentRetainedModel_unique singleBonded model]
  exact mem_analyze_iff input atom outcome

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.retainedContextualOutcomeAt_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.retainedContextualOutcomeAt_congr_keys
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.contextOccurrence_path_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.realUnitPath_length_le
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.referenceState_independentRetainedModel
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.independentRetainedModel_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.existsUnique_independentRetainedModel
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.stateMap_referenceState
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics.mem_analyze_iff_independentRetainedModel
