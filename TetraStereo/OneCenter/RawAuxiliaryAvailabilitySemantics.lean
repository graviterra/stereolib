import TetraStereo.OneCenter.ConstitutionalRootStageAvailability
import TetraStereo.OneCenter.OccurrenceStructuralNonbearingFacts
import TetraStereo.OneCenter.RawFramedConstitutionalIndependence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Raw auxiliary availability semantics

This module isolates the exact availability boundary of the accepted occurrence-fact evaluator
over the actual generated molecule used by `ConstitutionalRootStageAvailability`:

    C[C@@H](Cl)[C@@H]([C@H](Cl)C)Br

Under this repository's bracket-token convention (`ChemistrySemantics.takeBracketParity` maps
`@@` to `clockwise` and `@` to `anticlockwise`) the kernel-checked `source_parse` of
`ConstitutionalRootStageAvailability` materializes the source atoms C2 clockwise, C0 clockwise,
C3 anticlockwise.  The string written with the opposite bracket pattern is the enantiomer under
this convention and is not used anywhere below.

The scientific distinction formalized here is:

* a *real* occurrence with no recorded auxiliary fact is `unavailable` (unknown), never
  `knownNonchiral` (proven non-bearing);
* the `occurrenceNodePriority` fallback `0` for an absent fact is an availability result, not a
  chemical/non-bearing verdict;
* at the accepted root C2 the actual production auxiliary state `[c3Fact, c0AuxFact]` and the
  empty auxiliary state produce the *same* occurrence fact and the same accepted descriptor `R`;
* at the auxiliary occurrence C0 the absence of a fact at the C2 arm is load-bearing for the
  *occurrence-local* label: the missing arm receives Rule-4a priority `0` while the C3 arm receives
  `2`, and the actual decision changes from `eq` (empty state) to `lt` (`[c3Fact]`).  This is not the
  accepted final descriptor at C2.

The separation certificate is a concrete computation over the twelve ordered pairs of C2's actual
four-ligand frame: every ordered pair of distinct cursors has a *strict* actual framed
constitutional result, so C2's resolved frame is `RootsConstitutionallySeparated`.  That certificate
is consumed directly by the existing theorem
`RawFramedConstitutionalIndependence.framedOccurrenceFactAuthoritative?_state_independent`, which
lifts pair locality through the actual tracked sorter and adjacency pass; no bespoke read-set layer
is introduced.  The resulting `c2_framed_fact_any_state` and `c2_occurrence_fact_any_state` quantify
over *every* auxiliary state, so the accepted C2 fact `c2Fact` and its descriptor `R` do not depend
on auxiliary availability at all.

No production function, comparator, parser, filter, or stored distance is modified.  Every
scientific export below is guarded by `assert_kernel_only`.
-/

namespace TetraStereo
namespace OneCenter
namespace RawAuxiliaryAvailabilitySemantics

open RawMolecule
open ConstitutionalRootStageAvailability

/-! ## The actual C2 frame and its ordered pairs -/

/-- The actual C2 ligand frame, in the order produced by `occurrenceLigandCursors`: methyl carbon,
bracket H, Cl, middle carbon C0. -/
def c2Roots : List CanonicalRerootCursor :=
  [methylCursor, hCursor, clCursor, middleCursor]

/-- The twelve ordered pairs of distinct members of the actual C2 frame. -/
def c2RootPairList : List (CanonicalRerootCursor × CanonicalRerootCursor) :=
  [ (methylCursor, hCursor)
  , (methylCursor, clCursor)
  , (methylCursor, middleCursor)
  , (hCursor, methylCursor)
  , (hCursor, clCursor)
  , (hCursor, middleCursor)
  , (clCursor, methylCursor)
  , (clCursor, hCursor)
  , (clCursor, middleCursor)
  , (middleCursor, methylCursor)
  , (middleCursor, hCursor)
  , (middleCursor, clCursor) ]

/-- The concrete frame order is the production frame order. -/
theorem c2Roots_eq_ligandCursors :
    c2Roots = occurrenceLigandCursors mol c2Root := by
  decide

/-- Every ordered pair of distinct actual frame members occurs in the twelve-pair list. -/
theorem c2Roots_pairList_complete (left right : CanonicalRerootCursor)
    (hleft : left ∈ c2Roots) (hright : right ∈ c2Roots) (hne : left ≠ right) :
    (left, right) ∈ c2RootPairList := by
  simp only [c2Roots, List.mem_cons, List.not_mem_nil, or_false] at hleft hright
  rcases hleft with rfl | rfl | rfl | rfl <;>
    rcases hright with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | decide

/-! ## Lifting pair-level locality to the accepted evaluator

The intrinsic separation certificate below is a concrete computation over the twelve ordered pairs;
it assumes no order, no sort output, and no evaluator equality.  It is then fed to the established
state-independence theorem of the actual framed evaluator. -/

theorem c2Roots_nodup : c2Roots.Nodup := by
  rw [c2Roots_eq_ligandCursors]
  exact ConstitutionalRootStageAvailability.frame_membership.2.1

/-- The concrete separation certificate: every ordered pair in the actual frame has a *strict*
actual framed constitutional result (not `none`, not `eq`). -/
theorem c2RootPairList_separated :
    c2RootPairList.all (fun pair =>
      match FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
          (FrameRuntime.Cursor.actual pair.1) (FrameRuntime.Cursor.actual pair.2) with
      | some order => decide (order ≠ Ordering.eq)
      | none => false) = true := by
  decide

theorem c2RootPairList_separated_of_mem (left right : CanonicalRerootCursor)
    (hmem : (left, right) ∈ c2RootPairList) :
    ∃ order : Ordering, order ≠ Ordering.eq ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some order := by
  have hall : ∀ pair ∈ c2RootPairList,
      (match FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
          (FrameRuntime.Cursor.actual pair.1) (FrameRuntime.Cursor.actual pair.2) with
      | some order => decide (order ≠ Ordering.eq)
      | none => false) = true :=
    List.all_eq_true.mp c2RootPairList_separated
  have hpair := hall (left, right) hmem
  have hpair' : (match FrameRuntime.compareBranch? mol c2Profile true fuel
      CanonicalRuleStage.rule2
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) with
    | some order => decide (order ≠ Ordering.eq)
    | none => false) = true := by
    simpa using hpair
  cases hcomp : FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) with
  | none =>
      rw [hcomp] at hpair'
      simp at hpair'
  | some order =>
      rw [hcomp] at hpair'
      exact ⟨order, of_decide_eq_true (by simpa using hpair'), rfl⟩

theorem c2Roots_pairSeparated (left right : CanonicalRerootCursor)
    (hleft : left ∈ c2Roots) (hright : right ∈ c2Roots) (hne : left ≠ right) :
    ∃ order : Ordering, order ≠ Ordering.eq ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some order :=
  c2RootPairList_separated_of_mem left right
    (c2Roots_pairList_complete left right hleft hright hne)

/-- The actual resolved C2 frame satisfies the existing separation hypothesis of the framed
evaluator.  Nothing about sorting, order, or evaluator output is assumed. -/
theorem c2Roots_separated :
    RawFramedConstitutionalIndependence.RootsConstitutionallySeparated
      mol c2Profile fuel c2Roots :=
  ⟨c2Roots_nodup, fun left hleft right hright hne =>
    c2Roots_pairSeparated left right hleft hright hne⟩

/-- **Pair-level locality theorem.**  Every distinct ordered pair of actual C2 frame cursors gives
the same complete framed decision in every auxiliary state.  This is the existing imported
state-independence theorem applied to the concrete frame certificate, not a re-derived generic
read-set argument. -/
theorem c2Roots_decision_state_independent (left right : CanonicalRerootCursor)
    (hleft : left ∈ c2Roots) (hright : right ∈ c2Roots) (hne : left ≠ right) :
    ∀ state state' : OccurrenceAuxState,
      FrameRuntime.decisionComplete? mol c2Profile true state fuel left right =
        FrameRuntime.decisionComplete? mol c2Profile true state' fuel left right :=
  fun state state' =>
    RawFramedConstitutionalIndependence.decisionComplete?_state_independent_of_separated
      mol c2Profile fuel c2Roots state state'
      (fun a ha b hb hne' => c2Roots_pairSeparated a b ha hb hne') hleft hright hne

/-! ## The accepted C2 fact is state-independent for every auxiliary state

The existing theorem `framedOccurrenceFactAuthoritative?_state_independent` consumes exactly the
separation certificate just proved.  Its statement quantifies over *arbitrary* pair states, so the
only remaining input is the empty-state value already computed in
`ConstitutionalRootStageAvailability.c2_empty_state_facts`.  This yields the all-state form, not
merely a comparison of the two states that happen to occur on the current production path. -/

theorem c2_framed_fact_state_independent (state₁ state₂ : OccurrenceAuxState) :
    framedOccurrenceFactAuthoritative? mol fuel state₁ c2Root =
      framedOccurrenceFactAuthoritative? mol fuel state₂ c2Root := by
  have hframe : occurrenceLigandFrame? mol c2Root = some c2Roots := by
    rw [c2Roots_eq_ligandCursors]
    exact ConstitutionalRootStageAvailability.frame_membership.2.2.2.1
  exact
    RawFramedConstitutionalIndependence.framedOccurrenceFactAuthoritative?_state_independent
      mol fuel c2Root c2Profile c2Roots state₁ state₂
      ConstitutionalRootStageAvailability.profiles_resolve.1 hframe c2Roots_separated

/-- The actual framed evaluator returns the accepted C2 fact in **every** auxiliary state. -/
theorem c2_framed_fact_any_state (state : OccurrenceAuxState) :
    framedOccurrenceFactAuthoritative? mol fuel state c2Root = some c2Fact := by
  rw [c2_framed_fact_state_independent state [],
    ← occurrenceFactAuthoritative?_eq_framed_of_profile_some mol fuel [] c2Root c2Profile
      ConstitutionalRootStageAvailability.profiles_resolve.1]
  exact ConstitutionalRootStageAvailability.c2_empty_state_facts.2.1

/-- The public selected evaluator (`occurrenceFactAuthoritative?`, which is
`framedOccurrenceFactAuthoritative?` here because the actual profile resolves) returns the same C2
fact in every auxiliary state.  In particular the unavailable C2-arm fact at C0 cannot influence
the accepted root descriptor: it is not even read. -/
theorem c2_occurrence_fact_any_state (state : OccurrenceAuxState) :
    occurrenceFactAuthoritative? mol fuel state c2Root = some c2Fact := by
  rw [occurrenceFactAuthoritative?_eq_framed_of_profile_some mol fuel state c2Root c2Profile
    ConstitutionalRootStageAvailability.profiles_resolve.1]
  exact c2_framed_fact_any_state state

/-! ## Unknown versus proven non-bearing -/

/-- A real occurrence with no recorded fact is `unavailable` and is never `knownNonchiral`.  The
`none` classification is a refusal to conclude, not a proof of non-bearing. -/
theorem missing_real_fact_classification (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance = CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none) :
    occurrenceSelectorChiralityClassification? state cursor = none ∧
      occurrenceSelectorChiralityClass state cursor = .unavailable ∧
      occurrenceSelectorChiralityClass state cursor ≠ .knownNonchiral := by
  exact ⟨(occurrenceSelectorChiralityClassification?_eq_none_iff state cursor).mpr
            ⟨hProvenance, hMissing⟩,
         occurrenceSelectorChiralityClass_eq_unavailable_of_missing state cursor
           hProvenance hMissing,
         occurrenceSelectorChiralityClass_ne_knownNonchiral_of_real state cursor hProvenance⟩

/-- The production classifier's `knownNonchiral` verdict is exactly non-real provenance. -/
theorem knownNonchiral_iff_nonReal (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    occurrenceSelectorChiralityClass state cursor = .knownNonchiral ↔
      cursor.node.provenance ≠ CanonicalNodeProvenance.realAtom :=
  occurrenceSelectorChiralityClass_eq_knownNonchiral_iff state cursor

/-! ## Priority semantics of an absent fact -/

/-- An absent fact gives priority `0` at every stage and side.  This is the fallback branch of
`occurrenceNodePriority`, independent of any chemical reading. -/
theorem occurrenceNodePriority_eq_zero_of_factAt?_eq_none
    (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (cursor : CanonicalRerootCursor)
    (hMissing : state.factAt? cursor.node = none) :
    occurrenceNodePriority state stage leftSide cursor = 0 := by
  cases hprovenance : cursor.node.provenance <;>
    simp [occurrenceNodePriority, hprovenance, hMissing]

/-- When the fact is present and the provenance is real, Rule-4a priority is the uppercase-dependent
`2` or `1`. -/
theorem occurrenceNodePriority_rule4a_eq_of_factAt?_eq_some
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (fact : OccurrenceAuxFact) (leftSide : Bool)
    (hProvenance : cursor.node.provenance = CanonicalNodeProvenance.realAtom)
    (hFact : state.factAt? cursor.node = some fact) :
    occurrenceNodePriority state RawDescriptorRuleStage.rule4a leftSide cursor =
      if fact.uppercase then 2 else 1 := by
  simp [occurrenceNodePriority, hProvenance, hFact]

theorem occurrenceNodePriority_rule4a_eq_two_of_uppercase
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (fact : OccurrenceAuxFact) (leftSide : Bool)
    (hProvenance : cursor.node.provenance = CanonicalNodeProvenance.realAtom)
    (hFact : state.factAt? cursor.node = some fact)
    (hUppercase : fact.uppercase = true) :
    occurrenceNodePriority state RawDescriptorRuleStage.rule4a leftSide cursor = 2 := by
  rw [occurrenceNodePriority_rule4a_eq_of_factAt?_eq_some state cursor fact leftSide
        hProvenance hFact, hUppercase]
  rfl

/-- **Fallback priority `0` is not a non-bearing verdict.**  At a real occurrence with no recorded
fact, priority is `0` while the selector classification is `unavailable` and provably not
`knownNonchiral`. -/
theorem priority_zero_of_missing_is_not_nonbearing
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (hProvenance : cursor.node.provenance = CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none) :
    occurrenceNodePriority state stage leftSide cursor = 0 ∧
      occurrenceSelectorChiralityClass state cursor ≠ .knownNonchiral := by
  exact ⟨occurrenceNodePriority_eq_zero_of_factAt?_eq_none state stage leftSide cursor hMissing,
    occurrenceSelectorChiralityClass_ne_knownNonchiral_of_real state cursor hProvenance⟩

/-! ## The actual C0 missing-fact witness -/

/-- The C2 fact is keyed exactly at the original root. -/
theorem c2Fact_key_eq_canonicalRootKey :
    c2Fact.key = canonicalOccurrenceKey c2Root := by
  decide

/-- If a state carried the actual `c2Fact` at the C2 arm key, Rule-4a priority at that arm would be
`2` (the fact is uppercase).  This is a universally quantified availability statement; it does not
assert that any production state actually contains this fact at that key. -/
theorem c2Arm_rule4a_priority_two_if_c2Fact_available
    (state : OccurrenceAuxState) (leftSide : Bool)
    (hFact : state.factAt? c2ArmCursor.node = some c2Fact) :
    occurrenceNodePriority state RawDescriptorRuleStage.rule4a leftSide c2ArmCursor = 2 :=
  occurrenceNodePriority_rule4a_eq_two_of_uppercase state c2ArmCursor c2Fact leftSide
    (by decide) hFact (by decide)

/-- **Minimal actual missing-fact witness at C0.**

In the actually produced batch state `[c3Fact]` the C2 arm of the framed C0 comparison has no fact.
Its Rule-4a priority is therefore the fallback `0`, while the C3 arm, which does carry `c3Fact`,
has priority `2`.  The selector classification of the C2 arm is `unavailable`, not
`knownNonchiral`.  The final conjunct records that availability, not chemistry, is what changes the
priority: any state carrying the actual uppercase `c2Fact` at this key would give priority `2`.

The state `[c3Fact]` is the exact batch state produced immediately before C0 is labelled
(`occurrence_production_facts` in `ConstitutionalRootStageAvailability`). -/
theorem c0_minimal_missing_fact_witness :
    OccurrenceAuxState.factAt? [c3Fact] c2ArmCursor.node = none ∧
      c2ArmCursor.node.provenance = CanonicalNodeProvenance.realAtom ∧
      occurrenceNodePriority [c3Fact] RawDescriptorRuleStage.rule4a true c2ArmCursor = 0 ∧
      occurrenceNodePriority [c3Fact] RawDescriptorRuleStage.rule4a false c3ArmCursor = 2 ∧
      occurrenceSelectorChiralityClassification? [c3Fact] c2ArmCursor = none ∧
      occurrenceSelectorChiralityClass [c3Fact] c2ArmCursor = .unavailable ∧
      occurrenceSelectorChiralityClass [c3Fact] c2ArmCursor ≠ .knownNonchiral ∧
      (∀ state : OccurrenceAuxState,
        state.factAt? c2ArmCursor.node = some c2Fact →
          occurrenceNodePriority state RawDescriptorRuleStage.rule4a true c2ArmCursor = 2) := by
  have hMissing : OccurrenceAuxState.factAt? [c3Fact] c2ArmCursor.node = none := by
    decide
  have hProvenance : c2ArmCursor.node.provenance = CanonicalNodeProvenance.realAtom := by
    decide
  obtain ⟨_, _, _, _, _, hPriorityC3⟩ := c0_framed_state_sensitivity
  exact ⟨hMissing,
    hProvenance,
    occurrenceNodePriority_eq_zero_of_factAt?_eq_none [c3Fact]
      RawDescriptorRuleStage.rule4a true c2ArmCursor hMissing,
    hPriorityC3,
    (occurrenceSelectorChiralityClassification?_eq_none_iff [c3Fact] c2ArmCursor).mpr
      ⟨hProvenance, hMissing⟩,
    occurrenceSelectorChiralityClass_eq_unavailable_of_missing [c3Fact] c2ArmCursor
      hProvenance hMissing,
    occurrenceSelectorChiralityClass_ne_knownNonchiral_of_real [c3Fact] c2ArmCursor
      hProvenance,
    fun state hFact => c2Arm_rule4a_priority_two_if_c2Fact_available state true hFact⟩

/-- The actual framed C0 decision changes when the C3 fact becomes available. C2 is absent in
both states: the empty state ties,
the real batch state `[c3Fact]` separates as `lt` because of the priority `0` vs `2` witness. -/
theorem c0_auxiliary_decision_changes_when_c3_fact_available :
    FrameRuntime.decisionComplete? mol c0Profile true [] fuel c2ArmCursor c3ArmCursor =
        some { ordering := Ordering.eq } ∧
      FrameRuntime.decisionComplete? mol c0Profile true [c3Fact] fuel c2ArmCursor
          c3ArmCursor = some { ordering := Ordering.lt } := by
  obtain ⟨hEmpty, hBatch, _⟩ := c0_framed_state_sensitivity
  exact ⟨hEmpty, hBatch⟩

/-- The C0 label is occurrence-local and is not the accepted root fact. -/
theorem c0AuxFact_not_accepted_root_fact :
    c0AuxFact.atom ≠ c2ProductionFact.atom ∧
      c0AuxFact.key ≠ canonicalOccurrenceKey c2Root ∧
      c0AuxFact.descriptor = RS.S ∧
      c2ProductionFact.descriptor = RS.R := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-! ## The actual accepted root C2 is insensitive to the produced auxiliary state -/

/-- The actual production builder state for center C2 is `[c3Fact, c0AuxFact]`. -/
theorem c2_production_aux_state :
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel c2Atom = some [c3Fact, c0AuxFact] :=
  aux_state_production.2

/-- That state contains no fact keyed at the root C2 itself: the auxiliary-occurrence filter excludes
the centre under evaluation. -/
theorem c2_root_absent_from_production_aux_state :
    OccurrenceAuxState.factAt? [c3Fact, c0AuxFact] c2Root = none :=
  aux_state_properties.2.1

/-- **Accepted-descriptor invariance over the actual produced auxiliary facts.**

The empty auxiliary state and the actually produced state `[c3Fact, c0AuxFact]` both evaluate C2 to
the same fact, and the production entry point returns `c2ProductionFact` with descriptor `R`. -/
theorem c2_accepted_fact_independent_of_production_auxiliary_facts :
    OccurrenceAuxState.factAt? [c3Fact, c0AuxFact] c2Root = none ∧
      occurrenceFactAuthoritative? mol fuel [] c2Root = some c2Fact ∧
      occurrenceFactAuthoritative? mol fuel [c3Fact, c0AuxFact] c2Root = some c2Fact ∧
      tetrahedralOccurrenceFactAuthoritative? mol fuel c2Atom = some c2ProductionFact := by
  obtain ⟨_, hEmpty, hProduction⟩ := c2_empty_state_facts
  exact ⟨aux_state_properties.2.1, hEmpty, hProduction, production_fact_c2⟩

/-- Consequently the accepted descriptor is `R` in the empty state, in the actual production state,
and at the production entry point. -/
theorem c2_accepted_descriptor_R_independent_of_auxiliary_availability :
    (occurrenceFactAuthoritative? mol fuel [] c2Root).map
        (fun fact => fact.descriptor) = some RS.R ∧
      (occurrenceFactAuthoritative? mol fuel [c3Fact, c0AuxFact] c2Root).map
        (fun fact => fact.descriptor) = some RS.R ∧
      (tetrahedralOccurrenceFactAuthoritative? mol fuel c2Atom).map
        (fun fact => fact.descriptor) = some RS.R := by
  obtain ⟨_, hEmpty, hProduction⟩ := c2_empty_state_facts
  exact ⟨by rw [hEmpty]; rfl, by rw [hProduction]; rfl, c2_final_descriptor_R⟩

/-! ## The structural candidate policy at the missing C2 arm -/

/-- The C2 arm has a complete four-ligand frame, so the terminal-vertex structural branch cannot
apply. -/
theorem c2Arm_ligandCount_four :
    (mol.ligandsWithLonePair c2ArmCursor.node.atom).length = 4 := by
  decide

/-- The geometric producer's structural route at the C2 arm is exactly the uniform-terminal-arms
condition.  The terminal-vertex branch is excluded by the four-ligand count. -/
theorem c2Arm_structural_fact_iff_uniformTerminalArms :
    occurrenceStructuralNonbearingFact? mol c2ArmCursor = none ↔
      ¬ Nonempty (UniformTerminalArmData mol c2ArmCursor) := by
  rw [occurrenceStructuralNonbearingFact?_eq_none_iff]
  constructor
  · intro hNoStructural hArms
    exact hNoStructural ⟨by decide, Or.inr hArms⟩
  · intro hNoArms hConjunction
    rcases hConjunction with ⟨_, hCount | hArms⟩
    · rw [c2Arm_ligandCount_four] at hCount
      exact Nat.lt_irrefl 4 hCount
    · exact hNoArms hArms

/-- The production selector nevertheless classifies the missing C2 arm as `unavailable`, not
`knownNonchiral`: the structural candidate producer is not part of the accepted evaluator. -/
theorem c2Arm_missing_fact_is_unknown_not_nonbearing :
    occurrenceSelectorChiralityClassification? [c3Fact] c2ArmCursor = none ∧
      occurrenceSelectorChiralityClass [c3Fact] c2ArmCursor = .unavailable ∧
      occurrenceSelectorChiralityClass [c3Fact] c2ArmCursor ≠ .knownNonchiral := by
  have hMissing : OccurrenceAuxState.factAt? [c3Fact] c2ArmCursor.node = none := by
    decide
  have hProvenance : c2ArmCursor.node.provenance = CanonicalNodeProvenance.realAtom := by
    decide
  exact missing_real_fact_classification [c3Fact] c2ArmCursor hProvenance hMissing

/-! ## Parse provenance re-export -/

/-- The corrected actual string parses to the concrete source used below. -/
theorem actual_smiles_parse :
    parseOpenSMILES smiles = Except.ok source :=
  source_parse

end RawAuxiliaryAvailabilitySemantics
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Roots
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2RootPairList
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Roots_eq_ligandCursors
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Roots_pairList_complete
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Roots_nodup
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2RootPairList_separated
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2RootPairList_separated_of_mem
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Roots_pairSeparated
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Roots_separated
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Roots_decision_state_independent
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2_framed_fact_state_independent
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2_framed_fact_any_state
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2_occurrence_fact_any_state
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.missing_real_fact_classification
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.knownNonchiral_iff_nonReal
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.occurrenceNodePriority_eq_zero_of_factAt?_eq_none
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.occurrenceNodePriority_rule4a_eq_of_factAt?_eq_some
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.occurrenceNodePriority_rule4a_eq_two_of_uppercase
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.priority_zero_of_missing_is_not_nonbearing
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Fact_key_eq_canonicalRootKey
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Arm_rule4a_priority_two_if_c2Fact_available
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c0_minimal_missing_fact_witness
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c0_auxiliary_decision_changes_when_c3_fact_available
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c0AuxFact_not_accepted_root_fact
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2_production_aux_state
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2_root_absent_from_production_aux_state
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2_accepted_fact_independent_of_production_auxiliary_facts
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2_accepted_descriptor_R_independent_of_auxiliary_availability
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Arm_ligandCount_four
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Arm_structural_fact_iff_uniformTerminalArms
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.c2Arm_missing_fact_is_unknown_not_nonbearing
assert_kernel_only TetraStereo.OneCenter.RawAuxiliaryAvailabilitySemantics.actual_smiles_parse
