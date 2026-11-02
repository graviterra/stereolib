import TetraStereo.Certificate.DependencySource
import TetraStereo.UniversalProof.NextFrontier.ParsedParitySameSourceModel

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace TetraStereo.Certificate.ParsedParityDependencyAdapter

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.Certificate.Dependency
open TetraStereo.UniversalProof.FramedParsedParityFamily
open TetraStereo.UniversalProof.FramedParsedParitySeed
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
open TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySameSourceModel

/-! The fixed eight-member parsed family has two descriptor-independent arm seeds
and a descriptor-dependent center. Certificates serialize precisely those three
root-relative occurrences, not arbitrary atom numbers. The center must reference
both established arm records in their physical order. The local evaluator reads the
actual parsed/normalized molecule and recomputes the existing runtime operation.

Source meaning is independently bound to the existing own-source occurrence model.
The adapter proves preservation of that meaning on certified inputs. It does not
claim unrestricted runtime/source correspondence for arbitrary fabricated states,
nor does it equate this compressed descriptor graph to every occurrence-depth edge.
It establishes neither unbounded molecular coverage nor cyclic certificates. -/

inductive Occurrence where
  | leftArm | rightArm | center
  deriving DecidableEq, Repr

def atom : Occurrence → Nat
  | .leftArm => 2
  | .rightArm => 7
  | .center => 1

def dependencies : Occurrence → List Occurrence
  | .leftArm | .rightArm => []
  | .center => [.leftArm, .rightArm]

noncomputable def sourceTarget (c l r : TetrahedralInputParity) :
    Occurrence → (ownSource (raw c l r)).AromaticCanonicalOccurrence 1
  | .leftArm => armTarget c l r true
  | .rightArm => armTarget c l r false
  | .center => centralTarget c l r

private theorem occurrence_atom_of_node (source : AuthoritativeChemicalInput) (fuel : Nat)
    (target : source.AromaticCanonicalOccurrence fuel)
    (parent current : source.AromaticCanonicalAtom)
    (node : target.1.node = OfficialCIPNode.rootFromEdge parent current) :
    target.1.node.current?.map Fin.val = some current.val := by
  exact congrArg (fun value : OfficialCIPNode source.AromaticCanonicalAtom =>
    value.current?.map Fin.val) node

private theorem final_occurrence_atom (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    ((source.aromaticCanonicalFinalOccurrence fuel center).1.node.current?).map Fin.val =
      some center.1.val := by
  rfl

theorem source_target_atom (c l r : TetrahedralInputParity) (target : Occurrence) :
    ((sourceTarget c l r target).1.node.current?).map Fin.val = some (atom target) := by
  cases target with
  | leftArm =>
      simpa only [sourceTarget, armTarget, atom, armIndex, ite_true] using
        (occurrence_atom_of_node (ownSource (raw c l r)) 1 (armCursor c l r true).occurrence
          (sourceCenter c l r).1 (armAtom c l r true) (arm_cursor_node c l r true)).trans
          (congrArg some (armAtom_index c l r true))
  | rightArm =>
      simpa only [sourceTarget, armTarget, atom, armIndex, Bool.false_eq_true, ite_false] using
        (occurrence_atom_of_node (ownSource (raw c l r)) 1 (armCursor c l r false).occurrence
          (sourceCenter c l r).1 (armAtom c l r false) (arm_cursor_node c l r false)).trans
          (congrArg some (armAtom_index c l r false))
  | center =>
      simpa only [sourceTarget, centralTarget, atom] using
        (final_occurrence_atom (ownSource (raw c l r)) 1 (sourceCenter c l r)).trans
          (congrArg some (sourceCenter_index c l r))

theorem dependencies_wellFounded : WellFounded (relation dependencies) := by
  have left : Acc (relation dependencies) Occurrence.leftArm := by
    constructor
    intro inner depends
    simp [relation, dependencies] at depends
  have right : Acc (relation dependencies) Occurrence.rightArm := by
    constructor
    intro inner depends
    simp [relation, dependencies] at depends
  constructor
  intro target
  cases target with
  | leftArm => exact left
  | rightArm => exact right
  | center =>
      constructor
      intro inner depends
      cases inner with
      | leftArm => exact left
      | rightArm => exact right
      | center => simp [relation, dependencies] at depends

/-- The two serialized references name actual arm occurrences below the same center. -/
theorem source_dependency (c l r : TetrahedralInputParity) (inner target : Occurrence)
    (depends : relation dependencies inner target) :
    (ownSource (raw c l r)).AromaticCanonicalDepthDependency
      (sourceTarget c l r inner) (sourceTarget c l r target) := by
  cases target with
  | leftArm => simp [relation, dependencies] at depends
  | rightArm => simp [relation, dependencies] at depends
  | center =>
      cases inner with
      | leftArm => exact arm_is_central_dependency c l r true
      | rightArm => exact arm_is_central_dependency c l r false
      | center => simp [relation, dependencies] at depends

def armFact (parity : TetrahedralInputParity) (index : Nat) : RawDescriptorFact :=
  { atom := index
    descriptor := descriptorOfParity parity false
    uppercase := true
    priorityPositions := [3, 2, 0, 1] }

/-- Mathematical finite-family candidates. These are certificate payload, never the evaluator. -/
def candidate (c l r : TetrahedralInputParity) : Occurrence → Option RawDescriptorFact
  | .leftArm => some (armFact l 2)
  | .rightArm => some (armFact r 7)
  | .center => centralCandidate c l r

/-- Actual independent seed discovery, with no certificate or auxiliary label input. -/
def actualSeeds (c l r : TetrahedralInputParity) : RawDescriptorState :=
  initialRawDescriptorState (actualResult c l r) (actualMol c l r) (actualFuel c l r)

def armState (state : Occurrence → Option RawDescriptorFact) : RawDescriptorState :=
  (state .leftArm).toList ++ (state .rightArm).toList

/-- Recomputes actual production operations. In particular the central outcome is not
read from `candidate`, `centralLabel`, a certificate field or a solved source model. -/
def localStep (c l r : TetrahedralInputParity)
    (state : Occurrence → Option RawDescriptorFact) : Occurrence → Option RawDescriptorFact
  | .leftArm => (actualSeeds c l r).factAt? 2
  | .rightArm => (actualSeeds c l r).factAt? 7
  | .center => tetrahedralFactFromState? (actualResult c l r) (actualMol c l r)
      (armState state) 100 (actualFuel c l r) 1

/-- Both exact runtime metadata and the label at the exact independent source occurrence. -/
def SourceMeaning (c l r : TetrahedralInputParity) (target : Occurrence)
    (outcome : Option RawDescriptorFact) : Prop :=
  outcome = candidate c l r target ∧
    familyScheduledState c l r (sourceTarget c l r target) = outcome.map runtimeFactLabel

/-- An operational adapter with independently bound source meaning. We deliberately
do not assert DerivationStepCorrespondence on arbitrary unvalidated environments. -/
def system (c l r : TetrahedralInputParity) : OccurrenceSystem Occurrence Occurrence RawDescriptorFact where
  finalOccurrence := id
  descriptorOf := fun fact => match fact.uppercase, fact.descriptor with
    | true, .R => .R | true, .S => .S | false, .R => .r | false, .S => .s
  DeclarativeDerivation := fun _ target outcome => SourceMeaning c l r target outcome
  executableStep := localStep c l r

private theorem system_step (c l r : TetrahedralInputParity)
    (state : Occurrence → Option RawDescriptorFact) (target : Occurrence) :
    (system c l r).executableStep state target = localStep c l r state target := by
  rfl

theorem evaluator_local (c l r : TetrahedralInputParity) :
    (system c l r).EvaluatorLocalFor (relation dependencies) := by
  intro first second target agree
  cases target with
  | leftArm => rfl
  | rightArm => rfl
  | center =>
      have left := agree .leftArm (by simp [relation, dependencies])
      have right := agree .rightArm (by simp [relation, dependencies])
      change localStep c l r first .center = localStep c l r second .center
      simp only [localStep, armState, left, right]

theorem actual_seeds (c l r : TetrahedralInputParity) :
    actualSeeds c l r = [armFact l 2, armFact r 7] :=
  actual_initial c l r

theorem local_arm (c l r : TetrahedralInputParity)
    (state : Occurrence → Option RawDescriptorFact) :
    localStep c l r state .leftArm = some (armFact l 2) ∧
      localStep c l r state .rightArm = some (armFact r 7) := by
  constructor
  · change (actualSeeds c l r).factAt? 2 = some (armFact l 2)
    rw [actual_seeds]
    rfl
  · change (actualSeeds c l r).factAt? 7 = some (armFact r 7)
    rw [actual_seeds]
    rfl

theorem local_center (c l r : TetrahedralInputParity)
    (state : Occurrence → Option RawDescriptorFact)
    (left : state .leftArm = some (armFact l 2))
    (right : state .rightArm = some (armFact r 7)) :
    localStep c l r state .center = centralCandidate c l r := by
  change tetrahedralFactFromState? (actualResult c l r) (actualMol c l r)
    (armState state) 100 (actualFuel c l r) 1 = _
  have seeded : armState state = expectedSeed l r := by
    simp only [armState, left, right, Option.toList_some, List.singleton_append]
    rfl
  rw [seeded]
  exact central_update_fact c l r

theorem candidate_source_meaning (c l r : TetrahedralInputParity) (target : Occurrence) :
    SourceMeaning c l r target (candidate c l r target) := by
  refine ⟨rfl, ?_⟩
  cases target with
  | leftArm =>
      rw [show sourceTarget c l r .leftArm = armTarget c l r true from rfl,
        arm_scheduled_descriptor]
      cases l <;> cases r <;> rfl
  | rightArm =>
      rw [show sourceTarget c l r .rightArm = armTarget c l r false from rfl,
        arm_scheduled_descriptor]
      cases l <;> cases r <;> rfl
  | center =>
      rw [show sourceTarget c l r .center = centralTarget c l r from rfl,
        central_scheduled_descriptor]
      cases c <;> cases l <;> cases r <;> decide +kernel

/-- The actual local operation preserves source meaning from meaningful references. -/
theorem local_source_sound (c l r : TetrahedralInputParity)
    (target : Occurrence)
    (inputs : ∀ inner, relation dependencies inner target → Option RawDescriptorFact)
    (meaning : ∀ inner h, SourceMeaning c l r inner (inputs inner h)) :
    SourceMeaning c l r target ((system c l r).executableStep
      ((system c l r).dependencyEnvironment (relation dependencies) target inputs) target) := by
  cases target with
  | leftArm =>
      rw [system_step, (local_arm c l r
        ((system c l r).dependencyEnvironment (relation dependencies) .leftArm inputs)).1]
      exact candidate_source_meaning c l r .leftArm
  | rightArm =>
      rw [system_step, (local_arm c l r
        ((system c l r).dependencyEnvironment (relation dependencies) .rightArm inputs)).2]
      exact candidate_source_meaning c l r .rightArm
  | center =>
      have leftDep : relation dependencies .leftArm .center := by simp [relation, dependencies]
      have rightDep : relation dependencies .rightArm .center := by simp [relation, dependencies]
      have left := (meaning .leftArm leftDep).1
      have right := (meaning .rightArm rightDep).1
      have leftValue : (system c l r).dependencyEnvironment (relation dependencies) .center inputs
          .leftArm = some (armFact l 2) := by
        simpa only [OccurrenceSystem.dependencyEnvironment, dif_pos leftDep, candidate] using left
      have rightValue : (system c l r).dependencyEnvironment (relation dependencies) .center inputs
          .rightArm = some (armFact r 7) := by
        simpa only [OccurrenceSystem.dependencyEnvironment, dif_pos rightDep, candidate] using right
      rw [system_step, local_center c l r
        ((system c l r).dependencyEnvironment (relation dependencies) .center inputs)
        leftValue rightValue]
      exact candidate_source_meaning c l r .center

def nodes (c l r : TetrahedralInputParity) : List (Node Occurrence RawDescriptorFact) :=
  [⟨.leftArm, candidate c l r .leftArm, []⟩,
   ⟨.rightArm, candidate c l r .rightArm, []⟩,
   ⟨.center, candidate c l r .center, [0, 1]⟩]

def facts (c l r : TetrahedralInputParity) : List (Fact Occurrence RawDescriptorFact) :=
  [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm),
   (.center, candidate c l r .center)]

/-- Keep checker recursion abstract so proof normalization cannot unfold the concrete
chemical evaluator while traversing the two already justified seed nodes. -/
private theorem check_three_after_two_valid
    {FinalUnit Target Label : Type} [DecidableEq Target] [DecidableEq Label]
    (abstractSystem : OccurrenceSystem FinalUnit Target Label)
    (dependencyList : Target → List Target)
    (first second third : Node Target Label)
    (firstValid : ValidNode abstractSystem dependencyList [] first)
    (secondValid : ValidNode abstractSystem dependencyList
      [(first.target, first.outcome)] second) :
    check abstractSystem dependencyList [first, second, third] =
      if ValidNode abstractSystem dependencyList
        [(first.target, first.outcome), (second.target, second.outcome)] third then
        some [(first.target, first.outcome), (second.target, second.outcome),
          (third.target, third.outcome)] else none := by
  change checkFrom abstractSystem dependencyList [] [first, second, third] = _
  rw [checkFrom, if_pos firstValid]
  change checkFrom abstractSystem dependencyList
    [(first.target, first.outcome)] [second, third] = _
  rw [checkFrom, if_pos secondValid]
  rfl

theorem check_after_arms (c l r : TetrahedralInputParity) (node : Node Occurrence RawDescriptorFact) :
    check (system c l r) dependencies
      [⟨.leftArm, candidate c l r .leftArm, []⟩,
       ⟨.rightArm, candidate c l r .rightArm, []⟩, node] =
      if ValidNode (system c l r) dependencies
        [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)] node then
        some [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm),
          (node.target, node.outcome)] else none := by
  have left : ValidNode (system c l r) dependencies []
      ⟨.leftArm, candidate c l r .leftArm, []⟩ := by
    refine ⟨by change ([] : List Nat).Nodup; decide, by simp, rfl, ?_⟩
    exact ((system_step c l r (lookup (referenced [] [])) .leftArm).trans
      (local_arm c l r (lookup (referenced [] []))).1).symm
  have right : ValidNode (system c l r) dependencies
      [(.leftArm, candidate c l r .leftArm)]
      ⟨.rightArm, candidate c l r .rightArm, []⟩ := by
    refine ⟨by change ([] : List Nat).Nodup; decide, by simp, rfl, ?_⟩
    exact ((system_step c l r
      (lookup (referenced [(.leftArm, candidate c l r .leftArm)] [])) .rightArm).trans
      (local_arm c l r
        (lookup (referenced [(.leftArm, candidate c l r .leftArm)] []))).2).symm
  exact check_three_after_two_valid (system c l r) dependencies
    ⟨.leftArm, candidate c l r .leftArm, []⟩
    ⟨.rightArm, candidate c l r .rightArm, []⟩ node left right

theorem nodes_accepted (c l r : TetrahedralInputParity) :
    check (system c l r) dependencies (nodes c l r) = some (facts c l r) := by
  have center : ValidNode (system c l r) dependencies
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      ⟨.center, candidate c l r .center, [0, 1]⟩ := by
    refine ⟨by change ([0, 1] : List Nat).Nodup; decide, by simp, rfl, ?_⟩
    exact ((system_step c l r (lookup (referenced
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      [0, 1])) .center).trans
      (local_center c l r (lookup (referenced
        [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
        [0, 1])) (by rfl) (by rfl))).symm
  simp only [nodes, facts, check_after_arms, if_pos center]

/-- A successful certificate can justify absence of a central label. This is not
checker failure; the actual public refusal is joined by `checked_public_center`. -/
theorem equal_arm_none_verified (c arm : TetrahedralInputParity) :
    (check (system c arm arm) dependencies (nodes c arm arm)).map
      (fun accepted => lookup accepted .center) = some none := by
  rw [nodes_accepted]
  cases c <;> cases arm <;> decide +kernel

theorem opposite_arm_lowercase_verified (c l r : TetrahedralInputParity) (opposite : l ≠ r) :
    (check (system c l r) dependencies (nodes c l r)).map
      (fun accepted => (lookup accepted .center).map RawDescriptorFact.uppercase) = some (some false) := by
  rw [nodes_accepted]
  cases c <;> cases l <;> cases r <;> first | exact absurd rfl opposite | decide +kernel

def withCenterReferences (c l r : TetrahedralInputParity) (references : List Nat) :
    List (Node Occurrence RawDescriptorFact) :=
  [⟨.leftArm, candidate c l r .leftArm, []⟩,
   ⟨.rightArm, candidate c l r .rightArm, []⟩,
   ⟨.center, candidate c l r .center, references⟩]

theorem missing_reference_rejected (c l r : TetrahedralInputParity) :
    check (system c l r) dependencies (withCenterReferences c l r [0]) = none := by
  rw [withCenterReferences, check_after_arms]
  have invalid : ¬ ValidNode (system c l r) dependencies
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      ⟨.center, candidate c l r .center, [0]⟩ := by
    intro valid
    have domain := valid.2.2.1
    change [Occurrence.leftArm] = [Occurrence.leftArm, Occurrence.rightArm] at domain
    cases domain
  exact if_neg invalid

theorem swapped_reference_rejected (c l r : TetrahedralInputParity) :
    check (system c l r) dependencies (withCenterReferences c l r [1, 0]) = none := by
  rw [withCenterReferences, check_after_arms]
  have invalid : ¬ ValidNode (system c l r) dependencies
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      ⟨.center, candidate c l r .center, [1, 0]⟩ := by
    intro valid
    have domain := valid.2.2.1
    change [Occurrence.rightArm, Occurrence.leftArm] =
      [Occurrence.leftArm, Occurrence.rightArm] at domain
    cases domain
  exact if_neg invalid

theorem forward_reference_rejected (c l r : TetrahedralInputParity) :
    check (system c l r) dependencies (withCenterReferences c l r [0, 2]) = none := by
  rw [withCenterReferences, check_after_arms]
  have invalid : ¬ ValidNode (system c l r) dependencies
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      ⟨.center, candidate c l r .center, [0, 2]⟩ := by
    intro valid
    have bound := valid.2.1 2 (by simp)
    change 2 < 2 at bound
    omega
  exact if_neg invalid

theorem duplicate_reference_rejected (c l r : TetrahedralInputParity) :
    check (system c l r) dependencies (withCenterReferences c l r [0, 0]) = none := by
  rw [withCenterReferences, check_after_arms]
  have invalid : ¬ ValidNode (system c l r) dependencies
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      ⟨.center, candidate c l r .center, [0, 0]⟩ := by
    intro valid
    have distinct := valid.1
    simp at distinct
  exact if_neg invalid

private theorem invalid_node_of_wrong_outcome
    {FinalUnit Target Label : Type} [DecidableEq Target]
    (abstractSystem : OccurrenceSystem FinalUnit Target Label)
    (dependencyList : Target → List Target)
    (priorFacts : List (Fact Target Label)) (node : Node Target Label)
    (expected : Option Label)
    (computed : abstractSystem.executableStep
      (lookup (referenced priorFacts node.references)) node.target = expected)
    (different : node.outcome ≠ expected) :
    ¬ ValidNode abstractSystem dependencyList priorFacts node := by
  intro valid
  exact different (valid.2.2.2.trans computed)

/-- Keep the runtime equality conversion symbolic before specializing a wrong payload
to concrete parities. The actual local evaluator and checker remain unchanged. -/
private theorem wrong_central_outcome_rejected (c l r : TetrahedralInputParity)
    (wrong : Option RawDescriptorFact) (different : wrong ≠ centralCandidate c l r) :
    check (system c l r) dependencies
      [⟨.leftArm, candidate c l r .leftArm, []⟩,
       ⟨.rightArm, candidate c l r .rightArm, []⟩,
       ⟨.center, wrong, [0, 1]⟩] = none := by
  have invalid : ¬ ValidNode (system c l r) dependencies
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      ⟨.center, wrong, [0, 1]⟩ := by
    refine invalid_node_of_wrong_outcome (system c l r) dependencies
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      ⟨.center, wrong, [0, 1]⟩ (centralCandidate c l r) ?_ different
    exact (system_step c l r (lookup (referenced
      [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
      [0, 1])) .center).trans
      (local_center c l r (lookup (referenced
        [(.leftArm, candidate c l r .leftArm), (.rightArm, candidate c l r .rightArm)]
        [0, 1])) (by rfl) (by rfl))
  exact (check_after_arms c l r ⟨.center, wrong, [0, 1]⟩).trans (if_neg invalid)

/-- Changing only the proposed central written parity cannot reuse the certificate for the
opposite marker. The actual molecule remains the anticlockwise-center, R/S-arm input. -/
theorem changed_central_parity_rejected :
    check (system .anticlockwise .anticlockwise .clockwise) dependencies
      [⟨.leftArm, candidate .anticlockwise .anticlockwise .clockwise .leftArm, []⟩,
       ⟨.rightArm, candidate .anticlockwise .anticlockwise .clockwise .rightArm, []⟩,
       ⟨.center, candidate .clockwise .anticlockwise .clockwise .center, [0, 1]⟩] = none := by
  have different : candidate .clockwise .anticlockwise .clockwise .center ≠
      candidate .anticlockwise .anticlockwise .clockwise .center := by decide +kernel
  exact wrong_central_outcome_rejected .anticlockwise .anticlockwise .clockwise
    (candidate .clockwise .anticlockwise .clockwise .center) different

/-- Arbitrary accepted payloads agree with the independently constructed own-source
model, including equal-arm `none`, and preserve every runtime metadata field. -/
theorem checked_source_agreement (c l r : TetrahedralInputParity)
    (payload : List (Node Occurrence RawDescriptorFact))
    (result : List (Fact Occurrence RawDescriptorFact))
    (accepted : check (system c l r) dependencies payload = some result)
    (fact : Fact Occurrence RawDescriptorFact) (member : fact ∈ result) :
    SourceMeaning c l r fact.1 fact.2 :=
  DependencySource.checked_source_sound (system c l r) dependencies (SourceMeaning c l r)
    (local_source_sound c l r) payload result accepted fact member

theorem incorrect_payload_not_accepted (c l r : TetrahedralInputParity)
    (payload : List (Node Occurrence RawDescriptorFact))
    (result : List (Fact Occurrence RawDescriptorFact))
    (fact : Fact Occurrence RawDescriptorFact) (member : fact ∈ result)
    (incorrect : fact.2 ≠ candidate c l r fact.1) :
    check (system c l r) dependencies payload ≠ some result := by
  intro accepted
  exact incorrect (checked_source_agreement c l r payload result accepted fact member).1

/-- The same checked central label is the actual public assigned/refused outcome. -/
theorem checked_public_center (c l r : TetrahedralInputParity)
    (payload : List (Node Occurrence RawDescriptorFact))
    (result : List (Fact Occurrence RawDescriptorFact))
    (accepted : check (system c l r) dependencies payload = some result)
    (outcome : Option RawDescriptorFact) (member : (.center, outcome) ∈ result) :
    annotatedTetrahedralOutcome? (actualResult c l r) (actualMol c l r)
      (discoverRawDescriptors (actualResult c l r) (actualMol c l r) (actualFuel c l r))
      (actualFuel c l r) 1 = some (sourceOutcome (outcome.map runtimeFactLabel)) := by
  have source := (checked_source_agreement c l r payload result accepted (.center, outcome) member).2
  rw [actual_public_center_agreement]
  exact congrArg (fun label => some (sourceOutcome label)) source

end TetraStereo.Certificate.ParsedParityDependencyAdapter
