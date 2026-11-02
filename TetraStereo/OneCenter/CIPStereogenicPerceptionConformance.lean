import TetraStereo.OneCenter.CIPMoleculeDigraphConformance
import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456
import TetraStereo.OneCenter.P92StereogenicUnitSemantics
import TetraStereo.OneCenter.P93AcyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open ProductionCIPOccurrenceDiscovery
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456

/-!
# Independent stereogenic-perception boundary

Perception is deliberately three-valued.  A strict ligand ranking establishes a stereogenic
unit; a proved tie establishes a nonstereogenic unit; failure after the bounded fast path and the
width-unbounded constitutional fallback remains unresolved.  No theorem in this file turns `none`
into chemical nonstereogenicity.

The tetrahedral reference side is proof-relevant: it names the annotated parity carrier, the
four-ligand frame, the complete ranking derivation, every adjacent Rule-4/5 decision, and their
strictness.  The ordinary production evaluator is proved equivalent to those clauses.  The
existing final fixed-point judgment then includes the independently derived Rule-6 alternative.
-/

namespace BlueBookP92.Perception

/-- Independent evidence that an atom belongs to the ordinary tetrahedral perception domain.
This is a candidate predicate, not yet the claim that its four ligands have distinct priorities. -/
structure TetrahedralCandidateEvidence (mol : RawMolecule)
    (center : Fin mol.atomCount) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  atom_spec : mol.atomAt? center.val = some spec
  parity_spec : spec.tetrahedral? = some parity
  not_extended : mol.isExtendedTetrahedralParityCarrier center.val = false
  four_ligands : (mol.ligandsWithLonePair center.val).length = 4

def TetrahedralCandidate (mol : RawMolecule) (center : Fin mol.atomCount) : Prop :=
  Nonempty (TetrahedralCandidateEvidence mol center)

/-- Independent public-perception decision over a separately supplied four-atom frame.

The specification is deliberately phrased as a precedence-ordered relation between observable
facts: strict Rules 1--5 ranking, a proved terminal constitutional tie, and the Rule-6 fallback.
It does not call `tetrahedralStereogenicity`. -/
def unannotatedTetrahedralDecision
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) : TetrahedralStereogenicity :=
  match mol.writtenNeighbors center with
  | ligands =>
      if ¬ConnectivityOnlyTetrahedralFrame result mol center then
        .notCandidate
      else if
        (rankBranchPositionsThroughOfficialContext? result mol state fuel center ligands).isSome
      then
        .stereogenic
      else if hasTerminalTetrahedralTie result mol state fuel center ligands then
        .notStereogenic
      else
        match tetrahedralRule6Stereogenicity? result mol state fuel center with
        | some true => .stereogenic
        | some false => .notStereogenic
        | none => .unresolved

/-- Independent ordinary perception judgment.  `OrdinaryFactClauses` is relational: it names
the primitive ranking derivations and does not mention `occurrenceFact?`. -/
def OrdinaryTetrahedralPerceived (mol : RawMolecule) (fuel : Nat)
    (aux : OccurrenceAuxState) (center : Fin mol.atomCount) (fact : OccurrenceAuxFact) : Prop :=
  TetrahedralCandidate mol center ∧
    OrdinaryFactClauses (mol := mol) aux fuel (canonicalCenterRoot center.val) fact

/-- Independent three-valued priority observation consumed by double-bond perception. -/
inductive PriorityObservation where
  | lower
  | higher
  | tied
  | unresolved
  deriving DecidableEq, Repr

def priorityObservationOfProduction : RawMolecule.BranchComparisonStatus → PriorityObservation
  | .lower => .lower
  | .higher => .higher
  | .tied => .tied
  | .unresolved => .unresolved

-- Keep `fuel` explicit for source-compatible named applications of this public definition.
set_option linter.unusedVariables false in
/-- Constitutional priority observation from the width-unbounded bonding-number-six comparator.
The legacy bounded sphere result is deliberately absent from this independent perception
specification. -/
def constitutionalPriorityObservation (mol : RawMolecule) (fuel center left right : Nat) :
    PriorityObservation :=
  priorityObservationOfProduction
    (mol.compareBranchesAuthoritativeStatus center left right)

/-- Independent three-valued perception result for one geometrical unit. -/
inductive GeometricalPerception where
  | stereogenic
  | nonstereogenic
  | unresolved
  deriving DecidableEq, Repr

def GeometricalPerception.toProduction : GeometricalPerception → DoubleBondStereogenicity
  | .stereogenic => .stereogenic
  | .nonstereogenic => .notStereogenic
  | .unresolved => .unresolved

attribute [simp] priorityObservationOfProduction GeometricalPerception.toProduction

/-- P-92 geometrical-unit endpoint criterion: two substituents must be strictly distinguishable;
one written substituent is sufficient only when the other side is a perceived lone pair. -/
def doubleBondEndpointDecision (substituents : List Nat)
    (priority : Nat → Nat → PriorityObservation) (hasLonePair : Bool) :
    GeometricalPerception :=
  match substituents with
  | [left, right] =>
      match priority left right with
      | .lower | .higher => .stereogenic
      | .tied => .nonstereogenic
      | .unresolved => .unresolved
  | [_] => if hasLonePair then .stereogenic else .nonstereogenic
  | _ => .nonstereogenic

/-- Both endpoints must be stereogenic; a proved nonstereogenic endpoint dominates an unresolved
other endpoint because the whole double bond then cannot be stereogenic. -/
def combineDoubleBondEndpoints
    (left right : GeometricalPerception) : GeometricalPerception :=
  match left, right with
  | .nonstereogenic, _ | _, .nonstereogenic => .nonstereogenic
  | .unresolved, _ | _, .unresolved => .unresolved
  | .stereogenic, .stereogenic => .stereogenic

/-- Independent ordinary-double-bond perception instantiated only with molecular observations and
the lower-level branch-priority oracle. -/
def doubleBondDecision (mol : RawMolecule) (fuel left right : Nat) :
    GeometricalPerception :=
  let endpoint := fun atom partner =>
    doubleBondEndpointDecision
      ((mol.writtenNeighbors atom).filter fun other => other != partner)
      (fun first second =>
        constitutionalPriorityObservation mol fuel atom first second)
      (mol.doubleBondEndpointHasLonePairSide atom partner)
  combineDoubleBondEndpoints (endpoint left right) (endpoint right left)

end BlueBookP92.Perception

/-! ## Tetrahedral candidate and strict-ranking correspondence -/

theorem centreElementSupported_iff_connectivityOnlyTetrahedralElement (element : Element) :
    RawMolecule.centreElementSupported element = true ↔
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement element := by
  cases element <;> simp [RawMolecule.centreElementSupported,
    BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement]

/-- Production admits exactly the independently stated four-atom connectivity frame.  This is
the load-bearing guard that prevents a three-coordinate amide nitrogen (or any other
three-coordinate heteroatom without geometry evidence) from being promoted merely by appending a
phantom lone pair. -/
theorem connectivityOnlyTetrahedralLigands?_isSome_iff_independentFrame
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (center : Nat) :
    (connectivityOnlyTetrahedralLigands? result mol center).isSome ↔
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center := by
  cases atomEq : result.parsed.atomAt? center with
  | none => simp [connectivityOnlyTetrahedralLigands?, atomEq,
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame]
  | some spec =>
      cases elementEq : spec.element <;>
        cases extendedEq : mol.isExtendedTetrahedralParityCarrier center <;>
          simp [connectivityOnlyTetrahedralLigands?, atomEq,
            BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame,
            BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement,
            RawMolecule.centreElementSupported, elementEq, extendedEq]

/-- The complete public unannotated-tetrahedral perception result is extensionally equal to the
independent four-state specification, including its four-atom applicability guard and Rule-6
fallback. -/
theorem tetrahedralStereogenicity_conforms_independent_unannotatedDecision
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) :
    tetrahedralStereogenicity result mol state fuel center =
      BlueBookP92.Perception.unannotatedTetrahedralDecision
        result mol state fuel center := by
  rw [tetrahedralStereogenicity,
    BlueBookP92.Perception.unannotatedTetrahedralDecision]
  cases frameEq : connectivityOnlyTetrahedralLigands? result mol center with
  | none =>
      have notFrame :
          ¬BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center := by
        intro frame
        have present :=
          (connectivityOnlyTetrahedralLigands?_isSome_iff_independentFrame
            result mol center).2 frame
        simp [frameEq] at present
      simp [notFrame]
  | some ligands =>
      have frame :
          BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center :=
        (connectivityOnlyTetrahedralLigands?_isSome_iff_independentFrame
          result mol center).1 (by simp [frameEq])
      have ligandEq : mol.writtenNeighbors center = ligands := by
        cases atomEq : result.parsed.atomAt? center with
        | none => simp [connectivityOnlyTetrahedralLigands?, atomEq] at frameEq
        | some spec =>
            unfold connectivityOnlyTetrahedralLigands? at frameEq
            simp only [atomEq] at frameEq
            split at frameEq
            · simp at frameEq
            · split at frameEq
              · exact Option.some.inj frameEq
              · simp at frameEq
      subst ligands
      cases rankingEq : rankBranchPositionsThroughOfficialContext?
          result mol state fuel center (mol.writtenNeighbors center) with
      | some positions => simp [frame, rankingEq]
      | none =>
          cases tieEq : hasTerminalTetrahedralTie result mol state fuel center
              (mol.writtenNeighbors center) with
          | true => simp [frame, rankingEq, tieEq]
          | false =>
              cases rule6Eq : tetrahedralRule6Stereogenicity?
                  result mol state fuel center with
              | none => simp [frame, rankingEq, tieEq]
              | some decision =>
                  cases decision <;> simp [frame, rankingEq, tieEq]

/-! ## Public unannotated-tetrahedral output -/

/-- Independent judgment for the only two public outcomes that descriptor-free tetrahedral
perception may report.  The atom must be present without an input tetrahedral parity carrier, and
the outcome is determined by the independent four-state perception decision: a perceived
stereogenic unit is reported as configuration-unspecified, while an unresolved ranking is
reported explicitly.  Proved nonstereogenic units and noncandidates have no judgment because the
public analyzer omits them. -/
def BlueBookP92.Perception.UnannotatedTetrahedralOutcomeJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (outcome : StereoOutcome) : Prop :=
  ∃ spec : AtomSpec,
    result.parsed.atomAt? center = some spec ∧
      spec.tetrahedral? = none ∧
        ((unannotatedTetrahedralDecision result mol state fuel center =
              TetrahedralStereogenicity.stereogenic ∧
            outcome = StereoOutcome.refused StereoRefusal.notSpecified) ∨
          (unannotatedTetrahedralDecision result mol state fuel center =
              TetrahedralStereogenicity.unresolved ∧
            outcome = StereoOutcome.refused StereoRefusal.rankingUnresolved))

/-- The public unannotated outcome adapter is sound and complete for the independent perception
judgment.  In particular, neither a proved tie nor an inapplicable center can leak into the public
assignment list as a descriptor-bearing or refusal outcome. -/
theorem unannotatedTetrahedralOutcome?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (outcome : StereoOutcome) :
    unannotatedTetrahedralOutcome? result mol state fuel center = some outcome ↔
      BlueBookP92.Perception.UnannotatedTetrahedralOutcomeJudgment
        result mol state fuel center outcome := by
  rw [unannotatedTetrahedralOutcome?,
    tetrahedralStereogenicity_conforms_independent_unannotatedDecision]
  unfold BlueBookP92.Perception.UnannotatedTetrahedralOutcomeJudgment
  cases atomEq : result.parsed.atomAt? center with
  | none => simp
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | some parity => simp [parityEq]
      | none =>
          cases decisionEq : BlueBookP92.Perception.unannotatedTetrahedralDecision
              result mol state fuel center <;> simp [parityEq, eq_comm]

/-- Assignment-level form of the exact unannotated-tetrahedral output theorem. -/
def BlueBookP92.Perception.UnannotatedTetrahedralAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (assignment : StereoAssignment) : Prop :=
  assignment.unit = StereoUnit.tetrahedral center ∧
    UnannotatedTetrahedralOutcomeJudgment
      result mol state fuel center assignment.outcome

theorem unannotatedTetrahedralAssignment?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (assignment : StereoAssignment) :
    (unannotatedTetrahedralOutcome? result mol state fuel center).map
        (fun outcome =>
          ({ unit := StereoUnit.tetrahedral center, outcome := outcome } : StereoAssignment)) =
        some assignment ↔
      BlueBookP92.Perception.UnannotatedTetrahedralAssignmentJudgment
        result mol state fuel center assignment := by
  constructor
  · intro emitted
    cases outcomeEq : unannotatedTetrahedralOutcome? result mol state fuel center with
    | none => simp [outcomeEq] at emitted
    | some outcome =>
        simp only [outcomeEq, Option.map_some, Option.some.injEq] at emitted
        subst assignment
        exact ⟨rfl,
          (unannotatedTetrahedralOutcome?_eq_some_iff_independent_judgment
            result mol state fuel center outcome).1 outcomeEq⟩
  · rintro ⟨unitEq, judgment⟩
    have outcomeEq :=
      (unannotatedTetrahedralOutcome?_eq_some_iff_independent_judgment
        result mol state fuel center assignment.outcome).2 judgment
    rw [outcomeEq]
    simp only [Option.map_some, Option.some.injEq]
    cases assignment with
    | mk unit outcome =>
        simp only at unitEq
        cases unitEq
        rfl

/-! ## Public annotated-tetrahedral output -/

namespace BlueBookP93.Acyclic

/-- Independent truth table joining OpenSMILES tetrahedral parity, the parity of the
written-to-priority permutation, and the uppercase P-93 descriptor. -/
def TetrahedralParityDescriptorJudgment
    (parity : TetrahedralInputParity) (evenPermutation : Bool) (descriptor : RS) : Prop :=
  match parity, evenPermutation, descriptor with
  | .clockwise, true, .R
  | .clockwise, false, .S
  | .anticlockwise, true, .S
  | .anticlockwise, false, .R => True
  | _, _, _ => False

/-- Independent uppercase-to-lowercase descriptor correspondence used for a
pseudoasymmetric tetrahedral outcome. -/
def PseudoTetrahedralDescriptorJudgment (descriptor : RS) (pseudo : PseudoRS) : Prop :=
  match descriptor, pseudo with
  | .R, .r | .S, .s => True
  | _, _ => False

/-- Independent public meaning of one stabilized descriptor fact. -/
def RawDescriptorFactOutcomeJudgment
    (fact : RawDescriptorFact) (outcome : StereoOutcome) : Prop :=
  match fact.uppercase, fact.descriptor with
  | true, descriptor => outcome = StereoOutcome.tetrahedral descriptor
  | false, .R => outcome = StereoOutcome.pseudoTetrahedral PseudoRS.r
  | false, .S => outcome = StereoOutcome.pseudoTetrahedral PseudoRS.s

/-- Descriptor-free residual judgment after no stabilized Rules-3--6 fact was available.

The comparator and Rule-6 result are named observations at this boundary.  The relation specifies
their chemically conservative interpretation: only a complete Rules-1--5 order emits `R/S`; a
checked Rule-6 symmetry emits `notStereogenic`; every other failed ranking is unresolved. -/
def AnnotatedTetrahedralFallbackJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (outcome : StereoOutcome) : Prop :=
  if !RawMolecule.centreElementSupported spec.element then
    outcome = StereoOutcome.refused StereoRefusal.unsupportedCentreElement
  else
    let ligands := mol.ligandsWithLonePair idx
    if ligands.length != 4 then
      outcome = StereoOutcome.refused (StereoRefusal.wrongLigandCount ligands.length)
    else
      match rankBranchPositionsThroughOfficialContext? result mol state fuel idx ligands with
      | some positions =>
          ∃ descriptor,
            TetrahedralParityDescriptorJudgment parity
                (RawMolecule.permutationIsEven positions) descriptor ∧
              outcome = StereoOutcome.tetrahedral descriptor
      | none =>
          match tetrahedralRule6Stereogenicity? result mol state fuel idx with
          | some false => outcome = StereoOutcome.refused StereoRefusal.notStereogenic
          | some true | none =>
              outcome = StereoOutcome.refused StereoRefusal.rankingUnresolved

/-- Independent final-output judgment for one annotated ordinary tetrahedral center.

The annotation and exclusion of extended-tetrahedral carriers are explicit.  A stabilized fact
is interpreted by `RawDescriptorFactOutcomeJudgment`; in its absence the fail-closed fallback
relation above applies. -/
def AnnotatedTetrahedralOutcomeJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : Nat) (outcome : StereoOutcome) : Prop :=
  ∃ spec parity,
    result.parsed.atomAt? idx = some spec ∧
      spec.tetrahedral? = some parity ∧
      mol.isExtendedTetrahedralParityCarrier idx = false ∧
      match Option.first (state.factAt? idx)
          (tetrahedralFactThroughExtendedTetrahedralPseudo? mol fuel idx) with
      | some fact => RawDescriptorFactOutcomeJudgment fact outcome
      | none =>
          AnnotatedTetrahedralFallbackJudgment
            result mol state fuel idx spec parity outcome

/-- Assignment-level form of the annotated output judgment. -/
def AnnotatedTetrahedralAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : Nat) (assignment : StereoAssignment) : Prop :=
  assignment.unit = StereoUnit.tetrahedral idx ∧
    AnnotatedTetrahedralOutcomeJudgment
      result mol state fuel idx assignment.outcome

end BlueBookP93.Acyclic

theorem descriptorOfParity_eq_iff_tetrahedralParityDescriptorJudgment
    (parity : TetrahedralInputParity) (evenPermutation : Bool) (descriptor : RS) :
    RawMolecule.descriptorOfParity parity evenPermutation = descriptor ↔
      BlueBookP93.Acyclic.TetrahedralParityDescriptorJudgment
        parity evenPermutation descriptor := by
  cases parity <;> cases evenPermutation <;> cases descriptor <;>
    simp [RawMolecule.descriptorOfParity,
      BlueBookP93.Acyclic.TetrahedralParityDescriptorJudgment]

/-- Outcome-level form of the independent tetrahedral parity truth table. -/
theorem tetrahedralOutcome_eq_iff_tetrahedralParityDescriptorJudgment
    (parity : TetrahedralInputParity) (evenPermutation : Bool)
    (outcome : StereoOutcome) :
    StereoOutcome.tetrahedral
        (RawMolecule.descriptorOfParity parity evenPermutation) = outcome ↔
      ∃ descriptor,
        BlueBookP93.Acyclic.TetrahedralParityDescriptorJudgment
            parity evenPermutation descriptor ∧
          outcome = StereoOutcome.tetrahedral descriptor := by
  constructor
  · intro emitted
    refine ⟨RawMolecule.descriptorOfParity parity evenPermutation, ?_, emitted.symm⟩
    exact (descriptorOfParity_eq_iff_tetrahedralParityDescriptorJudgment
      parity evenPermutation
      (RawMolecule.descriptorOfParity parity evenPermutation)).mp rfl
  · rintro ⟨descriptor, judged, outcomeEq⟩
    have descriptorEq :=
      (descriptorOfParity_eq_iff_tetrahedralParityDescriptorJudgment
        parity evenPermutation descriptor).mpr judged
    rw [descriptorEq]
    exact outcomeEq.symm

theorem rawDescriptorFactOutcome_eq_iff_independent_judgment
    (fact : RawDescriptorFact) (outcome : StereoOutcome) :
    rawDescriptorFactOutcome fact = outcome ↔
      BlueBookP93.Acyclic.RawDescriptorFactOutcomeJudgment fact outcome := by
  cases uppercaseEq : fact.uppercase <;> cases descriptorEq : fact.descriptor <;>
    cases outcome <;>
    simp [rawDescriptorFactOutcome,
      BlueBookP93.Acyclic.RawDescriptorFactOutcomeJudgment,
      uppercaseEq, descriptorEq, eq_comm]

theorem annotatedTetrahedralOutcome?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : Nat) (outcome : StereoOutcome) :
    annotatedTetrahedralOutcome? result mol state fuel idx = some outcome ↔
      BlueBookP93.Acyclic.AnnotatedTetrahedralOutcomeJudgment
        result mol state fuel idx outcome := by
  unfold annotatedTetrahedralOutcome?
  unfold BlueBookP93.Acyclic.AnnotatedTetrahedralOutcomeJudgment
  cases atomEq : result.parsed.atomAt? idx with
  | none => simp
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none => simp [parityEq]
      | some parity =>
          cases extendedEq : mol.isExtendedTetrahedralParityCarrier idx with
          | true => simp
          | false =>
              cases factEq : Option.first (state.factAt? idx)
                  (tetrahedralFactThroughExtendedTetrahedralPseudo? mol fuel idx) with
              | some fact =>
                  simp [parityEq,
                    rawDescriptorFactOutcome_eq_iff_independent_judgment]
              | none =>
                  simp only [Option.some.injEq, true_and]
                  unfold BlueBookP93.Acyclic.AnnotatedTetrahedralFallbackJudgment
                  cases supportedEq : RawMolecule.centreElementSupported spec.element with
                  | false =>
                      simp [parityEq, supportedEq]
                      exact eq_comm
                  | true =>
                      cases ligandCountEq :
                          (mol.ligandsWithLonePair idx).length == 4 with
                      | false =>
                          have ligandsLength :
                              (mol.ligandsWithLonePair idx).length ≠ 4 := by
                            simpa using ligandCountEq
                          simp [parityEq, supportedEq, ligandsLength]
                          exact eq_comm
                      | true =>
                          have ligandsLength :
                              (mol.ligandsWithLonePair idx).length = 4 := by
                            simpa using ligandCountEq
                          cases rankingEq : rankBranchPositionsThroughOfficialContext?
                              result mol state fuel idx (mol.ligandsWithLonePair idx) with
                          | some positions =>
                              simp [parityEq, supportedEq, ligandsLength, rankingEq]
                              exact
                                tetrahedralOutcome_eq_iff_tetrahedralParityDescriptorJudgment
                                  parity
                                  (RawMolecule.permutationIsEven positions)
                                  outcome
                          | none =>
                              cases rule6Eq : tetrahedralRule6Stereogenicity?
                                  result mol state fuel idx with
                              | none =>
                                  simp [parityEq, supportedEq, ligandsLength, rankingEq]
                                  exact eq_comm
                              | some decision =>
                                  cases decision <;>
                                    simp [parityEq, supportedEq, ligandsLength, rankingEq] <;>
                                    exact eq_comm

theorem annotatedTetrahedralAssignment?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : Nat) (assignment : StereoAssignment) :
    annotatedTetrahedralAssignment? result mol state fuel idx = some assignment ↔
      BlueBookP93.Acyclic.AnnotatedTetrahedralAssignmentJudgment
        result mol state fuel idx assignment := by
  unfold annotatedTetrahedralAssignment?
  constructor
  · intro emitted
    cases outcomeEq : annotatedTetrahedralOutcome? result mol state fuel idx with
    | none => simp [outcomeEq] at emitted
    | some outcome =>
        simp only [outcomeEq, Option.map_some, Option.some.injEq] at emitted
        subst assignment
        exact ⟨rfl,
          (annotatedTetrahedralOutcome?_eq_some_iff_independent_judgment
            result mol state fuel idx outcome).mp outcomeEq⟩
  · rintro ⟨unitEq, judgment⟩
    have outcomeEq :=
      (annotatedTetrahedralOutcome?_eq_some_iff_independent_judgment
        result mol state fuel idx assignment.outcome).mpr judgment
    rw [outcomeEq]
    cases assignment with
    | mk unit assignmentOutcome =>
        simp only at unitEq
        cases unitEq
        rfl

/-- Independent dispatch judgment for the complete ordinary-tetrahedral subanalyzer.  Parsed
parity evidence selects the annotated P-93 assignment relation; its absence selects the P-92
configuration-unspecified perception relation. -/
def BlueBookP93.Acyclic.PublicTetrahedralAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : Nat) (assignment : StereoAssignment) : Prop :=
  match result.parsed.atomAt? idx with
  | none => False
  | some spec =>
      match spec.tetrahedral? with
      | none =>
          BlueBookP92.Perception.UnannotatedTetrahedralAssignmentJudgment
            result mol state fuel idx assignment
      | some _ =>
          AnnotatedTetrahedralAssignmentJudgment
            result mol state fuel idx assignment

/-- Exact one-atom adapter theorem for the annotated/unannotated tetrahedral dispatch. -/
theorem tetrahedralAssignment?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : Nat) (assignment : StereoAssignment) :
    tetrahedralAssignment? result mol state fuel idx = some assignment ↔
      BlueBookP93.Acyclic.PublicTetrahedralAssignmentJudgment
        result mol state fuel idx assignment := by
  unfold tetrahedralAssignment?
  unfold BlueBookP93.Acyclic.PublicTetrahedralAssignmentJudgment
  cases atomEq : result.parsed.atomAt? idx with
  | none => simp
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none =>
          simpa [atomEq, parityEq] using
            (unannotatedTetrahedralAssignment?_eq_some_iff_independent_judgment
              result mol state fuel idx assignment)
      | some parity =>
          simpa [atomEq, parityEq] using
            (annotatedTetrahedralAssignment?_eq_some_iff_independent_judgment
              result mol state fuel idx assignment)

/-- Exact list-level boundary for every ordinary tetrahedral assignment reported by the normalized
analyzer.  The witness is the parsed atom index and its independently derived P-92/P-93 judgment. -/
theorem mem_tetrahedralAssignments_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) (assignment : StereoAssignment) :
    assignment ∈ tetrahedralAssignments result mol state fuel ↔
      ∃ idx < result.parsed.atomCount,
        BlueBookP93.Acyclic.PublicTetrahedralAssignmentJudgment
          result mol state fuel idx assignment := by
  constructor
  · intro present
    rw [tetrahedralAssignments, List.mem_filterMap] at present
    obtain ⟨idx, idxPresent, emitted⟩ := present
    exact ⟨idx, List.mem_range.mp idxPresent,
      (tetrahedralAssignment?_eq_some_iff_independent_judgment
        result mol state fuel idx assignment).mp emitted⟩
  · rintro ⟨idx, idxBound, judgment⟩
    rw [tetrahedralAssignments, List.mem_filterMap]
    exact ⟨idx, List.mem_range.mpr idxBound,
      (tetrahedralAssignment?_eq_some_iff_independent_judgment
        result mol state fuel idx assignment).mpr judgment⟩

theorem finalUnitEligible_iff_blueBookP92Candidate
    (mol : RawMolecule) (center : Fin mol.atomCount) :
    FinalUnitEligible mol center ↔ BlueBookP92.Perception.TetrahedralCandidate mol center := by
  constructor
  · rintro ⟨annotated, notExtended, fourLigands⟩
    cases atomEq : mol.atomAt? center.val with
    | none => simp [atomEq] at annotated
    | some spec =>
        cases parityEq : spec.tetrahedral? with
        | none => simp [atomEq, parityEq] at annotated
        | some parity =>
            exact ⟨{
              spec := spec
              parity := parity
              atom_spec := atomEq
              parity_spec := parityEq
              not_extended := notExtended
              four_ligands := fourLigands }⟩
  · rintro ⟨candidate⟩
    exact ⟨by simp [candidate.atom_spec, candidate.parity_spec],
      candidate.not_extended, candidate.four_ligands⟩

/-- The executable root filter recognizes exactly the independently stated tetrahedral candidate
domain. -/
theorem rootAt?_isSome_iff_blueBookP92Candidate
    (mol : RawMolecule) (center : Fin mol.atomCount) :
    (rootAt? mol center).isSome ↔ BlueBookP92.Perception.TetrahedralCandidate mol center := by
  rw [← finalUnitEligible_iff_blueBookP92Candidate]
  simp [rootAt?]

/-- On an admitted final unit, production ordinary perception is sound and complete for the
independent strict-ranking clauses. -/
theorem occurrenceFact?_iff_blueBookP92OrdinaryTetrahedralPerceived
    (mol : RawMolecule) (fuel : Nat) (aux : OccurrenceAuxState)
    (center : Fin mol.atomCount) (eligible : FinalUnitEligible mol center)
    (fact : OccurrenceAuxFact) :
    occurrenceFact? mol fuel aux (canonicalCenterRoot center.val) = some fact ↔
      BlueBookP92.Perception.OrdinaryTetrahedralPerceived mol fuel aux center fact := by
  rw [BlueBookP92.Perception.OrdinaryTetrahedralPerceived,
    ordinaryFactClauses_iff_production]
  simp [(finalUnitEligible_iff_blueBookP92Candidate mol center).1 eligible]

/-- The complete state-sensitive production perception judgment, including its Rule-6 fallback,
is exactly the independent final occurrence derivation. -/
theorem production_tetrahedral_perception_iff_independent_final_judgment
    {mol : RawMolecule} (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (unit : FinalUnit mol) (descriptor : Descriptor) :
    ProductionDescriptorJudgment discovery fuel state unit descriptor ↔
      (occurrenceSystem discovery fuel).FinalDescriptorJudgment state unit descriptor :=
  productionDescriptorJudgment_iff_finalDescriptorJudgment
    discovery fuel state unit descriptor

/-! ## Ordinary double-bond perception correspondence -/

/-- Production ordinary-double-bond perception agrees with the independently typed three-valued
endpoint specification.  The theorem is about perception after branch-priority observations; the
chemical correctness of those observations is the separate CIP comparator layer. -/
theorem doubleBondStereogenicity_conforms_blueBookP92Perception
    (mol : RawMolecule) (fuel left right : Nat) :
    doubleBondStereogenicity mol fuel left right =
      (BlueBookP92.Perception.doubleBondDecision mol fuel left right).toProduction := by
  simp only [doubleBondStereogenicity, BlueBookP92.Perception.doubleBondDecision]
  generalize leftSubstituentsEq :
      (mol.writtenNeighbors left).filter (fun other => other != right) = leftSubstituents
  generalize rightSubstituentsEq :
      (mol.writtenNeighbors right).filter (fun other => other != left) = rightSubstituents
  cases leftSubstituents with
  | nil => simp [BlueBookP92.Perception.doubleBondEndpointDecision,
      BlueBookP92.Perception.combineDoubleBondEndpoints]
  | cons leftFirst leftTail =>
      cases leftTail with
      | nil =>
          cases leftLonePair : mol.doubleBondEndpointHasLonePairSide left right <;>
            cases rightSubstituents with
            | nil => simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                BlueBookP92.Perception.combineDoubleBondEndpoints]
            | cons rightFirst rightTail =>
                cases rightTail with
                | nil =>
                    cases rightLonePair :
                        mol.doubleBondEndpointHasLonePairSide right left <;>
                      simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                        BlueBookP92.Perception.combineDoubleBondEndpoints]
                | cons rightSecond rightRest =>
                    cases rightRest with
                    | nil =>
                        cases rightPriority :
                            mol.compareBranchesStatus fuel right rightFirst rightSecond <;>
                          cases rightAuthoritative :
                            mol.compareBranchesAuthoritativeStatus right rightFirst rightSecond <;>
                          simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                            BlueBookP92.Perception.combineDoubleBondEndpoints,
                            BlueBookP92.Perception.priorityObservationOfProduction,
                            BlueBookP92.Perception.constitutionalPriorityObservation,
                            rightAuthoritative]
                    | cons rightThird rightMore =>
                        simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                          BlueBookP92.Perception.combineDoubleBondEndpoints]
      | cons leftSecond leftRest =>
          cases leftRest with
          | nil =>
              cases leftPriority :
                  mol.compareBranchesStatus fuel left leftFirst leftSecond <;>
                cases leftAuthoritative :
                  mol.compareBranchesAuthoritativeStatus left leftFirst leftSecond <;>
                cases rightSubstituents with
                | nil => simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                    BlueBookP92.Perception.combineDoubleBondEndpoints,
                    BlueBookP92.Perception.priorityObservationOfProduction,
                    BlueBookP92.Perception.constitutionalPriorityObservation,
                    leftAuthoritative]
                | cons rightFirst rightTail =>
                    cases rightTail with
                    | nil =>
                        cases rightLonePair :
                            mol.doubleBondEndpointHasLonePairSide right left <;>
                          simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                            BlueBookP92.Perception.combineDoubleBondEndpoints,
                            BlueBookP92.Perception.priorityObservationOfProduction,
                            BlueBookP92.Perception.constitutionalPriorityObservation,
                            leftAuthoritative]
                    | cons rightSecond rightRest =>
                        cases rightRest with
                        | nil =>
                            cases rightPriority :
                                mol.compareBranchesStatus fuel right rightFirst rightSecond <;>
                              cases rightAuthoritative :
                                mol.compareBranchesAuthoritativeStatus right rightFirst
                                  rightSecond <;>
                              simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                                BlueBookP92.Perception.combineDoubleBondEndpoints,
                                BlueBookP92.Perception.priorityObservationOfProduction,
                                BlueBookP92.Perception.constitutionalPriorityObservation,
                                leftAuthoritative,
                                rightAuthoritative]
                        | cons rightThird rightMore =>
                            simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                              BlueBookP92.Perception.combineDoubleBondEndpoints,
                              BlueBookP92.Perception.priorityObservationOfProduction,
                              BlueBookP92.Perception.constitutionalPriorityObservation,
                              leftAuthoritative]
          | cons leftThird leftMore =>
              simp [BlueBookP92.Perception.doubleBondEndpointDecision,
                BlueBookP92.Perception.combineDoubleBondEndpoints]

/-! ## Ordinary double-bond geometry and public output -/

namespace BlueBookP93.Acyclic

/-- Independent P-93 meaning of an ordinary alkene descriptor once the two CIP-senior
substituent sides are known.  Equal sides mean `Z`; different sides mean `E`.  `unspecified` is
not a descriptor satisfying this relation. -/
def OrdinaryAlkeneDescriptorJudgment
    (leftSide rightSide : DirectionalBondMarker) (descriptor : DoubleBondStereo) : Prop :=
  (leftSide = rightSide ∧ descriptor = DoubleBondStereo.Z) ∨
    (leftSide ≠ rightSide ∧ descriptor = DoubleBondStereo.E)

/-- Proof-relevant geometry observation consumed by the ordinary alkene descriptor rule.

A specified stored value is admitted as supplied geometry evidence.  Otherwise both endpoint
sides must be those of the Rules-1a--5 senior substituents and the final descriptor must satisfy
the independent same-side/opposite-side relation.  This relation deliberately exposes the
geometry-observation boundary rather than pretending Lean proves a laboratory observation. -/
def OrdinaryAlkeneGeometryJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel left right : Nat)
    (descriptor : DoubleBondStereo) : Prop :=
  result.stereobonds.storedDoubleBondStereo? left right = some descriptor ∨
    (result.stereobonds.storedDoubleBondStereo? left right = none ∧
      ∃ leftSide rightSide,
        seniorSideThroughOfficialContext? result mol state fuel left right = some leftSide ∧
          seniorSideThroughOfficialContext? result mol state fuel right left = some rightSide ∧
          OrdinaryAlkeneDescriptorJudgment leftSide rightSide descriptor)

/-- The public result associated with usable geometry evidence. -/
def ordinaryAlkeneGeometryOutcome (descriptor : DoubleBondStereo) : StereoOutcome :=
  match descriptor with
  | .unspecified => StereoOutcome.refused StereoRefusal.markerEvidenceUnusable
  | value => StereoOutcome.alkene value

/-- Whether neither endpoint carries directional geometry evidence. -/
def OrdinaryAlkeneMarkersAbsent
    (result : ChemistryNormalizationResult) (left right : Nat) : Prop :=
  (result.stereobonds.directionalMarkersAtSide left right).isEmpty = true ∧
    (result.stereobonds.directionalMarkersAtSide right left).isEmpty = true

instance (result : ChemistryNormalizationResult) (left right : Nat) :
    Decidable (OrdinaryAlkeneMarkersAbsent result left right) := by
  unfold OrdinaryAlkeneMarkersAbsent
  infer_instance

/-- Independent combined P-92/P-93 judgment for one public ordinary-double-bond assignment.
Nonstereogenic units are omitted.  Unresolved endpoint priority is reported explicitly.  A
stereogenic unit either carries geometry satisfying `OrdinaryAlkeneGeometryJudgment`, is reported
configuration-unspecified when no markers were supplied, or is refused because supplied marker
evidence could not be converted into senior-side geometry. -/
def OrdinaryDoubleBondAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (record : Nat × Nat × DoubleBondStereo) (assignment : StereoAssignment) : Prop :=
  let left := record.1
  let right := record.2.1
  assignment.unit = StereoUnit.doubleBond left right ∧
    match BlueBookP92.Perception.doubleBondDecision mol fuel left right with
    | .nonstereogenic => False
    | .unresolved =>
        assignment.outcome = StereoOutcome.refused StereoRefusal.rankingUnresolved
    | .stereogenic =>
        (∃ descriptor,
          OrdinaryAlkeneGeometryJudgment result mol state fuel left right descriptor ∧
            assignment.outcome = ordinaryAlkeneGeometryOutcome descriptor) ∨
        ((¬∃ descriptor,
            OrdinaryAlkeneGeometryJudgment result mol state fuel left right descriptor) ∧
          if OrdinaryAlkeneMarkersAbsent result left right then
            assignment.outcome = StereoOutcome.refused StereoRefusal.notSpecified
          else
            assignment.outcome = StereoOutcome.refused StereoRefusal.rankingUnresolved)

end BlueBookP93.Acyclic

theorem stereoFromDirectionalMarkers_eq_iff_ordinaryAlkeneDescriptorJudgment
    (leftSide rightSide : DirectionalBondMarker) (descriptor : DoubleBondStereo) :
    StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide = descriptor ↔
      BlueBookP93.Acyclic.OrdinaryAlkeneDescriptorJudgment
        leftSide rightSide descriptor := by
  cases leftSide <;> cases rightSide <;> cases descriptor <;>
    simp [StereobondSemantics.stereoFromDirectionalMarkers,
      BlueBookP93.Acyclic.OrdinaryAlkeneDescriptorJudgment]

theorem cipDoubleBondStereoThroughOfficialContext?_eq_some_iff_geometryJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel left right : Nat) (descriptor : DoubleBondStereo) :
    result.cipDoubleBondStereoThroughOfficialContext? mol state fuel left right =
        some descriptor ↔
      ∃ leftSide rightSide,
        seniorSideThroughOfficialContext? result mol state fuel left right = some leftSide ∧
          seniorSideThroughOfficialContext? result mol state fuel right left = some rightSide ∧
          BlueBookP93.Acyclic.OrdinaryAlkeneDescriptorJudgment
            leftSide rightSide descriptor := by
  unfold ChemistryNormalizationResult.cipDoubleBondStereoThroughOfficialContext?
  cases leftEq : seniorSideThroughOfficialContext? result mol state fuel left right <;>
    cases rightEq : seniorSideThroughOfficialContext? result mol state fuel right left <;>
    simp [
      stereoFromDirectionalMarkers_eq_iff_ordinaryAlkeneDescriptorJudgment]

theorem perceivedDoubleBondStereoThroughOfficialContext?_eq_some_iff_geometryJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel left right : Nat) (descriptor : DoubleBondStereo) :
    result.perceivedDoubleBondStereoThroughOfficialContext? mol state fuel left right =
        some descriptor ↔
      BlueBookP93.Acyclic.OrdinaryAlkeneGeometryJudgment
        result mol state fuel left right descriptor := by
  unfold ChemistryNormalizationResult.perceivedDoubleBondStereoThroughOfficialContext?
  unfold BlueBookP93.Acyclic.OrdinaryAlkeneGeometryJudgment
  cases storedEq : result.stereobonds.storedDoubleBondStereo? left right with
  | none =>
      simp [Option.first,
        cipDoubleBondStereoThroughOfficialContext?_eq_some_iff_geometryJudgment]
  | some stored =>
      simp [Option.first]

theorem stereoAssignment_mk_eq_iff
    (unit : StereoUnit) (outcome : StereoOutcome) (assignment : StereoAssignment) :
    ({ unit := unit, outcome := outcome } : StereoAssignment) = assignment ↔
      assignment.unit = unit ∧ assignment.outcome = outcome := by
  cases assignment
  simp [eq_comm]

/-- Exact refinement of the extracted public ordinary-double-bond branch to the independent
combined endpoint-perception and senior-side geometry judgment. -/
theorem ordinaryDoubleBondAssignment?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (record : Nat × Nat × DoubleBondStereo) (assignment : StereoAssignment) :
    ordinaryDoubleBondAssignment? result mol state fuel record = some assignment ↔
      BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment
        result mol state fuel record assignment := by
  rcases record with ⟨left, right, inputStereo⟩
  unfold ordinaryDoubleBondAssignment?
  dsimp only [Prod.fst, Prod.snd]
  rw [doubleBondStereogenicity_conforms_blueBookP92Perception]
  cases decisionEq : BlueBookP92.Perception.doubleBondDecision mol fuel left right with
  | nonstereogenic =>
      simp [
        BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment, decisionEq]
  | unresolved =>
      simp [
        BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment,
        stereoAssignment_mk_eq_iff, decisionEq]
  | stereogenic =>
      cases geometryEq :
          result.perceivedDoubleBondStereoThroughOfficialContext?
            mol state fuel left right with
      | some descriptor =>
          have geometry :
              BlueBookP93.Acyclic.OrdinaryAlkeneGeometryJudgment
                result mol state fuel left right descriptor :=
            (perceivedDoubleBondStereoThroughOfficialContext?_eq_some_iff_geometryJudgment
              result mol state fuel left right descriptor).1 geometryEq
          cases descriptor <;>
            simp [
              BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment,
              BlueBookP93.Acyclic.ordinaryAlkeneGeometryOutcome,
              stereoAssignment_mk_eq_iff,
              ← perceivedDoubleBondStereoThroughOfficialContext?_eq_some_iff_geometryJudgment,
              decisionEq, geometryEq]
      | none =>
          have noGeometry :
              ¬∃ descriptor,
                BlueBookP93.Acyclic.OrdinaryAlkeneGeometryJudgment
                  result mol state fuel left right descriptor := by
            rintro ⟨descriptor, geometry⟩
            have emitted :=
              (perceivedDoubleBondStereoThroughOfficialContext?_eq_some_iff_geometryJudgment
                result mol state fuel left right descriptor).2 geometry
            simp [geometryEq] at emitted
          cases leftMarkers :
              (result.stereobonds.directionalMarkersAtSide left right).isEmpty <;>
            cases rightMarkers :
              (result.stereobonds.directionalMarkersAtSide right left).isEmpty <;>
            simp [
              BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment,
              BlueBookP93.Acyclic.OrdinaryAlkeneMarkersAbsent,
              stereoAssignment_mk_eq_iff,
              ← perceivedDoubleBondStereoThroughOfficialContext?_eq_some_iff_geometryJudgment,
              decisionEq, geometryEq, leftMarkers, rightMarkers]

/-- Exact list-level boundary for the ordinary-double-bond subanalyzer.  Membership retains the
particular parsed double-bond record and its independent combined P-92/P-93 judgment. -/
theorem mem_ordinaryDoubleBondAssignments_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) (assignment : StereoAssignment) :
    assignment ∈ ordinaryDoubleBondAssignments result mol state fuel ↔
      ∃ record ∈ result.stereobonds.doubleBondAssignments,
        BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment
          result mol state fuel record assignment := by
  constructor
  · intro present
    rw [ordinaryDoubleBondAssignments, List.mem_filterMap] at present
    obtain ⟨record, recordPresent, emitted⟩ := present
    exact ⟨record, recordPresent,
      (ordinaryDoubleBondAssignment?_eq_some_iff_independent_judgment
        result mol state fuel record assignment).mp emitted⟩
  · rintro ⟨record, recordPresent, judgment⟩
    rw [ordinaryDoubleBondAssignments, List.mem_filterMap]
    exact ⟨record, recordPresent,
      (ordinaryDoubleBondAssignment?_eq_some_iff_independent_judgment
        result mol state fuel record assignment).mpr judgment⟩

/-! ## Odd-cumulene and enantiomorphic-double-bond output -/

namespace BlueBookP93.Acyclic

/-- Independent together/opposite observation for the two CIP-senior terminal sides of a planar
odd cumulene. -/
def OddCumuleneTerminalGeometryJudgment
    (leftSide rightSide : DirectionalBondMarker)
    (geometry : OddCumuleneTerminalGeometry) : Prop :=
  match geometry with
  | .together => leftSide = rightSide
  | .opposite => leftSide ≠ rightSide

/-- The corresponding P-92 geometry observation when exactly one endpoint is an enantiomorphic
ligand pair. -/
def EnantiomorphicDoubleBondTerminalGeometryJudgment
    (leftSide rightSide : DirectionalBondMarker)
    (geometry : BlueBookP92.EnantiomorphicDoubleBondTerminalGeometry) : Prop :=
  match geometry with
  | .together => leftSide = rightSide
  | .opposite => leftSide ≠ rightSide

/-- Correspondence between the independently transcribed P-92 descriptor and the production
public-output type. -/
def SequenceDoubleBondOutcomeJudgment
    (descriptor : BlueBookP92.EnantiomorphicDoubleBondDescriptor)
    (outcome : StereoOutcome) : Prop :=
  match descriptor with
  | .seqCis =>
      outcome = StereoOutcome.enantiomorphicDoubleBond
        SequenceDoubleBondDescriptor.seqCis
  | .seqTrans =>
      outcome = StereoOutcome.enantiomorphicDoubleBond
        SequenceDoubleBondDescriptor.seqTrans

/-- Correspondence between the independently transcribed P-93 odd-cumulene descriptor and the
ordinary production `E/Z` output. -/
def OddCumuleneEZOutcomeJudgment (descriptor : Descriptor) (outcome : StereoOutcome) : Prop :=
  match descriptor with
  | .Z => outcome = StereoOutcome.alkene DoubleBondStereo.Z
  | .E => outcome = StereoOutcome.alkene DoubleBondStereo.E
  | _ => False

/-- Independent public-outcome judgment at the P-92/P-93 boundary.

Exactly one Rule-5 enantiomorphic endpoint makes the extended planar unit geometrically
enantiomorphic and therefore selects `seqCis/seqTrans`.  Two ordinary endpoints, or two
enantiomorphic endpoints whose mirror-induced reference changes cancel, use ordinary `Z/E`. -/
def OddCumulenePublicOutcomeJudgment
    (leftEnantiomorphic rightEnantiomorphic : Prop)
    (leftSide rightSide : DirectionalBondMarker) (outcome : StereoOutcome) : Prop :=
  (((leftEnantiomorphic ∧ ¬rightEnantiomorphic) ∨
      (¬leftEnantiomorphic ∧ rightEnantiomorphic)) ∧
    ∃ geometry descriptor,
      EnantiomorphicDoubleBondTerminalGeometryJudgment
          leftSide rightSide geometry ∧
        BlueBookP92.EnantiomorphicDoubleBondDescriptorAssignment geometry descriptor ∧
        SequenceDoubleBondOutcomeJudgment descriptor outcome) ∨
  (((leftEnantiomorphic ∧ rightEnantiomorphic) ∨
      (¬leftEnantiomorphic ∧ ¬rightEnantiomorphic)) ∧
    ∃ geometry descriptor,
      OddCumuleneTerminalGeometryJudgment leftSide rightSide geometry ∧
        OddCumuleneEZAssignment geometry descriptor ∧
        OddCumuleneEZOutcomeJudgment descriptor outcome)

/-- Independent reference geometry selected from the two terminal sides. -/
def oddCumuleneTerminalGeometryOfSides
    (leftSide rightSide : DirectionalBondMarker) : OddCumuleneTerminalGeometry :=
  if leftSide = rightSide then .together else .opposite

/-- Independent P-92 reference geometry selected from the same terminal observation. -/
def enantiomorphicDoubleBondTerminalGeometryOfSides
    (leftSide rightSide : DirectionalBondMarker) :
    BlueBookP92.EnantiomorphicDoubleBondTerminalGeometry :=
  if leftSide = rightSide then .together else .opposite

theorem oddCumuleneTerminalGeometryJudgment_iff_eq_reference
    (leftSide rightSide : DirectionalBondMarker)
    (geometry : OddCumuleneTerminalGeometry) :
    OddCumuleneTerminalGeometryJudgment leftSide rightSide geometry ↔
      geometry = oddCumuleneTerminalGeometryOfSides leftSide rightSide := by
  cases leftSide <;> cases rightSide <;> cases geometry <;>
    simp [OddCumuleneTerminalGeometryJudgment, oddCumuleneTerminalGeometryOfSides]

theorem enantiomorphicDoubleBondTerminalGeometryJudgment_iff_eq_reference
    (leftSide rightSide : DirectionalBondMarker)
    (geometry : BlueBookP92.EnantiomorphicDoubleBondTerminalGeometry) :
    EnantiomorphicDoubleBondTerminalGeometryJudgment leftSide rightSide geometry ↔
      geometry = enantiomorphicDoubleBondTerminalGeometryOfSides leftSide rightSide := by
  cases leftSide <;> cases rightSide <;> cases geometry <;>
    simp [EnantiomorphicDoubleBondTerminalGeometryJudgment,
      enantiomorphicDoubleBondTerminalGeometryOfSides]

/-- Independent final P-93 outcome evaluator, used only as a reference for the relational rule. -/
def oddCumuleneOutcomeOfGeometry : OddCumuleneTerminalGeometry → StereoOutcome
  | .together => StereoOutcome.alkene DoubleBondStereo.Z
  | .opposite => StereoOutcome.alkene DoubleBondStereo.E

/-- Independent final P-92 outcome evaluator for an enantiomorphic planar unit. -/
def enantiomorphicDoubleBondOutcomeOfGeometry :
    BlueBookP92.EnantiomorphicDoubleBondTerminalGeometry → StereoOutcome
  | .together => StereoOutcome.enantiomorphicDoubleBond
      SequenceDoubleBondDescriptor.seqCis
  | .opposite => StereoOutcome.enantiomorphicDoubleBond
      SequenceDoubleBondDescriptor.seqTrans

theorem oddCumuleneOutcomeOfGeometry_eq_iff_relational
    (geometry : OddCumuleneTerminalGeometry) (outcome : StereoOutcome) :
    oddCumuleneOutcomeOfGeometry geometry = outcome ↔
      ∃ descriptor,
        OddCumuleneEZAssignment geometry descriptor ∧
          OddCumuleneEZOutcomeJudgment descriptor outcome := by
  cases geometry
  · constructor
    · intro emitted
      exact ⟨.Z, trivial, emitted.symm⟩
    · rintro ⟨descriptor, assigned, judged⟩
      cases descriptor <;>
        simp_all [OddCumuleneEZAssignment, OddCumuleneEZOutcomeJudgment,
          oddCumuleneOutcomeOfGeometry]
  · constructor
    · intro emitted
      exact ⟨.E, trivial, emitted.symm⟩
    · rintro ⟨descriptor, assigned, judged⟩
      cases descriptor <;>
        simp_all [OddCumuleneEZAssignment, OddCumuleneEZOutcomeJudgment,
          oddCumuleneOutcomeOfGeometry]

theorem enantiomorphicDoubleBondOutcomeOfGeometry_eq_iff_relational
    (geometry : BlueBookP92.EnantiomorphicDoubleBondTerminalGeometry)
    (outcome : StereoOutcome) :
    enantiomorphicDoubleBondOutcomeOfGeometry geometry = outcome ↔
      ∃ descriptor,
        BlueBookP92.EnantiomorphicDoubleBondDescriptorAssignment geometry descriptor ∧
          SequenceDoubleBondOutcomeJudgment descriptor outcome := by
  cases geometry
  · constructor
    · intro emitted
      exact ⟨.seqCis, trivial, emitted.symm⟩
    · rintro ⟨descriptor, assigned, judged⟩
      cases descriptor <;>
        simp_all [BlueBookP92.EnantiomorphicDoubleBondDescriptorAssignment,
          SequenceDoubleBondOutcomeJudgment, enantiomorphicDoubleBondOutcomeOfGeometry]
  · constructor
    · intro emitted
      exact ⟨.seqTrans, trivial, emitted.symm⟩
    · rintro ⟨descriptor, assigned, judged⟩
      cases descriptor <;>
        simp_all [BlueBookP92.EnantiomorphicDoubleBondDescriptorAssignment,
          SequenceDoubleBondOutcomeJudgment, enantiomorphicDoubleBondOutcomeOfGeometry]

end BlueBookP93.Acyclic

/-- Independent endpoint-domain statement corresponding to a decisive P-92 Rule-5 comparison.
The endpoint must have exactly two explicit substituent branches and their first decisive official
family must be the enantiomorphic-descriptor tiebreak. -/
def BlueBookP92.Perception.Rule5EnantiomorphicEndpointJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel carbon partner : Nat) : Prop :=
  ∃ left right,
    mol.alkeneSubstituents carbon partner = [left, right] ∧
      decisiveOfficialFamilyForBranches? result mol state fuel carbon left right =
        some CIPRuleFamily.pseudoasymmetricTiebreak

theorem alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel carbon partner : Nat) :
    alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel carbon partner = true ↔
      BlueBookP92.Perception.Rule5EnantiomorphicEndpointJudgment
        result mol state fuel carbon partner := by
  unfold alkeneEndpointUsesPseudoasymmetricTiebreak
  unfold BlueBookP92.Perception.Rule5EnantiomorphicEndpointJudgment
  cases substituentsEq : mol.alkeneSubstituents carbon partner with
  | nil =>
      constructor
      · intro impossible
        simp at impossible
      · rintro ⟨left, right, listEq, decisionEq⟩
        simp at listEq
  | cons first rest =>
      cases rest with
      | nil =>
          constructor
          · intro impossible
            simp at impossible
          · rintro ⟨left, right, listEq, decisionEq⟩
            simp at listEq
      | cons second tail =>
          cases tail with
          | nil =>
              constructor
              · intro computed
                refine ⟨first, second, rfl, ?_⟩
                exact beq_iff_eq.mp computed
              · rintro ⟨left, right, listEq, decisionEq⟩
                injection listEq with firstEq restEq
                injection restEq with secondEq tailEq
                subst left
                subst right
                exact beq_iff_eq.mpr decisionEq
          | cons third more =>
              constructor
              · intro impossible
                simp at impossible
              · rintro ⟨left, right, listEq, decisionEq⟩
                simp at listEq

/-- Physical-chain parity used by P-93.4.2.3.  A chain of atoms has one fewer physical
double-bond edges. -/
def BlueBookP93.Acyclic.HasOddPhysicalDoubleBondCount (chain : List Nat) : Prop :=
  Odd (chain.length - 1)

theorem chain_length_even_iff_odd_physical_double_bond_count
    (chain : List Nat) (atLeastTwo : 2 ≤ chain.length) :
    chain.length % 2 = 0 ↔
      BlueBookP93.Acyclic.HasOddPhysicalDoubleBondCount chain := by
  unfold BlueBookP93.Acyclic.HasOddPhysicalDoubleBondCount
  rw [Nat.odd_sub (by omega)]
  simp [Nat.even_iff, Nat.not_odd_iff_even]

theorem ordinaryOddCumuleneComputedOutcome_eq_iff_independent_judgment
    (leftSide rightSide : DirectionalBondMarker) (outcome : StereoOutcome) :
    StereoOutcome.alkene
        (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide) = outcome ↔
      ∃ geometry descriptor,
        BlueBookP93.Acyclic.OddCumuleneTerminalGeometryJudgment
            leftSide rightSide geometry ∧
          BlueBookP93.Acyclic.OddCumuleneEZAssignment geometry descriptor ∧
          BlueBookP93.Acyclic.OddCumuleneEZOutcomeJudgment descriptor outcome := by
  let geometry :=
    BlueBookP93.Acyclic.oddCumuleneTerminalGeometryOfSides leftSide rightSide
  have productionReference :
      StereoOutcome.alkene
          (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide) =
        BlueBookP93.Acyclic.oddCumuleneOutcomeOfGeometry geometry := by
    cases leftSide <;> cases rightSide <;> rfl
  rw [productionReference]
  constructor
  · intro emitted
    obtain ⟨descriptor, assigned, outcomeJudgment⟩ :=
      (BlueBookP93.Acyclic.oddCumuleneOutcomeOfGeometry_eq_iff_relational
        geometry outcome).1 emitted
    exact ⟨geometry, descriptor,
      (BlueBookP93.Acyclic.oddCumuleneTerminalGeometryJudgment_iff_eq_reference
        leftSide rightSide geometry).2 rfl,
      assigned, outcomeJudgment⟩
  · rintro ⟨observedGeometry, descriptor, geometryJudgment, assigned, outcomeJudgment⟩
    have geometryEq :=
      (BlueBookP93.Acyclic.oddCumuleneTerminalGeometryJudgment_iff_eq_reference
        leftSide rightSide observedGeometry).1 geometryJudgment
    subst observedGeometry
    exact (BlueBookP93.Acyclic.oddCumuleneOutcomeOfGeometry_eq_iff_relational
      geometry outcome).2 ⟨descriptor, assigned, outcomeJudgment⟩

theorem enantiomorphicDoubleBondComputedOutcome_eq_iff_independent_judgment
    (leftSide rightSide : DirectionalBondMarker) (outcome : StereoOutcome) :
    sequenceDoubleBondOutcomeOfGeometry
        (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide) = outcome ↔
      ∃ geometry descriptor,
        BlueBookP93.Acyclic.EnantiomorphicDoubleBondTerminalGeometryJudgment
            leftSide rightSide geometry ∧
          BlueBookP92.EnantiomorphicDoubleBondDescriptorAssignment geometry descriptor ∧
          BlueBookP93.Acyclic.SequenceDoubleBondOutcomeJudgment descriptor outcome := by
  let geometry :=
    BlueBookP93.Acyclic.enantiomorphicDoubleBondTerminalGeometryOfSides leftSide rightSide
  have productionReference :
      sequenceDoubleBondOutcomeOfGeometry
          (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide) =
        BlueBookP93.Acyclic.enantiomorphicDoubleBondOutcomeOfGeometry geometry := by
    cases leftSide <;> cases rightSide <;> rfl
  rw [productionReference]
  constructor
  · intro emitted
    obtain ⟨descriptor, assigned, outcomeJudgment⟩ :=
      (BlueBookP93.Acyclic.enantiomorphicDoubleBondOutcomeOfGeometry_eq_iff_relational
        geometry outcome).1 emitted
    exact ⟨geometry, descriptor,
      (BlueBookP93.Acyclic.enantiomorphicDoubleBondTerminalGeometryJudgment_iff_eq_reference
          leftSide rightSide geometry).2 rfl,
      assigned, outcomeJudgment⟩
  · rintro ⟨observedGeometry, descriptor, geometryJudgment, assigned, outcomeJudgment⟩
    have geometryEq :=
      (BlueBookP93.Acyclic.enantiomorphicDoubleBondTerminalGeometryJudgment_iff_eq_reference
          leftSide rightSide observedGeometry).1 geometryJudgment
    subst observedGeometry
    exact (BlueBookP93.Acyclic.enantiomorphicDoubleBondOutcomeOfGeometry_eq_iff_relational
      geometry outcome).2 ⟨descriptor, assigned, outcomeJudgment⟩

theorem oddCumuleneComputedOutcome_eq_iff_independent_judgment
    (leftEnantiomorphic rightEnantiomorphic : Bool)
    (leftSide rightSide : DirectionalBondMarker) (outcome : StereoOutcome) :
    (if leftEnantiomorphic != rightEnantiomorphic then
        sequenceDoubleBondOutcomeOfGeometry
          (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide)
      else StereoOutcome.alkene
        (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide)) = outcome ↔
      BlueBookP93.Acyclic.OddCumulenePublicOutcomeJudgment
        (leftEnantiomorphic = true) (rightEnantiomorphic = true)
        leftSide rightSide outcome := by
  cases leftEnantiomorphic <;> cases rightEnantiomorphic <;>
    simp [BlueBookP93.Acyclic.OddCumulenePublicOutcomeJudgment,
      ordinaryOddCumuleneComputedOutcome_eq_iff_independent_judgment,
      enantiomorphicDoubleBondComputedOutcome_eq_iff_independent_judgment]

/-- Independent P-92/P-93 meaning of one descriptor-dependent physical double-bond result.

The relation exposes both CIP-senior terminal sides and both Rule-5 endpoint classifications.  It
does not transport the resulting geometry: after the senior sides have been selected, their
together/opposite relationship is already the final reference frame prescribed by P-92.4 and
P-92.6. -/
def BlueBookP93.Acyclic.DescriptorDependentDoubleBondAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (record : Nat × Nat × DoubleBondStereo) (assignment : StereoAssignment) : Prop :=
  let left := record.1
  let right := record.2.1
  assignment.unit = StereoUnit.doubleBond left right ∧
    ∃ leftSide rightSide,
      seniorSideThroughOfficialContext? result mol state fuel left right = some leftSide ∧
        seniorSideThroughOfficialContext? result mol state fuel right left = some rightSide ∧
        BlueBookP93.Acyclic.OddCumulenePublicOutcomeJudgment
          (BlueBookP92.Perception.Rule5EnantiomorphicEndpointJudgment
            result mol state fuel left right)
          (BlueBookP92.Perception.Rule5EnantiomorphicEndpointJudgment
            result mol state fuel right left)
          leftSide rightSide assignment.outcome

/-- Exact refinement of the direct descriptor-dependent double-bond adapter.

This theorem is the kernel-checked boundary that rules out the former double reflection: the
production result is characterized by the independent senior-side geometry relation itself, not
by a transported copy of that geometry. -/
theorem descriptorDependentDoubleBondAssignment?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (record : Nat × Nat × DoubleBondStereo) (assignment : StereoAssignment) :
    descriptorDependentDoubleBondAssignment? result mol state fuel record = some assignment ↔
      BlueBookP93.Acyclic.DescriptorDependentDoubleBondAssignmentJudgment
        result mol state fuel record assignment := by
  rcases record with ⟨left, right, inputStereo⟩
  unfold descriptorDependentDoubleBondAssignment?
  dsimp only [Prod.fst, Prod.snd]
  cases geometryEq :
      result.cipDoubleBondStereoThroughOfficialContext? mol state fuel left right with
  | none =>
      constructor
      · simp
      · intro judged
        unfold BlueBookP93.Acyclic.DescriptorDependentDoubleBondAssignmentJudgment at judged
        rcases judged with
          ⟨_unitEq, leftSide, rightSide, leftSideEq, rightSideEq, _outcomeJudgment⟩
        have impossible :
            result.cipDoubleBondStereoThroughOfficialContext? mol state fuel left right =
              some (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide) := by
          simp [ChemistryNormalizationResult.cipDoubleBondStereoThroughOfficialContext?,
            leftSideEq, rightSideEq]
        simp [geometryEq] at impossible
  | some geometry =>
      obtain ⟨leftSide, rightSide, leftSideEq, rightSideEq, geometryJudgment⟩ :=
        (cipDoubleBondStereoThroughOfficialContext?_eq_some_iff_geometryJudgment
          result mol state fuel left right geometry).1 geometryEq
      have geometryIsTerminal :
          StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide = geometry :=
        (stereoFromDirectionalMarkers_eq_iff_ordinaryAlkeneDescriptorJudgment
          leftSide rightSide geometry).2 geometryJudgment
      constructor
      · intro emitted
        have recordEq :
            ({ unit := StereoUnit.doubleBond left right
               outcome :=
                 if alkeneEndpointUsesPseudoasymmetricTiebreak
                        result mol state fuel left right !=
                      alkeneEndpointUsesPseudoasymmetricTiebreak
                        result mol state fuel right left then
                   sequenceDoubleBondOutcomeOfGeometry geometry
                 else StereoOutcome.alkene geometry } : StereoAssignment) = assignment :=
          Option.some.inj emitted
        have components :=
          (stereoAssignment_mk_eq_iff
            (StereoUnit.doubleBond left right)
            (if alkeneEndpointUsesPseudoasymmetricTiebreak
                    result mol state fuel left right !=
                  alkeneEndpointUsesPseudoasymmetricTiebreak
                    result mol state fuel right left then
               sequenceDoubleBondOutcomeOfGeometry geometry
             else StereoOutcome.alkene geometry)
            assignment).1 recordEq
        unfold BlueBookP93.Acyclic.DescriptorDependentDoubleBondAssignmentJudgment
        refine ⟨components.1, leftSide, rightSide, leftSideEq, rightSideEq, ?_⟩
        rw [← alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment,
          ← alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment]
        apply (oddCumuleneComputedOutcome_eq_iff_independent_judgment
          (alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel left right)
          (alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel right left)
          leftSide rightSide assignment.outcome).1
        rw [geometryIsTerminal]
        exact components.2.symm
      · intro judged
        unfold BlueBookP93.Acyclic.DescriptorDependentDoubleBondAssignmentJudgment at judged
        rcases judged with
          ⟨unitEq, observedLeft, observedRight,
            observedLeftEq, observedRightEq, outcomeJudgment⟩
        have observedGeometryEq :
            StereobondSemantics.stereoFromDirectionalMarkers observedLeft observedRight =
              geometry := by
          have observedComputed :
              result.cipDoubleBondStereoThroughOfficialContext? mol state fuel left right =
                some (StereobondSemantics.stereoFromDirectionalMarkers
                  observedLeft observedRight) := by
            simp [ChemistryNormalizationResult.cipDoubleBondStereoThroughOfficialContext?,
              observedLeftEq, observedRightEq]
          exact Option.some.inj (observedComputed.symm.trans geometryEq)
        rw [← alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment,
          ← alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment]
          at outcomeJudgment
        have outcomeEq :=
          (oddCumuleneComputedOutcome_eq_iff_independent_judgment
            (alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel left right)
            (alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel right left)
            observedLeft observedRight assignment.outcome).2 outcomeJudgment
        rw [observedGeometryEq] at outcomeEq
        apply congrArg some
        exact
          (stereoAssignment_mk_eq_iff
            (StereoUnit.doubleBond left right)
            (if alkeneEndpointUsesPseudoasymmetricTiebreak
                    result mol state fuel left right !=
                  alkeneEndpointUsesPseudoasymmetricTiebreak
                    result mol state fuel right left then
               sequenceDoubleBondOutcomeOfGeometry geometry
             else StereoOutcome.alkene geometry)
            assignment).2 ⟨unitEq, outcomeEq.symm⟩

/-- The retired coupled-network final-assignment residual.

A coupled network may supply occurrence-local Rule-3 ranking evidence, but it is not a proof that
one of its constituent physical bonds is a final stereogenic double-bond unit.  The production
router no longer has such an emission case, so its former residual proposition is empty.  Keeping
the named proposition makes the elimination theorem explicit and prevents a future network
optimization from silently reintroducing an unjudged public descriptor. -/
def NetworkCoupledDoubleBondAssignmentResidual
    (_result : ChemistryNormalizationResult) (_mol : RawMolecule)
    (_state : RawDescriptorState) (_fuel : Nat)
    (_ordinaryAssignments : List StereoAssignment)
    (_networks : List CoupledGeometryNetwork)
    (_record : Nat × Nat × DoubleBondStereo) (_assignment : StereoAssignment) : Prop :=
  False

/-- No coupled network can independently license a final constituent-bond descriptor. -/
theorem not_networkCoupledDoubleBondAssignmentResidual
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (ordinaryAssignments : List StereoAssignment)
    (networks : List CoupledGeometryNetwork)
    (record : Nat × Nat × DoubleBondStereo) (assignment : StereoAssignment) :
    ¬ NetworkCoupledDoubleBondAssignmentResidual
        result mol state fuel ordinaryAssignments networks record assignment := by
  exact id

/-- Independent meaning of the complete post-ordinary router.  The ordinary branch did not report
this unit, and the direct Rule-5/P-92 senior-side judgment licenses the emitted descriptor.
Coupled networks are deliberately absent: they are ranking observations, not final units. -/
def BlueBookP93.Acyclic.RoutedDescriptorDependentDoubleBondAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (ordinaryAssignments : List StereoAssignment)
    (_networks : List CoupledGeometryNetwork)
    (record : Nat × Nat × DoubleBondStereo) (assignment : StereoAssignment) : Prop :=
  let left := record.1
  let right := record.2.1
  (ordinaryAssignments.any fun reported =>
      reported.unit == StereoUnit.doubleBond left right) = false ∧
    DescriptorDependentDoubleBondAssignmentJudgment
      result mol state fuel record assignment

/-- Exact disjoint split of the post-ordinary router.

The residual disjunct is definitionally empty.  It is retained in this compatibility theorem so
older callers cannot mistake removal of the network override for an unproved equivalence. -/
theorem coupledOrDescriptorDependentDoubleBondAssignment?_eq_some_iff_judged_or_network_residual
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (ordinaryAssignments : List StereoAssignment)
    (networks : List CoupledGeometryNetwork)
    (record : Nat × Nat × DoubleBondStereo) (assignment : StereoAssignment) :
    coupledOrDescriptorDependentDoubleBondAssignment?
        result mol state fuel ordinaryAssignments networks record = some assignment ↔
      BlueBookP93.Acyclic.RoutedDescriptorDependentDoubleBondAssignmentJudgment
          result mol state fuel ordinaryAssignments networks record assignment ∨
        NetworkCoupledDoubleBondAssignmentResidual
          result mol state fuel ordinaryAssignments networks record assignment := by
  rcases record with ⟨left, right, inputStereo⟩
  cases ordinaryEq : ordinaryAssignments.any fun reported =>
      reported.unit == StereoUnit.doubleBond left right <;>
    simp [coupledOrDescriptorDependentDoubleBondAssignment?,
      BlueBookP93.Acyclic.RoutedDescriptorDependentDoubleBondAssignmentJudgment,
      NetworkCoupledDoubleBondAssignmentResidual, ordinaryEq,
      descriptorDependentDoubleBondAssignment?_eq_some_iff_independent_judgment]

/-- Exact independent specification of the complete post-ordinary physical-double-bond router. -/
theorem coupledOrDescriptorDependentDoubleBondAssignment?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (ordinaryAssignments : List StereoAssignment)
    (networks : List CoupledGeometryNetwork)
    (record : Nat × Nat × DoubleBondStereo) (assignment : StereoAssignment) :
    coupledOrDescriptorDependentDoubleBondAssignment?
        result mol state fuel ordinaryAssignments networks record = some assignment ↔
      BlueBookP93.Acyclic.RoutedDescriptorDependentDoubleBondAssignmentJudgment
        result mol state fuel ordinaryAssignments networks record assignment := by
  simpa [NetworkCoupledDoubleBondAssignmentResidual] using
    (coupledOrDescriptorDependentDoubleBondAssignment?_eq_some_iff_judged_or_network_residual
      result mol state fuel ordinaryAssignments networks record assignment)

/-- Exact independent meaning of the normalized post-ordinary double-bond segment.

Every member retains its particular parsed double-bond record and satisfies the independent
P-92/P-93 senior-side judgment.  Compiled coupled networks cannot create list members. -/
theorem mem_normalizedCoupledDoubleBond_iff_independent_judgment
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    assignment ∈ (normalizedStereoAnalysisBranches result).coupledDoubleBond ↔
      let mol := result.parsed.withExplicitHydrogens
      let fuel := analysisFuel mol
      let descriptorState := discoverRawDescriptors result mol fuel
      let state := normalizedGeometryDescriptorState result mol fuel descriptorState
      let ordinaryAssignments :=
        ordinaryDoubleBondAssignments result mol descriptorState fuel
      let networks := normalizedCoupledGeometryNetworks result mol state fuel
      ∃ record ∈ result.stereobonds.doubleBondAssignments,
        BlueBookP93.Acyclic.RoutedDescriptorDependentDoubleBondAssignmentJudgment
          result mol state fuel ordinaryAssignments networks record assignment := by
  rw [normalizedStereoAnalysisBranches_coupledDoubleBond]
  dsimp only
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨record, present, emitted⟩
    exact ⟨record, present,
      (coupledOrDescriptorDependentDoubleBondAssignment?_eq_some_iff_independent_judgment
        result result.parsed.withExplicitHydrogens
        (normalizedGeometryDescriptorState result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens)))
        (analysisFuel result.parsed.withExplicitHydrogens)
        (ordinaryDoubleBondAssignments result result.parsed.withExplicitHydrogens
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens))
          (analysisFuel result.parsed.withExplicitHydrogens))
        (normalizedCoupledGeometryNetworks result result.parsed.withExplicitHydrogens
          (normalizedGeometryDescriptorState result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens)
            (discoverRawDescriptors result result.parsed.withExplicitHydrogens
              (analysisFuel result.parsed.withExplicitHydrogens)))
          (analysisFuel result.parsed.withExplicitHydrogens))
        record assignment).1 emitted⟩
  · rintro ⟨record, present, judged⟩
    exact ⟨record, present,
      (coupledOrDescriptorDependentDoubleBondAssignment?_eq_some_iff_independent_judgment
        result result.parsed.withExplicitHydrogens
        (normalizedGeometryDescriptorState result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens)))
        (analysisFuel result.parsed.withExplicitHydrogens)
        (ordinaryDoubleBondAssignments result result.parsed.withExplicitHydrogens
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens))
          (analysisFuel result.parsed.withExplicitHydrogens))
        (normalizedCoupledGeometryNetworks result result.parsed.withExplicitHydrogens
          (normalizedGeometryDescriptorState result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens)
            (discoverRawDescriptors result result.parsed.withExplicitHydrogens
              (analysisFuel result.parsed.withExplicitHydrogens)))
          (analysisFuel result.parsed.withExplicitHydrogens))
        record assignment).2 judged⟩

/-- Independent P-92/P-93 judgment for one maximal-chain adapter result.  Parser topology,
physical odd-double-bond parity, both terminal senior-priority observations, the Rule-5 endpoint
classification, and the final descriptor relation remain explicit. -/
def BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) (chain : List Nat)
    (assignment : StereoAssignment) : Prop :=
  HasOddPhysicalDoubleBondCount chain ∧
    match cumulatedChainTerminalFrame? chain with
    | none => False
    | some (left, leftPartner, right, rightPartner) =>
        assignment.unit = StereoUnit.doubleBond left right ∧
          ∃ leftSide rightSide,
            seniorSideThroughOfficialContext? result mol state fuel left leftPartner =
                some leftSide ∧
              seniorSideThroughOfficialContext? result mol state fuel right rightPartner =
                some rightSide ∧
              OddCumulenePublicOutcomeJudgment
                (BlueBookP92.Perception.Rule5EnantiomorphicEndpointJudgment
                  result mol state fuel left leftPartner)
                (BlueBookP92.Perception.Rule5EnantiomorphicEndpointJudgment
                  result mol state fuel right rightPartner)
                leftSide rightSide assignment.outcome

/-- The production maximal-chain adapter emits exactly the assignments licensed by the
independent P-92/P-93 odd-cumulene judgment.  This equivalence includes failure: malformed
terminal frames, even physical double-bond counts, or unavailable senior-side observations are
rejected on both sides. -/
theorem oddCumuleneDoubleBondAssignment?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) (chain : List Nat)
    (assignment : StereoAssignment) :
    oddCumuleneDoubleBondAssignment? result mol state fuel chain = some assignment ↔
      BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment
        result mol state fuel chain assignment := by
  cases frameEq : cumulatedChainTerminalFrame? chain with
  | none =>
      simp [oddCumuleneDoubleBondAssignment?,
        BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment, frameEq]
  | some frame =>
      rcases frame with ⟨left, leftPartner, right, rightPartner⟩
      have atLeastTwo : 2 ≤ chain.length :=
        cumulatedChainTerminalFrame?_eq_some_length_at_least_two chain
          (left, leftPartner, right, rightPartner) frameEq
      have parityIff :=
        chain_length_even_iff_odd_physical_double_bond_count chain atLeastTwo
      by_cases even : chain.length % 2 = 0
      · have odd := parityIff.mp even
        cases leftSideEq :
            seniorSideThroughOfficialContext? result mol state fuel left leftPartner with
        | none =>
            simp [oddCumuleneDoubleBondAssignment?,
              BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment,
              frameEq, even, odd, leftSideEq]
        | some leftSide =>
            cases rightSideEq :
                seniorSideThroughOfficialContext? result mol state fuel right rightPartner with
            | none =>
                simp [oddCumuleneDoubleBondAssignment?,
                  BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment,
                  frameEq, even, odd, leftSideEq, rightSideEq]
            | some rightSide =>
                have guardFalse : ¬ ((chain.length % 2 != 0) = true) := by
                  simp [even]
                rw [oddCumuleneDoubleBondAssignment?, if_neg guardFalse]
                simp only [frameEq, leftSideEq, rightSideEq]
                constructor
                · intro emitted
                  have recordEq :
                      ({ unit := StereoUnit.doubleBond left right
                         outcome :=
                           if alkeneEndpointUsesPseudoasymmetricTiebreak
                                result mol state fuel left leftPartner !=
                              alkeneEndpointUsesPseudoasymmetricTiebreak
                                result mol state fuel right rightPartner then
                             sequenceDoubleBondOutcomeOfGeometry
                               (StereobondSemantics.stereoFromDirectionalMarkers
                                 leftSide rightSide)
                           else StereoOutcome.alkene
                             (StereobondSemantics.stereoFromDirectionalMarkers
                               leftSide rightSide) } : StereoAssignment) = assignment :=
                    Option.some.inj emitted
                  have components :=
                    (stereoAssignment_mk_eq_iff
                      (StereoUnit.doubleBond left right)
                      (if alkeneEndpointUsesPseudoasymmetricTiebreak
                            result mol state fuel left leftPartner !=
                          alkeneEndpointUsesPseudoasymmetricTiebreak
                            result mol state fuel right rightPartner then
                        sequenceDoubleBondOutcomeOfGeometry
                          (StereobondSemantics.stereoFromDirectionalMarkers
                            leftSide rightSide)
                       else StereoOutcome.alkene
                          (StereobondSemantics.stereoFromDirectionalMarkers
                            leftSide rightSide)) assignment).1 recordEq
                  unfold BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment
                  refine ⟨odd, ?_⟩
                  rw [frameEq]
                  refine ⟨components.1, leftSide, rightSide,
                    leftSideEq, rightSideEq, ?_⟩
                  rw [← alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment,
                    ← alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment]
                  exact
                    (oddCumuleneComputedOutcome_eq_iff_independent_judgment
                      (alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel
                        left leftPartner)
                      (alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel
                        right rightPartner)
                      leftSide rightSide assignment.outcome).1 components.2.symm
                · intro judged
                  unfold BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment at judged
                  rcases judged with ⟨_oddJudged, rest⟩
                  rw [frameEq] at rest
                  rcases rest with
                    ⟨unitEq, observedLeft, observedRight,
                      observedLeftEq, observedRightEq, publicJudgment⟩
                  have observedLeftIsLeft : observedLeft = leftSide :=
                    Option.some.inj (observedLeftEq.symm.trans leftSideEq)
                  have observedRightIsRight : observedRight = rightSide :=
                    Option.some.inj (observedRightEq.symm.trans rightSideEq)
                  subst observedLeft
                  subst observedRight
                  rw [← alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment,
                    ← alkeneEndpointUsesPseudoasymmetricTiebreak_eq_true_iff_independent_judgment]
                    at publicJudgment
                  have outcomeEq :=
                    (oddCumuleneComputedOutcome_eq_iff_independent_judgment
                      (alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel
                        left leftPartner)
                      (alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel
                        right rightPartner)
                      leftSide rightSide assignment.outcome).2 publicJudgment
                  apply congrArg some
                  exact
                    (stereoAssignment_mk_eq_iff
                      (StereoUnit.doubleBond left right)
                      (if alkeneEndpointUsesPseudoasymmetricTiebreak
                            result mol state fuel left leftPartner !=
                          alkeneEndpointUsesPseudoasymmetricTiebreak
                            result mol state fuel right rightPartner then
                        sequenceDoubleBondOutcomeOfGeometry
                          (StereobondSemantics.stereoFromDirectionalMarkers
                            leftSide rightSide)
                       else StereoOutcome.alkene
                          (StereobondSemantics.stereoFromDirectionalMarkers
                            leftSide rightSide)) assignment).2
                      ⟨unitEq, outcomeEq.symm⟩
      · have notOdd :
            ¬BlueBookP93.Acyclic.HasOddPhysicalDoubleBondCount chain := by
          intro odd
          exact even (parityIff.mpr odd)
        simp [oddCumuleneDoubleBondAssignment?,
          BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment,
          frameEq, even, notOdd]

/-- Exact list-level boundary for the P-93.4.2.3 odd-cumulene subanalyzer.  The witness is the
particular parser-perceived chain, so the theorem preserves both its identity and the full
independent descriptor judgment. -/
theorem mem_oddCumuleneDoubleBondAssignments_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) (assignment : StereoAssignment) :
    assignment ∈ oddCumuleneDoubleBondAssignments result mol state fuel ↔
      ∃ chain ∈ result.parsed.extendedDoubleBondChains,
        BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment
          result mol state fuel chain assignment := by
  constructor
  · intro present
    rw [oddCumuleneDoubleBondAssignments, List.mem_filterMap] at present
    obtain ⟨chain, chainPresent, emitted⟩ := present
    exact ⟨chain, chainPresent,
      (oddCumuleneDoubleBondAssignment?_eq_some_iff_independent_judgment
        result mol state fuel chain assignment).mp emitted⟩
  · rintro ⟨chain, chainPresent, judgment⟩
    rw [oddCumuleneDoubleBondAssignments, List.mem_filterMap]
    exact ⟨chain, chainPresent,
      (oddCumuleneDoubleBondAssignment?_eq_some_iff_independent_judgment
        result mol state fuel chain assignment).mpr judgment⟩

/-! ## Extended-tetrahedral even-cumulene axial output -/

namespace BlueBookP93.Acyclic

/-- Independent parity of the written endpoint-pair order after strict CIP ranking.  Exchanging
the two substituents at exactly one end is odd; exchanging neither or both is even. -/
def AxialEndpointOrderParityJudgment
    (leftDecision rightDecision : Ordering) (evenPermutation : Bool) : Prop :=
  match leftDecision, rightDecision, evenPermutation with
  | .gt, .gt, true
  | .lt, .lt, true
  | .gt, .lt, false
  | .lt, .gt, false => True
  | _, _, _ => False

/-- Independent correspondence from the collapsed-tetrahedron `R/S` sense to the general axial
`Rₐ/Sₐ` descriptor family. -/
def CollapsedTetrahedralAxialDescriptorJudgment
    (sense : RS) (descriptor : AxialDescriptor) : Prop :=
  match sense, descriptor with
  | .R, .Ra | .S, .Sa => True
  | _, _ => False

/-- Independent P-92/OpenSMILES interpretation of strict priority at both terminal pairs and the
annotated extended-tetrahedral parity. -/
def ExtendedTetrahedralAxialParityOutcomeJudgment
    (parity : TetrahedralInputParity)
    (leftDecision rightDecision : Ordering) (outcome : StereoOutcome) : Prop :=
  ∃ evenPermutation sense descriptor,
    AxialEndpointOrderParityJudgment leftDecision rightDecision evenPermutation ∧
      TetrahedralParityDescriptorJudgment parity evenPermutation sense ∧
      CollapsedTetrahedralAxialDescriptorJudgment sense descriptor ∧
      outcome = StereoOutcome.axial descriptor

/-- Independent final meaning of one parser-perceived extended-tetrahedral carrier.

The parser supplies the oriented axis and parity.  This relation independently states the
fail-closed endpoint ranking policy and the two-endpoint permutation truth table; it does not call
`extendedTetrahedralAxialOutcome`. -/
def ExtendedTetrahedralAxialOutcomeJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (carrier : ExtendedTetrahedralParityCarrier) (outcome : StereoOutcome) : Prop :=
  let leftLigands := (mol.writtenNeighbors carrier.left).filter fun atom =>
    atom != carrier.leftPartner
  let rightLigands := (mol.writtenNeighbors carrier.right).filter fun atom =>
    atom != carrier.rightPartner
  match leftLigands, rightLigands with
  | [leftFirst, leftSecond], [rightFirst, rightSecond] =>
      match compareBranchesThroughOfficialContext? result mol state fuel carrier.left
          leftFirst leftSecond,
        compareBranchesThroughOfficialContext? result mol state fuel carrier.right
          rightFirst rightSecond with
      | some Ordering.eq, _ | _, some Ordering.eq =>
          outcome = StereoOutcome.refused StereoRefusal.notStereogenic
      | none, _ | _, none =>
          outcome = StereoOutcome.refused StereoRefusal.rankingUnresolved
      | some leftDecision, some rightDecision =>
          ExtendedTetrahedralAxialParityOutcomeJudgment
            carrier.parity leftDecision rightDecision outcome
  | _, _ => outcome = StereoOutcome.refused StereoRefusal.rankingUnresolved

/-- Assignment-level form retaining the parser-perceived axis identity. -/
def ExtendedTetrahedralAxialAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (carrier : ExtendedTetrahedralParityCarrier)
    (assignment : StereoAssignment) : Prop :=
  assignment.unit = StereoUnit.axis carrier.left carrier.right ∧
    ExtendedTetrahedralAxialOutcomeJudgment
      result mol state fuel carrier assignment.outcome

end BlueBookP93.Acyclic

/-- The executable collapsed-parity calculation is exactly the independent axial truth table. -/
theorem extendedTetrahedralAxialParityOutcome_eq_iff_independent_judgment
    (parity : TetrahedralInputParity) (evenPermutation : Bool)
    (leftDecision rightDecision : Ordering)
    (endpointParity :
      BlueBookP93.Acyclic.AxialEndpointOrderParityJudgment
        leftDecision rightDecision evenPermutation)
    (outcome : StereoOutcome) :
    StereoOutcome.axial
        (match RawMolecule.descriptorOfParity parity evenPermutation with
         | .R => .Ra | .S => .Sa) = outcome ↔
      BlueBookP93.Acyclic.ExtendedTetrahedralAxialParityOutcomeJudgment
        parity leftDecision rightDecision outcome := by
  cases parity <;> cases evenPermutation <;> cases leftDecision <;>
    cases rightDecision <;>
    simp_all [BlueBookP93.Acyclic.AxialEndpointOrderParityJudgment,
      BlueBookP93.Acyclic.ExtendedTetrahedralAxialParityOutcomeJudgment,
      BlueBookP93.Acyclic.TetrahedralParityDescriptorJudgment,
      BlueBookP93.Acyclic.CollapsedTetrahedralAxialDescriptorJudgment,
      RawMolecule.descriptorOfParity] <;> aesop

/-- Exact outcome-level conformance for one parser-perceived extended-tetrahedral carrier. -/
theorem extendedTetrahedralAxialOutcome_eq_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (carrier : ExtendedTetrahedralParityCarrier) (outcome : StereoOutcome) :
    extendedTetrahedralAxialOutcome result mol state fuel carrier = outcome ↔
      BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment
        result mol state fuel carrier outcome := by
  generalize leftLigandsEq :
      (mol.writtenNeighbors carrier.left).filter
        (fun atom => atom != carrier.leftPartner) = leftLigands
  generalize rightLigandsEq :
      (mol.writtenNeighbors carrier.right).filter
        (fun atom => atom != carrier.rightPartner) = rightLigands
  cases leftLigands with
  | nil =>
      simp [extendedTetrahedralAxialOutcome,
        BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
        leftLigandsEq, rightLigandsEq, eq_comm]
  | cons leftFirst leftTail =>
      cases leftTail with
      | nil =>
          simp [extendedTetrahedralAxialOutcome,
            BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
            leftLigandsEq, rightLigandsEq, eq_comm]
      | cons leftSecond leftRest =>
          cases leftRest with
          | cons leftThird leftRest =>
              simp [extendedTetrahedralAxialOutcome,
                BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                leftLigandsEq, rightLigandsEq, eq_comm]
          | nil =>
              cases rightLigands with
              | nil =>
                  simp [extendedTetrahedralAxialOutcome,
                    BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                    leftLigandsEq, rightLigandsEq, eq_comm]
              | cons rightFirst rightTail =>
                  cases rightTail with
                  | nil =>
                      simp [extendedTetrahedralAxialOutcome,
                        BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                        leftLigandsEq, rightLigandsEq, eq_comm]
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | cons rightThird rightRest =>
                          simp [extendedTetrahedralAxialOutcome,
                            BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                            leftLigandsEq, rightLigandsEq, eq_comm]
                      | nil =>
                          cases leftCompared : compareBranchesThroughOfficialContext?
                              result mol state fuel carrier.left leftFirst leftSecond with
                          | none =>
                              cases rightCompared : compareBranchesThroughOfficialContext?
                                  result mol state fuel carrier.right rightFirst rightSecond with
                              | none =>
                                  simp [extendedTetrahedralAxialOutcome,
                                    BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                    leftLigandsEq, rightLigandsEq, leftCompared, rightCompared,
                                    eq_comm]
                              | some rightDecision =>
                                  cases rightDecision <;>
                                    simp [extendedTetrahedralAxialOutcome,
                                      BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                      leftLigandsEq, rightLigandsEq, leftCompared, rightCompared,
                                      eq_comm]
                          | some leftDecision =>
                              cases leftDecision with
                              | eq =>
                                  simp [extendedTetrahedralAxialOutcome,
                                    BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                    leftLigandsEq, rightLigandsEq, leftCompared, eq_comm]
                              | lt =>
                                  cases rightCompared : compareBranchesThroughOfficialContext?
                                      result mol state fuel carrier.right rightFirst rightSecond with
                                  | none =>
                                      simp [extendedTetrahedralAxialOutcome,
                                        BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                        leftLigandsEq, rightLigandsEq, leftCompared, rightCompared,
                                        eq_comm]
                                  | some rightDecision =>
                                      cases rightDecision with
                                      | eq =>
                                          simp [extendedTetrahedralAxialOutcome,
                                            BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                            leftLigandsEq, rightLigandsEq, leftCompared,
                                            rightCompared, eq_comm]
                                      | lt =>
                                          simpa [extendedTetrahedralAxialOutcome,
                                            BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                            leftLigandsEq, rightLigandsEq, leftCompared,
                                            rightCompared, RawMolecule.permutationIsEven,
                                            RawMolecule.inversionCount] using
                                            (extendedTetrahedralAxialParityOutcome_eq_iff_independent_judgment
                                              carrier.parity true Ordering.lt Ordering.lt
                                              (by trivial) outcome)
                                      | gt =>
                                          simpa [extendedTetrahedralAxialOutcome,
                                            BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                            leftLigandsEq, rightLigandsEq, leftCompared,
                                            rightCompared, RawMolecule.permutationIsEven,
                                            RawMolecule.inversionCount] using
                                            (extendedTetrahedralAxialParityOutcome_eq_iff_independent_judgment
                                              carrier.parity false Ordering.lt Ordering.gt
                                              (by trivial) outcome)
                              | gt =>
                                  cases rightCompared : compareBranchesThroughOfficialContext?
                                      result mol state fuel carrier.right rightFirst rightSecond with
                                  | none =>
                                      simp [extendedTetrahedralAxialOutcome,
                                        BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                        leftLigandsEq, rightLigandsEq, leftCompared, rightCompared,
                                        eq_comm]
                                  | some rightDecision =>
                                      cases rightDecision with
                                      | eq =>
                                          simp [extendedTetrahedralAxialOutcome,
                                            BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                            leftLigandsEq, rightLigandsEq, leftCompared,
                                            rightCompared, eq_comm]
                                      | lt =>
                                          simpa [extendedTetrahedralAxialOutcome,
                                            BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                            leftLigandsEq, rightLigandsEq, leftCompared,
                                            rightCompared, RawMolecule.permutationIsEven,
                                            RawMolecule.inversionCount] using
                                            (extendedTetrahedralAxialParityOutcome_eq_iff_independent_judgment
                                              carrier.parity false Ordering.gt Ordering.lt
                                              (by trivial) outcome)
                                      | gt =>
                                          simpa [extendedTetrahedralAxialOutcome,
                                            BlueBookP93.Acyclic.ExtendedTetrahedralAxialOutcomeJudgment,
                                            leftLigandsEq, rightLigandsEq, leftCompared,
                                            rightCompared, RawMolecule.permutationIsEven,
                                            RawMolecule.inversionCount] using
                                            (extendedTetrahedralAxialParityOutcome_eq_iff_independent_judgment
                                              carrier.parity true Ordering.gt Ordering.gt
                                              (by trivial) outcome)

/-- The public assignment adapter is exactly the independent axis/outcome judgment. -/
theorem extendedTetrahedralAxialAssignment_eq_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (carrier : ExtendedTetrahedralParityCarrier) (assignment : StereoAssignment) :
    extendedTetrahedralAxialAssignment result mol state fuel carrier = assignment ↔
      BlueBookP93.Acyclic.ExtendedTetrahedralAxialAssignmentJudgment
        result mol state fuel carrier assignment := by
  rw [extendedTetrahedralAxialAssignment, stereoAssignment_mk_eq_iff]
  exact and_congr_right fun _ => by
    simpa [eq_comm] using
      (extendedTetrahedralAxialOutcome_eq_iff_independent_judgment
        result mol state fuel carrier assignment.outcome)

/-- Exact membership in the complete normalized extended-axial segment. -/
theorem mem_normalizedExtendedAxial_iff_independent_judgment
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    assignment ∈ (normalizedStereoAnalysisBranches result).extendedAxial ↔
      let mol := result.parsed.withExplicitHydrogens
      let fuel := analysisFuel mol
      let descriptorState := discoverRawDescriptors result mol fuel
      let state := normalizedGeometryDescriptorState result mol fuel descriptorState
      ∃ carrier ∈ mol.extendedTetrahedralParityCarriers,
        BlueBookP93.Acyclic.ExtendedTetrahedralAxialAssignmentJudgment
          result mol state fuel carrier assignment := by
  rw [normalizedStereoAnalysisBranches_extendedAxial]
  dsimp only
  rw [List.mem_map]
  constructor
  · rintro ⟨carrier, present, emitted⟩
    exact ⟨carrier, present,
      (extendedTetrahedralAxialAssignment_eq_iff_independent_judgment
        result result.parsed.withExplicitHydrogens
        (normalizedGeometryDescriptorState result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens)))
        (analysisFuel result.parsed.withExplicitHydrogens) carrier assignment).mp emitted⟩
  · rintro ⟨carrier, present, judged⟩
    exact ⟨carrier, present,
      (extendedTetrahedralAxialAssignment_eq_iff_independent_judgment
        result result.parsed.withExplicitHydrogens
        (normalizedGeometryDescriptorState result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens)))
        (analysisFuel result.parsed.withExplicitHydrogens) carrier assignment).mpr judged⟩


/-! ## Exact classification of the normalized public output -/

/-- The independently judged complete normalized post-ordinary double-bond segment. -/
def IndependentlyJudgedNormalizedDescriptorDependentDoubleBondAssignment
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  let mol := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel mol
  let descriptorState := discoverRawDescriptors result mol fuel
  let state := normalizedGeometryDescriptorState result mol fuel descriptorState
  let ordinaryAssignments :=
    ordinaryDoubleBondAssignments result mol descriptorState fuel
  let networks := normalizedCoupledGeometryNetworks result mol state fuel
  ∃ record ∈ result.stereobonds.doubleBondAssignments,
    BlueBookP93.Acyclic.RoutedDescriptorDependentDoubleBondAssignmentJudgment
      result mol state fuel ordinaryAssignments networks record assignment

/-- Compatibility name for the retired network-coupled final-assignment remainder. -/
def NormalizedNetworkCoupledDoubleBondResidual
    (_result : ChemistryNormalizationResult) (_assignment : StereoAssignment) : Prop :=
  False

/-- The independent assignment meanings proved for tetrahedral, ordinary-double-bond, direct
descriptor-dependent double-bond, odd-cumulene, and extended-axial public results.

The local names reproduce the exact ranking molecule, fuel, and both descriptor states used by
`normalizedStereoAnalysisBranches`; no reconstructed or merely extensionally similar context is
substituted into any judgment. -/
def IndependentlyJudgedNormalizedStereoAssignment
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  let mol := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel mol
  let state := discoverRawDescriptors result mol fuel
  let geometryState := normalizedGeometryDescriptorState result mol fuel state
  (∃ idx < result.parsed.atomCount,
      BlueBookP93.Acyclic.PublicTetrahedralAssignmentJudgment
        result mol state fuel idx assignment) ∨
    (∃ record ∈ result.stereobonds.doubleBondAssignments,
      BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment
        result mol state fuel record assignment) ∨
    IndependentlyJudgedNormalizedDescriptorDependentDoubleBondAssignment result assignment ∨
      (∃ chain ∈ result.parsed.extendedDoubleBondChains,
        BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment
          result mol geometryState fuel chain assignment) ∨
        ∃ carrier ∈ mol.extendedTetrahedralParityCarriers,
          BlueBookP93.Acyclic.ExtendedTetrahedralAxialAssignmentJudgment
            result mol geometryState fuel carrier assignment

/-- There is no unjudged normalized-output family.  This compatibility proposition is empty. -/
def NormalizedStereoAnalysisResidualAssignment
    (_result : ChemistryNormalizationResult) (_assignment : StereoAssignment) : Prop :=
  False

/-- Every normalized-output residual hypothesis eliminates. -/
theorem not_normalizedStereoAnalysisResidualAssignment
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    ¬ NormalizedStereoAnalysisResidualAssignment result assignment := by
  exact id

/-- Exact normal form for every independently judged normalized-output family. -/
theorem independentlyJudgedNormalizedStereoAssignment_iff_branch_membership
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    IndependentlyJudgedNormalizedStereoAssignment result assignment ↔
      assignment ∈ (normalizedStereoAnalysisBranches result).tetrahedral ∨
        assignment ∈ (normalizedStereoAnalysisBranches result).ordinaryDoubleBond ∨
          IndependentlyJudgedNormalizedDescriptorDependentDoubleBondAssignment
              result assignment ∨
            assignment ∈
              (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond ∨
              assignment ∈
                (normalizedStereoAnalysisBranches result).extendedAxial := by
  simp only [IndependentlyJudgedNormalizedStereoAssignment,
    normalizedStereoAnalysisBranches_tetrahedral,
    normalizedStereoAnalysisBranches_ordinaryDoubleBond,
    normalizedStereoAnalysisBranches_oddCumuleneDoubleBond,
    mem_tetrahedralAssignments_iff_independent_judgment,
    mem_ordinaryDoubleBondAssignments_iff_independent_judgment,
    mem_oddCumuleneDoubleBondAssignments_iff_independent_judgment,
    mem_normalizedExtendedAxial_iff_independent_judgment]

/-- The former normalized-output residual is mathematically impossible. -/
theorem normalizedStereoAnalysisResidualAssignment_iff_branch_membership
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    NormalizedStereoAnalysisResidualAssignment result assignment ↔
      NormalizedNetworkCoupledDoubleBondResidual result assignment := by
  rfl

/-- Exact independent specification of the complete normalized analyzer.

An output exists precisely after both molecule-wide admission guards pass and one independently
specified assignment judgment holds.  Coupled topology may affect internal Rule-3 observations,
but cannot bypass a final stereogenic-unit judgment. -/
theorem mem_analyzeNormalized_iff_independently_judged
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    assignment ∈ analyzeNormalized result ↔
      result.parsed.rule2MassesKnown? = true ∧
        result.expandedStereochemicalAdmissible? = true ∧
          IndependentlyJudgedNormalizedStereoAssignment result assignment := by
  cases massesKnown : result.parsed.rule2MassesKnown? <;>
    cases admissible : result.expandedStereochemicalAdmissible? <;>
    simp [analyzeNormalized, massesKnown, admissible, List.mem_append,
      independentlyJudgedNormalizedStereoAssignment_iff_branch_membership,
      mem_normalizedCoupledDoubleBond_iff_independent_judgment,
      IndependentlyJudgedNormalizedDescriptorDependentDoubleBondAssignment]

/-- Backward-compatible statement of the former judged-or-residual partition.  Its residual
disjunct reduces to `False`; use `mem_analyzeNormalized_iff_independently_judged` for the sharp
authority theorem. -/
theorem mem_analyzeNormalized_iff_independently_judged_or_residual
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    assignment ∈ analyzeNormalized result ↔
      result.parsed.rule2MassesKnown? = true ∧
        result.expandedStereochemicalAdmissible? = true ∧
          (IndependentlyJudgedNormalizedStereoAssignment result assignment ∨
            NormalizedStereoAnalysisResidualAssignment result assignment) := by
  simpa [NormalizedStereoAnalysisResidualAssignment] using
    (mem_analyzeNormalized_iff_independently_judged result assignment)

/-! ## Packaged supported-domain result -/

/-- One checked certificate for the perception layers whose current production domains are
actually connected to independent predicates.  It deliberately says `Supported`: unannotated
The internal occurrence root remains annotation-gated; the public analyzer separately perceives
unannotated tetrahedral stereogenicity. General geometry-dependent unit discovery remains an
explicit observation boundary. -/
structure SupportedPerceptionConformance : Prop where
  tetrahedralCandidates : ∀ (mol : RawMolecule) (center : Fin mol.atomCount),
    FinalUnitEligible mol center ↔ BlueBookP92.Perception.TetrahedralCandidate mol center
  ordinaryTetrahedral : ∀ (mol : RawMolecule) (fuel : Nat) (aux : OccurrenceAuxState)
      (center : Fin mol.atomCount),
    FinalUnitEligible mol center → ∀ fact : OccurrenceAuxFact,
      (occurrenceFact? mol fuel aux (canonicalCenterRoot center.val) = some fact ↔
        BlueBookP92.Perception.OrdinaryTetrahedralPerceived mol fuel aux center fact)
  finalTetrahedral : ∀ {mol : RawMolecule} (discovery : Discovery mol) (fuel : Nat)
      (state : State discovery) (unit : FinalUnit mol) (descriptor : Descriptor),
    ProductionDescriptorJudgment discovery fuel state unit descriptor ↔
      (occurrenceSystem discovery fuel).FinalDescriptorJudgment state unit descriptor
  ordinaryDoubleBond : ∀ (mol : RawMolecule) (fuel left right : Nat),
    doubleBondStereogenicity mol fuel left right =
      (BlueBookP92.Perception.doubleBondDecision mol fuel left right).toProduction
  unannotatedTetrahedral : ∀ (result : ChemistryNormalizationResult)
      (mol : RawMolecule) (state : RawDescriptorState) (fuel center : Nat),
    tetrahedralStereogenicity result mol state fuel center =
      BlueBookP92.Perception.unannotatedTetrahedralDecision
        result mol state fuel center

theorem supportedPerceptionConforms_blueBookP92 : SupportedPerceptionConformance where
  tetrahedralCandidates := finalUnitEligible_iff_blueBookP92Candidate
  ordinaryTetrahedral := by
    intro mol fuel aux center eligible fact
    exact occurrenceFact?_iff_blueBookP92OrdinaryTetrahedralPerceived
      mol fuel aux center eligible fact
  finalTetrahedral := production_tetrahedral_perception_iff_independent_final_judgment
  ordinaryDoubleBond := doubleBondStereogenicity_conforms_blueBookP92Perception
  unannotatedTetrahedral :=
    tetrahedralStereogenicity_conforms_independent_unannotatedDecision

/-- Combined certificate for all independently connected layers on one successfully discovered
molecule: primitive sequence-rule decisions, faithful physical-ligand digraph construction, and
the supported perception judgments above. -/
structure SupportedMoleculeCIPConformance
    (mol : RawMolecule) (discovery : Discovery mol) : Prop where
  primitiveRules : PrimitiveP92Conformance
  moleculeDigraph : BlueBookP92.Digraph.MoleculeConformance mol discovery
  perception : SupportedPerceptionConformance

/-- Proof-carrying result of executing complete molecule-wide occurrence discovery on an admitted
ranking molecule. -/
structure ExecutableSupportedMoleculeCIPConformance (mol : RawMolecule) where
  discovery : Discovery mol
  conformance : SupportedMoleculeCIPConformance mol discovery

theorem supportedMoleculeCIPConforms_blueBookP92
    {mol : RawMolecule} (discovery : Discovery mol)
    (hadmissible : mol.Admissible)
    (hrootBonds : BlueBookP92.Digraph.PhysicalLigandRootsBonded mol) :
    SupportedMoleculeCIPConformance mol discovery where
  primitiveRules := primitiveRules_conform_blueBookP92
  moleculeDigraph := discovery.moleculeConformance hadmissible hrootBonds
  perception := supportedPerceptionConforms_blueBookP92

/-- Input-integrity form of the combined certificate: sound written-neighbor storage entails the
physical-root-bond premise needed by the molecular digraph layer. -/
theorem supportedMoleculeCIPConforms_blueBookP92_of_writtenNeighborSound
    {mol : RawMolecule} (discovery : Discovery mol)
    (hadmissible : mol.Admissible)
    (hsound : BlueBookP92.Digraph.WrittenNeighborSound mol) :
    SupportedMoleculeCIPConformance mol discovery where
  primitiveRules := primitiveRules_conform_blueBookP92
  moleculeDigraph := discovery.moleculeConformance_of_writtenNeighborSound hadmissible hsound
  perception := supportedPerceptionConforms_blueBookP92

/-- Fully checked stereochemical admission discharges every molecular input-integrity premise of
the combined primitive-rule, molecule-to-digraph, and stereogenic-perception certificate. -/
theorem supportedMoleculeCIPConforms_blueBookP92_of_stereochemicalAdmissible
    {mol : RawMolecule} (discovery : Discovery mol)
    (hadmissible : mol.StereochemicalAdmissible) :
    SupportedMoleculeCIPConformance mol discovery where
  primitiveRules := primitiveRules_conform_blueBookP92
  moleculeDigraph := discovery.moleculeConformance_of_stereochemicalAdmissible hadmissible
  perception := supportedPerceptionConforms_blueBookP92

/-- Execute exhaustive discovery and, on success, attach the independent P-92 digraph and
perception certificate derived solely from checked stereochemical admission. -/
def executableSupportedMoleculeCIPConformance?
    (mol : RawMolecule) (hadmissible : mol.StereochemicalAdmissible) :
    Option (ExecutableSupportedMoleculeCIPConformance mol) :=
  match discoverAll? mol with
  | none => none
  | some discovery =>
      some ⟨discovery,
        supportedMoleculeCIPConforms_blueBookP92_of_stereochemicalAdmissible
          discovery hadmissible⟩

/-- The proof-producing wrapper succeeds exactly when the production exhaustive discovery does. -/
@[simp] theorem executableSupportedMoleculeCIPConformance?_isSome
    (mol : RawMolecule) (hadmissible : mol.StereochemicalAdmissible) :
    (executableSupportedMoleculeCIPConformance? mol hadmissible).isSome =
      allCentersSucceeded? mol := by
  unfold executableSupportedMoleculeCIPConformance?
  cases discovered : discoverAll? mol <;> simp [← discoverAll?_isSome, discovered]

/-- An assignment returned by the production normalized-molecule analyzer can be connected
directly to the independent primitive-rule, molecule-to-digraph, and perception certificates for
the exact hydrogen-expanded ranking molecule.  Completeness of `discoverAll?` remains a separate
premise represented here by the supplied `Discovery`. -/
theorem supportedMoleculeCIPConforms_blueBookP92_of_analyzeNormalized_member
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeNormalized result)
    (discovery : Discovery result.parsed.withExplicitHydrogens) :
    SupportedMoleculeCIPConformance result.parsed.withExplicitHydrogens discovery :=
  supportedMoleculeCIPConforms_blueBookP92_of_stereochemicalAdmissible discovery
    (analyzeNormalized_member_expandedStereochemicalAdmissible result assignment member)

/-- Execute the proof-producing discovery wrapper for the exact molecule behind one returned
normalized-analysis member. -/
def executableSupportedMoleculeCIPConformanceOfAnalyzeNormalizedMember?
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeNormalized result) :
    Option (ExecutableSupportedMoleculeCIPConformance
      result.parsed.withExplicitHydrogens) :=
  executableSupportedMoleculeCIPConformance? result.parsed.withExplicitHydrogens
    (analyzeNormalized_member_expandedStereochemicalAdmissible result assignment member)

@[simp] theorem executableSupportedMoleculeCIPConformanceOfAnalyzeNormalizedMember?_isSome
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeNormalized result) :
    (executableSupportedMoleculeCIPConformanceOfAnalyzeNormalizedMember?
      result assignment member).isSome =
        allCentersSucceeded? result.parsed.withExplicitHydrogens := by
  exact executableSupportedMoleculeCIPConformance?_isSome _ _

end TetraStereo.OneCenter
