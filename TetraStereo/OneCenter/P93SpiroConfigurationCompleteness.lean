import TetraStereo.OneCenter.P93CyclicConfiguration
import TetraStereo.OneCenter.PolyhedralConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# Exact supplied-evidence configuration for P-93.5.3 spiro systems

The short `SpiroFamilySupported` table records descriptor families, but it does not say that every
listed family is emitted simultaneously.  P-93.5.3 instead has four distinct cases: ordinary
`R/S`, pseudoasymmetric `r/s` after the occurrence-sensitive `Xabab` traversal, the permitted
`M/P` description of an `Xaabb` axis, and coordination `A/C` notation for lambda-4 through
lambda-6 spiro atoms.  This module gives those cases an exact executable boundary.

Connectivity recognition, the actual CIP ranking, and coordinate-to-polyhedron perception remain
upstream evidence obligations.  Once a caller supplies that evidence, success and every refusal
below are complete and functional.
-/

/-- Mutually explicit descriptor modes occurring in P-93.5.3. -/
inductive SpiroConfigurationMode where
  | centerRS
  | centerPseudoRS
  | axialMP
  | polyhedralAC
  deriving DecidableEq, Repr

def SpiroConfigurationMode.family :
    SpiroConfigurationMode → SpiroDescriptorFamily
  | .centerRS => .centerRS
  | .centerPseudoRS => .centerRrSs
  | .axialMP => .axialMP
  | .polyhedralAC => .polyhedralAC

/-- Independent applicability relation for one chosen P-93.5.3 descriptor mode.

The tetrahedral cases reproduce the encoded ligand-pattern table.  The coordination case is
separate: lambda-4, lambda-5, and lambda-6 centers use polyhedral `A/C`, rather than also emitting
all tetrahedral pattern descriptors. -/
def SpiroConfigurationModeApplicable
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode) : Prop :=
  match coordination, pattern, mode with
  | .tetrahedral, .Xabcd, .centerRS
  | .tetrahedral, .Xabab, .centerRS
  | .tetrahedral, .Xabab, .centerPseudoRS
  | .tetrahedral, .Xaabb, .centerRS
  | .tetrahedral, .Xaabb, .axialMP
  | .lambda4, _, .polyhedralAC
  | .lambda5, _, .polyhedralAC
  | .lambda6, _, .polyhedralAC => True
  | _, _, _ => False

instance (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode) :
    Decidable (SpiroConfigurationModeApplicable pattern coordination mode) := by
  cases coordination <;> cases pattern <;> cases mode <;>
    simp [SpiroConfigurationModeApplicable] <;> exact inferInstance

/-- Exhaustive list of the modes admitted by the ligand pattern and coordination class. -/
def applicableSpiroConfigurationModes
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination) : List SpiroConfigurationMode :=
  match coordination, pattern with
  | .tetrahedral, .Xabcd => [.centerRS]
  | .tetrahedral, .Xabab => [.centerRS, .centerPseudoRS]
  | .tetrahedral, .Xaabb => [.centerRS, .axialMP]
  | .lambda4, _ | .lambda5, _ | .lambda6, _ => [.polyhedralAC]

@[simp] theorem mem_applicableSpiroConfigurationModes_iff
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode) :
    mode ∈ applicableSpiroConfigurationModes pattern coordination ↔
      SpiroConfigurationModeApplicable pattern coordination mode := by
  cases coordination <;> cases pattern <;> cases mode <;>
    simp [applicableSpiroConfigurationModes, SpiroConfigurationModeApplicable]

theorem applicableSpiroConfigurationModes_nodup
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination) :
    (applicableSpiroConfigurationModes pattern coordination).Nodup := by
  cases coordination <;> cases pattern <;>
    simp [applicableSpiroConfigurationModes]

theorem applicableSpiroConfigurationModes_ne_nil
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination) :
    applicableSpiroConfigurationModes pattern coordination ≠ [] := by
  cases coordination <;> cases pattern <;>
    simp [applicableSpiroConfigurationModes]

/-- On tetrahedral spiro atoms the new relation is exactly the pre-existing descriptor-family
table, with `centerPseudoRS` spelling its `centerRrSs` row. -/
theorem tetrahedral_mode_applicable_iff_family_supported
    (pattern : SpiroLigandPattern)
    (mode : SpiroConfigurationMode)
    (notPolyhedral : mode ≠ .polyhedralAC) :
    SpiroConfigurationModeApplicable pattern .tetrahedral mode ↔
      SpiroFamilySupported pattern mode.family := by
  cases pattern <;> cases mode <;>
    simp [SpiroConfigurationModeApplicable, SpiroConfigurationMode.family,
      SpiroFamilySupported] at notPolyhedral ⊢

/-- Executable form of the three occurrence choices required by the `Xabab` explanation in
P-93.5.3.2. -/
structure XababTraversalEvidence where
  firstSeniorChosen : Bool
  secondSeniorDistinguishedByTraversal : Bool
  juniorOnFirstSeniorBranchChosenFirst : Bool
  deriving DecidableEq, Repr

def ValidXababTraversalEvidence (evidence : XababTraversalEvidence) : Prop :=
  evidence.firstSeniorChosen = true ∧
    evidence.secondSeniorDistinguishedByTraversal = true ∧
    evidence.juniorOnFirstSeniorBranchChosenFirst = true

instance (evidence : XababTraversalEvidence) :
    Decidable (ValidXababTraversalEvidence evidence) := by
  unfold ValidXababTraversalEvidence
  infer_instance

/-- Exact bridge back to the original proof-relevant P-93.5.3.2 record. -/
def XababTraversalEvidence.toOccurrenceOrder
    (evidence : XababTraversalEvidence) : XababOccurrenceOrder where
  firstSeniorChosen := evidence.firstSeniorChosen = true
  secondSeniorDistinguishedByTraversal :=
    evidence.secondSeniorDistinguishedByTraversal = true
  juniorOnFirstSeniorBranchChosenFirst :=
    evidence.juniorOnFirstSeniorBranchChosenFirst = true

@[simp] theorem valid_toOccurrenceOrder_iff
    (evidence : XababTraversalEvidence) :
    ValidXababOccurrenceOrder evidence.toOccurrenceOrder ↔
      ValidXababTraversalEvidence evidence := by
  rfl

/-- Supplied descriptor evidence.  A local P-91 token is used for the three tetrahedral/axial
modes; the complete typed polyhedral descriptor is kept for the coordination mode. -/
structure SpiroConfigurationEvidence where
  xababTraversal? : Option XababTraversalEvidence
  localDescriptor? : Option BlueBookP91.Descriptor
  polyhedralDescriptor? : Option PolyhedralDescriptor
  deriving DecidableEq, Repr

/-- Boolean validator for the three occurrence choices in P-93.5.3.2. -/
def xababTraversalEvidenceValid (evidence : XababTraversalEvidence) : Bool :=
  evidence.firstSeniorChosen &&
    evidence.secondSeniorDistinguishedByTraversal &&
    evidence.juniorOnFirstSeniorBranchChosenFirst

@[simp] theorem xababTraversalEvidenceValid_eq_true_iff
    (evidence : XababTraversalEvidence) :
    xababTraversalEvidenceValid evidence = true ↔
      ValidXababTraversalEvidence evidence := by
  (cases evidence;
    simp [xababTraversalEvidenceValid, ValidXababTraversalEvidence, and_assoc])

/-- The occurrence-sensitive traversal is required exactly for center descriptors at an `Xabab`
spiro atom. -/
def spiroOccurrenceEvidenceReadyBool
    (pattern : SpiroLigandPattern)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) : Bool :=
  match pattern, mode with
  | .Xabab, .centerRS | .Xabab, .centerPseudoRS =>
      match evidence.xababTraversal? with
      | none => false
      | some traversal => xababTraversalEvidenceValid traversal
  | _, _ => true

def SpiroOccurrenceEvidenceReady
    (pattern : SpiroLigandPattern)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) : Prop :=
  spiroOccurrenceEvidenceReadyBool pattern mode evidence = true

instance (pattern : SpiroLigandPattern)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) :
    Decidable (SpiroOccurrenceEvidenceReady pattern mode evidence) := by
  unfold SpiroOccurrenceEvidenceReady
  infer_instance

/-- Explicit absence or invalidity of the occurrence traversal. -/
def SpiroOccurrenceEvidenceRefusal
    (pattern : SpiroLigandPattern)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) : Prop :=
  pattern = .Xabab ∧
    (mode = .centerRS ∨ mode = .centerPseudoRS) ∧
    (evidence.xababTraversal? = none ∨
      ∃ traversal,
        evidence.xababTraversal? = some traversal ∧
          ¬ValidXababTraversalEvidence traversal)

theorem not_spiroOccurrenceEvidenceReady_iff_refusal
    (pattern : SpiroLigandPattern)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) :
    ¬SpiroOccurrenceEvidenceReady pattern mode evidence ↔
      SpiroOccurrenceEvidenceRefusal pattern mode evidence := by
  cases pattern <;> cases mode <;> cases traversalEq : evidence.xababTraversal? with
  | none =>
      simp [SpiroOccurrenceEvidenceReady, spiroOccurrenceEvidenceReadyBool,
        SpiroOccurrenceEvidenceRefusal, traversalEq]
  | some traversal =>
      simp [SpiroOccurrenceEvidenceReady, spiroOccurrenceEvidenceReadyBool,
        SpiroOccurrenceEvidenceRefusal, traversalEq,
        xababTraversalEvidenceValid_eq_true_iff]

/-- P-91 token admitted by each local spiro descriptor mode. -/
def SpiroLocalDescriptorApplies :
    SpiroConfigurationMode → BlueBookP91.Descriptor → Prop
  | .centerRS, .capitalR | .centerRS, .capitalS
  | .centerPseudoRS, .lowercaseR | .centerPseudoRS, .lowercaseS
  | .axialMP, .capitalM | .axialMP, .capitalP => True
  | _, _ => False

instance (mode : SpiroConfigurationMode)
    (descriptor : BlueBookP91.Descriptor) :
    Decidable (SpiroLocalDescriptorApplies mode descriptor) := by
  cases mode <;> cases descriptor <;>
    simp [SpiroLocalDescriptorApplies] <;> exact inferInstance

/-- Every admitted local token also has the corresponding independent P-91 stereogenic-unit
applicability. -/
theorem spiroLocalDescriptorApplies_implies_P91
    (mode : SpiroConfigurationMode)
    (descriptor : BlueBookP91.Descriptor)
    (applies : SpiroLocalDescriptorApplies mode descriptor) :
    match mode with
    | .centerRS =>
        BlueBookP91.DescriptorApplies descriptor
          .quadriligantChiralityCenter
    | .centerPseudoRS =>
        BlueBookP91.DescriptorApplies descriptor .pseudoasymmetricCenter
    | .axialMP =>
        BlueBookP91.DescriptorApplies descriptor .axialHelicityEntity
    | .polyhedralAC => False := by
  cases mode <;> cases descriptor <;>
    simp [SpiroLocalDescriptorApplies, BlueBookP91.DescriptorApplies] at applies ⊢

def SpiroCenterCoordination.number : SpiroCenterCoordination → Nat
  | .tetrahedral | .lambda4 => 4
  | .lambda5 => 5
  | .lambda6 => 6

/-- Independent validity of a coordination descriptor used for a lambda-4 through lambda-6 spiro
atom: its idealized geometry has the stated coordination number and its absolute suffix is `A/C`.
-/
def SpiroPolyhedralACDescriptorJudgment
    (coordination : SpiroCenterCoordination)
    (descriptor : PolyhedralDescriptor) : Prop :=
  PolyhedralACApplicable coordination ∧
    descriptor.geometry.coordinationNumber = coordination.number ∧
    ∃ symbol, descriptor.absolute? = some (.ac symbol)

instance (coordination : SpiroCenterCoordination)
    (descriptor : PolyhedralDescriptor) :
    Decidable (SpiroPolyhedralACDescriptorJudgment coordination descriptor) := by
  cases coordination <;> cases absoluteEq : descriptor.absolute? with
  | none =>
      simp [SpiroPolyhedralACDescriptorJudgment, PolyhedralACApplicable,
        SpiroCenterCoordination.number, absoluteEq]; exact inferInstance
  | some absolute =>
      cases absolute <;>
        simp [SpiroPolyhedralACDescriptorJudgment, PolyhedralACApplicable,
          SpiroCenterCoordination.number, absoluteEq] <;>
        exact inferInstance

/-- Typed payload emitted by the supplied-evidence spiro analyzer. -/
inductive SpiroConfigurationPayload where
  | local (descriptor : BlueBookP91.Descriptor)
  | polyhedral (descriptor : PolyhedralDescriptor)
  deriving DecidableEq, Repr

/-- Independent exact payload meaning, including family applicability, occurrence traversal, token
family, polyhedral coordination number, and the `A/C` absolute suffix. -/
def SpiroConfigurationPayloadJudgment
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence)
    (payload : SpiroConfigurationPayload) : Prop :=
  SpiroConfigurationModeApplicable pattern coordination mode ∧
    SpiroOccurrenceEvidenceReady pattern mode evidence ∧
    match mode with
    | .centerRS | .centerPseudoRS | .axialMP =>
        ∃ descriptor,
          evidence.localDescriptor? = some descriptor ∧
            SpiroLocalDescriptorApplies mode descriptor ∧
            payload = .local descriptor
    | .polyhedralAC =>
        ∃ descriptor,
          evidence.polyhedralDescriptor? = some descriptor ∧
            SpiroPolyhedralACDescriptorJudgment coordination descriptor ∧
            payload = .polyhedral descriptor

/-- Executable local payload materializer. -/
def spiroConfigurationPayload?
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) :
    Option SpiroConfigurationPayload :=
  if _ : SpiroConfigurationModeApplicable pattern coordination mode then
    if _ : SpiroOccurrenceEvidenceReady pattern mode evidence then
      match mode with
      | .centerRS | .centerPseudoRS | .axialMP => do
          let descriptor ← evidence.localDescriptor?
          if _descriptorApplies : SpiroLocalDescriptorApplies mode descriptor then
            some (.local descriptor)
          else none
      | .polyhedralAC => do
          let descriptor ← evidence.polyhedralDescriptor?
          if _descriptorApplies :
              SpiroPolyhedralACDescriptorJudgment coordination descriptor then
            some (.polyhedral descriptor)
          else none
    else none
  else none

/-- Payload materialization is exact against the independent P-93/P-91/IR-9 judgment. -/
@[simp] theorem spiroConfigurationPayload?_eq_some_iff
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence)
    (payload : SpiroConfigurationPayload) :
    spiroConfigurationPayload? pattern coordination mode evidence = some payload ↔
      SpiroConfigurationPayloadJudgment pattern coordination mode evidence payload := by
  by_cases modeApplicable :
      SpiroConfigurationModeApplicable pattern coordination mode
  · by_cases occurrenceReady :
        SpiroOccurrenceEvidenceReady pattern mode evidence
    · cases mode with
      | centerRS =>
          cases descriptorEq : evidence.localDescriptor? with
          | none =>
              simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                modeApplicable, occurrenceReady, descriptorEq]
          | some descriptor =>
              by_cases descriptorApplies :
                  SpiroLocalDescriptorApplies .centerRS descriptor
              · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                  modeApplicable, occurrenceReady, descriptorEq, descriptorApplies, eq_comm]
              · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                  modeApplicable, occurrenceReady, descriptorEq, descriptorApplies]
      | centerPseudoRS =>
          cases descriptorEq : evidence.localDescriptor? with
          | none =>
              simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                modeApplicable, occurrenceReady, descriptorEq]
          | some descriptor =>
              by_cases descriptorApplies :
                  SpiroLocalDescriptorApplies .centerPseudoRS descriptor
              · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                  modeApplicable, occurrenceReady, descriptorEq, descriptorApplies, eq_comm]
              · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                  modeApplicable, occurrenceReady, descriptorEq, descriptorApplies]
      | axialMP =>
          cases descriptorEq : evidence.localDescriptor? with
          | none =>
              simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                modeApplicable, occurrenceReady, descriptorEq]
          | some descriptor =>
              by_cases descriptorApplies :
                  SpiroLocalDescriptorApplies .axialMP descriptor
              · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                  modeApplicable, occurrenceReady, descriptorEq, descriptorApplies, eq_comm]
              · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                  modeApplicable, occurrenceReady, descriptorEq, descriptorApplies]
      | polyhedralAC =>
          cases descriptorEq : evidence.polyhedralDescriptor? with
          | none =>
              simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                modeApplicable, occurrenceReady, descriptorEq]
          | some descriptor =>
              by_cases descriptorApplies :
                  SpiroPolyhedralACDescriptorJudgment coordination descriptor
              · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                  modeApplicable, occurrenceReady, descriptorEq, descriptorApplies, eq_comm]
              · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
                  modeApplicable, occurrenceReady, descriptorEq, descriptorApplies]
    · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
        modeApplicable, occurrenceReady]
  · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadJudgment,
      modeApplicable]

/-- Explicit missing-or-wrong-family descriptor evidence. -/
def SpiroDescriptorEvidenceRefusal
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) : Prop :=
  match mode with
  | .centerRS | .centerPseudoRS | .axialMP =>
      evidence.localDescriptor? = none ∨
        ∃ descriptor,
          evidence.localDescriptor? = some descriptor ∧
            ¬SpiroLocalDescriptorApplies mode descriptor
  | .polyhedralAC =>
      evidence.polyhedralDescriptor? = none ∨
        ∃ descriptor,
          evidence.polyhedralDescriptor? = some descriptor ∧
            ¬SpiroPolyhedralACDescriptorJudgment coordination descriptor


def SpiroConfigurationPayloadRefusal
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) : Prop :=
  ¬SpiroConfigurationModeApplicable pattern coordination mode ∨
    SpiroOccurrenceEvidenceRefusal pattern mode evidence ∨
    SpiroDescriptorEvidenceRefusal coordination mode evidence

theorem spiroConfigurationPayload?_eq_none_iff_refusal
    (pattern : SpiroLigandPattern)
    (coordination : SpiroCenterCoordination)
    (mode : SpiroConfigurationMode)
    (evidence : SpiroConfigurationEvidence) :
    spiroConfigurationPayload? pattern coordination mode evidence = none ↔
      SpiroConfigurationPayloadRefusal pattern coordination mode evidence := by
  by_cases modeApplicable :
      SpiroConfigurationModeApplicable pattern coordination mode
  · by_cases occurrenceReady :
        SpiroOccurrenceEvidenceReady pattern mode evidence
    · have occurrenceNotRefusal :
          ¬SpiroOccurrenceEvidenceRefusal pattern mode evidence := by
        intro refusal
        exact ((not_spiroOccurrenceEvidenceReady_iff_refusal
          pattern mode evidence).mpr refusal) occurrenceReady
      cases mode with
      | centerRS =>
          cases descriptorEq : evidence.localDescriptor? with
          | none =>
              simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
                SpiroDescriptorEvidenceRefusal, modeApplicable, occurrenceReady,
                occurrenceNotRefusal, descriptorEq]
          | some descriptor =>
              by_cases descriptorApplies :
                  SpiroLocalDescriptorApplies .centerRS descriptor <;>
                simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
                  SpiroDescriptorEvidenceRefusal, modeApplicable, occurrenceReady,
                  occurrenceNotRefusal, descriptorEq, descriptorApplies]
      | centerPseudoRS =>
          cases descriptorEq : evidence.localDescriptor? with
          | none =>
              simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
                SpiroDescriptorEvidenceRefusal, modeApplicable, occurrenceReady,
                occurrenceNotRefusal, descriptorEq]
          | some descriptor =>
              by_cases descriptorApplies :
                  SpiroLocalDescriptorApplies .centerPseudoRS descriptor <;>
                simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
                  SpiroDescriptorEvidenceRefusal, modeApplicable, occurrenceReady,
                  occurrenceNotRefusal, descriptorEq, descriptorApplies]
      | axialMP =>
          cases descriptorEq : evidence.localDescriptor? with
          | none =>
              simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
                SpiroDescriptorEvidenceRefusal, modeApplicable, occurrenceReady,
                occurrenceNotRefusal, descriptorEq]
          | some descriptor =>
              by_cases descriptorApplies :
                  SpiroLocalDescriptorApplies .axialMP descriptor <;>
                simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
                  SpiroDescriptorEvidenceRefusal, modeApplicable, occurrenceReady,
                  occurrenceNotRefusal, descriptorEq, descriptorApplies]
      | polyhedralAC =>
          cases descriptorEq : evidence.polyhedralDescriptor? with
          | none =>
              simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
                SpiroDescriptorEvidenceRefusal, modeApplicable, occurrenceReady,
                occurrenceNotRefusal, descriptorEq]
          | some descriptor =>
              by_cases descriptorApplies :
                  SpiroPolyhedralACDescriptorJudgment coordination descriptor <;>
                simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
                  SpiroDescriptorEvidenceRefusal, modeApplicable, occurrenceReady,
                  occurrenceNotRefusal, descriptorEq, descriptorApplies]
    · have occurrenceRefusal :=
        (not_spiroOccurrenceEvidenceReady_iff_refusal
          pattern mode evidence).mp occurrenceReady
      simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
        modeApplicable, occurrenceReady, occurrenceRefusal]
  · simp [spiroConfigurationPayload?, SpiroConfigurationPayloadRefusal,
      modeApplicable]

/-- One caller-identified spiro unit and its supplied classification/descriptor evidence. -/
structure SpiroConfigurationInput where
  unit : List Nat
  pattern : SpiroLigandPattern
  coordination : SpiroCenterCoordination
  mode : SpiroConfigurationMode
  evidence : SpiroConfigurationEvidence
  deriving DecidableEq, Repr

structure SpiroConfigurationAssignment where
  unit : List Nat
  pattern : SpiroLigandPattern
  coordination : SpiroCenterCoordination
  mode : SpiroConfigurationMode
  payload : SpiroConfigurationPayload
  deriving DecidableEq, Repr

def SpiroConfigurationAssignmentJudgment
    (input : SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) : Prop :=
  ∃ payload,
    SpiroConfigurationPayloadJudgment input.pattern input.coordination
      input.mode input.evidence payload ∧
    assignment =
      { unit := input.unit
        pattern := input.pattern
        coordination := input.coordination
        mode := input.mode
        payload }

def spiroConfigurationAssignment?
    (input : SpiroConfigurationInput) :
    Option SpiroConfigurationAssignment := do
  let payload ← spiroConfigurationPayload? input.pattern input.coordination
    input.mode input.evidence
  some
    { unit := input.unit
      pattern := input.pattern
      coordination := input.coordination
      mode := input.mode
      payload }

theorem spiroConfigurationAssignment?_eq_some_iff
    (input : SpiroConfigurationInput)
    (assignment : SpiroConfigurationAssignment) :
    spiroConfigurationAssignment? input = some assignment ↔
      SpiroConfigurationAssignmentJudgment input assignment := by
  constructor
  · intro computed
    unfold spiroConfigurationAssignment? at computed
    cases payloadEq : spiroConfigurationPayload? input.pattern input.coordination
        input.mode input.evidence with
    | none => simp [payloadEq] at computed
    | some payload =>
        simp [payloadEq] at computed
        subst assignment
        exact ⟨payload,
          (spiroConfigurationPayload?_eq_some_iff input.pattern input.coordination
            input.mode input.evidence payload).mp payloadEq,
          rfl⟩
  · rintro ⟨payload, payloadJudged, rfl⟩
    have payloadEq :=
      (spiroConfigurationPayload?_eq_some_iff input.pattern input.coordination
        input.mode input.evidence payload).mpr payloadJudged
    simp [spiroConfigurationAssignment?, payloadEq]

def SpiroConfigurationRefusal (input : SpiroConfigurationInput) : Prop :=
  SpiroConfigurationPayloadRefusal input.pattern input.coordination
    input.mode input.evidence

theorem spiroConfigurationAssignment?_eq_none_iff_refusal
    (input : SpiroConfigurationInput) :
    spiroConfigurationAssignment? input = none ↔
      SpiroConfigurationRefusal input := by
  unfold spiroConfigurationAssignment? SpiroConfigurationRefusal
  cases payloadEq : spiroConfigurationPayload? input.pattern input.coordination
      input.mode input.evidence with
  | none =>
      simpa [payloadEq] using
        (spiroConfigurationPayload?_eq_none_iff_refusal
          input.pattern input.coordination input.mode input.evidence).mp payloadEq
  | some payload =>
      have notRefusal : ¬SpiroConfigurationPayloadRefusal input.pattern
          input.coordination input.mode input.evidence := by
        intro refusal
        have noneEq :=
          (spiroConfigurationPayload?_eq_none_iff_refusal input.pattern
            input.coordination input.mode input.evidence).mpr refusal
        rw [payloadEq] at noneEq
        contradiction
      simp [notRefusal]

def SpiroConfigurationReady (input : SpiroConfigurationInput) : Prop :=
  ∃ assignment, SpiroConfigurationAssignmentJudgment input assignment

theorem spiroConfigurationAssignment?_isSome_iff_ready
    (input : SpiroConfigurationInput) :
    (spiroConfigurationAssignment? input).isSome = true ↔
      SpiroConfigurationReady input := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    spiroConfigurationAssignment?_eq_some_iff input assignment

theorem spiroConfigurationReady_iff_not_refusal
    (input : SpiroConfigurationInput) :
    SpiroConfigurationReady input ↔ ¬SpiroConfigurationRefusal input := by
  rw [← spiroConfigurationAssignment?_isSome_iff_ready]
  rw [← spiroConfigurationAssignment?_eq_none_iff_refusal]
  exact Option.isSome_iff_ne_none

theorem spiroConfigurationAssignmentJudgment_subsingleton
    (input : SpiroConfigurationInput)
    {left right : SpiroConfigurationAssignment}
    (leftJudged : SpiroConfigurationAssignmentJudgment input left)
    (rightJudged : SpiroConfigurationAssignmentJudgment input right) :
    left = right := by
  have leftComputed :=
    (spiroConfigurationAssignment?_eq_some_iff input left).mpr leftJudged
  have rightComputed :=
    (spiroConfigurationAssignment?_eq_some_iff input right).mpr rightJudged
  rw [leftComputed] at rightComputed
  exact Option.some.inj rightComputed

/-- Exact general boundary behind the two concrete seven/eight-member examples already present
in `P93CyclicConfiguration`. -/
theorem spiroDoubleBondDescriptorRequired_eq_true_iff
    (ringSize : Nat) :
    SpiroDoubleBondDescriptorRequired ringSize = true ↔ 8 ≤ ringSize := by
  simp [SpiroDoubleBondDescriptorRequired]

theorem spiroDoubleBondDescriptorRequired_eq_false_iff
    (ringSize : Nat) :
    SpiroDoubleBondDescriptorRequired ringSize = false ↔ ¬8 ≤ ringSize := by
  simp [SpiroDoubleBondDescriptorRequired]

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
