import TetraStereo.OneCenter.P93RCTReferenceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# Exact descriptor-bearing RCT pair configuration

This module composes the exact P-93.5.1.3.2 reference selector with the independent ring-side
relation.  Inputs remain observation-scoped: a caller identifies the ring, candidates, ligand,
mean-plane sides, and non-reentrant applicability facts.  The result is nevertheless exact at that
boundary—success has an independent semantic judgment and every `none` is one of the explicit
evidence or mean-plane failures.
-/

/-- Supplied evidence for one RCT ligand relative to the selected ring reference. -/
structure RCTPairConfigurationInput where
  unit : List Nat
  candidates : List RCTReferenceCandidate
  ligand : RCTReferenceCandidate
  referenceSide : RingSide
  ligandSide : RingSide
  usesMeanPlane : Bool
  referenceNotReentrant : Bool
  ligandNotReentrant : Bool
  deriving DecidableEq, Repr

/-- Complete result for one physical ring/ligand unit. -/
structure RCTPairConfigurationAssignment where
  unit : List Nat
  reference : RCTReferenceCandidate
  ligand : RCTReferenceCandidate
  descriptor : RCTDescriptor
  deriving DecidableEq, Repr

/-- Independent descriptor relation after a reference candidate has been established. -/
def RCTPairDescriptorJudgment
    (reference ligand : RCTReferenceCandidate)
    (referenceSide ligandSide : RingSide)
    (descriptor : RCTDescriptor) : Prop :=
  (ligand = reference ∧ descriptor = .reference) ∨
    (ligand ≠ reference ∧
      ((RelativeRingSide referenceSide ligandSide .cis ∧
          descriptor = .cisToReference) ∨
        (RelativeRingSide referenceSide ligandSide .trans ∧
          descriptor = .transToReference)))

/-- Executable descriptor compiler for the selected reference/ligand pair. -/
def rctPairDescriptor?
    (reference ligand : RCTReferenceCandidate)
    (referenceSide ligandSide : RingSide) : Option RCTDescriptor :=
  if ligand = reference then some .reference
  else rctDescriptor referenceSide ligandSide

/-- Pair descriptor compilation is exact against the independent reference-or-relative-side
relation. -/
theorem rctPairDescriptor?_eq_some_iff
    (reference ligand : RCTReferenceCandidate)
    (referenceSide ligandSide : RingSide)
    (descriptor : RCTDescriptor) :
    rctPairDescriptor? reference ligand referenceSide ligandSide = some descriptor ↔
      RCTPairDescriptorJudgment reference ligand referenceSide ligandSide descriptor := by
  by_cases same : ligand = reference
  · subst ligand
    simp [rctPairDescriptor?, RCTPairDescriptorJudgment, eq_comm]
  · cases referenceSide <;> cases ligandSide <;> cases descriptor <;>
      simp [rctPairDescriptor?, RCTPairDescriptorJudgment, rctDescriptor,
        RelativeRingSide, same]

/-- Exhaustive reason the selected pair cannot receive an RCT descriptor: it is not the reference
itself and at least one position lies on the ring mean plane. -/
def RCTPairDescriptorRefusal
    (reference ligand : RCTReferenceCandidate)
    (referenceSide ligandSide : RingSide) : Prop :=
  ligand ≠ reference ∧
    (referenceSide = .onMeanPlane ∨ ligandSide = .onMeanPlane)

theorem rctPairDescriptor?_eq_none_iff_refusal
    (reference ligand : RCTReferenceCandidate)
    (referenceSide ligandSide : RingSide) :
    rctPairDescriptor? reference ligand referenceSide ligandSide = none ↔
      RCTPairDescriptorRefusal reference ligand referenceSide ligandSide := by
  by_cases same : ligand = reference
  · subst ligand
    simp [rctPairDescriptor?, RCTPairDescriptorRefusal]
  · cases referenceSide <;> cases ligandSide <;>
      simp [rctPairDescriptor?, RCTPairDescriptorRefusal, rctDescriptor, same]

/-- Reflected nonspatial admission facts checked before reference selection. -/
def RCTPairConfigurationEvidenceReady
    (input : RCTPairConfigurationInput) : Prop :=
  RCTCandidateLocantsUnique input.candidates ∧
    input.ligand ∈ input.candidates ∧
    input.usesMeanPlane = true ∧
    input.referenceNotReentrant = true ∧
    input.ligandNotReentrant = true

instance (input : RCTPairConfigurationInput) :
    Decidable (RCTPairConfigurationEvidenceReady input) := by
  unfold RCTPairConfigurationEvidenceReady RCTCandidateLocantsUnique
  infer_instance

/-- Independent complete meaning of one emitted RCT pair assignment. -/
def RCTPairConfigurationAssignmentJudgment
    (input : RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) : Prop :=
  RCTPairConfigurationEvidenceReady input ∧
    ∃ reference descriptor,
      IsRCTReference input.candidates reference ∧
      RCTPairDescriptorJudgment reference input.ligand
        input.referenceSide input.ligandSide descriptor ∧
      assignment =
        { unit := input.unit
          reference
          ligand := input.ligand
          descriptor }

/-- Executable local RCT analyzer. -/
def rctPairConfigurationAssignment?
    (input : RCTPairConfigurationInput) :
    Option RCTPairConfigurationAssignment :=
  if RCTPairConfigurationEvidenceReady input then do
    let reference ← rctReference? input.candidates
    let descriptor ← rctPairDescriptor? reference input.ligand
      input.referenceSide input.ligandSide
    some { unit := input.unit, reference, ligand := input.ligand, descriptor }
  else none

/-- End-to-end local RCT success is exactly the independent reference, applicability, and
relative-side judgment. -/
theorem rctPairConfigurationAssignment?_eq_some_iff
    (input : RCTPairConfigurationInput)
    (assignment : RCTPairConfigurationAssignment) :
    rctPairConfigurationAssignment? input = some assignment ↔
      RCTPairConfigurationAssignmentJudgment input assignment := by
  constructor
  · intro computed
    by_cases evidenceReady : RCTPairConfigurationEvidenceReady input
    · simp only [rctPairConfigurationAssignment?, evidenceReady, ↓reduceIte] at computed
      cases referenceComputed : rctReference? input.candidates with
      | none => simp [referenceComputed] at computed
      | some reference =>
          cases descriptorComputed : rctPairDescriptor? reference input.ligand
              input.referenceSide input.ligandSide with
          | none => simp [referenceComputed, descriptorComputed] at computed
          | some descriptor =>
              simp [referenceComputed, descriptorComputed] at computed
              subst assignment
              exact ⟨evidenceReady, reference, descriptor,
                (rctReference?_eq_some_iff input.candidates evidenceReady.1 reference).mp
                  referenceComputed,
                (rctPairDescriptor?_eq_some_iff reference input.ligand
                  input.referenceSide input.ligandSide descriptor).mp descriptorComputed,
                rfl⟩
    · simp [rctPairConfigurationAssignment?, evidenceReady] at computed
  · rintro ⟨evidenceReady, reference, descriptor, referenceJudged,
      descriptorJudged, rfl⟩
    have referenceComputed :=
      (rctReference?_eq_some_iff input.candidates evidenceReady.1 reference).mpr
        referenceJudged
    have descriptorComputed :=
      (rctPairDescriptor?_eq_some_iff reference input.ligand
        input.referenceSide input.ligandSide descriptor).mpr descriptorJudged
    simp [rctPairConfigurationAssignment?, evidenceReady, referenceComputed,
      descriptorComputed]

/-- Explicit failure of the reflected admission evidence. -/
def RCTPairConfigurationEvidenceRefusal
    (input : RCTPairConfigurationInput) : Prop :=
  ¬ RCTCandidateLocantsUnique input.candidates ∨
    input.ligand ∉ input.candidates ∨
    input.usesMeanPlane = false ∨
    input.referenceNotReentrant = false ∨
    input.ligandNotReentrant = false

theorem not_rctPairConfigurationEvidenceReady_iff_refusal
    (input : RCTPairConfigurationInput) :
    ¬ RCTPairConfigurationEvidenceReady input ↔
      RCTPairConfigurationEvidenceRefusal input := by
  classical
  constructor
  · intro notReady
    by_cases locantsUnique : RCTCandidateLocantsUnique input.candidates
    · by_cases ligandPresent : input.ligand ∈ input.candidates
      · cases usesMeanPlane : input.usesMeanPlane with
        | false => exact .inr (.inr (.inl usesMeanPlane))
        | true =>
            cases referenceNotReentrant : input.referenceNotReentrant with
            | false => exact .inr (.inr (.inr (.inl referenceNotReentrant)))
            | true =>
                cases ligandNotReentrant : input.ligandNotReentrant with
                | false => exact .inr (.inr (.inr (.inr ligandNotReentrant)))
                | true =>
                    exact False.elim (notReady ⟨locantsUnique, ligandPresent,
                      usesMeanPlane, referenceNotReentrant, ligandNotReentrant⟩)
      · exact .inr (.inl ligandPresent)
    · exact .inl locantsUnique
  · intro refusal ready
    rcases refusal with notUnique | ligandAbsent | usesFalse | referenceFalse | ligandFalse
    · exact notUnique ready.1
    · exact ligandAbsent ready.2.1
    · rw [ready.2.2.1] at usesFalse
      contradiction
    · rw [ready.2.2.2.1] at referenceFalse
      contradiction
    · rw [ready.2.2.2.2] at ligandFalse
      contradiction

/-- Exhaustive local refusal: either reflected admission evidence fails, or the uniquely selected
reference/ligand pair is spatially undefined because a position is on the mean plane. -/
def RCTPairConfigurationRefusal
    (input : RCTPairConfigurationInput) : Prop :=
  RCTPairConfigurationEvidenceRefusal input ∨
    ∃ reference,
      RCTPairConfigurationEvidenceReady input ∧
      IsRCTReference input.candidates reference ∧
      RCTPairDescriptorRefusal reference input.ligand
        input.referenceSide input.ligandSide

/-- The local RCT analyzer returns `none` exactly for the explicit evidence-or-mean-plane
refusal. -/
theorem rctPairConfigurationAssignment?_eq_none_iff_refusal
    (input : RCTPairConfigurationInput) :
    rctPairConfigurationAssignment? input = none ↔
      RCTPairConfigurationRefusal input := by
  constructor
  · intro computed
    by_cases evidenceReady : RCTPairConfigurationEvidenceReady input
    · have candidatesNonempty : input.candidates ≠ [] := by
        intro empty
        have ligandPresent := evidenceReady.2.1
        rw [empty] at ligandPresent
        simp at ligandPresent
      obtain ⟨reference, referenceJudged⟩ :=
        exists_isRCTReference_of_ne_nil input.candidates candidatesNonempty
      have referenceComputed :=
        (rctReference?_eq_some_iff input.candidates evidenceReady.1 reference).mpr
          referenceJudged
      have descriptorNone : rctPairDescriptor? reference input.ligand
          input.referenceSide input.ligandSide = none := by
        cases descriptorComputed : rctPairDescriptor? reference input.ligand
            input.referenceSide input.ligandSide with
        | none => rfl
        | some descriptor =>
            simp [rctPairConfigurationAssignment?, evidenceReady, referenceComputed,
              descriptorComputed] at computed
      exact .inr ⟨reference, evidenceReady, referenceJudged,
        (rctPairDescriptor?_eq_none_iff_refusal reference input.ligand
          input.referenceSide input.ligandSide).mp descriptorNone⟩
    · exact .inl
        ((not_rctPairConfigurationEvidenceReady_iff_refusal input).mp evidenceReady)
  · intro refusal
    rcases refusal with evidenceRefusal |
      ⟨reference, evidenceReady, referenceJudged, descriptorRefusal⟩
    · have notReady :=
        (not_rctPairConfigurationEvidenceReady_iff_refusal input).mpr evidenceRefusal
      simp [rctPairConfigurationAssignment?, notReady]
    · have referenceComputed :=
        (rctReference?_eq_some_iff input.candidates evidenceReady.1 reference).mpr
          referenceJudged
      have descriptorNone :=
        (rctPairDescriptor?_eq_none_iff_refusal reference input.ligand
          input.referenceSide input.ligandSide).mpr descriptorRefusal
      simp [rctPairConfigurationAssignment?, evidenceReady, referenceComputed, descriptorNone]

def RCTPairConfigurationReady (input : RCTPairConfigurationInput) : Prop :=
  ∃ assignment, RCTPairConfigurationAssignmentJudgment input assignment

theorem rctPairConfigurationAssignment?_isSome_iff_ready
    (input : RCTPairConfigurationInput) :
    (rctPairConfigurationAssignment? input).isSome = true ↔
      RCTPairConfigurationReady input := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    rctPairConfigurationAssignment?_eq_some_iff input assignment


theorem rctPairConfigurationReady_iff_not_refusal
    (input : RCTPairConfigurationInput) :
    RCTPairConfigurationReady input ↔
      ¬ RCTPairConfigurationRefusal input := by
  rw [← rctPairConfigurationAssignment?_isSome_iff_ready]
  rw [← rctPairConfigurationAssignment?_eq_none_iff_refusal]
  exact Option.isSome_iff_ne_none

/-- A fixed supplied RCT pair has at most one independently valid assignment. -/
theorem rctPairConfigurationAssignmentJudgment_subsingleton
    (input : RCTPairConfigurationInput)
    {left right : RCTPairConfigurationAssignment}
    (leftJudged : RCTPairConfigurationAssignmentJudgment input left)
    (rightJudged : RCTPairConfigurationAssignmentJudgment input right) :
    left = right := by
  have leftComputed :=
    (rctPairConfigurationAssignment?_eq_some_iff input left).mpr leftJudged
  have rightComputed :=
    (rctPairConfigurationAssignment?_eq_some_iff input right).mpr rightJudged
  rw [leftComputed] at rightComputed
  exact Option.some.inj rightComputed

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
