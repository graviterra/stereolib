import TetraStereo.OneCenter.P93MolecularFullereneThreeLocantGeometry

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

open P94MolecularRingCycleScheduler

/-!
# General exterior orientation for fullerene descriptors

The P-93.5.6 `f,xC/A` rule asks a viewer outside the cage to inspect the polygon in which
numbering starts.  “Outside” is a side of the closed oriented surface, not a requirement that the
plane through C-1, C-2, and C-3 support every molecular coordinate.  This module therefore models
the general finite case by adding one typed global fact: whether the already coherent face lists
run clockwise or anticlockwise when viewed from outside.

The C-1→C-2→C-3 progression is still derived from the named starting face, and the resulting turn
is functional.  Exact supporting-coordinate evidence remains a stronger specialization.  Whenever
that coordinate judgment applies, a general record is admitted only if both routes give the same
turn; non-supporting but otherwise valid embedded cages are no longer rejected merely because the
local locant plane cuts through the cage.
-/

/-- Direction in which locants 1→2→3 traverse the declared starting-face list. -/
inductive FullereneNumberingProgression where
  | forward
  | reverse
  deriving DecidableEq, Repr

/-- Semantic orientation of every coherently ordered face list when viewed from outside the
fullerene cage. -/
inductive FullereneExteriorFaceSense where
  | clockwiseFromOutside
  | anticlockwiseFromOutside
  deriving DecidableEq, Repr

/-- `List.next` has one value at a fixed member of a fixed face. -/
theorem isForwardNamedCycleEdge_right_unique
    (face : List ℕ) (left first second : ℕ)
    (firstEdge : IsForwardNamedCycleEdge face left first)
    (secondEdge : IsForwardNamedCycleEdge face left second) :
    first = second := by
  rcases firstEdge with ⟨firstMember, firstEq⟩
  rcases secondEdge with ⟨secondMember, secondEq⟩
  rw [← firstEq, ← secondEq]

/-- Two consecutive undirected edges through three distinct vertices of a simple named cycle
traverse that cycle either wholly forward or wholly in reverse. -/
private theorem isNamedCycleEdge_path_forward_or_reverse
    (face : List ℕ) (first second third : ℕ)
    (faceNodup : face.Nodup)
    (firstNeThird : first ≠ third)
    (firstEdge : IsNamedCycleEdge face first second)
    (secondEdge : IsNamedCycleEdge face second third) :
    (IsForwardNamedCycleEdge face first second ∧
        IsForwardNamedCycleEdge face second third) ∨
      (IsForwardNamedCycleEdge face second first ∧
        IsForwardNamedCycleEdge face third second) := by
  rcases firstEdge with ⟨firstMember, firstNext | firstPrev⟩
  · rcases secondEdge with ⟨secondMember, secondNext | secondPrev⟩
    · exact .inl ⟨⟨firstMember, firstNext⟩, ⟨secondMember, secondNext⟩⟩
    · exfalso
      subst second
      have cycle :
          face.prev (face.next first firstMember) secondMember = first := by
        simpa only using List.prev_next face faceNodup first firstMember
      have thirdEqFirst : third = first := secondPrev.symm.trans cycle
      exact firstNeThird thirdEqFirst.symm
  · rcases secondEdge with ⟨secondMember, secondNext | secondPrev⟩
    · exfalso
      subst second
      have cycle :
          face.next (face.prev first firstMember) secondMember = first := by
        simpa only using List.next_prev face faceNodup first firstMember
      have firstEqThird : first = third := cycle.symm.trans secondNext
      exact firstNeThird firstEqThird
    · apply Or.inr
      subst second
      subst third
      refine ⟨⟨secondMember, ?_⟩, ⟨List.prev_mem face _ secondMember, ?_⟩⟩
      · simpa only using List.next_prev face faceNodup first firstMember
      · simpa only using
          List.next_prev face faceNodup (face.prev first firstMember) secondMember

/-- The numbered path follows or reverses the coherent orientation of its starting face. -/
def MolecularFullereneNumberingProgressionJudgment
    (evidence : MolecularFullereneNumberingEvidence) :
    FullereneNumberingProgression → Prop
  | .forward =>
      IsForwardNamedCycleEdge evidence.startingFace
          (molecularFullereneNumberedAtom evidence 0)
          (molecularFullereneNumberedAtom evidence 1) ∧
        IsForwardNamedCycleEdge evidence.startingFace
          (molecularFullereneNumberedAtom evidence 1)
          (molecularFullereneNumberedAtom evidence 2)
  | .reverse =>
      IsForwardNamedCycleEdge evidence.startingFace
          (molecularFullereneNumberedAtom evidence 1)
          (molecularFullereneNumberedAtom evidence 0) ∧
        IsForwardNamedCycleEdge evidence.startingFace
          (molecularFullereneNumberedAtom evidence 2)
          (molecularFullereneNumberedAtom evidence 1)

noncomputable instance molecularFullereneNumberingProgressionJudgmentDecidable
    (evidence : MolecularFullereneNumberingEvidence)
    (progression : FullereneNumberingProgression) :
    Decidable (MolecularFullereneNumberingProgressionJudgment evidence progression) :=
  Classical.propDecidable _

private theorem molecularFullereneNumberedAtom_zero_ne_two
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (judged : MolecularFullereneNumberingEvidenceJudgment input evidence) :
    molecularFullereneNumberedAtom evidence 0 ≠
      molecularFullereneNumberedAtom evidence 2 := by
  rcases judged.2.2.2 with
    ⟨first, second, third, firstEq, _secondEq, thirdEq,
      _firstNeSecond, _secondNeThird, firstNeThird, _firstEdge, _secondEdge⟩
  simpa [molecularFullereneNumberedAtom, firstEq, thirdEq] using firstNeThird

/-- A duplicate-free numbered starting polygon cannot traverse locants 1→2→3 both forward and
backward. -/
theorem molecularFullereneNumberingProgressionJudgment_functional
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (numberingJudged : MolecularFullereneNumberingEvidenceJudgment input evidence)
    (first second : FullereneNumberingProgression)
    (firstJudged : MolecularFullereneNumberingProgressionJudgment evidence first)
    (secondJudged : MolecularFullereneNumberingProgressionJudgment evidence second) :
    first = second := by
  have firstNeThird :=
    molecularFullereneNumberedAtom_zero_ne_two input evidence numberingJudged
  cases first <;> cases second
  · rfl
  · exfalso
    have thirdEqFirst := isForwardNamedCycleEdge_right_unique
      evidence.startingFace
      (molecularFullereneNumberedAtom evidence 1)
      (molecularFullereneNumberedAtom evidence 2)
      (molecularFullereneNumberedAtom evidence 0)
      firstJudged.2 secondJudged.1
    exact firstNeThird thirdEqFirst.symm
  · exfalso
    have firstEqThird := isForwardNamedCycleEdge_right_unique
      evidence.startingFace
      (molecularFullereneNumberedAtom evidence 1)
      (molecularFullereneNumberedAtom evidence 0)
      (molecularFullereneNumberedAtom evidence 2)
      firstJudged.1 secondJudged.2
    exact firstNeThird firstEqThird
  · rfl

/-- Every valid three-locant start on a coherently oriented molecular face has a forward or reverse
progression.  This is the no-omission companion to progression functionality. -/
theorem molecularFullereneNumberingProgressionJudgment_exists
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (orientedJudged : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (numberingJudged : MolecularFullereneNumberingEvidenceJudgment input evidence) :
    ∃ progression,
      MolecularFullereneNumberingProgressionJudgment evidence progression := by
  rcases numberingJudged.2.2.2 with
    ⟨first, second, third, firstEq, secondEq, thirdEq,
      _firstNeSecond, _secondNeThird, firstNeThird, firstEdge, secondEdge⟩
  have faceNodup : evidence.startingFace.Nodup :=
    (orientedJudged.1.facesValid evidence.startingFace numberingJudged.2.2.1).1.2.1
  have numberedFirstNeThird :
      molecularFullereneNumberedAtom evidence 0 ≠
        molecularFullereneNumberedAtom evidence 2 := by
    simpa [molecularFullereneNumberedAtom, firstEq, thirdEq] using firstNeThird
  have numberedFirstEdge :
      IsNamedCycleEdge evidence.startingFace
        (molecularFullereneNumberedAtom evidence 0)
        (molecularFullereneNumberedAtom evidence 1) := by
    simpa [molecularFullereneNumberedAtom, firstEq, secondEq] using firstEdge
  have numberedSecondEdge :
      IsNamedCycleEdge evidence.startingFace
        (molecularFullereneNumberedAtom evidence 1)
        (molecularFullereneNumberedAtom evidence 2) := by
    simpa [molecularFullereneNumberedAtom, secondEq, thirdEq] using secondEdge
  rcases isNamedCycleEdge_path_forward_or_reverse evidence.startingFace
      (molecularFullereneNumberedAtom evidence 0)
      (molecularFullereneNumberedAtom evidence 1)
      (molecularFullereneNumberedAtom evidence 2)
      faceNodup numberedFirstNeThird numberedFirstEdge numberedSecondEdge with
    forward | reverse
  · exact ⟨.forward, forward⟩
  · exact ⟨.reverse, reverse⟩

/-- Convert an outside-oriented face traversal and the numbered path direction to the official
clockwise/anticlockwise turn. -/
def fullereneExteriorTurn :
    FullereneExteriorFaceSense → FullereneNumberingProgression → ThreeLocantTurn
  | .clockwiseFromOutside, .forward => .clockwise
  | .clockwiseFromOutside, .reverse => .anticlockwise
  | .anticlockwiseFromOutside, .forward => .anticlockwise
  | .anticlockwiseFromOutside, .reverse => .clockwise

/-- Independent general meaning of the P-93.5.6 turn on an exterior-oriented finite face map. -/
def MolecularFullereneExteriorTurnJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (exteriorSense : FullereneExteriorFaceSense)
    (turn : ThreeLocantTurn) : Prop :=
  OrientedMolecularFullereneFaceMapJudgment molecule input ∧
    MolecularFullereneNumberingEvidenceJudgment input evidence ∧
    ∃ progression,
      MolecularFullereneNumberingProgressionJudgment evidence progression ∧
        fullereneExteriorTurn exteriorSense progression = turn

/-- Generic constructor: once the face orientation, numbered start, declared exterior sense, and
progression are known, the turn is forced by the mathematical two-by-two orientation table.
Source-facing users must authorize the exterior sense independently. -/
theorem molecularFullereneExteriorTurnJudgment_of_progression
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (exteriorSense : FullereneExteriorFaceSense)
    (progression : FullereneNumberingProgression)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (numbering : MolecularFullereneNumberingEvidenceJudgment input evidence)
    (progressionJudged :
      MolecularFullereneNumberingProgressionJudgment evidence progression) :
    MolecularFullereneExteriorTurnJudgment molecule input evidence exteriorSense
      (fullereneExteriorTurn exteriorSense progression) := by
  exact ⟨oriented, numbering, progression, progressionJudged, rfl⟩

noncomputable instance molecularFullereneExteriorTurnJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (exteriorSense : FullereneExteriorFaceSense)
    (turn : ThreeLocantTurn) :
    Decidable (MolecularFullereneExteriorTurnJudgment
      molecule input evidence exteriorSense turn) :=
  Classical.propDecidable _

/-- One exterior-oriented numbered face map has at most one official turn. -/
theorem molecularFullereneExteriorTurnJudgment_functional
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (exteriorSense : FullereneExteriorFaceSense)
    (first second : ThreeLocantTurn)
    (firstJudged : MolecularFullereneExteriorTurnJudgment
      molecule input evidence exteriorSense first)
    (secondJudged : MolecularFullereneExteriorTurnJudgment
      molecule input evidence exteriorSense second) :
    first = second := by
  rcases firstJudged.2.2 with ⟨firstProgression, firstProgressionJudged, firstEq⟩
  rcases secondJudged.2.2 with ⟨secondProgression, secondProgressionJudged, secondEq⟩
  have progressionEq :=
    molecularFullereneNumberingProgressionJudgment_functional input evidence
      firstJudged.2.1 firstProgression secondProgression
      firstProgressionJudged secondProgressionJudged
  subst secondProgression
  exact firstEq.symm.trans secondEq

/-- Every valid exterior-oriented numbered face map has an official clockwise or anticlockwise
turn. -/
theorem molecularFullereneExteriorTurnJudgment_exists
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (exteriorSense : FullereneExteriorFaceSense)
    (orientedJudged : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (numberingJudged : MolecularFullereneNumberingEvidenceJudgment input evidence) :
    ∃ turn,
      MolecularFullereneExteriorTurnJudgment
        molecule input evidence exteriorSense turn := by
  rcases molecularFullereneNumberingProgressionJudgment_exists molecule input evidence
      orientedJudged numberingJudged with ⟨progression, progressionJudged⟩
  exact ⟨fullereneExteriorTurn exteriorSense progression,
    orientedJudged, numberingJudged, progression, progressionJudged, rfl⟩

/-- Derive the official turn from a general exterior-oriented molecular face map. -/
noncomputable def molecularFullereneExteriorTurn?
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (exteriorSense : FullereneExteriorFaceSense) : Option ThreeLocantTurn :=
  if MolecularFullereneExteriorTurnJudgment
      molecule input evidence exteriorSense .clockwise then
    some .clockwise
  else if MolecularFullereneExteriorTurnJudgment
      molecule input evidence exteriorSense .anticlockwise then
    some .anticlockwise
  else
    none

/-- General turn derivation is exact against the independent exterior-surface judgment. -/
@[simp] theorem molecularFullereneExteriorTurn?_eq_some_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (exteriorSense : FullereneExteriorFaceSense)
    (turn : ThreeLocantTurn) :
    molecularFullereneExteriorTurn? molecule input evidence exteriorSense = some turn ↔
      MolecularFullereneExteriorTurnJudgment
        molecule input evidence exteriorSense turn := by
  by_cases clockwise : MolecularFullereneExteriorTurnJudgment
      molecule input evidence exteriorSense .clockwise
  · have notAnticlockwise : ¬MolecularFullereneExteriorTurnJudgment
        molecule input evidence exteriorSense .anticlockwise := by
      intro anticlockwise
      cases molecularFullereneExteriorTurnJudgment_functional molecule input evidence
        exteriorSense .clockwise .anticlockwise clockwise anticlockwise
    cases turn <;>
      simp [molecularFullereneExteriorTurn?, clockwise, notAnticlockwise]
  · by_cases anticlockwise : MolecularFullereneExteriorTurnJudgment
        molecule input evidence exteriorSense .anticlockwise
    · cases turn <;>
        simp [molecularFullereneExteriorTurn?, clockwise, anticlockwise]
    · cases turn <;>
        simp [molecularFullereneExteriorTurn?, clockwise, anticlockwise]

/-- Refusal is exactly the absence of either exterior-oriented turn judgment. -/
@[simp] theorem molecularFullereneExteriorTurn?_eq_none_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (exteriorSense : FullereneExteriorFaceSense) :
    molecularFullereneExteriorTurn? molecule input evidence exteriorSense = none ↔
      ¬∃ turn,
        MolecularFullereneExteriorTurnJudgment
          molecule input evidence exteriorSense turn := by
  constructor
  · intro computed
    rintro ⟨turn, judged⟩
    have success :=
      (molecularFullereneExteriorTurn?_eq_some_iff
        molecule input evidence exteriorSense turn).mpr judged
    rw [computed] at success
    cases success
  · intro noTurn
    cases computed : molecularFullereneExteriorTurn?
        molecule input evidence exteriorSense with
    | none => rfl
    | some turn =>
        have judged :=
          (molecularFullereneExteriorTurn?_eq_some_iff
            molecule input evidence exteriorSense turn).mp computed
        exact False.elim (noTurn ⟨turn, judged⟩)

/-- General source record: the outside side is carried by the global coherent surface orientation,
while exact coordinates remain available for consistency checks whenever the supporting test
applies. -/
structure ExteriorDerivedMolecularFullereneConfigurationInput where
  symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput
  numberingEvidence : MolecularFullereneNumberingEvidence
  exteriorSense : FullereneExteriorFaceSense

/-- General admission accepts every coherent exterior-oriented cage numbering, requires exact
descriptor agreement, and forbids disagreement with the stronger supporting-coordinate test on
the subdomain where that test applies. -/
def ExteriorDerivedMolecularFullereneConfigurationInputJudgment
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : ExteriorDerivedMolecularFullereneConfigurationInput) : Prop :=
  SymmetryDerivedMolecularFullereneConfigurationInputJudgment
      molecule input.symmetryInput ∧
    ∃ turn,
      MolecularFullereneExteriorTurnJudgment molecule input.symmetryInput.cage
          input.numberingEvidence input.exteriorSense turn ∧
        input.symmetryInput.cage.descriptorEvidence.cageNumberingKind =
          some input.numberingEvidence.numberingKind ∧
        input.symmetryInput.cage.descriptorEvidence.cageTurn = some turn ∧
        ∀ supportingTurn,
          MolecularFullereneThreeLocantTurnJudgment spatial input.symmetryInput.cage
              input.numberingEvidence supportingTurn →
            supportingTurn = turn

noncomputable instance exteriorDerivedMolecularFullereneConfigurationInputJudgmentDecidable
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : ExteriorDerivedMolecularFullereneConfigurationInput) :
    Decidable (ExteriorDerivedMolecularFullereneConfigurationInputJudgment
      molecule spatial input) :=
  Classical.propDecidable _

/-- On the supporting-coordinate subdomain, the admitted general surface turn is forced to agree
with the coordinate-derived outside view. -/
theorem ExteriorDerivedMolecularFullereneConfigurationInputJudgment.supporting_turn_agrees
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : ExteriorDerivedMolecularFullereneConfigurationInput)
    (judged : ExteriorDerivedMolecularFullereneConfigurationInputJudgment
      molecule spatial input)
    (surfaceTurn supportingTurn : ThreeLocantTurn)
    (surfaceJudged : MolecularFullereneExteriorTurnJudgment molecule input.symmetryInput.cage
      input.numberingEvidence input.exteriorSense surfaceTurn)
    (supportingJudged : MolecularFullereneThreeLocantTurnJudgment spatial
      input.symmetryInput.cage input.numberingEvidence supportingTurn) :
    supportingTurn = surfaceTurn := by
  rcases judged.2 with
    ⟨admittedTurn, admittedJudged, _numberingEq, _turnEq, supportingAgreement⟩
  have admittedEqSurface := molecularFullereneExteriorTurnJudgment_functional
    molecule input.symmetryInput.cage input.numberingEvidence input.exteriorSense
      admittedTurn surfaceTurn admittedJudged surfaceJudged
  exact (supportingAgreement supportingTurn supportingJudged).trans admittedEqSurface

/-- Admit a general exterior-oriented source record only after all exact judgments agree. -/
noncomputable def exteriorDerivedMolecularFullereneConfigurationInput?
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : ExteriorDerivedMolecularFullereneConfigurationInput) :
    Option SymmetryDerivedMolecularFullereneConfigurationInput :=
  if ExteriorDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input then
    some input.symmetryInput
  else
    none

@[simp] theorem exteriorDerivedMolecularFullereneConfigurationInput?_eq_some_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : ExteriorDerivedMolecularFullereneConfigurationInput)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput) :
    exteriorDerivedMolecularFullereneConfigurationInput? molecule spatial input =
        some symmetryInput ↔
      ExteriorDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input ∧
        symmetryInput = input.symmetryInput := by
  by_cases valid :
      ExteriorDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input
  · simp [exteriorDerivedMolecularFullereneConfigurationInput?, valid, eq_comm]
  · simp [exteriorDerivedMolecularFullereneConfigurationInput?, valid]

@[simp] theorem exteriorDerivedMolecularFullereneConfigurationInput?_eq_none_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (input : ExteriorDerivedMolecularFullereneConfigurationInput) :
    exteriorDerivedMolecularFullereneConfigurationInput? molecule spatial input = none ↔
      ¬ExteriorDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input := by
  by_cases valid :
      ExteriorDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input
  · simp [exteriorDerivedMolecularFullereneConfigurationInput?, valid]
  · simp [exteriorDerivedMolecularFullereneConfigurationInput?, valid]

/-- All and only general exterior-oriented source records admitted by the exact boundary. -/
noncomputable def validatedExteriorDerivedMolecularFullereneConfigurationInputs
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List ExteriorDerivedMolecularFullereneConfigurationInput) :
    List SymmetryDerivedMolecularFullereneConfigurationInput :=
  inputs.filterMap
    (exteriorDerivedMolecularFullereneConfigurationInput? molecule spatial)

/-- Exact finite-family membership at the general exterior-orientation boundary. -/
theorem mem_validatedExteriorDerivedMolecularFullereneConfigurationInputs_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput) :
    symmetryInput ∈
        validatedExteriorDerivedMolecularFullereneConfigurationInputs
          molecule spatial inputs ↔
      ∃ input ∈ inputs,
        ExteriorDerivedMolecularFullereneConfigurationInputJudgment
            molecule spatial input ∧
          symmetryInput = input.symmetryInput := by
  simp [validatedExteriorDerivedMolecularFullereneConfigurationInputs,
    exteriorDerivedMolecularFullereneConfigurationInput?_eq_some_iff]

/-- Complete assignment meaning for the general exterior-oriented family. -/
def ExteriorDerivedMolecularFullereneConfigurationAssignmentJudgment
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs,
    ExteriorDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input ∧
      FullereneConfigurationAssignmentJudgment
        input.symmetryInput.cage.toFullereneConfigurationInput assignment ∧
      FullereneConfigurationAssignmentAgreement
        (validatedMolecularFullereneConfigurationInputs molecule
          (validatedSymmetryDerivedMolecularFullereneConfigurationInputs molecule
            (validatedExteriorDerivedMolecularFullereneConfigurationInputs
              molecule spatial inputs)))
        assignment

/-- The general source judgment is exactly the symmetry-backed assignment judgment over records
admitted by the exterior-orientation boundary. -/
theorem exteriorDerivedMolecularFullereneConfigurationAssignmentJudgment_iff_symmetry
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    ExteriorDerivedMolecularFullereneConfigurationAssignmentJudgment
        molecule spatial inputs assignment ↔
      SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment molecule
        (validatedExteriorDerivedMolecularFullereneConfigurationInputs
          molecule spatial inputs)
        assignment := by
  unfold ExteriorDerivedMolecularFullereneConfigurationAssignmentJudgment
  unfold SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
  constructor
  · rintro ⟨input, inputPresent, exteriorJudged, localJudged, agreement⟩
    exact ⟨input.symmetryInput,
      (mem_validatedExteriorDerivedMolecularFullereneConfigurationInputs_iff
        molecule spatial inputs input.symmetryInput).mpr
          ⟨input, inputPresent, exteriorJudged, rfl⟩,
      exteriorJudged.1, localJudged, agreement⟩
  · rintro ⟨symmetryInput, symmetryPresent, _symmetryJudged, localJudged, agreement⟩
    rcases (mem_validatedExteriorDerivedMolecularFullereneConfigurationInputs_iff
      molecule spatial inputs symmetryInput).mp symmetryPresent with
      ⟨input, inputPresent, exteriorJudged, symmetryEq⟩
    subst symmetryInput
    exact ⟨input, inputPresent, exteriorJudged, localJudged, agreement⟩

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
