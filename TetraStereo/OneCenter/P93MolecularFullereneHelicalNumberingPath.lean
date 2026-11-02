import TetraStereo.OneCenter.P93MolecularFullereneReferenceSymmetry

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

open P94MolecularRingCycleScheduler

/-!
# Contiguous systematic fullerene numbering helices

IUPAC Fu-3 describes a contiguous numbering helix as a bond-contiguous atom pathway that begins
by numbering one whole elementary ring and then covers the remaining cage while maintaining one
clockwise or anticlockwise direction with the pitch kept as small (the movement as tight) as
possible.  On a coherently oriented cubic face map, this has an exact finite combinatorial meaning:
after entering a vertex, continue around the face on the selected side whenever that next vertex
is still unnumbered; only when that tight continuation is blocked may the path leave along another
unnumbered cage bond.

The judgment below records all parts independently: the complete starting ring, ordinary molecular
bond continuity, and every local tight-turn choice.  It is therefore intentionally stronger than a
Hamiltonian-path test.  Exhaustive enumerators filter the previously proved universe of every
carrier permutation, first without a reference element and then against the ring/bond/atom ends of
one grouped proper rotation axis required by Fu-3.1.1.
-/

/-! ## Direction-preserving tight steps -/

/-- The outgoing bond continues around the same oriented face on the selected side of the incoming
bond.  `forward` and `reverse` are the two possible helical directions; their physical `C/A` sense
is obtained later by combining this progression with the declared outside orientation. -/
def MolecularFullereneHelicalTurnJudgment
    (input : MolecularFullereneConfigurationInput)
    (progression : FullereneNumberingProgression)
    (previous current next : ℕ) : Prop :=
  match progression with
  | .forward =>
      ∃ face ∈ input.faces,
        IsForwardNamedCycleEdge face previous current ∧
          IsForwardNamedCycleEdge face current next
  | .reverse =>
      ∃ face ∈ input.faces,
        IsForwardNamedCycleEdge face current previous ∧
          IsForwardNamedCycleEdge face next current

noncomputable instance molecularFullereneHelicalTurnJudgmentDecidable
    (input : MolecularFullereneConfigurationInput)
    (progression : FullereneNumberingProgression)
    (previous current next : ℕ) :
    Decidable (MolecularFullereneHelicalTurnJudgment
      input progression previous current next) :=
  Classical.propDecidable _

/-- Independent local meaning of “maintain direction and keep the helix tight”.  The proposed next
atom must be a new cage neighbor.  If an unnumbered neighbor continues around the oriented face on
the selected side, the proposed next atom must make that turn; otherwise the remaining unnumbered
cage neighbor is allowed. -/
def MolecularFullereneTightHelicalStepJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (progression : FullereneNumberingProgression)
    (visited : List ℕ)
    (previous current next : ℕ) : Prop :=
  next ∈ input.carrier ∧
    0 < molecule.bondOrder current next ∧
    next ∉ visited ∧
    ((∃ preferred,
        preferred ∈ input.carrier ∧
          0 < molecule.bondOrder current preferred ∧
          preferred ∉ visited ∧
          MolecularFullereneHelicalTurnJudgment
            input progression previous current preferred) →
      MolecularFullereneHelicalTurnJudgment
        input progression previous current next)

noncomputable instance molecularFullereneTightHelicalStepJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (progression : FullereneNumberingProgression)
    (visited : List ℕ)
    (previous current next : ℕ) :
    Decidable (MolecularFullereneTightHelicalStepJudgment
      molecule input progression visited previous current next) :=
  Classical.propDecidable _

/-- Check every remaining locant against the accumulated numbered prefix. -/
def MolecularFullereneTightHelicalTailJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (progression : FullereneNumberingProgression)
    (visited : List ℕ)
    (previous current : ℕ) : List ℕ → Prop
  | [] => True
  | next :: remainder =>
      MolecularFullereneTightHelicalStepJudgment
          molecule input progression visited previous current next ∧
        MolecularFullereneTightHelicalTailJudgment
          molecule input progression (next :: visited) current next remainder

noncomputable instance molecularFullereneTightHelicalTailJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (progression : FullereneNumberingProgression)
    (visited : List ℕ)
    (previous current : ℕ)
    (remainder : List ℕ) :
    Decidable (MolecularFullereneTightHelicalTailJudgment
      molecule input progression visited previous current remainder) :=
  Classical.propDecidable _

/-- Every step after the first cage bond obeys the local tight-turn rule. -/
def MolecularFullereneTightHelicalPathJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (progression : FullereneNumberingProgression) : List ℕ → Prop
  | first :: second :: remainder =>
      MolecularFullereneTightHelicalTailJudgment
        molecule input progression [second, first] first second remainder
  | _ => False

noncomputable instance molecularFullereneTightHelicalPathJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (progression : FullereneNumberingProgression)
    (path : List ℕ) :
    Decidable (MolecularFullereneTightHelicalPathJudgment
      molecule input progression path) :=
  Classical.propDecidable _

/-! ## Complete contiguous helix judgment -/

/-- The initial locants traverse every atom of the declared elementary starting ring, in exactly
the selected direction and up to the arbitrary first vertex used to store that cyclic face. -/
def MolecularFullereneWholeStartingRingJudgment
    (evidence : MolecularFullereneNumberingEvidence)
    (progression : FullereneNumberingProgression) : Prop :=
  let startingPrefix := evidence.atomsByLocant.take evidence.startingFace.length
  match progression with
  | .forward => List.IsRotated startingPrefix evidence.startingFace
  | .reverse => List.IsRotated startingPrefix.reverse evidence.startingFace

noncomputable instance molecularFullereneWholeStartingRingJudgmentDecidable
    (evidence : MolecularFullereneNumberingEvidence)
    (progression : FullereneNumberingProgression) :
    Decidable (MolecularFullereneWholeStartingRingJudgment evidence progression) :=
  Classical.propDecidable _

/-- Exact independent meaning of one systematic contiguous helical numbering of the complete
molecular cage. -/
structure MolecularFullereneContiguousHelicalNumberingJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (progression : FullereneNumberingProgression) : Prop where
  orientedFaceMap : OrientedMolecularFullereneFaceMapJudgment molecule input
  systematic : evidence.numberingKind = .systematic
  numbering : MolecularFullereneNumberingEvidenceJudgment input evidence
  progressionJudged : MolecularFullereneNumberingProgressionJudgment evidence progression
  wholeStartingRing : MolecularFullereneWholeStartingRingJudgment evidence progression
  consecutivelyBonded :
    P94ConformationUnit.ConsecutivelyBonded molecule evidence.atomsByLocant
  tight : MolecularFullereneTightHelicalPathJudgment
    molecule input progression evidence.atomsByLocant

noncomputable instance molecularFullereneContiguousHelicalNumberingJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (progression : FullereneNumberingProgression) :
    Decidable (MolecularFullereneContiguousHelicalNumberingJudgment
      molecule input evidence progression) :=
  Classical.propDecidable _

/-- A proposed numbering paired with one of the two finite helical directions. -/
structure MolecularFullereneContiguousHelicalNumberingCandidate where
  evidence : MolecularFullereneNumberingEvidence
  progression : FullereneNumberingProgression

/-- All locally valid systematic numberings in both directions, filtered by the complete
contiguous-helix judgment. -/
noncomputable def molecularFullereneContiguousHelicalNumberingCandidates
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    List MolecularFullereneContiguousHelicalNumberingCandidate :=
  ((molecularFullereneSystematicNumberingEvidenceCandidates input).flatMap fun evidence =>
    ([.forward, .reverse] : List FullereneNumberingProgression).map fun progression =>
      { evidence := evidence
        progression := progression }).filter fun candidate =>
          decide (MolecularFullereneContiguousHelicalNumberingJudgment
            molecule input candidate.evidence candidate.progression)

/-- The finite enumeration contains exactly the independently judged contiguous systematic
helices; neither a carrier permutation nor a direction can be supplied outside this theorem. -/
@[simp] theorem mem_molecularFullereneContiguousHelicalNumberingCandidates_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneContiguousHelicalNumberingCandidate) :
    candidate ∈ molecularFullereneContiguousHelicalNumberingCandidates molecule input ↔
      MolecularFullereneContiguousHelicalNumberingJudgment
        molecule input candidate.evidence candidate.progression := by
  classical
  constructor
  · intro present
    exact of_decide_eq_true (List.mem_filter.mp present).2
  · intro judged
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using judged⟩
    apply List.mem_flatMap.mpr
    refine ⟨candidate.evidence, ?_, ?_⟩
    · exact (mem_molecularFullereneSystematicNumberingEvidenceCandidates_iff
        input candidate.evidence).mpr ⟨judged.systematic, judged.numbering⟩
    · apply List.mem_map.mpr
      refine ⟨candidate.progression, ?_, ?_⟩
      · cases candidate.progression <;> simp
      · cases candidate
        rfl

/-- A contiguous systematic helix exists exactly when the exhaustive finite enumeration is
nonempty. -/
theorem molecularFullereneContiguousHelicalNumberingCandidates_nonempty_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    molecularFullereneContiguousHelicalNumberingCandidates molecule input ≠ [] ↔
      ∃ candidate : MolecularFullereneContiguousHelicalNumberingCandidate,
        MolecularFullereneContiguousHelicalNumberingJudgment
          molecule input candidate.evidence candidate.progression := by
  constructor
  · intro nonempty
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨candidate,
      (mem_molecularFullereneContiguousHelicalNumberingCandidates_iff
        molecule input candidate).mp present⟩
  · rintro ⟨candidate, judged⟩
    exact List.ne_nil_of_mem
      ((mem_molecularFullereneContiguousHelicalNumberingCandidates_iff
        molecule input candidate).mpr judged)

/-! ## Fu-3.1.1 proper-axis eligibility -/

/-- A numbering begins at the chosen surface end of a reference axis.  For a ring end, the named
ring is the whole starting polygon; for a bisected bond, either endpoint may receive locant 1; for
an atom end, that atom receives locant 1. -/
def MolecularFullereneNumberingStartsAtAxisEndJudgment
    (evidence : MolecularFullereneNumberingEvidence) :
    FullereneProperRotationAxisEnd → Prop
  | .ring face => evidence.startingFace = face
  | .bond edge =>
      (evidence.atomsByLocant[0]? = some edge.1 ∧
          evidence.atomsByLocant[1]? = some edge.2) ∨
        (evidence.atomsByLocant[0]? = some edge.2 ∧
          evidence.atomsByLocant[1]? = some edge.1)
  | .atom atom => evidence.atomsByLocant.head? = some atom

noncomputable instance molecularFullereneNumberingStartsAtAxisEndJudgmentDecidable
    (evidence : MolecularFullereneNumberingEvidence)
    (axisEnd : FullereneProperRotationAxisEnd) :
    Decidable (MolecularFullereneNumberingStartsAtAxisEndJudgment evidence axisEnd) :=
  Classical.propDecidable _

@[simp] theorem molecularFullereneNumberingStartsAtAxisEnd_ring_iff
    (evidence : MolecularFullereneNumberingEvidence)
    (face : List ℕ) :
    MolecularFullereneNumberingStartsAtAxisEndJudgment evidence (.ring face) ↔
      evidence.startingFace = face := by
  rfl

@[simp] theorem molecularFullereneNumberingStartsAtAxisEnd_bond_iff
    (evidence : MolecularFullereneNumberingEvidence)
    (edge : ℕ × ℕ) :
    MolecularFullereneNumberingStartsAtAxisEndJudgment evidence (.bond edge) ↔
      ((evidence.atomsByLocant[0]? = some edge.1 ∧
          evidence.atomsByLocant[1]? = some edge.2) ∨
        (evidence.atomsByLocant[0]? = some edge.2 ∧
          evidence.atomsByLocant[1]? = some edge.1)) := by
  rfl

@[simp] theorem molecularFullereneNumberingStartsAtAxisEnd_atom_iff
    (evidence : MolecularFullereneNumberingEvidence)
    (atom : ℕ) :
    MolecularFullereneNumberingStartsAtAxisEndJudgment evidence (.atom atom) ↔
      evidence.atomsByLocant.head? = some atom := by
  rfl

/-- One complete helical path paired with the particular end cell at which it begins. -/
structure MolecularFullereneAxisContiguousHelicalNumberingCandidate where
  axisEnd : FullereneProperRotationAxisEnd
  evidence : MolecularFullereneNumberingEvidence
  progression : FullereneNumberingProgression

/-- Fu-3.1.1 eligibility for a contiguous helix about one grouped proper axis. -/
structure MolecularFullereneAxisContiguousHelicalNumberingJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis)
    (candidate : MolecularFullereneAxisContiguousHelicalNumberingCandidate) : Prop where
  axisPresent : axis ∈ molecularFullereneProperRotationAxes molecule input
  axisEndPresent : candidate.axisEnd ∈ axis
  helical : MolecularFullereneContiguousHelicalNumberingJudgment
    molecule input candidate.evidence candidate.progression
  startsAtAxisEnd : MolecularFullereneNumberingStartsAtAxisEndJudgment
    candidate.evidence candidate.axisEnd

noncomputable instance molecularFullereneAxisContiguousHelicalNumberingJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis)
    (candidate : MolecularFullereneAxisContiguousHelicalNumberingCandidate) :
    Decidable (MolecularFullereneAxisContiguousHelicalNumberingJudgment
      molecule input axis candidate) :=
  Classical.propDecidable _

/-- Exhaustive Fu-3.1.1 candidates for one grouped proper axis and all of its invariant ring,
bond, or atom ends. -/
noncomputable def molecularFullereneAxisContiguousHelicalNumberingCandidates
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis) :
    List MolecularFullereneAxisContiguousHelicalNumberingCandidate :=
  (axis.toList.flatMap fun axisEnd =>
    (molecularFullereneContiguousHelicalNumberingCandidates molecule input).map fun helical =>
      { axisEnd := axisEnd
        evidence := helical.evidence
        progression := helical.progression }).filter fun candidate =>
          decide (MolecularFullereneAxisContiguousHelicalNumberingJudgment
            molecule input axis candidate)

/-- Axis-filtered enumeration is exact against the independent Fu-3.1.1 judgment. -/
@[simp] theorem mem_molecularFullereneAxisContiguousHelicalNumberingCandidates_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis)
    (candidate : MolecularFullereneAxisContiguousHelicalNumberingCandidate) :
    candidate ∈ molecularFullereneAxisContiguousHelicalNumberingCandidates
        molecule input axis ↔
      MolecularFullereneAxisContiguousHelicalNumberingJudgment
        molecule input axis candidate := by
  classical
  constructor
  · intro present
    exact of_decide_eq_true (List.mem_filter.mp present).2
  · intro judged
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using judged⟩
    apply List.mem_flatMap.mpr
    refine ⟨candidate.axisEnd, by simpa using judged.axisEndPresent, ?_⟩
    apply List.mem_map.mpr
    let helical : MolecularFullereneContiguousHelicalNumberingCandidate :=
      { evidence := candidate.evidence
        progression := candidate.progression }
    refine ⟨helical, ?_, ?_⟩
    · exact (mem_molecularFullereneContiguousHelicalNumberingCandidates_iff
        molecule input helical).mpr judged.helical
    · cases candidate
      rfl

/-- An eligible contiguous helix exists around an axis exactly when its exhaustive finite family
is nonempty. -/
theorem molecularFullereneAxisContiguousHelicalNumberingCandidates_nonempty_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis) :
    molecularFullereneAxisContiguousHelicalNumberingCandidates molecule input axis ≠ [] ↔
      ∃ candidate,
        MolecularFullereneAxisContiguousHelicalNumberingJudgment
          molecule input axis candidate := by
  constructor
  · intro nonempty
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨candidate,
      (mem_molecularFullereneAxisContiguousHelicalNumberingCandidates_iff
        molecule input axis candidate).mp present⟩
  · rintro ⟨candidate, judged⟩
    exact List.ne_nil_of_mem
      ((mem_molecularFullereneAxisContiguousHelicalNumberingCandidates_iff
        molecule input axis candidate).mpr judged)

/-- A proposed end-cell set that is not an admitted proper rotation axis cannot manufacture any
Fu-3.1.1 helical candidate. -/
theorem molecularFullereneAxisContiguousHelicalNumberingCandidates_eq_empty_of_axis_not_present
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axis : MolecularFullereneProperRotationAxis)
    (axisNotPresent : axis ∉ molecularFullereneProperRotationAxes molecule input) :
    molecularFullereneAxisContiguousHelicalNumberingCandidates molecule input axis = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro candidate present
  have judged :=
    (mem_molecularFullereneAxisContiguousHelicalNumberingCandidates_iff
      molecule input axis candidate).mp present
  exact axisNotPresent judged.axisPresent

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
