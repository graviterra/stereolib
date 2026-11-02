import TetraStereo.OneCenter.IUPACP93CanonicalFullereneDerivativeRelationalEvidence
import TetraStereo.OneCenter.P93MolecularFullereneExecutableRelationalAudit
import TetraStereo.OneCenter.P93MolecularFullereneFaceIncidenceSymmetry

set_option autoImplicit false
set_option maxRecDepth 100000











namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

abbrev iupacP93CanonicalFullereneC76DerivativeTopologyInput :
    MolecularFullereneConfigurationInput :=
  iupacP93CanonicalFullereneC76Transcription.numberedPackage.topologyInput

abbrev iupacP93CanonicalFullereneC76Type1Molecule : RawMolecule :=
  iupacP93CanonicalFullereneC76Type1Assembly.compileExtension.assemble

/-- Source-level pentagon incidence; the first twelve frozen faces are exactly the pentagons. -/
def iupacP93C76SourcePentagonIncidence (atom : Nat) : Nat :=
  (iupacP93CanonicalFullereneC76Faces.take 12).countP fun face =>
    decide (atom ∈ face)

/-- The efficient source count is extensionally the generic face-carrier cardinality on every
admitted cage atom. -/
theorem iupacP93C76SourcePentagonIncidence_eq_generic
    (atom : MolecularFullereneCarrierAtom
      iupacP93CanonicalFullereneC76DerivativeTopologyInput) :
    iupacP93C76SourcePentagonIncidence atom.1 =
      molecularFullerenePentagonIncidence
        iupacP93CanonicalFullereneC76DerivativeTopologyInput atom.1 := by
  have bound : atom.1 < 76 := by
    have present := atom.2
    change atom.1 ∈ Finset.range 76 at present
    exact Finset.mem_range.mp present
  interval_cases atom.1 <;> decide

inductive IUPACP93C76ParentProbe
  | site0
  | site1
  | site2
  | site9
  deriving DecidableEq, Fintype

def iupacP93C76FlagWordTo2 : List MolecularFullereneFlagMove :=
  [.continueLeftFace, .reverseEdge]

def iupacP93C76FlagWordTo9 : List MolecularFullereneFlagMove :=
  [.reverseEdge, .continueLeftFace, .reverseEdge]

def iupacP93CanonicalFullereneC76SourceDart :
    MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC76DerivativeTopologyInput :=
  (⟨0, by decide⟩, ⟨1, by decide⟩)

def iupacP93C76ParentProbe : IUPACP93C76ParentProbe →
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC76DerivativeTopologyInput
  | .site0 => ⟨0, by decide⟩
  | .site1 => ⟨1, by decide⟩
  | .site2 => ⟨2, by decide⟩
  | .site9 => ⟨9, by decide⟩

def iupacP93C76ParentAddress : IUPACP93C76ParentProbe →
    List MolecularFullereneFlagMove
  | .site0 => []
  | .site1 => [.reverseEdge]
  | .site2 => iupacP93C76FlagWordTo2
  | .site9 => iupacP93C76FlagWordTo9

private theorem c76ParentProbe_recovers : ∀ index,
    (walkMolecularFullereneFlag
      (molecularFullereneContinueForwardFace
        iupacP93CanonicalFullereneC76DerivativeTopologyInput)
      iupacP93CanonicalFullereneC76SourceDart
      (iupacP93C76ParentAddress index)).1 = iupacP93C76ParentProbe index := by
  intro index
  cases index <;> decide

private theorem c76ParentProbe_sourceIncidence_zero : ∀ index,
    iupacP93C76SourcePentagonIncidence (iupacP93C76ParentProbe index).1 = 0 := by
  intro index
  cases index <;> decide

def iupacP93C76ParentIncidenceObstruction
    (image : IUPACP93C76ParentProbe →
      MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC76DerivativeTopologyInput) : Prop :=
  ∀ index, iupacP93C76SourcePentagonIncidence (image index).1 = 0

private def c76CarrierAtomAt (atom : Nat) :
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC76DerivativeTopologyInput :=
  if present : atom ∈ iupacP93CanonicalFullereneC76DerivativeTopologyInput.carrier then
    ⟨atom, present⟩
  else ⟨0, by decide⟩

private def c76DartAt (left right : Nat) : MolecularFullereneDirectedCarrierEdge
    iupacP93CanonicalFullereneC76DerivativeTopologyInput :=
  (c76CarrierAtomAt left, c76CarrierAtomAt right)

private theorem c76DartAt_eq (target : MolecularFullereneDirectedCarrierEdge
    iupacP93CanonicalFullereneC76DerivativeTopologyInput) :
    c76DartAt target.1.1 target.2.1 = target := by
  apply Prod.ext
  · apply Subtype.ext
    simp [c76DartAt, c76CarrierAtomAt, target.1.2]
  · apply Subtype.ext
    simp [c76DartAt, c76CarrierAtomAt, target.2.2]

private def c76ParentTargetDecision
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC76DerivativeTopologyInput) :
    Decidable (¬iupacP93C76ParentIncidenceObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC76DerivativeTopologyInput)
        target (iupacP93C76ParentAddress index)).1) := by
  unfold iupacP93C76ParentIncidenceObstruction
  infer_instance

private def c76ParentTargetWordAudit : Bool :=
  iupacP93CanonicalFullereneC76Edges.all fun edge =>
    @decide (¬iupacP93C76ParentIncidenceObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC76DerivativeTopologyInput)
        (c76DartAt edge.1 edge.2) (iupacP93C76ParentAddress index)).1)
      (c76ParentTargetDecision (c76DartAt edge.1 edge.2)) &&
    @decide (¬iupacP93C76ParentIncidenceObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC76DerivativeTopologyInput)
        (c76DartAt edge.2 edge.1) (iupacP93C76ParentAddress index)).1)
      (c76ParentTargetDecision (c76DartAt edge.2 edge.1))

set_option maxHeartbeats 0 in
private theorem c76ParentTargetWordAudit_true : c76ParentTargetWordAudit = true := by
  unfold c76ParentTargetWordAudit
  decide

private theorem c76Parent_targetWordsReject
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC76DerivativeTopologyInput)
    (targetBond : 0 < iupacP93CanonicalFullereneC76Type1Molecule.bondOrder
      target.1.1 target.2.1) :
    ¬iupacP93C76ParentIncidenceObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC76DerivativeTopologyInput)
        target (iupacP93C76ParentAddress index)).1 := by
  have coreBond : 0 < iupacP93CanonicalFullereneC76Transcription.cageMolecule.bondOrder
      target.1.1 target.2.1 := by
    rw [← iupacP93CanonicalFullereneC76Type1Assembly.compileExtension.bondOrder_on_carrier
      target.1.1 target.2.1 target.1.2 target.2.2]
    exact targetBond
  have leftBound : target.1.1 < 76 := by
    have present := target.1.2
    change target.1.1 ∈ Finset.range 76 at present
    exact Finset.mem_range.mp present
  have rightBound : target.2.1 < 76 := by
    have present := target.2.2
    change target.2.1 ∈ Finset.range 76 at present
    exact Finset.mem_range.mp present
  have distinct : target.1.1 ≠ target.2.1 := by
    intro equal
    have targetEq : target.1 = target.2 := Subtype.ext equal
    rw [targetEq, RawMolecule.bondOrder_self] at coreBond
    simp at coreBond
  have faceEdge :=
    (NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
      iupacP93CanonicalFullereneC76Transcription target.1.1 target.2.1
      leftBound rightBound distinct).1 coreBond
  have sourceEdge :
      iupacP93CanonicalFullereneC76HasSourceEdge target.1.1 target.2.1 = true :=
    (iupacP93CanonicalFullereneC76_hasFaceEdge_iff_hasSourceEdge
      target.1.1 target.2.1 leftBound rightBound distinct).1 faceEdge
  have sourcePresent : iupacP93C76CanonicalEdge (target.1.1, target.2.1) ∈
      iupacP93CanonicalFullereneC76Edges := by
    simpa [iupacP93CanonicalFullereneC76HasSourceEdge] using sourceEdge
  have checked := (List.all_eq_true.mp c76ParentTargetWordAudit_true)
    (iupacP93C76CanonicalEdge (target.1.1, target.2.1)) sourcePresent
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · have canonical : iupacP93C76CanonicalEdge (target.1.1, target.2.1) =
        (target.1.1, target.2.1) := by
      simp [iupacP93C76CanonicalEdge, ordered]
    rw [canonical] at checked
    simp only [Bool.and_eq_true] at checked
    have rejected := @of_decide_eq_true _
      (c76ParentTargetDecision (c76DartAt target.1.1 target.2.1)) checked.1
    rw [c76DartAt_eq target] at rejected
    exact rejected
  · have canonical : iupacP93C76CanonicalEdge (target.1.1, target.2.1) =
        (target.2.1, target.1.1) := by
      simp [iupacP93C76CanonicalEdge, Nat.not_lt.mpr (Nat.le_of_lt ordered)]
    rw [canonical] at checked
    simp only [Bool.and_eq_true] at checked
    have rejected := @of_decide_eq_true _
      (c76ParentTargetDecision (c76DartAt target.1.1 target.2.1)) checked.2
    rw [c76DartAt_eq target] at rejected
    exact rejected

private theorem c76Parent_sourceBond :
    0 < iupacP93CanonicalFullereneC76Type1Molecule.bondOrder
      iupacP93CanonicalFullereneC76SourceDart.1.1
      iupacP93CanonicalFullereneC76SourceDart.2.1 := by
  rw [iupacP93CanonicalFullereneC76Type1Assembly.compileExtension.bondOrder_on_carrier
    _ _ iupacP93CanonicalFullereneC76SourceDart.1.2
      iupacP93CanonicalFullereneC76SourceDart.2.2]
  decide

private theorem c76Parent_admissible_implies_obstruction
    (oriented : OrientedMolecularFullereneFaceMapJudgment
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76DerivativeTopologyInput)
    (symmetry : Equiv.Perm
      (MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC76DerivativeTopologyInput))
    (reversing : MolecularFullereneFaceOrientationReversing
      iupacP93CanonicalFullereneC76DerivativeTopologyInput symmetry) :
    iupacP93C76ParentIncidenceObstruction fun index =>
      symmetry (iupacP93C76ParentProbe index) := by
  intro index
  rw [iupacP93C76SourcePentagonIncidence_eq_generic]
  rw [molecularFullerenePentagonIncidence_map_eq oriented symmetry reversing]
  rw [← iupacP93C76SourcePentagonIncidence_eq_generic]
  exact c76ParentProbe_sourceIncidence_zero index

theorem iupacP93CanonicalFullereneC76_parent_chiral :
    MolecularFullereneColoringChiral
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76DerivativeTopologyInput
      molecularFullereneParentColor := by
  have oriented :=
    (iupacP93CanonicalFullereneC76Type1Assembly.transportCertificate
      iupacP93CanonicalFullereneC76SharedNumberedCage.certificate).oriented
  have noReversing : MolecularFullereneRelationalChiral
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76DerivativeTopologyInput (fun _ => True) := by
    apply molecularFullereneRelationalChiral_of_flagWord_obstruction
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76DerivativeTopologyInput (fun _ => True)
      iupacP93C76ParentIncidenceObstruction oriented
      iupacP93CanonicalFullereneC76SourceDart c76Parent_sourceBond
      iupacP93C76ParentProbe iupacP93C76ParentAddress c76ParentProbe_recovers
    · intro symmetry _automorphism reversing _preserved
      exact c76Parent_admissible_implies_obstruction oriented symmetry reversing
    · exact c76Parent_targetWordsReject
  rcases noReversing with ⟨orientedExact, rejects⟩
  refine ⟨orientedExact, ?_⟩
  rintro ⟨symmetry, automorphism, reversing, _parentPreserved⟩
  exact rejects ⟨symmetry, automorphism, reversing, True.intro⟩

theorem iupacP93CanonicalFullereneC76Type1_sameTest_chiral :
    MolecularFullereneSameTestAddendPatternChiral
      iupacP93CanonicalFullereneC76Type1RelationalEvidence :=
  molecularFullereneParentChiral_implies_relational
    iupacP93CanonicalFullereneC76_parent_chiral
    (MolecularFullereneSameTestAddendPatternPreserved
      iupacP93CanonicalFullereneC76Type1RelationalEvidence)

theorem iupacP93CanonicalFullereneC76Type1_actual_chiral :
    MolecularFullereneActualAddendPatternChiral
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76DerivativeTopologyInput
      iupacP93CanonicalFullereneC76Type1RelationalEvidence :=
  molecularFullereneParentChiral_implies_relational
    iupacP93CanonicalFullereneC76_parent_chiral
    (MolecularFullereneActualAddendPatternPreserved
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76DerivativeTopologyInput
      iupacP93CanonicalFullereneC76Type1RelationalEvidence)

end


end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93C76SourcePentagonIncidence_eq_generic
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC76_parent_chiral
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC76Type1_sameTest_chiral
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC76Type1_actual_chiral
