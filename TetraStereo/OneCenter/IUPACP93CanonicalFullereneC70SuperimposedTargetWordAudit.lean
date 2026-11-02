import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70SuperimposedSymmetryCore

set_option autoImplicit false
set_option maxRecDepth 100000

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

private def c70CarrierAtomAt (atom : Nat) :
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70SuperimposedTopologyInput :=
  if present : atom ∈ iupacP93CanonicalFullereneC70SuperimposedTopologyInput.carrier then
    ⟨atom, present⟩
  else ⟨0, by decide⟩

private def c70DartAt (left right : Nat) : MolecularFullereneDirectedCarrierEdge
    iupacP93CanonicalFullereneC70SuperimposedTopologyInput :=
  (c70CarrierAtomAt left, c70CarrierAtomAt right)

private theorem c70DartAt_eq (target : MolecularFullereneDirectedCarrierEdge
    iupacP93CanonicalFullereneC70SuperimposedTopologyInput) :
    c70DartAt target.1.1 target.2.1 = target := by
  apply Prod.ext
  · apply Subtype.ext
    simp [c70DartAt, c70CarrierAtomAt, target.1.2]
  · apply Subtype.ext
    simp [c70DartAt, c70CarrierAtomAt, target.2.2]

private def c70SuperimposedTargetDecision
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC70SuperimposedTopologyInput) :
    Decidable (¬iupacP93C70SuperimposedObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
        target (iupacP93C70SuperimposedAddress index)).1) := by
  unfold iupacP93C70SuperimposedObstruction iupacP93C70SuperimposedImagePair
  infer_instance

private def c70SuperimposedTargetWordAudit : Bool :=
  iupacP93CanonicalFullereneC70Edges.all fun edge =>
    @decide (¬iupacP93C70SuperimposedObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
        (c70DartAt edge.1 edge.2) (iupacP93C70SuperimposedAddress index)).1)
      (c70SuperimposedTargetDecision (c70DartAt edge.1 edge.2)) &&
    @decide (¬iupacP93C70SuperimposedObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
        (c70DartAt edge.2 edge.1) (iupacP93C70SuperimposedAddress index)).1)
      (c70SuperimposedTargetDecision (c70DartAt edge.2 edge.1))

set_option maxHeartbeats 0 in
private theorem c70SuperimposedTargetWordAudit_true :
    c70SuperimposedTargetWordAudit = true := by
  unfold c70SuperimposedTargetWordAudit
  decide

private theorem c70Superimposed_targetWordsReject
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
    (targetBond : 0 < iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder
      target.1.1 target.2.1) :
    ¬iupacP93C70SuperimposedObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
        target (iupacP93C70SuperimposedAddress index)).1 := by
  have coreBond : 0 < iupacP93CanonicalFullereneC70Transcription.cageMolecule.bondOrder
      target.1.1 target.2.1 := by
    rw [← iupacP93CanonicalFullereneC70SuperimposedAssembly.compileExtension.bondOrder_on_carrier
      target.1.1 target.2.1 target.1.2 target.2.2]
    exact targetBond
  have leftBound : target.1.1 < 70 := by
    have present := target.1.2
    change target.1.1 ∈ Finset.range 70 at present
    exact Finset.mem_range.mp present
  have rightBound : target.2.1 < 70 := by
    have present := target.2.2
    change target.2.1 ∈ Finset.range 70 at present
    exact Finset.mem_range.mp present
  have distinct : target.1.1 ≠ target.2.1 := by
    intro equal
    have targetEq : target.1 = target.2 := Subtype.ext equal
    rw [targetEq, RawMolecule.bondOrder_self] at coreBond
    simp at coreBond
  have faceEdge :=
    (NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
      iupacP93CanonicalFullereneC70Transcription target.1.1 target.2.1
      leftBound rightBound distinct).1 coreBond
  have sourceEdge :
      iupacP93CanonicalFullereneC70HasSourceEdge target.1.1 target.2.1 = true :=
    (iupacP93CanonicalFullereneC70_sourceEdge_iff_faceEdge
      target.1.1 target.2.1 leftBound rightBound distinct).2 faceEdge
  have sourcePresent : iupacP93C70CanonicalEdge (target.1.1, target.2.1) ∈
      iupacP93CanonicalFullereneC70Edges := by
    simpa [iupacP93CanonicalFullereneC70HasSourceEdge] using sourceEdge
  have checked := (List.all_eq_true.mp c70SuperimposedTargetWordAudit_true)
    (iupacP93C70CanonicalEdge (target.1.1, target.2.1)) sourcePresent
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · have canonical : iupacP93C70CanonicalEdge (target.1.1, target.2.1) =
        (target.1.1, target.2.1) := by
      simp [iupacP93C70CanonicalEdge, ordered]
    rw [canonical] at checked
    simp only [Bool.and_eq_true] at checked
    have rejected := @of_decide_eq_true _
      (c70SuperimposedTargetDecision (c70DartAt target.1.1 target.2.1)) checked.1
    rw [c70DartAt_eq target] at rejected
    exact rejected
  · have canonical : iupacP93C70CanonicalEdge (target.1.1, target.2.1) =
        (target.2.1, target.1.1) := by
      simp [iupacP93C70CanonicalEdge, Nat.not_lt.mpr (Nat.le_of_lt ordered)]
    rw [canonical] at checked
    simp only [Bool.and_eq_true] at checked
    have rejected := @of_decide_eq_true _
      (c70SuperimposedTargetDecision (c70DartAt target.1.1 target.2.1)) checked.2
    rw [c70DartAt_eq target] at rejected
    exact rejected


theorem iupacP93C70SuperimposedTargetWordsReject
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
    (targetBond : 0 < iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder
      target.1.1 target.2.1) :
    ¬iupacP93C70SuperimposedObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
        target (iupacP93C70SuperimposedAddress index)).1 :=
  c70Superimposed_targetWordsReject target targetBond

end

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
