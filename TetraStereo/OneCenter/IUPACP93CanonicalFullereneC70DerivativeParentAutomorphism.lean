import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70DerivativeSymmetryCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

theorem iupacP93CanonicalFullereneC70Type4ReversingSymmetry_parentAutomorphism :
    MolecularFullereneCarrierAutomorphism
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70DerivativeInput
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry := by
  apply molecularFullereneCarrierAutomorphism_of_involutive_forward
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70DerivativeInput
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry_involutive
  intro left right positive
  have leftBound : left.1 < iupacP93CanonicalFullereneC70Transcription.atomCount := by
    simpa [iupacP93CanonicalFullereneC70Transcription] using
      iupacP93CanonicalFullereneC70DerivativeCarrierAtom_lt left
  have rightBound : right.1 < iupacP93CanonicalFullereneC70Transcription.atomCount := by
    simpa [iupacP93CanonicalFullereneC70Transcription] using
      iupacP93CanonicalFullereneC70DerivativeCarrierAtom_lt right
  have distinct : left.1 ≠ right.1 := by
    intro equal
    have leftEqRight : left = right := Subtype.ext equal
    subst right
    simp [RawMolecule.bondOrder_self] at positive
  have faceEdge :=
    (NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
      iupacP93CanonicalFullereneC70Transcription left.1 right.1
      leftBound rightBound distinct).mp positive
  have mappedLeftBound :
      (iupacP93CanonicalFullereneC70Type4ReversingSymmetry left).1 <
        iupacP93CanonicalFullereneC70Transcription.atomCount := by
    simpa [iupacP93CanonicalFullereneC70Transcription] using
      iupacP93CanonicalFullereneC70DerivativeCarrierAtom_lt
        (iupacP93CanonicalFullereneC70Type4ReversingSymmetry left)
  have mappedRightBound :
      (iupacP93CanonicalFullereneC70Type4ReversingSymmetry right).1 <
        iupacP93CanonicalFullereneC70Transcription.atomCount := by
    simpa [iupacP93CanonicalFullereneC70Transcription] using
      iupacP93CanonicalFullereneC70DerivativeCarrierAtom_lt
        (iupacP93CanonicalFullereneC70Type4ReversingSymmetry right)
  have mappedDistinct :
      (iupacP93CanonicalFullereneC70Type4ReversingSymmetry left).1 ≠
        (iupacP93CanonicalFullereneC70Type4ReversingSymmetry right).1 := by
    intro equal
    exact distinct (Subtype.ext_iff.mp
      (iupacP93CanonicalFullereneC70Type4ReversingSymmetry.injective
        (Subtype.ext equal)))
  apply (NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
    iupacP93CanonicalFullereneC70Transcription _ _ mappedLeftBound mappedRightBound
    mappedDistinct).mpr
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · have edgePresent : (left.1, right.1) ∈
        iupacP93CanonicalFullereneC70Transcription.edgeTable :=
      (numberedFaceTranscription_mem_edgeTable_iff _ _ _).mpr
        ⟨leftBound, rightBound, ordered, faceEdge⟩
    have audited := (List.all_eq_true.mp
      iupacP93CanonicalFullereneC70Type4ReversingLocantTable_preservesEdgeTable)
        (left.1, right.1) edgePresent
    simpa [iupacP93CanonicalFullereneC70Type4ReversingSymmetry,
      MolecularFullereneLocantInvolutionCertificate.toPerm,
      iupacP93CanonicalFullereneC70Type4ReversingInvolution] using audited
  · have reverseFaceEdge :
        iupacP93CanonicalFullereneC70Transcription.hasFaceEdge right.1 left.1 = true := by
      rw [numberedFaceTranscription_hasFaceEdge_symm]
      exact faceEdge
    have edgePresent : (right.1, left.1) ∈
        iupacP93CanonicalFullereneC70Transcription.edgeTable :=
      (numberedFaceTranscription_mem_edgeTable_iff _ _ _).mpr
        ⟨rightBound, leftBound, ordered, reverseFaceEdge⟩
    have audited := (List.all_eq_true.mp
      iupacP93CanonicalFullereneC70Type4ReversingLocantTable_preservesEdgeTable)
        (right.1, left.1) edgePresent
    rw [numberedFaceTranscription_hasFaceEdge_symm]
    simpa [iupacP93CanonicalFullereneC70Type4ReversingSymmetry,
      MolecularFullereneLocantInvolutionCertificate.toPerm,
      iupacP93CanonicalFullereneC70Type4ReversingInvolution] using audited

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
