import TetraStereo.OneCenter.IUPACP93CanonicalFullereneDerivativeRelationalEvidence
import TetraStereo.OneCenter.P93MolecularFullereneCageSymmetryTransport
import TetraStereo.OneCenter.P93MolecularFullereneExecutableRelationalAudit
import TetraStereo.OneCenter.P93MolecularFullereneLocantInvolution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0









namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

abbrev iupacP93CanonicalFullereneC70DerivativeInput :
    MolecularFullereneConfigurationInput :=
  iupacP93CanonicalFullereneC70Transcription.numberedPackage.topologyInput

/-! ## Explicit Type-4 reversing involution -/

def iupacP93CanonicalFullereneC70Type4ReversingLocantTable : List Nat :=
  [5, 4, 3, 2, 1, 0, 8, 7, 6, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11,
    10, 9, 26, 25, 24, 23, 22, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31,
    30, 29, 28, 27, 47, 46, 45, 44, 43, 42, 59, 58, 57, 56, 55, 54, 53, 52,
    51, 50, 49, 48, 63, 62, 61, 60, 69, 68, 67, 66, 65, 64]

theorem iupacP93CanonicalFullereneC70Type4ReversingLocantTable_length :
    iupacP93CanonicalFullereneC70Type4ReversingLocantTable.length = 70 := by
  decide

def iupacP93CanonicalFullereneC70Type4ReversingInvolution :
    MolecularFullereneLocantInvolutionCertificate
      iupacP93CanonicalFullereneC70DerivativeInput where
  table := iupacP93CanonicalFullereneC70Type4ReversingLocantTable
  mapsCarrier := by
    intro atom atomPresent
    have atomBound : atom < 70 := by
      simpa [iupacP93CanonicalFullereneC70DerivativeInput,
        MolecularFullereneNumberedCagePackage.topologyInput,
        MolecularFullereneNumberedCagePackage.toConfigurationInput,
        MolecularFullereneNumberedCagePackage.carrier,
        NumberedFaceTranscription.numberedPackage,
        NumberedFaceTranscription.atomsByLocant,
        iupacP93CanonicalFullereneC70Transcription] using atomPresent
    interval_cases atom <;> decide
  involutive := by
    intro atom atomPresent
    have atomBound : atom < 70 := by
      simpa [iupacP93CanonicalFullereneC70DerivativeInput,
        MolecularFullereneNumberedCagePackage.topologyInput,
        MolecularFullereneNumberedCagePackage.toConfigurationInput,
        MolecularFullereneNumberedCagePackage.carrier,
        NumberedFaceTranscription.numberedPackage,
        NumberedFaceTranscription.atomsByLocant,
        iupacP93CanonicalFullereneC70Transcription] using atomPresent
    interval_cases atom <;> decide

def iupacP93CanonicalFullereneC70Type4ReversingSymmetry :
    Equiv.Perm (MolecularFullereneCarrierAtom
      iupacP93CanonicalFullereneC70DerivativeInput) :=
  iupacP93CanonicalFullereneC70Type4ReversingInvolution.toPerm

theorem iupacP93CanonicalFullereneC70Type4ReversingSymmetry_involutive
    (atom : MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70DerivativeInput) :
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry
        (iupacP93CanonicalFullereneC70Type4ReversingSymmetry atom) = atom :=
  iupacP93CanonicalFullereneC70Type4ReversingInvolution.toPerm_involutive atom

theorem iupacP93CanonicalFullereneC70DerivativeCarrierAtom_lt
    (atom : MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70DerivativeInput) :
    atom.1 < 70 := by
  have member := atom.2
  change atom.1 ∈ Finset.range 70 at member
  exact Finset.mem_range.mp member

theorem iupacP93CanonicalFullereneC70Type4ReversingLocantTable_preservesEdgeTable :
    iupacP93CanonicalFullereneC70Transcription.edgeTable.all (fun edge =>
      iupacP93CanonicalFullereneC70Transcription.hasFaceEdge
        (iupacP93CanonicalFullereneC70Type4ReversingLocantTable.getD edge.1 edge.1)
        (iupacP93CanonicalFullereneC70Type4ReversingLocantTable.getD edge.2 edge.2)) = true := by
  decide

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
