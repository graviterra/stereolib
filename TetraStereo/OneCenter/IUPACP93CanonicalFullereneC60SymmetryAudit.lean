import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC60CagePackage
import TetraStereo.OneCenter.P93MolecularFullereneExecutableFlagSymmetryCardinality

set_option autoImplicit false
set_option maxRecDepth 100000









namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

abbrev iupacP93CanonicalFullereneC60TopologyInput :
    MolecularFullereneConfigurationInput :=
  iupacP93CanonicalFullereneC60Transcription.numberedPackage.topologyInput

def iupacP93CanonicalFullereneC60SourceDart :
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60TopologyInput ×
      MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60TopologyInput :=
  (⟨0, by decide⟩, ⟨1, by decide⟩)

theorem iupacP93CanonicalFullereneC60SourceDart_bonded :
    0 < iupacP93CanonicalFullereneC60Transcription.cageMolecule.bondOrder
      iupacP93CanonicalFullereneC60SourceDart.1.1
      iupacP93CanonicalFullereneC60SourceDart.2.1 := by
  decide

def iupacP93CanonicalFullereneC60FlagSpanning :
    MolecularFullereneDeduplicatedFlagSpanningCertificate
      iupacP93CanonicalFullereneC60Transcription.cageMolecule
      iupacP93CanonicalFullereneC60TopologyInput :=
  MolecularFullereneDeduplicatedFlagSpanningCertificate.ofOrientedFaceMap
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60TopologyInput
    iupacP93CanonicalFullereneC60Certificate.oriented
    iupacP93CanonicalFullereneC60SourceDart
    iupacP93CanonicalFullereneC60SourceDart_bonded

abbrev iupacP93CanonicalFullereneC60ReversingAutomorphisms :=
  molecularFullereneExecutableReversingAutomorphisms
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60TopologyInput
    iupacP93CanonicalFullereneC60FlagSpanning

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem iupacP93CanonicalFullereneC60_reversingTargetDartCount :
    (molecularFullereneExecutableReversingTargetDarts
      iupacP93CanonicalFullereneC60Transcription.cageMolecule
      iupacP93CanonicalFullereneC60TopologyInput
      iupacP93CanonicalFullereneC60FlagSpanning).card = 60 := by
  rfl

theorem iupacP93CanonicalFullereneC60_reversingAutomorphismCount :
    iupacP93CanonicalFullereneC60ReversingAutomorphisms.card = 60 := by
  rw [molecularFullereneExecutableReversingAutomorphisms_card_eq_targetDarts]
  exact iupacP93CanonicalFullereneC60_reversingTargetDartCount

theorem iupacP93CanonicalFullereneC60_existsReversingAutomorphism :
    ∃ symmetry : Equiv.Perm
        (MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60TopologyInput),
      MolecularFullereneCarrierAutomorphism
          iupacP93CanonicalFullereneC60Transcription.cageMolecule
          iupacP93CanonicalFullereneC60TopologyInput symmetry ∧
        MolecularFullereneFaceOrientationReversing
          iupacP93CanonicalFullereneC60TopologyInput symmetry := by
  have nonempty : iupacP93CanonicalFullereneC60ReversingAutomorphisms.Nonempty := by
    rw [← Finset.card_pos]
    rw [iupacP93CanonicalFullereneC60_reversingAutomorphismCount]
    decide
  rcases nonempty with ⟨symmetry, present⟩
  exact ⟨symmetry,
    iupacP93CanonicalFullereneC60FlagSpanning.toExecutableReversingCertificate
      iupacP93CanonicalFullereneC60Transcription.cageMolecule
      iupacP93CanonicalFullereneC60TopologyInput |>.sound symmetry present⟩

theorem iupacP93CanonicalFullereneC60_parent_achiral :
    ¬MolecularFullereneColoringChiral
      iupacP93CanonicalFullereneC60Transcription.cageMolecule
      iupacP93CanonicalFullereneC60TopologyInput
      molecularFullereneParentColor := by
  rintro ⟨_oriented, noReversing⟩
  rcases iupacP93CanonicalFullereneC60_existsReversingAutomorphism with
    ⟨symmetry, automorphism, reversing⟩
  apply noReversing
  exact ⟨symmetry, automorphism, reversing, by
    intro atom
    rfl⟩

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60_reversingAutomorphismCount
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60_parent_achiral
