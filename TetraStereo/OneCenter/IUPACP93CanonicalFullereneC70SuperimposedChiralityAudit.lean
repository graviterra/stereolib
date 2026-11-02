import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70SuperimposedTargetWordAudit

set_option autoImplicit false
set_option maxRecDepth 100000

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

private theorem c70Superimposed_sourceBond :
    0 < iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder
      iupacP93CanonicalFullereneC70SuperimposedSourceDart.1.1
      iupacP93CanonicalFullereneC70SuperimposedSourceDart.2.1 := by
  rw [iupacP93CanonicalFullereneC70SuperimposedAssembly.compileExtension.bondOrder_on_carrier
    _ _ iupacP93CanonicalFullereneC70SuperimposedSourceDart.1.2
      iupacP93CanonicalFullereneC70SuperimposedSourceDart.2.2]
  decide

private theorem c70Superimposed_preserved_implies_obstruction
    (symmetry : Equiv.Perm
      (MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70SuperimposedTopologyInput))
    (preserved : MolecularFullereneSameTestAddendPatternPreserved
      iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence symmetry) :
    iupacP93C70SuperimposedObstruction fun index =>
      symmetry (iupacP93C70SuperimposedProbe index) := by
  have addendsExact :
      iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence.addends =
        [iupacP93CanonicalFullereneC70SuperimposedFirstAddend,
          iupacP93CanonicalFullereneC70SuperimposedSecondAddend] :=
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2
  have mapped := (molecularFullereneSameTestAddendPatternPreserved_two_iff_mappedSites
    iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence symmetry
    iupacP93CanonicalFullereneC70SuperimposedFirstAddend
    iupacP93CanonicalFullereneC70SuperimposedSecondAddend addendsExact).1 preserved
  rcases mapped with fixed | swapped
  · left
    constructor
    · simpa [mappedMolecularFullereneAttachmentSites,
        iupacP93CanonicalFullereneC70SuperimposedCoreAudit.firstAttachmentSites,
        iupacP93C70SuperimposedObstruction, iupacP93C70SuperimposedImagePair,
        iupacP93C70SuperimposedProbe, mapMolecularFullereneCarrierAtom] using fixed.1
    · simpa [mappedMolecularFullereneAttachmentSites,
        iupacP93CanonicalFullereneC70SuperimposedCoreAudit.secondAttachmentSites,
        iupacP93C70SuperimposedObstruction, iupacP93C70SuperimposedImagePair,
        iupacP93C70SuperimposedProbe, mapMolecularFullereneCarrierAtom] using fixed.2
  · right
    constructor
    · simpa [mappedMolecularFullereneAttachmentSites,
        iupacP93CanonicalFullereneC70SuperimposedCoreAudit.firstAttachmentSites,
        iupacP93CanonicalFullereneC70SuperimposedCoreAudit.secondAttachmentSites,
        iupacP93C70SuperimposedObstruction, iupacP93C70SuperimposedImagePair,
        iupacP93C70SuperimposedProbe, mapMolecularFullereneCarrierAtom] using swapped.1
    · simpa [mappedMolecularFullereneAttachmentSites,
        iupacP93CanonicalFullereneC70SuperimposedCoreAudit.firstAttachmentSites,
        iupacP93CanonicalFullereneC70SuperimposedCoreAudit.secondAttachmentSites,
        iupacP93C70SuperimposedObstruction, iupacP93C70SuperimposedImagePair,
        iupacP93C70SuperimposedProbe, mapMolecularFullereneCarrierAtom] using swapped.2

theorem iupacP93CanonicalFullereneC70Superimposed_sameTest_chiral :
    MolecularFullereneSameTestAddendPatternChiral
      iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence := by
  apply molecularFullereneRelationalChiral_of_flagWord_obstruction
    iupacP93CanonicalFullereneC70SuperimposedMolecule
    iupacP93CanonicalFullereneC70SuperimposedTopologyInput
    (MolecularFullereneSameTestAddendPatternPreserved
      iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence)
    iupacP93C70SuperimposedObstruction
    (iupacP93CanonicalFullereneC70SuperimposedAssembly.transportCertificate
      iupacP93CanonicalFullereneC70SharedNumberedCage.certificate).oriented
    iupacP93CanonicalFullereneC70SuperimposedSourceDart c70Superimposed_sourceBond
    iupacP93C70SuperimposedProbe iupacP93C70SuperimposedAddress
    iupacP93CanonicalFullereneC70SuperimposedCoreAudit.probeRecovers
  · intro symmetry _automorphism _reversing preserved
    exact c70Superimposed_preserved_implies_obstruction symmetry preserved
  · exact iupacP93C70SuperimposedTargetWordsReject

theorem iupacP93CanonicalFullereneC70Superimposed_actual_chiral :
    MolecularFullereneActualAddendPatternChiral
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedTopologyInput
      iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence :=
  molecularFullereneSameTestAddendPatternChiral_implies_actual
    iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence
    iupacP93CanonicalFullereneC70Superimposed_sameTest_chiral

end


end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
