import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalClassification
import TetraStereo.OneCenter.IUPACP93RelationalFullereneAuthorityCarrier

set_option autoImplicit false












namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic
open P94MolecularRingCycleScheduler

noncomputable section

def iupacP93CanonicalFullereneHandedDescriptorEvidence : FullereneDescriptorEvidence :=
  { cageNumberingKind := some .systematic
    cageTurn := some .clockwise
    everyChiralSubstituentHasCIP := false }

def iupacP93CanonicalFullereneType4DescriptorEvidence : FullereneDescriptorEvidence :=
  { cageNumberingKind := none
    cageTurn := none
    everyChiralSubstituentHasCIP := true }

def iupacP93CanonicalFullereneSuperimposedDescriptorEvidence :
    FullereneDescriptorEvidence :=
  { cageNumberingKind := some .systematic
    cageTurn := some .clockwise
    everyChiralSubstituentHasCIP := true }

def iupacP93CanonicalFullereneC76Type1RelationalInput :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC76Type1Molecule where
  topologyInput := iupacP93CanonicalFullereneC76DerivativeTopologyInput
  evidence := iupacP93CanonicalFullereneC76Type1RelationalEvidence
  descriptorEvidence := iupacP93CanonicalFullereneHandedDescriptorEvidence

def iupacP93CanonicalFullereneC60Type2RelationalInput :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC60Type2Molecule where
  topologyInput := iupacP93CanonicalFullereneC60DerivativeTopologyInput
  evidence := iupacP93CanonicalFullereneC60Type2RelationalEvidence
  descriptorEvidence := iupacP93CanonicalFullereneHandedDescriptorEvidence

def iupacP93CanonicalFullereneC60Type3RelationalInput :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC60Type3Molecule where
  topologyInput := iupacP93CanonicalFullereneC60DerivativeTopologyInput
  evidence := iupacP93CanonicalFullereneC60Type3RelationalEvidence
  descriptorEvidence := iupacP93CanonicalFullereneHandedDescriptorEvidence

def iupacP93CanonicalFullereneC70Type4RelationalInput :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble where
  topologyInput := iupacP93CanonicalFullereneC70DerivativeInput
  evidence := iupacP93CanonicalFullereneC70Type4RelationalEvidence
  descriptorEvidence := iupacP93CanonicalFullereneType4DescriptorEvidence

def iupacP93CanonicalFullereneC70SuperimposedRelationalInput :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC70SuperimposedMolecule where
  topologyInput := iupacP93CanonicalFullereneC70SuperimposedTopologyInput
  evidence := iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence
  descriptorEvidence := iupacP93CanonicalFullereneSuperimposedDescriptorEvidence

theorem iupacP93CanonicalFullereneC76Type1RelationalInput_judged :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76Type1RelationalInput := by
  simpa [RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment,
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput.cage,
    iupacP93CanonicalFullereneC76Type1RelationalInput] using
    (iupacP93CanonicalFullereneC76Type1Assembly.transportCertificate
      iupacP93CanonicalFullereneC76SharedNumberedCage.certificate).compile_oriented
        iupacP93CanonicalFullereneC76Type1Molecule
        iupacP93CanonicalFullereneC76Transcription.numberedPackage
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC76Type1Molecule
          iupacP93CanonicalFullereneC76DerivativeTopologyInput
          iupacP93CanonicalFullereneC76Type1RelationalEvidence)
        iupacP93CanonicalFullereneHandedDescriptorEvidence

theorem iupacP93CanonicalFullereneC60Type2RelationalInput_judged :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC60Type2RelationalInput := by
  simpa [RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment,
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput.cage,
    iupacP93CanonicalFullereneC60Type2RelationalInput] using
    (iupacP93CanonicalFullereneC60Type2Assembly.transportCertificate
      iupacP93CanonicalFullereneC60SharedNumberedCage.certificate).compile_oriented
        iupacP93CanonicalFullereneC60Type2Molecule
        iupacP93CanonicalFullereneC60Transcription.numberedPackage
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC60Type2Molecule
          iupacP93CanonicalFullereneC60DerivativeTopologyInput
          iupacP93CanonicalFullereneC60Type2RelationalEvidence)
        iupacP93CanonicalFullereneHandedDescriptorEvidence

theorem iupacP93CanonicalFullereneC60Type3RelationalInput_judged :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC60Type3RelationalInput := by
  simpa [RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment,
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput.cage,
    iupacP93CanonicalFullereneC60Type3RelationalInput] using
    (iupacP93CanonicalFullereneC60Type3Assembly.transportCertificate
      iupacP93CanonicalFullereneC60SharedNumberedCage.certificate).compile_oriented
        iupacP93CanonicalFullereneC60Type3Molecule
        iupacP93CanonicalFullereneC60Transcription.numberedPackage
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC60Type3Molecule
          iupacP93CanonicalFullereneC60DerivativeTopologyInput
          iupacP93CanonicalFullereneC60Type3RelationalEvidence)
        iupacP93CanonicalFullereneHandedDescriptorEvidence

theorem iupacP93CanonicalFullereneC70Type4RelationalInput_judged :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70Type4RelationalInput := by
  simpa [RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment,
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput.cage,
    iupacP93CanonicalFullereneC70Type4RelationalInput] using
    (iupacP93CanonicalFullereneC70Type4Assembly.transportCertificate
      iupacP93CanonicalFullereneC70SharedNumberedCage.certificate).compile_oriented
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        iupacP93CanonicalFullereneC70Transcription.numberedPackage
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
          iupacP93CanonicalFullereneC70DerivativeInput
          iupacP93CanonicalFullereneC70Type4RelationalEvidence)
        iupacP93CanonicalFullereneType4DescriptorEvidence

theorem iupacP93CanonicalFullereneC70SuperimposedRelationalInput_judged :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput := by
  simpa [RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment,
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput.cage,
    iupacP93CanonicalFullereneC70SuperimposedRelationalInput] using
    (iupacP93CanonicalFullereneC70SuperimposedAssembly.transportCertificate
      iupacP93CanonicalFullereneC70SharedNumberedCage.certificate).compile_oriented
        iupacP93CanonicalFullereneC70SuperimposedMolecule
        iupacP93CanonicalFullereneC70Transcription.numberedPackage
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC70SuperimposedMolecule
          iupacP93CanonicalFullereneC70SuperimposedTopologyInput
          iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence)
        iupacP93CanonicalFullereneSuperimposedDescriptorEvidence

/-! ## Three source-numbering records for the four handed rows -/

def iupacP93CanonicalFullereneC76FsCNumberingEvidence :
    MolecularFullereneNumberingEvidence where
  numberingKind := .systematic
  atomsByLocant := iupacP93CanonicalFullereneC76Transcription.atomsByLocant
  startingFace := iupacP93CanonicalFullereneC76FsCStartFace

def iupacP93CanonicalFullereneC60FsCNumberingEvidence :
    MolecularFullereneNumberingEvidence where
  numberingKind := .systematic
  atomsByLocant := iupacP93CanonicalFullereneC60Transcription.atomsByLocant
  startingFace := iupacP93CanonicalFullereneC60FsCStartFace

def iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence :
    MolecularFullereneNumberingEvidence where
  numberingKind := .systematic
  atomsByLocant := iupacP93CanonicalFullereneC70Transcription.atomsByLocant
  startingFace := iupacP93CanonicalFullereneC70Page83FsCStartFace

theorem iupacP93CanonicalFullereneC76FsCNumberingEvidence_judged :
    MolecularFullereneNumberingEvidenceJudgment
      iupacP93CanonicalFullereneC76Type1RelationalInput.cage
      iupacP93CanonicalFullereneC76FsCNumberingEvidence := by
  refine ⟨?_, ?_, iupacP93CanonicalFullereneC76Transcription_start_face_present, ?_⟩
  · simpa [iupacP93CanonicalFullereneC76FsCNumberingEvidence,
      iupacP93CanonicalFullereneC76Transcription_atomsByLocant] using
      (List.nodup_range : (List.range 76).Nodup)
  · rfl
  · refine ⟨0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · refine ⟨by simp [iupacP93CanonicalFullereneC76FsCNumberingEvidence,
          iupacP93CanonicalFullereneC76FsCStartFace], Or.inl ?_⟩
      simp [iupacP93CanonicalFullereneC76FsCNumberingEvidence,
        iupacP93CanonicalFullereneC76FsCStartFace, List.next]
    · refine ⟨by simp [iupacP93CanonicalFullereneC76FsCNumberingEvidence,
          iupacP93CanonicalFullereneC76FsCStartFace], Or.inl ?_⟩
      simp [iupacP93CanonicalFullereneC76FsCNumberingEvidence,
        iupacP93CanonicalFullereneC76FsCStartFace, List.next]
      decide

theorem iupacP93CanonicalFullereneC60FsCNumberingEvidence_judged
    (input : MolecularFullereneConfigurationInput)
    (carrier : input.carrier =
      iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier)
    (faces : input.faces = iupacP93CanonicalFullereneC60Transcription.numberedPackage.faces) :
    MolecularFullereneNumberingEvidenceJudgment input
      iupacP93CanonicalFullereneC60FsCNumberingEvidence := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [iupacP93CanonicalFullereneC60FsCNumberingEvidence,
      iupacP93CanonicalFullereneC60Transcription_atomsByLocant] using
      (List.nodup_range : (List.range 60).Nodup)
  · simpa [iupacP93CanonicalFullereneC60FsCNumberingEvidence] using carrier.symm
  · rw [faces]
    exact iupacP93CanonicalFullereneC60_fsCStartFace_mem
  · refine ⟨0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · refine ⟨by simp [iupacP93CanonicalFullereneC60FsCNumberingEvidence,
          iupacP93CanonicalFullereneC60FsCStartFace], Or.inl ?_⟩
      simp [iupacP93CanonicalFullereneC60FsCNumberingEvidence,
        iupacP93CanonicalFullereneC60FsCStartFace, List.next]
    · refine ⟨by simp [iupacP93CanonicalFullereneC60FsCNumberingEvidence,
          iupacP93CanonicalFullereneC60FsCStartFace], Or.inl ?_⟩
      simp [iupacP93CanonicalFullereneC60FsCNumberingEvidence,
        iupacP93CanonicalFullereneC60FsCStartFace, List.next]
      decide

theorem iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence_judged :
    MolecularFullereneNumberingEvidenceJudgment
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage
      iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence := by
  refine ⟨?_, ?_, iupacP93CanonicalFullereneC70_page83_start_face_present, ?_⟩
  · simpa [iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence,
      iupacP93CanonicalFullereneC70Transcription_atomsByLocant] using
      (List.nodup_range : (List.range 70).Nodup)
  · rfl
  · refine ⟨0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · refine ⟨by simp [iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence,
          iupacP93CanonicalFullereneC70Page83FsCStartFace], Or.inl ?_⟩
      simp [iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence,
        iupacP93CanonicalFullereneC70Page83FsCStartFace, List.next]
    · refine ⟨by simp [iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence,
          iupacP93CanonicalFullereneC70Page83FsCStartFace], Or.inl ?_⟩
      simp [iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence,
        iupacP93CanonicalFullereneC70Page83FsCStartFace, List.next]
      decide

/-! ## One mathematical progression for every printed `(f,sC)` start face -/

theorem iupacP93CanonicalFullereneC76FsCNumberingProgression_forward :
    MolecularFullereneNumberingProgressionJudgment
      iupacP93CanonicalFullereneC76FsCNumberingEvidence .forward := by
  simp [MolecularFullereneNumberingProgressionJudgment,
    IsForwardNamedCycleEdge, molecularFullereneNumberedAtom,
    iupacP93CanonicalFullereneC76FsCNumberingEvidence,
    iupacP93CanonicalFullereneC76Transcription_atomsByLocant,
    iupacP93CanonicalFullereneC76FsCStartFace, List.next]
  decide

theorem iupacP93CanonicalFullereneC60FsCNumberingProgression_forward :
    MolecularFullereneNumberingProgressionJudgment
      iupacP93CanonicalFullereneC60FsCNumberingEvidence .forward := by
  simp [MolecularFullereneNumberingProgressionJudgment,
    IsForwardNamedCycleEdge, molecularFullereneNumberedAtom,
    iupacP93CanonicalFullereneC60FsCNumberingEvidence,
    iupacP93CanonicalFullereneC60Transcription_atomsByLocant,
    iupacP93CanonicalFullereneC60FsCStartFace, List.next]
  decide

theorem iupacP93CanonicalFullereneC70Page83FsCNumberingProgression_forward :
    MolecularFullereneNumberingProgressionJudgment
      iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence .forward := by
  simp [MolecularFullereneNumberingProgressionJudgment,
    IsForwardNamedCycleEdge, molecularFullereneNumberedAtom,
    iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence,
    iupacP93CanonicalFullereneC70Transcription_atomsByLocant,
    iupacP93CanonicalFullereneC70Page83FsCStartFace, List.next]
  decide

/-! ## Clockwise turn conditional on exterior sense, and coordinate-free local admission -/

theorem iupacP93CanonicalFullereneC76Type1ExteriorTurn_clockwise :
    MolecularFullereneExteriorTurnJudgment
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76Type1RelationalInput.cage
      iupacP93CanonicalFullereneC76FsCNumberingEvidence
      .clockwiseFromOutside .clockwise := by
  simpa [fullereneExteriorTurn] using
    (molecularFullereneExteriorTurnJudgment_of_progression
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76Type1RelationalInput.cage
      iupacP93CanonicalFullereneC76FsCNumberingEvidence
      .clockwiseFromOutside .forward
      iupacP93CanonicalFullereneC76Type1RelationalInput_judged
      iupacP93CanonicalFullereneC76FsCNumberingEvidence_judged
      iupacP93CanonicalFullereneC76FsCNumberingProgression_forward)

theorem iupacP93CanonicalFullereneC60Type2ExteriorTurn_clockwise :
    MolecularFullereneExteriorTurnJudgment
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC60Type2RelationalInput.cage
      iupacP93CanonicalFullereneC60FsCNumberingEvidence
      .clockwiseFromOutside .clockwise := by
  simpa [fullereneExteriorTurn] using
    (molecularFullereneExteriorTurnJudgment_of_progression
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC60Type2RelationalInput.cage
      iupacP93CanonicalFullereneC60FsCNumberingEvidence
      .clockwiseFromOutside .forward
      iupacP93CanonicalFullereneC60Type2RelationalInput_judged
      (iupacP93CanonicalFullereneC60FsCNumberingEvidence_judged
        iupacP93CanonicalFullereneC60Type2RelationalInput.cage rfl rfl)
      iupacP93CanonicalFullereneC60FsCNumberingProgression_forward)

theorem iupacP93CanonicalFullereneC60Type3ExteriorTurn_clockwise :
    MolecularFullereneExteriorTurnJudgment
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC60Type3RelationalInput.cage
      iupacP93CanonicalFullereneC60FsCNumberingEvidence
      .clockwiseFromOutside .clockwise := by
  simpa [fullereneExteriorTurn] using
    (molecularFullereneExteriorTurnJudgment_of_progression
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC60Type3RelationalInput.cage
      iupacP93CanonicalFullereneC60FsCNumberingEvidence
      .clockwiseFromOutside .forward
      iupacP93CanonicalFullereneC60Type3RelationalInput_judged
      (iupacP93CanonicalFullereneC60FsCNumberingEvidence_judged
        iupacP93CanonicalFullereneC60Type3RelationalInput.cage rfl rfl)
      iupacP93CanonicalFullereneC60FsCNumberingProgression_forward)

theorem iupacP93CanonicalFullereneC70SuperimposedExteriorTurn_clockwise :
    MolecularFullereneExteriorTurnJudgment
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage
      iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence
      .clockwiseFromOutside .clockwise := by
  simpa [fullereneExteriorTurn] using
    (molecularFullereneExteriorTurnJudgment_of_progression
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage
      iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence
      .clockwiseFromOutside .forward
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput_judged
      iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence_judged
      iupacP93CanonicalFullereneC70Page83FsCNumberingProgression_forward)

def iupacP93CanonicalFullereneC76Type1RelationalSourceInput :
    RelationalSourceOrientedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC76Type1Molecule where
  symmetryInput := iupacP93CanonicalFullereneC76Type1RelationalInput
  numberingEvidence := iupacP93CanonicalFullereneC76FsCNumberingEvidence
  turnSource := .exterior .clockwiseFromOutside

def iupacP93CanonicalFullereneC60Type2RelationalSourceInput :
    RelationalSourceOrientedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC60Type2Molecule where
  symmetryInput := iupacP93CanonicalFullereneC60Type2RelationalInput
  numberingEvidence := iupacP93CanonicalFullereneC60FsCNumberingEvidence
  turnSource := .exterior .clockwiseFromOutside

def iupacP93CanonicalFullereneC60Type3RelationalSourceInput :
    RelationalSourceOrientedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC60Type3Molecule where
  symmetryInput := iupacP93CanonicalFullereneC60Type3RelationalInput
  numberingEvidence := iupacP93CanonicalFullereneC60FsCNumberingEvidence
  turnSource := .exterior .clockwiseFromOutside

def iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput :
    RelationalSourceOrientedMolecularFullereneConfigurationInput
      iupacP93CanonicalFullereneC70SuperimposedMolecule where
  symmetryInput := iupacP93CanonicalFullereneC70SuperimposedRelationalInput
  numberingEvidence := iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence
  turnSource := .exterior .clockwiseFromOutside

theorem iupacP93CanonicalFullereneC76Type1RelationalSourceInput_judged :
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC76Type1Molecule none
      iupacP93CanonicalFullereneC76Type1RelationalSourceInput := by
  simpa [iupacP93CanonicalFullereneC76Type1RelationalSourceInput] using
    (relationalSourceOriented_exterior_judgment_none_iff
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76Type1RelationalInput
      iupacP93CanonicalFullereneC76FsCNumberingEvidence
      .clockwiseFromOutside).2
        ⟨iupacP93CanonicalFullereneC76Type1RelationalInput_judged,
          .clockwise, iupacP93CanonicalFullereneC76Type1ExteriorTurn_clockwise,
          rfl, rfl⟩

theorem iupacP93CanonicalFullereneC60Type2RelationalSourceInput_judged :
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC60Type2Molecule none
      iupacP93CanonicalFullereneC60Type2RelationalSourceInput := by
  simpa [iupacP93CanonicalFullereneC60Type2RelationalSourceInput] using
    (relationalSourceOriented_exterior_judgment_none_iff
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC60Type2RelationalInput
      iupacP93CanonicalFullereneC60FsCNumberingEvidence
      .clockwiseFromOutside).2
        ⟨iupacP93CanonicalFullereneC60Type2RelationalInput_judged,
          .clockwise, iupacP93CanonicalFullereneC60Type2ExteriorTurn_clockwise,
          rfl, rfl⟩

theorem iupacP93CanonicalFullereneC60Type3RelationalSourceInput_judged :
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC60Type3Molecule none
      iupacP93CanonicalFullereneC60Type3RelationalSourceInput := by
  simpa [iupacP93CanonicalFullereneC60Type3RelationalSourceInput] using
    (relationalSourceOriented_exterior_judgment_none_iff
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC60Type3RelationalInput
      iupacP93CanonicalFullereneC60FsCNumberingEvidence
      .clockwiseFromOutside).2
        ⟨iupacP93CanonicalFullereneC60Type3RelationalInput_judged,
          .clockwise, iupacP93CanonicalFullereneC60Type3ExteriorTurn_clockwise,
          rfl, rfl⟩

theorem iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput_judged :
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      iupacP93CanonicalFullereneC70SuperimposedMolecule none
      iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput := by
  simpa [iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput] using
    (relationalSourceOriented_exterior_judgment_none_iff
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput
      iupacP93CanonicalFullereneC70Page83FsCNumberingEvidence
      .clockwiseFromOutside).2
        ⟨iupacP93CanonicalFullereneC70SuperimposedRelationalInput_judged,
          .clockwise, iupacP93CanonicalFullereneC70SuperimposedExteriorTurn_clockwise,
          rfl, rfl⟩

/-! ## Five end-to-end local assignments from the actual derived substitution tests -/

def iupacP93CanonicalFullereneC76Type1LocalAssignment :
    FullereneConfigurationAssignment :=
  { unit := iupacP93CanonicalFullereneC76Type1RelationalInput.cage.carrier.sort (· ≤ ·)
    chiralityType := .inherentlyChiralParent
    payloads := [.cageHandedness .systematic .C] }

def iupacP93CanonicalFullereneC60Type2LocalAssignment :
    FullereneConfigurationAssignment :=
  { unit := iupacP93CanonicalFullereneC60Type2RelationalInput.cage.carrier.sort (· ≤ ·)
    chiralityType := .inherentlyChiralSubstitutionPattern
    payloads := [.cageHandedness .systematic .C] }

def iupacP93CanonicalFullereneC60Type3LocalAssignment :
    FullereneConfigurationAssignment :=
  { unit := iupacP93CanonicalFullereneC60Type3RelationalInput.cage.carrier.sort (· ≤ ·)
    chiralityType := .noninherentlyChiralSubstitutionPattern
    payloads := [.cageHandedness .systematic .C] }

def iupacP93CanonicalFullereneC70Type4LocalAssignment :
    FullereneConfigurationAssignment :=
  { unit := iupacP93CanonicalFullereneC70Type4RelationalInput.cage.carrier.sort (· ≤ ·)
    chiralityType := .chiralSubstituentsOnly
    payloads := [.substituentCIPComplete] }

def iupacP93CanonicalFullereneC70SuperimposedLocalAssignment :
    FullereneConfigurationAssignment :=
  { unit := iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.carrier.sort (· ≤ ·)
    chiralityType := .inherentlyChiralSubstitutionPattern
    payloads := [.cageHandedness .systematic .C] }

theorem iupacP93CanonicalFullereneC76Type1LocalAssignment_judged :
    FullereneConfigurationAssignmentJudgment
      iupacP93CanonicalFullereneC76Type1RelationalInput.cage.toFullereneConfigurationInput
      iupacP93CanonicalFullereneC76Type1LocalAssignment := by
  refine ⟨.inherentlyChiralParent, [.cageHandedness .systematic .C], ?_, ?_, ?_⟩
  · exact (fullereneChiralityType?_eq_some_iff _ _).mp
      iupacP93CanonicalFullereneC76Type1DerivedClassifier_exact
  · exact ⟨.systematic, .clockwise, rfl, rfl, rfl⟩
  · rfl

theorem iupacP93CanonicalFullereneC60Type2LocalAssignment_judged :
    FullereneConfigurationAssignmentJudgment
      iupacP93CanonicalFullereneC60Type2RelationalInput.cage.toFullereneConfigurationInput
      iupacP93CanonicalFullereneC60Type2LocalAssignment := by
  refine ⟨.inherentlyChiralSubstitutionPattern,
    [.cageHandedness .systematic .C], ?_, ?_, ?_⟩
  · exact (fullereneChiralityType?_eq_some_iff _ _).mp
      iupacP93CanonicalFullereneC60Type2DerivedClassifier_exact
  · exact ⟨.systematic, .clockwise, rfl, rfl, rfl⟩
  · rfl

theorem iupacP93CanonicalFullereneC60Type3LocalAssignment_judged :
    FullereneConfigurationAssignmentJudgment
      iupacP93CanonicalFullereneC60Type3RelationalInput.cage.toFullereneConfigurationInput
      iupacP93CanonicalFullereneC60Type3LocalAssignment := by
  refine ⟨.noninherentlyChiralSubstitutionPattern,
    [.cageHandedness .systematic .C], ?_, ?_, ?_⟩
  · exact (fullereneChiralityType?_eq_some_iff _ _).mp
      iupacP93CanonicalFullereneC60Type3DerivedClassifier_exact
  · exact ⟨.systematic, .clockwise, rfl, rfl, rfl⟩
  · rfl

theorem iupacP93CanonicalFullereneC70Type4LocalAssignment_judged :
    FullereneConfigurationAssignmentJudgment
      iupacP93CanonicalFullereneC70Type4RelationalInput.cage.toFullereneConfigurationInput
      iupacP93CanonicalFullereneC70Type4LocalAssignment := by
  refine ⟨.chiralSubstituentsOnly, [.substituentCIPComplete], ?_, ?_, ?_⟩
  · exact (fullereneChiralityType?_eq_some_iff _ _).mp
      iupacP93CanonicalFullereneC70Type4DerivedClassifier_exact
  · exact ⟨rfl, rfl⟩
  · rfl

theorem iupacP93CanonicalFullereneC70SuperimposedLocalAssignment_judged :
    FullereneConfigurationAssignmentJudgment
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.toFullereneConfigurationInput
      iupacP93CanonicalFullereneC70SuperimposedLocalAssignment := by
  refine ⟨.inherentlyChiralSubstitutionPattern,
    [.cageHandedness .systematic .C], ?_, ?_, ?_⟩
  · exact (fullereneChiralityType?_eq_some_iff _ _).mp
      iupacP93CanonicalFullereneC70SuperimposedDerivedClassifier_exact
  · exact ⟨.systematic, .clockwise, rfl, rfl, rfl⟩
  · rfl

theorem iupacP93CanonicalFullereneLocalAssignments_all_judged :
    FullereneConfigurationAssignmentJudgment
        iupacP93CanonicalFullereneC76Type1RelationalInput.cage.toFullereneConfigurationInput
        iupacP93CanonicalFullereneC76Type1LocalAssignment ∧
    FullereneConfigurationAssignmentJudgment
        iupacP93CanonicalFullereneC60Type2RelationalInput.cage.toFullereneConfigurationInput
        iupacP93CanonicalFullereneC60Type2LocalAssignment ∧
    FullereneConfigurationAssignmentJudgment
        iupacP93CanonicalFullereneC60Type3RelationalInput.cage.toFullereneConfigurationInput
        iupacP93CanonicalFullereneC60Type3LocalAssignment ∧
    FullereneConfigurationAssignmentJudgment
        iupacP93CanonicalFullereneC70Type4RelationalInput.cage.toFullereneConfigurationInput
        iupacP93CanonicalFullereneC70Type4LocalAssignment ∧
    FullereneConfigurationAssignmentJudgment
        iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.toFullereneConfigurationInput
        iupacP93CanonicalFullereneC70SuperimposedLocalAssignment :=
  ⟨iupacP93CanonicalFullereneC76Type1LocalAssignment_judged,
    iupacP93CanonicalFullereneC60Type2LocalAssignment_judged,
    iupacP93CanonicalFullereneC60Type3LocalAssignment_judged,
    iupacP93CanonicalFullereneC70Type4LocalAssignment_judged,
    iupacP93CanonicalFullereneC70SuperimposedLocalAssignment_judged⟩

/-! ## Exact singleton-family analyzer judgments, prior to source-policy authorization -/

theorem iupacP93CanonicalFullereneC76Type1AuthorityAssignment_judged :
    P93RelationalFullereneAuthorityAssignmentJudgment
      iupacP93CanonicalFullereneC76Type1Molecule none
      [iupacP93CanonicalFullereneC76Type1RelationalSourceInput]
      iupacP93CanonicalFullereneC76Type1LocalAssignment :=
  relationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment_singleton
    iupacP93CanonicalFullereneC76Type1Molecule none
    iupacP93CanonicalFullereneC76Type1RelationalSourceInput
    iupacP93CanonicalFullereneC76Type1LocalAssignment
    iupacP93CanonicalFullereneC76Type1RelationalSourceInput_judged
    iupacP93CanonicalFullereneC76Type1LocalAssignment_judged

theorem iupacP93CanonicalFullereneC60Type2AuthorityAssignment_judged :
    P93RelationalFullereneAuthorityAssignmentJudgment
      iupacP93CanonicalFullereneC60Type2Molecule none
      [iupacP93CanonicalFullereneC60Type2RelationalSourceInput]
      iupacP93CanonicalFullereneC60Type2LocalAssignment :=
  relationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment_singleton
    iupacP93CanonicalFullereneC60Type2Molecule none
    iupacP93CanonicalFullereneC60Type2RelationalSourceInput
    iupacP93CanonicalFullereneC60Type2LocalAssignment
    iupacP93CanonicalFullereneC60Type2RelationalSourceInput_judged
    iupacP93CanonicalFullereneC60Type2LocalAssignment_judged

theorem iupacP93CanonicalFullereneC60Type3AuthorityAssignment_judged :
    P93RelationalFullereneAuthorityAssignmentJudgment
      iupacP93CanonicalFullereneC60Type3Molecule none
      [iupacP93CanonicalFullereneC60Type3RelationalSourceInput]
      iupacP93CanonicalFullereneC60Type3LocalAssignment :=
  relationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment_singleton
    iupacP93CanonicalFullereneC60Type3Molecule none
    iupacP93CanonicalFullereneC60Type3RelationalSourceInput
    iupacP93CanonicalFullereneC60Type3LocalAssignment
    iupacP93CanonicalFullereneC60Type3RelationalSourceInput_judged
    iupacP93CanonicalFullereneC60Type3LocalAssignment_judged

theorem iupacP93CanonicalFullereneC70SuperimposedAuthorityAssignment_judged :
    P93RelationalFullereneAuthorityAssignmentJudgment
      iupacP93CanonicalFullereneC70SuperimposedMolecule none
      [iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput]
      iupacP93CanonicalFullereneC70SuperimposedLocalAssignment :=
  relationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment_singleton
    iupacP93CanonicalFullereneC70SuperimposedMolecule none
    iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput
    iupacP93CanonicalFullereneC70SuperimposedLocalAssignment
    iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput_judged
    iupacP93CanonicalFullereneC70SuperimposedLocalAssignment_judged

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
