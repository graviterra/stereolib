import TetraStereo.OneCenter.P93MolecularFullereneExecutableFlagSymmetryCardinality
import TetraStereo.OneCenter.P93MolecularFullereneFiniteFaceCertificate

set_option autoImplicit false

/-!
# Target-dart normal form for relational fullerene audits

The executable reversing corpus is generated injectively from the accepted images of one
distinguished source dart.  Consequently a relational chirality proof never needs to quantify
over proof-carrying carrier permutations: it is exactly a finite rejection test on those target
darts.  Its negation, once the oriented cage judgment is known, is exactly one accepted target
dart whose generated symmetry preserves the relation.
-/

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

open TetraStereo.OneCenter.P93CanonicalProgramFullerene

/-- For the canonical face-derived cage molecule, positive bond order is exactly the frozen
face-edge relation on bounded distinct locants. -/
theorem NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
    (transcription : NumberedFaceTranscription) (left right : Nat)
    (leftBound : left < transcription.atomCount)
    (rightBound : right < transcription.atomCount) (distinct : left ≠ right) :
    0 < transcription.cageMolecule.bondOrder left right ↔
      transcription.hasFaceEdge left right = true := by
  rw [transcription.cageMolecule.bondOrder_pos_iff_exists_bond distinct]
  exact numberedFaceTranscription_bonded_iff_hasFaceEdge
    transcription left right leftBound rightBound distinct

/-- Constitutional preservation forgets to the common achiral-test port semantics. -/
theorem MolecularFullereneAddend.ConstitutionallyIsomorphicAlong.toUnlabeledSameTest
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    {symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)}
    {first second : MolecularFullereneAddend}
    (along : first.ConstitutionallyIsomorphicAlong molecule input symmetry second) :
    MolecularFullereneUnlabeledSameTestPortEquivalence input symmetry first second := by
  rcases along with
    ⟨_atomEquivalence, _atoms, _bonds, siteEquivalence, agrees,
      _portEquivalence, _sites, _endpoints, _attachmentBonds⟩
  exact ⟨siteEquivalence, agrees⟩

/-- Every actual-identity-preserving symmetry also preserves the corresponding all-`T` pattern. -/
theorem molecularFullereneActualAddendPatternPreserved_implies_sameTest
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    MolecularFullereneActualAddendPatternPreserved molecule input evidence symmetry →
      MolecularFullereneSameTestAddendPatternPreserved evidence symmetry := by
  rintro ⟨addendEquivalence, preserves⟩
  exact ⟨addendEquivalence, fun source => (preserves source).toUnlabeledSameTest⟩

/-- The all-`T` stage is coarser than the actual-identity stage, so chirality of the former
immediately forces chirality of the latter. -/
theorem molecularFullereneSameTestAddendPatternChiral_implies_actual
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier) :
    MolecularFullereneSameTestAddendPatternChiral evidence →
      MolecularFullereneActualAddendPatternChiral molecule input evidence := by
  rintro ⟨oriented, noSameTest⟩
  refine ⟨oriented, ?_⟩
  rintro ⟨symmetry, automorphism, reversing, actualPreserved⟩
  exact noSameTest ⟨symmetry, automorphism, reversing,
    molecularFullereneActualAddendPatternPreserved_implies_sameTest
      evidence symmetry actualPreserved⟩

/-- An intrinsically chiral parent cage makes every substitution relation chiral.  The parent
color is constant, so any reversing carrier automorphism would preserve it automatically,
independently of the chosen derivative relation. -/
theorem molecularFullereneParentChiral_implies_relational
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (parentChiral : MolecularFullereneColoringChiral molecule input
      molecularFullereneParentColor)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop) :
    MolecularFullereneRelationalChiral molecule input preserved := by
  rcases parentChiral with ⟨oriented, rejectsParent⟩
  refine ⟨oriented, ?_⟩
  rintro ⟨symmetry, automorphism, reversing, _relationPreserved⟩
  exact rejectsParent ⟨symmetry, automorphism, reversing, fun _atom => rfl⟩

/-- A handful of recovering flag words is enough to reject every preserving reversing symmetry.
Unlike a full spanning certificate, this theorem needs addresses only for the atoms observed by
the obstruction.  Equivariance transports those source recoveries to their exact images from the
image dart of any alleged reversing automorphism. -/
theorem molecularFullereneRelationalChiral_of_flagWord_obstruction
    {Probe : Type*}
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop)
    (obstruction : (Probe → MolecularFullereneCarrierAtom input) → Prop)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneDirectedCarrierEdge input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (probe : Probe → MolecularFullereneCarrierAtom input)
    (address : Probe → List MolecularFullereneFlagMove)
    (recovers : ∀ index,
      (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        source (address index)).1 = probe index)
    (admissibleImpliesObstruction : ∀ symmetry,
      MolecularFullereneCarrierAutomorphism molecule input symmetry →
        MolecularFullereneFaceOrientationReversing input symmetry →
          preserved symmetry → obstruction (fun index => symmetry (probe index)))
    (targetWordsReject : ∀ target : MolecularFullereneDirectedCarrierEdge input,
      0 < molecule.bondOrder target.1.1 target.2.1 →
        ¬obstruction (fun index =>
          (walkMolecularFullereneFlag (molecularFullereneContinueReverseFace input)
            target (address index)).1)) :
    MolecularFullereneRelationalChiral molecule input preserved := by
  refine ⟨oriented, ?_⟩
  rintro ⟨symmetry, automorphism, reversing, relationPreserved⟩
  let target := mapMolecularFullereneDirectedEdge symmetry source
  have targetBond : 0 < molecule.bondOrder target.1.1 target.2.1 :=
    (automorphism source.1 source.2).mp sourceBond
  apply targetWordsReject target targetBond
  have imageExact : (fun index =>
      (walkMolecularFullereneFlag (molecularFullereneContinueReverseFace input)
        target (address index)).1) = fun index => symmetry (probe index) := by
    funext index
    have walkEq := congrArg Prod.fst
      (walkMolecularFullereneFlag_equivariant
        (molecularFullereneContinueForwardFace input)
        (molecularFullereneContinueReverseFace input) symmetry
        (molecularFullereneContinueReverseFace_equivariant
          molecule input oriented symmetry automorphism reversing)
        source (address index))
    change (walkMolecularFullereneFlag (molecularFullereneContinueReverseFace input)
        target (address index)).1 =
      symmetry
        (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
          source (address index)).1 at walkEq
    rw [walkEq, recovers]
  rw [imageExact]
  exact admissibleImpliesObstruction symmetry automorphism reversing relationPreserved

/-- A source-spanning flag certificate converts any symmetry-level necessary condition for
preservation into a finite obstruction on raw generated vertex maps.  This avoids constructing,
comparing, or deciding equality of proof-carrying permutations: an alleged reversing preserving
automorphism is definitionally recovered by replaying the source addresses from the image of one
bonded dart. -/
theorem molecularFullereneRelationalChiral_of_generatedVertexMap_obstruction
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop)
    (obstruction :
      (MolecularFullereneCarrierAtom input → MolecularFullereneCarrierAtom input) → Prop)
    (certificate : MolecularFullereneConcreteFlagExtensionCertificate molecule input)
    (preservedImpliesObstruction : ∀ symmetry, preserved symmetry → obstruction symmetry)
    (generatedRejects : ∀ target : MolecularFullereneDirectedCarrierEdge input,
      0 < molecule.bondOrder target.1.1 target.2.1 →
        ¬obstruction
          (molecularFullereneGeneratedVertexMap
            (certificate.toReversingPropagation molecule input) target)) :
    MolecularFullereneRelationalChiral molecule input preserved := by
  refine ⟨certificate.oriented, ?_⟩
  rintro ⟨symmetry, automorphism, reversing, relationPreserved⟩
  let propagation := certificate.toReversingPropagation molecule input
  let target := mapMolecularFullereneDirectedEdge symmetry certificate.source
  have targetBond : 0 < molecule.bondOrder target.1.1 target.2.1 := by
    exact (automorphism certificate.source.1 certificate.source.2).mp certificate.sourceBond
  have generatedEq : molecularFullereneGeneratedVertexMap propagation target = symmetry :=
    molecularFullereneGeneratedVertexMap_imageSource propagation symmetry
      ⟨automorphism, reversing⟩
  apply generatedRejects target targetBond
  rw [generatedEq]
  exact preservedImpliesObstruction symmetry relationPreserved

/-- Relational chirality in the compact target-dart normal form. -/
theorem molecularFullereneRelationalChiral_iff_executableTargetDarts
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    MolecularFullereneRelationalChiral molecule input preserved ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ target ∈ molecularFullereneExecutableReversingTargetDarts
            molecule input certificate,
          ¬preserved
            (molecularFullereneExecutableGeneratedExtension molecule input
              (certificate.toExecutableConcreteFlagExtension molecule input) target) := by
  rw [molecularFullereneRelationalChiral_iff_executableFlagSymmetry
    molecule input preserved certificate]
  let targets := molecularFullereneExecutableReversingTargetDarts
    molecule input certificate
  let generated := molecularFullereneExecutableGeneratedExtension molecule input
    (certificate.toExecutableConcreteFlagExtension molecule input)
  have corpusExact : molecularFullereneExecutableReversingAutomorphisms
      molecule input certificate = targets.image generated :=
    molecularFullereneExecutableReversingAutomorphisms_eq_image_targetDarts
      molecule input certificate
  constructor
  · rintro ⟨oriented, rejects⟩
    refine ⟨oriented, ?_⟩
    intro target targetPresent preservedTarget
    exact rejects (generated target) (by
      rw [corpusExact]
      exact Finset.mem_image.mpr ⟨target, targetPresent, rfl⟩) preservedTarget
  · rintro ⟨oriented, rejects⟩
    refine ⟨oriented, ?_⟩
    intro symmetry symmetryPresent preservedSymmetry
    rw [corpusExact] at symmetryPresent
    obtain ⟨target, targetPresent, generatedEq⟩ := Finset.mem_image.mp symmetryPresent
    apply rejects target targetPresent
    change molecularFullereneExecutableGeneratedExtension molecule input
      (certificate.toExecutableConcreteFlagExtension molecule input) target = symmetry at generatedEq
    rw [generatedEq]
    exact preservedSymmetry

/-- With the oriented cage already certified, relational achirality is witnessed by one compact
accepted target dart and preservation by its generated symmetry. -/
theorem not_molecularFullereneRelationalChiral_iff_executableTargetDart
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input) :
    ¬MolecularFullereneRelationalChiral molecule input preserved ↔
      ∃ target ∈ molecularFullereneExecutableReversingTargetDarts
          molecule input certificate,
        preserved
          (molecularFullereneExecutableGeneratedExtension molecule input
            (certificate.toExecutableConcreteFlagExtension molecule input) target) := by
  rw [molecularFullereneRelationalChiral_iff_executableTargetDarts
    molecule input preserved certificate]
  simp [oriented]

end TetraStereo.OneCenter.BlueBookP93.Cyclic

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneAddend.ConstitutionallyIsomorphicAlong.toUnlabeledSameTest
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneActualAddendPatternPreserved_implies_sameTest
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneSameTestAddendPatternChiral_implies_actual
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneParentChiral_implies_relational
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneRelationalChiral_of_flagWord_obstruction
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneRelationalChiral_of_generatedVertexMap_obstruction
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneRelationalChiral_iff_executableTargetDarts
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.not_molecularFullereneRelationalChiral_iff_executableTargetDart
