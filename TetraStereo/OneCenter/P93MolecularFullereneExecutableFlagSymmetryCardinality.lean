import TetraStereo.OneCenter.P93MolecularFullereneExecutableFlagSymmetry

set_option autoImplicit false

/-!
# Compact cardinality certificates for executable fullerene symmetries

The complete reversing corpus stores permutations, so reducing its `Finset.card` directly also
reduces repeated extensional equality tests between proof-carrying equivalences.  This module
proves that the same corpus is the injective image of a filtered set of source-dart targets.
Concrete cage audits can therefore kernel-check a small directed-edge count and transport it to
the exact permutation corpus without trusting an external evaluator.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-- Candidate image darts which generate a reversing automorphism and are recovered as the
image of the distinguished source dart.  The last conjunct makes the generated-extension map
injective on this set. -/
def molecularFullereneExecutableReversingTargetDarts
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    Finset (MolecularFullereneDirectedCarrierEdge input) :=
  let concrete := certificate.toExecutableConcreteFlagExtension molecule input
  (molecularFullereneBondedDirectedEdges molecule input).filter fun target =>
    let symmetry :=
      molecularFullereneExecutableGeneratedExtension molecule input concrete target
    molecularFullereneCarrierAutomorphismChecked molecule input symmetry &&
      molecularFullereneFaceOrientationReversingChecked input symmetry &&
        decide (mapMolecularFullereneDirectedEdge symmetry concrete.source = target)

theorem mem_molecularFullereneExecutableReversingTargetDarts_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (target : MolecularFullereneDirectedCarrierEdge input) :
    target ∈ molecularFullereneExecutableReversingTargetDarts molecule input certificate ↔
      target ∈ molecularFullereneBondedDirectedEdges molecule input ∧
        let concrete := certificate.toExecutableConcreteFlagExtension molecule input
        let symmetry :=
          molecularFullereneExecutableGeneratedExtension molecule input concrete target
        MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
          MolecularFullereneFaceOrientationReversing input symmetry ∧
            mapMolecularFullereneDirectedEdge symmetry concrete.source = target := by
  simp [molecularFullereneExecutableReversingTargetDarts, Bool.and_eq_true, and_assoc]

theorem molecularFullereneExecutableReversingAutomorphisms_eq_image_targetDarts
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    molecularFullereneExecutableReversingAutomorphisms molecule input certificate =
      (molecularFullereneExecutableReversingTargetDarts molecule input certificate).image
        (molecularFullereneExecutableGeneratedExtension molecule input
          (certificate.toExecutableConcreteFlagExtension molecule input)) := by
  let concrete := certificate.toExecutableConcreteFlagExtension molecule input
  let generated :=
    molecularFullereneExecutableGeneratedExtension molecule input concrete
  apply Finset.ext
  intro symmetry
  constructor
  · intro present
    have filtered := Finset.mem_filter.mp present
    rcases Finset.mem_image.mp filtered.1 with ⟨target, targetBonded, generatedEq⟩
    have checks :
        molecularFullereneCarrierAutomorphismChecked molecule input symmetry = true ∧
          molecularFullereneFaceOrientationReversingChecked input symmetry = true := by
      simpa only [Bool.and_eq_true] using filtered.2
    have automorphism :=
      (molecularFullereneCarrierAutomorphismChecked_eq_true_iff
        molecule input symmetry).mp checks.1
    have reversing :=
      (molecularFullereneFaceOrientationReversingChecked_eq_true_iff
        input symmetry).mp checks.2
    let recovered := mapMolecularFullereneDirectedEdge symmetry concrete.source
    have recoveredBonded : recovered ∈ molecularFullereneBondedDirectedEdges molecule input := by
      simp only [molecularFullereneBondedDirectedEdges, Finset.mem_filter,
        Finset.mem_univ, true_and, decide_eq_true_eq]
      exact (automorphism concrete.source.1 concrete.source.2).mp concrete.sourceBond
    have generatedRecovered : generated recovered = symmetry := by
      exact molecularFullereneExecutableGeneratedExtension_imageSource
        molecule input concrete symmetry automorphism reversing
    change (molecularFullereneExecutableGeneratedExtension molecule input
      (certificate.toExecutableConcreteFlagExtension molecule input) recovered = symmetry) at generatedRecovered
    apply Finset.mem_image.mpr
    refine ⟨recovered, ?_, generatedRecovered⟩
    apply (mem_molecularFullereneExecutableReversingTargetDarts_iff
      molecule input certificate recovered).mpr
    refine ⟨recoveredBonded, ?_, ?_, ?_⟩
    · rw [generatedRecovered]
      exact automorphism
    · rw [generatedRecovered]
      exact reversing
    · rw [generatedRecovered]
  · intro present
    rcases Finset.mem_image.mp present with ⟨target, targetAccepted, generatedEq⟩
    have accepted := (mem_molecularFullereneExecutableReversingTargetDarts_iff
      molecule input certificate target).mp targetAccepted
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨target, accepted.1, generatedEq⟩, ?_⟩
    have automorphismChecked :
        molecularFullereneCarrierAutomorphismChecked molecule input symmetry = true := by
      rw [← generatedEq]
      exact
      (molecularFullereneCarrierAutomorphismChecked_eq_true_iff
        molecule input (generated target)).mpr accepted.2.1
    have reversingChecked :
        molecularFullereneFaceOrientationReversingChecked input symmetry = true := by
      rw [← generatedEq]
      exact
      (molecularFullereneFaceOrientationReversingChecked_eq_true_iff
        input (generated target)).mpr accepted.2.2.1
    simpa only [Bool.and_eq_true] using And.intro automorphismChecked reversingChecked

theorem molecularFullereneExecutableGeneratedExtension_injOn_targetDarts
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    Set.InjOn
      (molecularFullereneExecutableGeneratedExtension molecule input
        (certificate.toExecutableConcreteFlagExtension molecule input))
      (molecularFullereneExecutableReversingTargetDarts molecule input certificate) := by
  intro first firstAccepted second secondAccepted generatedEq
  have firstRecovered :=
    (mem_molecularFullereneExecutableReversingTargetDarts_iff
      molecule input certificate first).mp firstAccepted |>.2.2.2
  have secondRecovered :=
    (mem_molecularFullereneExecutableReversingTargetDarts_iff
      molecule input certificate second).mp secondAccepted |>.2.2.2
  rw [← firstRecovered, ← secondRecovered, generatedEq]


theorem molecularFullereneExecutableReversingAutomorphisms_card_eq_targetDarts
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    (molecularFullereneExecutableReversingAutomorphisms
        molecule input certificate).card =
      (molecularFullereneExecutableReversingTargetDarts molecule input certificate).card := by
  rw [molecularFullereneExecutableReversingAutomorphisms_eq_image_targetDarts]
  exact Finset.card_image_of_injOn
    (molecularFullereneExecutableGeneratedExtension_injOn_targetDarts
      molecule input certificate)

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneExecutableReversingAutomorphisms_card_eq_targetDarts
