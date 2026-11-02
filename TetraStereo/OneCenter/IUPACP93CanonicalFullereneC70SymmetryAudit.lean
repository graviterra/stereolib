import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70CagePackage
import TetraStereo.OneCenter.P93MolecularFullereneExecutableFlagSymmetryCardinality

set_option autoImplicit false
set_option maxRecDepth 100000








namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

abbrev iupacP93CanonicalFullereneC70TopologyInput :
    MolecularFullereneConfigurationInput :=
  iupacP93CanonicalFullereneC70Transcription.numberedPackage.topologyInput

def iupacP93CanonicalFullereneC70SourceDart :
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70TopologyInput ×
      MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70TopologyInput :=
  (⟨0, by decide⟩, ⟨1, by decide⟩)

theorem iupacP93CanonicalFullereneC70SourceDart_bonded :
    0 < iupacP93CanonicalFullereneC70Transcription.cageMolecule.bondOrder
      iupacP93CanonicalFullereneC70SourceDart.1.1
      iupacP93CanonicalFullereneC70SourceDart.2.1 := by
  decide

def iupacP93CanonicalFullereneC70FlagSpanning :
    MolecularFullereneDeduplicatedFlagSpanningCertificate
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70TopologyInput :=
  MolecularFullereneDeduplicatedFlagSpanningCertificate.ofOrientedFaceMap
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70TopologyInput
    iupacP93CanonicalFullereneC70SharedNumberedCage.certificate.oriented
    iupacP93CanonicalFullereneC70SourceDart
    iupacP93CanonicalFullereneC70SourceDart_bonded

abbrev iupacP93CanonicalFullereneC70ReversingAutomorphisms :=
  molecularFullereneExecutableReversingAutomorphisms
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70TopologyInput
    iupacP93CanonicalFullereneC70FlagSpanning

/-- Materialized, lexicographically ordered locant images of the accepted reversing darts. -/
def iupacP93CanonicalFullereneC70ReversingTargetLocants : List (Nat × Nat) :=
  [(2, 1), (5, 4), (10, 11), (18, 19), (30, 29),
    (40, 39), (48, 49), (57, 58), (60, 69), (65, 64)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem iupacP93CanonicalFullereneC70_reversingTargetLocantsExact :
    (molecularFullereneSortedDirectedEdges
      iupacP93CanonicalFullereneC70TopologyInput
      (molecularFullereneExecutableReversingTargetDarts
        iupacP93CanonicalFullereneC70Transcription.cageMolecule
        iupacP93CanonicalFullereneC70TopologyInput
        iupacP93CanonicalFullereneC70FlagSpanning)).map
          (fun edge => (edge.1.1, edge.2.1)) =
      iupacP93CanonicalFullereneC70ReversingTargetLocants := by
  decide

theorem iupacP93CanonicalFullereneC70_reversingTargetDartCount :
    (molecularFullereneExecutableReversingTargetDarts
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70TopologyInput
      iupacP93CanonicalFullereneC70FlagSpanning).card = 10 := by
  let targets := molecularFullereneExecutableReversingTargetDarts
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70TopologyInput
    iupacP93CanonicalFullereneC70FlagSpanning
  let sorted := molecularFullereneSortedDirectedEdges
    iupacP93CanonicalFullereneC70TopologyInput targets
  have sortedLength : sorted.length = targets.card := by
    simp only [sorted, molecularFullereneSortedDirectedEdges, List.length_map,
      Finset.length_sort]
    apply Finset.card_image_of_injective
    intro first second equal
    exact congrArg ofLex equal
  rw [← sortedLength]
  rw [← List.length_map (f := fun edge => (edge.1.1, edge.2.1))]
  change (sorted.map fun edge => (edge.1.1, edge.2.1)).length = 10
  rw [show sorted.map (fun edge => (edge.1.1, edge.2.1)) =
      iupacP93CanonicalFullereneC70ReversingTargetLocants by
    exact iupacP93CanonicalFullereneC70_reversingTargetLocantsExact]
  rfl

theorem iupacP93CanonicalFullereneC70_reversingAutomorphismCount :
    iupacP93CanonicalFullereneC70ReversingAutomorphisms.card = 10 := by
  rw [molecularFullereneExecutableReversingAutomorphisms_card_eq_targetDarts]
  exact iupacP93CanonicalFullereneC70_reversingTargetDartCount

theorem iupacP93CanonicalFullereneC70_existsReversingAutomorphism :
    ∃ symmetry : Equiv.Perm
        (MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70TopologyInput),
      MolecularFullereneCarrierAutomorphism
          iupacP93CanonicalFullereneC70Transcription.cageMolecule
          iupacP93CanonicalFullereneC70TopologyInput symmetry ∧
        MolecularFullereneFaceOrientationReversing
          iupacP93CanonicalFullereneC70TopologyInput symmetry := by
  have nonempty : iupacP93CanonicalFullereneC70ReversingAutomorphisms.Nonempty := by
    rw [← Finset.card_pos]
    rw [iupacP93CanonicalFullereneC70_reversingAutomorphismCount]
    decide
  rcases nonempty with ⟨symmetry, present⟩
  exact ⟨symmetry,
    iupacP93CanonicalFullereneC70FlagSpanning.toExecutableReversingCertificate
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70TopologyInput |>.sound symmetry present⟩

theorem iupacP93CanonicalFullereneC70_parent_achiral :
    ¬MolecularFullereneColoringChiral
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70TopologyInput
      molecularFullereneParentColor := by
  rintro ⟨_oriented, noReversing⟩
  rcases iupacP93CanonicalFullereneC70_existsReversingAutomorphism with
    ⟨symmetry, automorphism, reversing⟩
  apply noReversing
  exact ⟨symmetry, automorphism, reversing, by
    intro atom
    rfl⟩

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70_reversingAutomorphismCount
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70_parent_achiral
