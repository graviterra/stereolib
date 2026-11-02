import TetraStereo.OneCenter.P93MolecularFullereneReferenceSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Proof-carrying fullerene reversing-automorphism certificates

The direct definition of molecular fullerene chirality quantifies over every permutation of the
cage carrier.  That definition is mathematically exact but cannot be evaluated by factorial
enumeration on the 60--76 atom examples in P-93.5.6.  This module proves the transport theorem
from a complete finite reversing-automorphism certificate to the original independent judgment.

The certificate is not trusted output: `sound` proves that every listed permutation is a genuine
orientation-reversing cage automorphism, and `complete` proves that every such automorphism is
listed.  The directed-edge-indexed theorems below isolate the exact completeness obligation that
a later concrete embedded-map propagation algorithm must discharge.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-- A finite, sound, and complete corpus of the orientation-reversing automorphisms of one
checked molecular fullerene face map. -/
structure MolecularFullereneReversingAutomorphismCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) where
  members : Finset (Equiv.Perm (MolecularFullereneCarrierAtom input))
  sound : ∀ symmetry ∈ members,
    MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
      MolecularFullereneFaceOrientationReversing input symmetry
  complete : ∀ symmetry,
    MolecularFullereneCarrierAutomorphism molecule input symmetry →
      MolecularFullereneFaceOrientationReversing input symmetry →
        symmetry ∈ members

/-- A proof-carrying directed-edge-indexed extension family.  Completeness says that every
reversing automorphism occurs at the image of the source edge.  This structure alone bounds the
size of the candidate image; it does not assert how `extend` is implemented or bound its runtime.

For a connected coherently oriented cubic fullerene map, the intended `extend` propagates the
image through the rotation system: the image of one directed edge fixes the adjacent face, and
successive opposite-face steps fix the whole connected cage. -/
structure MolecularFullereneDirectedEdgeExtensionCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) where
  source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input
  sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1
  extend :
    (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) →
      Equiv.Perm (MolecularFullereneCarrierAtom input)
  complete : ∀ symmetry,
    MolecularFullereneCarrierAutomorphism molecule input symmetry →
      MolecularFullereneFaceOrientationReversing input symmetry →
        extend (symmetry source.1, symmetry source.2) = symmetry

/-- At most one extension candidate is generated for each ordered pair of cage atoms. -/
noncomputable def molecularFullereneDirectedEdgeExtensionCandidates
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneDirectedEdgeExtensionCertificate molecule input) :
    Finset (Equiv.Perm (MolecularFullereneCarrierAtom input)) :=
  Finset.univ.image certificate.extend

/-- Keep exactly the genuine orientation-reversing cage automorphisms from the quadratic-size
directed-edge-indexed candidate universe. -/
noncomputable def molecularFullereneDirectedEdgeReversingAutomorphisms
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneDirectedEdgeExtensionCertificate molecule input) :
    Finset (Equiv.Perm (MolecularFullereneCarrierAtom input)) :=
  (molecularFullereneDirectedEdgeExtensionCandidates molecule input certificate).filter
    fun symmetry => decide
      (MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
        MolecularFullereneFaceOrientationReversing input symmetry)

/-- A directed-edge extension certificate automatically produces the exact reversing-symmetry
certificate consumed by the independent chirality theorem. -/
noncomputable def MolecularFullereneDirectedEdgeExtensionCertificate.toReversingCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneDirectedEdgeExtensionCertificate molecule input) :
    MolecularFullereneReversingAutomorphismCertificate molecule input where
  members := molecularFullereneDirectedEdgeReversingAutomorphisms molecule input certificate
  sound := by
    intro symmetry member
    exact of_decide_eq_true (Finset.mem_filter.mp member).2
  complete := by
    intro symmetry automorphism reversing
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using And.intro automorphism reversing⟩
    apply Finset.mem_image.mpr
    refine ⟨(symmetry certificate.source.1, symmetry certificate.source.2),
      Finset.mem_univ _, ?_⟩
    exact certificate.complete symmetry automorphism reversing

/-- The reversing-automorphism corpus indexed by directed-edge images has cardinality at most
`|V|²`.  This is a cardinality theorem, not a runtime theorem about the opaque `extend` field. -/
theorem molecularFullereneDirectedEdgeReversingAutomorphisms_card_le
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneDirectedEdgeExtensionCertificate molecule input) :
    (molecularFullereneDirectedEdgeReversingAutomorphisms
        molecule input certificate).card ≤
      input.carrier.card * input.carrier.card := by
  calc
    (molecularFullereneDirectedEdgeReversingAutomorphisms
        molecule input certificate).card ≤
        (molecularFullereneDirectedEdgeExtensionCandidates
          molecule input certificate).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (Finset.univ : Finset
        (MolecularFullereneCarrierAtom input ×
          MolecularFullereneCarrierAtom input)).card := Finset.card_image_le
    _ = input.carrier.card * input.carrier.card := by simp

/-! ## Proper rotations from the same directed-edge indexing principle -/

/-- Directed-edge-indexed completeness for the orientation-preserving class.  The polarity is
fixed here because an orientation-preserving and an orientation-reversing map can agree on the
endpoints of one edge. -/
structure MolecularFullereneProperRotationDirectedEdgeExtensionCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) where
  source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input
  sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1
  extend :
    (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) →
      Equiv.Perm (MolecularFullereneCarrierAtom input)
  complete : ∀ symmetry,
    MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry →
      extend (symmetry source.1, symmetry source.2) = symmetry

/-- Quadratic candidate universe for proper reference rotations. -/
noncomputable def molecularFullereneDirectedEdgeProperRotationCandidates
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneProperRotationDirectedEdgeExtensionCertificate molecule input) :
    Finset (Equiv.Perm (MolecularFullereneCarrierAtom input)) :=
  Finset.univ.image certificate.extend

/-- Genuine proper rotations selected from the directed-edge extension universe. -/
noncomputable def molecularFullereneDirectedEdgeProperRotationSymmetries
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneProperRotationDirectedEdgeExtensionCertificate molecule input) :
    Finset (Equiv.Perm (MolecularFullereneCarrierAtom input)) :=
  (molecularFullereneDirectedEdgeProperRotationCandidates molecule input certificate).filter
    fun symmetry => decide
      (MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry)

/-- Exact membership of the directed-edge-indexed reference-rotation universe. -/
@[simp] theorem mem_molecularFullereneDirectedEdgeProperRotationSymmetries_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneProperRotationDirectedEdgeExtensionCertificate molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    symmetry ∈ molecularFullereneDirectedEdgeProperRotationSymmetries
        molecule input certificate ↔
      MolecularFullereneProperRotationSymmetryJudgment molecule input symmetry := by
  constructor
  · intro member
    exact of_decide_eq_true (Finset.mem_filter.mp member).2
  · intro judged
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using judged⟩
    apply Finset.mem_image.mpr
    refine ⟨(symmetry certificate.source.1, symmetry certificate.source.2),
      Finset.mem_univ _, ?_⟩
    exact certificate.complete symmetry judged

/-- The quadratic proper-rotation universe is extensionally identical to the original independent
definition that ranged over every carrier permutation. -/
theorem molecularFullereneDirectedEdgeProperRotationSymmetries_eq_reference
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneProperRotationDirectedEdgeExtensionCertificate molecule input) :
    molecularFullereneDirectedEdgeProperRotationSymmetries molecule input certificate =
      molecularFullereneProperRotationSymmetries molecule input := by
  ext symmetry
  rw [mem_molecularFullereneDirectedEdgeProperRotationSymmetries_iff,
    mem_molecularFullereneProperRotationSymmetries_iff]

/-- The complete proper-rotation corpus has at most `|V|²` members when generated by a
directed-edge extension. -/
theorem molecularFullereneDirectedEdgeProperRotationSymmetries_card_le
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate :
      MolecularFullereneProperRotationDirectedEdgeExtensionCertificate molecule input) :
    (molecularFullereneDirectedEdgeProperRotationSymmetries
        molecule input certificate).card ≤
      input.carrier.card * input.carrier.card := by
  calc
    (molecularFullereneDirectedEdgeProperRotationSymmetries
        molecule input certificate).card ≤
        (molecularFullereneDirectedEdgeProperRotationCandidates
          molecule input certificate).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (Finset.univ : Finset
        (MolecularFullereneCarrierAtom input ×
          MolecularFullereneCarrierAtom input)).card := Finset.card_image_le
    _ = input.carrier.card * input.carrier.card := by simp

/-- Under a complete certificate, the original independent chirality judgment is exactly the
finite statement that no listed reversing automorphism preserves the coloring. -/
theorem molecularFullereneColoringChiral_iff_certificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : Nat → Nat)
    (certificate :
      MolecularFullereneReversingAutomorphismCertificate molecule input) :
    MolecularFullereneColoringChiral molecule input color ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ certificate.members,
          ¬MolecularFullereneColoringPreserved input color symmetry := by
  unfold MolecularFullereneColoringChiral
  constructor
  · rintro ⟨oriented, noReversing⟩
    refine ⟨oriented, ?_⟩
    intro symmetry member coloringPreserved
    rcases certificate.sound symmetry member with ⟨automorphism, reversing⟩
    exact noReversing ⟨symmetry, automorphism, reversing, coloringPreserved⟩
  · rintro ⟨oriented, listedDoNotPreserve⟩
    refine ⟨oriented, ?_⟩
    rintro ⟨symmetry, automorphism, reversing, coloringPreserved⟩
    exact listedDoNotPreserve symmetry
      (certificate.complete symmetry automorphism reversing) coloringPreserved

/-- Boolean identity at the finite-certificate boundary.  Both sides remain noncomputable until
the certificate and its finite predicates receive concrete computable realizations. -/
theorem molecularFullereneColoringChiral_eq_certificateDecision
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : Nat → Nat)
    (certificate :
      MolecularFullereneReversingAutomorphismCertificate molecule input) :
    molecularFullereneColoringChiral molecule input color =
      decide (OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ certificate.members,
          ¬MolecularFullereneColoringPreserved input color symmetry) := by
  apply Bool.eq_iff_iff.mpr
  rw [molecularFullereneColoringChiral_eq_true_iff]
  simpa only [decide_eq_true_eq] using
    molecularFullereneColoringChiral_iff_certificate molecule input color certificate

/-- End-to-end transport from directed-edge-indexed completeness to the independent chirality
judgment.  The quantified candidate corpus has cardinality at most `|V|²`. -/
theorem molecularFullereneColoringChiral_iff_directedEdgeExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : Nat → Nat)
    (certificate :
      MolecularFullereneDirectedEdgeExtensionCertificate molecule input) :
    MolecularFullereneColoringChiral molecule input color ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneDirectedEdgeReversingAutomorphisms
            molecule input certificate,
          ¬MolecularFullereneColoringPreserved input color symmetry :=
  molecularFullereneColoringChiral_iff_certificate molecule input color
    (certificate.toReversingCertificate molecule input)

/-- Boolean equality for the directed-edge-indexed certificate boundary.  It is an extensional
replacement for the old all-permutation proposition, not yet a claim of executable performance. -/
theorem molecularFullereneColoringChiral_eq_directedEdgeExtensionDecision
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : Nat → Nat)
    (certificate :
      MolecularFullereneDirectedEdgeExtensionCertificate molecule input) :
    molecularFullereneColoringChiral molecule input color =
      decide (OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneDirectedEdgeReversingAutomorphisms
            molecule input certificate,
          ¬MolecularFullereneColoringPreserved input color symmetry) :=
  molecularFullereneColoringChiral_eq_certificateDecision molecule input color
    (certificate.toReversingCertificate molecule input)

/-- An empty certificate is complete exactly when the checked cage has no reversing
automorphism.  This is the useful specialization for an inherently chiral parent cage. -/
def MolecularFullereneReversingAutomorphismCertificate.ofNoReversing
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (none : ∀ symmetry,
      MolecularFullereneCarrierAutomorphism molecule input symmetry →
        ¬MolecularFullereneFaceOrientationReversing input symmetry) :
    MolecularFullereneReversingAutomorphismCertificate molecule input where
  members := ∅
  sound := by simp
  complete := by
    intro symmetry automorphism reversing
    exact False.elim (none symmetry automorphism reversing)

@[simp] theorem molecularFullereneColoringChiral_iff_noReversing
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : Nat → Nat)
    (none : ∀ symmetry,
      MolecularFullereneCarrierAutomorphism molecule input symmetry →
        ¬MolecularFullereneFaceOrientationReversing input symmetry) :
    MolecularFullereneColoringChiral molecule input color ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input := by
  rw [molecularFullereneColoringChiral_iff_certificate molecule input color
    (.ofNoReversing molecule input none)]
  simp [MolecularFullereneReversingAutomorphismCertificate.ofNoReversing]

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneColoringChiral_iff_certificate
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneColoringChiral_eq_certificateDecision
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneColoringChiral_iff_directedEdgeExtension
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneColoringChiral_eq_directedEdgeExtensionDecision
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_molecularFullereneDirectedEdgeProperRotationSymmetries_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneDirectedEdgeProperRotationSymmetries_eq_reference
