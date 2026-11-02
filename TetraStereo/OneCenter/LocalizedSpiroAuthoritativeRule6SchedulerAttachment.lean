import TetraStereo.OneCenter.LocalizedSpiroAuthoritativePromotedKeyMatrix
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Totality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open Rule6ReferenceFamilySemantics

/-!
# Spiro promoted-key matrix attachment to the P-92 scheduler

The spiro matrix is reference-dependent: its rows are the four possible P-92 reference
positions and its columns are the four ranked branches.  This module proves that exact matrix
readiness removes every operational failure from those four production ranking calls.  It then
specializes the generic P-92 reference-family failure theorem, so `none` has only the two
remaining semantic causes: a completed non-strict ranking or disagreement between strict
reference descriptors.
-/

/-- Every genuine four-position reference executes in the actual production Rules-3--6 backend
when the complete spiro key matrix is ready. -/
theorem AuthoritativeSpiroRule3Through6KeyMatrixReady.rankingBackend_total_of_lt_four
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady
      carrierFuel evaluationFuel center view)
    (referencePosition : Nat) (referenceLt : referencePosition < 4) :
    ∃ ranking,
      input.certified.input.aromaticCanonicalRule3Through6RankingBackend
          (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
          view evaluationFuel
          (input.authoritativeTetrahedralRootBranchCursors carrierFuel center)
          referencePosition = some ranking := by
  let reference : Fin 4 := ⟨referencePosition, referenceLt⟩
  have succeeds := ready.rankingBackend_isSome input carrierFuel evaluationFuel center view reference
  rw [Option.isSome_iff_exists] at succeeds
  simpa [reference] using succeeds

/-- The same totality result for the scheduler's pre-resolved-frame backend.  The frame premise is
the independent canonical frame relation, not an equation assumed about the executable builder. -/
theorem AuthoritativeSpiroRule3Through6KeyMatrixReady.rankingBackendForFrame_total_of_lt_four
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady
      carrierFuel evaluationFuel center view)
    (frame : input.certified.input.AromaticCanonicalRule3CanonicalKeyFrame)
    (frameCanonical : input.certified.input.CanonicalAromaticCanonicalRule3CanonicalKeyFrame
      evaluationFuel
      (input.authoritativeTetrahedralRootBranchCursors carrierFuel center) frame)
    (referencePosition : Nat) (referenceLt : referencePosition < 4) :
    ∃ ranking,
      input.certified.input.aromaticCanonicalRule3Through6RankingBackendForFrame
          frame
          (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
          view evaluationFuel
          (input.authoritativeTetrahedralRootBranchCursors carrierFuel center)
          referencePosition = some ranking := by
  let source := input.certified.input
  let roots := input.authoritativeTetrahedralRootBranchCursors carrierFuel center
  have rootsLength : roots.length = 4 :=
    input.authoritativeTetrahedralRootBranchCursors_length carrierFuel center
  have frameLength : frame.keys.length = 4 := by
    rw [frameCanonical.keys_length_eq, rootsLength]
  have frameComputed :
      source.buildAromaticCanonicalRule3CanonicalKeyFrame? evaluationFuel roots = some frame :=
    (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
      evaluationFuel roots frame).mpr frameCanonical
  have backendEq := source.aromaticCanonicalRule3Through6RankingBackend_eq_forFrame
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view evaluationFuel roots frame
    rootsLength frameLength frameComputed
  rw [← backendEq]
  exact ready.rankingBackend_total_of_lt_four input carrierFuel evaluationFuel center view
    referencePosition referenceLt

/-- Under matrix readiness, an arbitrary nonempty family of genuine four-position references
fails exactly for one non-strict ranking or for a descriptor conflict between strict rankings. -/
theorem AuthoritativeSpiroRule3Through6KeyMatrixReady.familyDescriptor_eq_none_iff_failureWitness
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady
      carrierFuel evaluationFuel center view)
    (parity : TetrahedralInputParity) (references : List Nat)
    (referencesNonempty : references ≠ [])
    (referencesLt : ∀ reference, reference ∈ references → reference < 4) :
    input.certified.input.aromaticCanonicalRule3Through6FamilyDescriptor?
        (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
        view evaluationFuel
        (input.authoritativeTetrahedralRootBranchCursors carrierFuel center)
        parity references = none ↔
      HasNonStrictRule6Reference
          (input.certified.input.aromaticCanonicalRule3Through6RankingBackend
            (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
            view evaluationFuel
            (input.authoritativeTetrahedralRootBranchCursors carrierFuel center)) references ∨
        HasRule6ReferenceDescriptorConflict
          (input.certified.input.aromaticCanonicalRule3Through6RankingBackend
            (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
            view evaluationFuel
            (input.authoritativeTetrahedralRootBranchCursors carrierFuel center))
          parity references := by
  apply rule6FamilyDescriptorWithBackend?_eq_none_iff_failureWitness
  · exact referencesNonempty
  · intro reference member
    exact ready.rankingBackend_total_of_lt_four input carrierFuel evaluationFuel center view
      reference (referencesLt reference member)

/-- Frame-specialized form used literally by the applicability-gated source scheduler. -/
theorem AuthoritativeSpiroRule3Through6KeyMatrixReady.familyDescriptorForFrame_eq_none_iff_failureWitness
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady
      carrierFuel evaluationFuel center view)
    (frame : input.certified.input.AromaticCanonicalRule3CanonicalKeyFrame)
    (frameCanonical : input.certified.input.CanonicalAromaticCanonicalRule3CanonicalKeyFrame
      evaluationFuel
      (input.authoritativeTetrahedralRootBranchCursors carrierFuel center) frame)
    (parity : TetrahedralInputParity) (references : List Nat)
    (referencesNonempty : references ≠ [])
    (referencesLt : ∀ reference, reference ∈ references → reference < 4) :
    rule6FamilyDescriptorWithBackend?
        (input.certified.input.aromaticCanonicalRule3Through6RankingBackendForFrame
          frame
          (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
          view evaluationFuel
          (input.authoritativeTetrahedralRootBranchCursors carrierFuel center))
        parity references = none ↔
      HasNonStrictRule6Reference
          (input.certified.input.aromaticCanonicalRule3Through6RankingBackendForFrame
            frame
            (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
            view evaluationFuel
            (input.authoritativeTetrahedralRootBranchCursors carrierFuel center)) references ∨
        HasRule6ReferenceDescriptorConflict
          (input.certified.input.aromaticCanonicalRule3Through6RankingBackendForFrame
            frame
            (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
            view evaluationFuel
            (input.authoritativeTetrahedralRootBranchCursors carrierFuel center))
          parity references := by
  apply rule6FamilyDescriptorWithBackend?_eq_none_iff_failureWitness
  · exact referencesNonempty
  · intro reference member
    exact ready.rankingBackendForFrame_total_of_lt_four input carrierFuel evaluationFuel center view
      frame frameCanonical reference (referencesLt reference member)

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
