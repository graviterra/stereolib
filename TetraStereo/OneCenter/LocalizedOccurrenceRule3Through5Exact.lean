import TetraStereo.OneCenter.LocalizedOccurrenceRule3Through5Descriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact optional-outcome boundary for the Rules-1a--5 occurrence descriptor

The positive declarative relation in the descriptor module is chemically meaningful but broader
than the current conservative spatial detector.  For a complete executable/refusal theorem we
therefore distinguish an *operational canonical* relation: it retains the exact accepted evidence
object, then rechecks final handedness independently over rational coordinates.  This relation is
exactly executable and every canonical success implies the broader molecule-backed declarative
relation.  It is not yet a theorem that every chemically valid IUPAC Rule-3 case has such current
evidence; implicit positions, cumulenes, and exhaustive coupled-unit topology remain open.
-/

namespace CertifiedLocalizedCIPInput

/-- Exact accepted implementation evidence plus an independently checked final handedness. -/
def CanonicalLocalizedOccurrenceRule3Through5Descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    input.localizedOccurrenceRule3Through5SpatialEvidence? target view = some evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

/-- Positive descriptor computation is exactly the operational canonical relation. -/
theorem localizedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.localizedOccurrenceRule3Through5Descriptor? target view = some descriptor ↔
      input.CanonicalLocalizedOccurrenceRule3Through5Descriptor
        target view descriptor := by
  constructor
  · intro computed
    unfold localizedOccurrenceRule3Through5Descriptor? at computed
    cases evidenceComputed : input.localizedOccurrenceRule3Through5SpatialEvidence?
        target view with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
        | none => simp [evidenceComputed, rawComputed] at computed
        | some raw =>
            simp [evidenceComputed, rawComputed] at computed
            subst descriptor
            exact ⟨evidence, raw, evidenceComputed,
              (descriptorOfPriorityOrderedPoints?_eq_some_iff
                evidence.points raw).mp rawComputed,
              rfl⟩
  · rintro ⟨evidence, raw, evidenceComputed, handedness, rfl⟩
    unfold localizedOccurrenceRule3Through5Descriptor?
    rw [evidenceComputed]
    change (do
      let observed ← descriptorOfPriorityOrderedPoints? evidence.points
      some (classifyTetrahedralRSPseudo observed
        evidence.tracked.pseudoComparisons)) =
      some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)
    rw [(descriptorOfPriorityOrderedPoints?_eq_some_iff
      evidence.points raw).mpr handedness]
    rfl

/-- Refusal is exactly absence of every operational canonical descriptor. -/
theorem localizedOccurrenceRule3Through5Descriptor?_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule3Through5Descriptor? target view = none ↔
      ¬ ∃ descriptor,
        input.CanonicalLocalizedOccurrenceRule3Through5Descriptor
          target view descriptor := by
  constructor
  · intro refused ⟨descriptor, canonical⟩
    have accepted :=
      (input.localizedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
        target view descriptor).mpr canonical
    rw [refused] at accepted
    contradiction
  · intro absent
    cases computed : input.localizedOccurrenceRule3Through5Descriptor? target view with
    | none => rfl
    | some descriptor =>
        exact (absent ⟨descriptor,
          (input.localizedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
            target view descriptor).mp computed⟩).elim

/-- Operational canonical success always has the broader independent molecule-backed meaning. -/
theorem CanonicalLocalizedOccurrenceRule3Through5Descriptor.implies_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (canonical : input.CanonicalLocalizedOccurrenceRule3Through5Descriptor
      target view descriptor) :
    input.DeclarativeLocalizedOccurrenceRule3Through5Descriptor
      target view descriptor := by
  rcases canonical with ⟨evidence, raw, evidenceComputed, handedness, descriptorEq⟩
  exact ⟨evidence, raw,
    input.localizedOccurrenceRule3Through5SpatialEvidence?_sound
      target view evidence evidenceComputed,
    handedness,
    descriptorEq⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
