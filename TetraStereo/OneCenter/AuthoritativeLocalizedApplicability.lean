import TetraStereo.OneCenter.AuthoritativeLocalizedStereochemicalPipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent applicability boundary for the localized authority pipeline

`AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry?` previously exposed only an
`Option`: callers could observe success or failure, but there was no theorem saying exactly which
semantic-source property controlled that choice.  This module supplies that missing boundary.

The predicate below mentions only the format-neutral input and the independently stated structural
and graph-normalization relations.  It does not mention analyzer success or a descriptor result.
Consequently the totality theorem is a genuine refinement theorem rather than a definition of
applicability by whatever the implementation happens to return.

This is the applicability domain of the *currently supported localized pair-bond pipeline*.  It is
not a claim that every structurally representable entity is physically realizable, and it does not
classify aromatic, delocalized, radical, coordinate, or multicentre input as chemically invalid.
Those representations require their own source-backed normalization branch before they can enter
the localized CIP graph.
-/

/-- Independent semantic-source applicability for the current localized authority pipeline. -/
def AuthoritativeChemicalInput.LocalizedCIPApplicable
    (source : AuthoritativeChemicalInput) : Prop :=
  source.StructurallyWellFormed ∧ source.molecule.LocalizedCIPGraphReady

/-- Executable reflection of current localized applicability. -/
def AuthoritativeChemicalInput.localizedCIPApplicable?
    (source : AuthoritativeChemicalInput) : Bool :=
  source.structurallyWellFormed? && source.molecule.localizedCIPGraphReady?

@[simp] theorem AuthoritativeChemicalInput.localizedCIPApplicable?_eq_true_iff
    (source : AuthoritativeChemicalInput) :
    source.localizedCIPApplicable? = true ↔ source.LocalizedCIPApplicable := by
  simp [AuthoritativeChemicalInput.localizedCIPApplicable?,
    AuthoritativeChemicalInput.LocalizedCIPApplicable]

/-- Proof-carrying current-scope applicability, constructed without running the analyzer. -/
structure CertifiedLocalizedCIPApplicableInput where
  source : AuthoritativeChemicalInput
  applicable : source.LocalizedCIPApplicable

namespace CertifiedLocalizedCIPApplicableInput

/-- Structural certification follows directly from the independent applicability evidence. -/
def toCertifiedAuthoritativeChemicalInput
    (admitted : CertifiedLocalizedCIPApplicableInput) :
    CertifiedAuthoritativeChemicalInput :=
  { input := admitted.source
    structurallyWellFormed := admitted.applicable.1 }

/-- The same evidence directly constructs the exact localized constitutional CIP input. -/
def toCertifiedLocalizedCIPInput
    (admitted : CertifiedLocalizedCIPApplicableInput) : CertifiedLocalizedCIPInput :=
  { certified := admitted.toCertifiedAuthoritativeChemicalInput
    graphReady := admitted.applicable.2 }

/-- Run the complete currently scheduled localized pipeline without another optional admission
step: the applicability carrier already contains both required proofs. -/
noncomputable def analyze (admitted : CertifiedLocalizedCIPApplicableInput) :
    SupportedAuthoritativeLocalizedStereochemicalAnalysis :=
  let localized := admitted.toCertifiedLocalizedCIPInput
  { input := localized
    entries := localized.analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries
      (defaultLocalizedStereochemicalFuel localized)
    entries_eq := rfl }

@[simp] theorem analyze_source (admitted : CertifiedLocalizedCIPApplicableInput) :
    admitted.analyze.input.certified.input = admitted.source := by
  rfl

/-- Every descriptor emitted by the direct total analysis has its independent scheduled-family
meaning for the exact admitted source. -/
theorem analyze_descriptorAssignment_member_conforms
    (admitted : CertifiedLocalizedCIPApplicableInput)
    (assignment : admitted.analyze.input.LocalizedScheduledStereochemicalAssignment
      (defaultLocalizedStereochemicalFuel admitted.analyze.input))
    (present :
      CertifiedLocalizedCIPInput.LocalizedScheduledStereochemicalAnalysisEntry.descriptorAssignment
          assignment ∈ admitted.analyze.entries) :
    admitted.analyze.input.DeclarativeLocalizedScheduledStereochemicalAssignment
      (defaultLocalizedStereochemicalFuel admitted.analyze.input) assignment := by
  exact admitted.analyze.descriptorAssignment_member_conforms assignment present

end CertifiedLocalizedCIPApplicableInput

/-- Structural certification succeeds exactly on the independently stated structural relation. -/
@[simp] theorem AuthoritativeChemicalInput.certify?_isSome
    (source : AuthoritativeChemicalInput) :
    source.certify?.isSome = true ↔ source.StructurallyWellFormed := by
  by_cases checked : source.structurallyWellFormed? = true
  · have structural := source.structurallyWellFormed?_eq_true_iff.mp checked
    simp [AuthoritativeChemicalInput.certify?, checked, structural]
  · have notStructural : ¬ source.StructurallyWellFormed := by
      intro structural
      exact checked (source.structurallyWellFormed?_eq_true_iff.mpr structural)
    simp [AuthoritativeChemicalInput.certify?, checked, notStructural]

/-- Exact admission theorem for the public optional analyzer.  In particular, implementation
success is neither assumed nor reused in the definition of applicability. -/
@[simp] theorem AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry?_isSome
    (source : AuthoritativeChemicalInput) :
    source.analyzeSupportedLocalizedStereochemistry?.isSome = true ↔
      source.LocalizedCIPApplicable := by
  unfold AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry?
  cases certifiedObserved : source.certify? with
  | none =>
      have notStructural : ¬ source.StructurallyWellFormed := by
        intro structural
        have present := (source.certify?_isSome).mpr structural
        simp [certifiedObserved] at present
      simp [AuthoritativeChemicalInput.LocalizedCIPApplicable, notStructural]
  | some certified =>
      have structural : source.StructurallyWellFormed := by
        apply (source.certify?_isSome).mp
        simp [certifiedObserved]
      have sourceEq : certified.input = source := by
        unfold AuthoritativeChemicalInput.certify? at certifiedObserved
        split at certifiedObserved
        · cases certifiedObserved
          rfl
        · simp at certifiedObserved
      subst source
      constructor
      · intro present
        have localizedSome : certified.certifyLocalizedCIP?.isSome = true := by
          cases localizedObserved : certified.certifyLocalizedCIP? <;>
            simp [localizedObserved] at present ⊢
        exact ⟨structural,
          (CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?_isSome certified).mp
            localizedSome⟩
      · rintro ⟨_, ready⟩
        have localizedSome : certified.certifyLocalizedCIP?.isSome = true :=
          (CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?_isSome certified).mpr ready
        obtain ⟨localized, localizedObserved⟩ := Option.isSome_iff_exists.mp localizedSome
        simp [localizedObserved]

/-- Public failure is exactly negation of the independent current-scope applicability relation. -/
@[simp] theorem AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry?_eq_none_iff
    (source : AuthoritativeChemicalInput) :
    source.analyzeSupportedLocalizedStereochemistry? = none ↔
      ¬ source.LocalizedCIPApplicable := by
  constructor
  · intro absent applicable
    have present : source.analyzeSupportedLocalizedStereochemistry?.isSome = true :=
      (source.analyzeSupportedLocalizedStereochemistry?_isSome).mpr applicable
    simp [absent] at present
  · intro notApplicable
    cases observed : source.analyzeSupportedLocalizedStereochemistry? with
    | none => rfl
    | some analysis =>
        exfalso
        apply notApplicable
        apply (source.analyzeSupportedLocalizedStereochemistry?_isSome).mp
        simp [observed]

/-- Independent failure partition: malformed evidence and a well-formed representation that still
needs normative graph normalization are kept distinct. -/
theorem AuthoritativeChemicalInput.not_localizedCIPApplicable_iff
    (source : AuthoritativeChemicalInput) :
    ¬ source.LocalizedCIPApplicable ↔
      ¬ source.StructurallyWellFormed ∨
        ¬ source.molecule.LocalizedCIPGraphReady := by
  unfold AuthoritativeChemicalInput.LocalizedCIPApplicable
  classical
  tauto

/-- The optional public boundary therefore has a complete, non-silent failure classification. -/
theorem AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry?_eq_none_iff_failure
    (source : AuthoritativeChemicalInput) :
    source.analyzeSupportedLocalizedStereochemistry? = none ↔
      ¬ source.StructurallyWellFormed ∨
        ¬ source.molecule.LocalizedCIPGraphReady := by
  rw [source.analyzeSupportedLocalizedStereochemistry?_eq_none_iff,
    source.not_localizedCIPApplicable_iff]

/-- Every independently applicable finite source has a public packaged analysis. -/
theorem AuthoritativeChemicalInput.exists_supportedLocalized_analysis_of_applicable
    (source : AuthoritativeChemicalInput) (applicable : source.LocalizedCIPApplicable) :
    ∃ analysis, source.analyzeSupportedLocalizedStereochemistry? = some analysis := by
  have present : source.analyzeSupportedLocalizedStereochemistry?.isSome = true :=
    (source.analyzeSupportedLocalizedStereochemistry?_isSome).mpr applicable
  exact Option.isSome_iff_exists.mp present

/-- Current-scope end-to-end totality and soundness: on every independently applicable finite
source, public analysis succeeds, retains that exact source, and every emitted descriptor has its
independent scheduled P-92/P-93 meaning. -/
theorem AuthoritativeChemicalInput.exists_supportedLocalized_analysis_all_descriptors_conform
    (source : AuthoritativeChemicalInput) (applicable : source.LocalizedCIPApplicable) :
    ∃ analysis,
      source.analyzeSupportedLocalizedStereochemistry? = some analysis ∧
      analysis.input.certified.input = source ∧
      ∀ assignment,
        CertifiedLocalizedCIPInput.LocalizedScheduledStereochemicalAnalysisEntry.descriptorAssignment
            assignment ∈ analysis.entries →
          analysis.input.DeclarativeLocalizedScheduledStereochemicalAssignment
            (defaultLocalizedStereochemicalFuel analysis.input) assignment := by
  obtain ⟨analysis, computed⟩ :=
    source.exists_supportedLocalized_analysis_of_applicable applicable
  refine ⟨analysis, computed,
    source.analyzeSupportedLocalizedStereochemistry?_source analysis computed, ?_⟩
  intro assignment present
  exact analysis.descriptorAssignment_member_conforms assignment present

end TetraStereo.OneCenter
