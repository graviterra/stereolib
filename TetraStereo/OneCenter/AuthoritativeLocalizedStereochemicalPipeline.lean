import TetraStereo.OneCenter.LocalizedOrdinaryMonocyclicDoubleBondAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Format-neutral authoritative localized stereochemical pipeline

This module packages the currently integrated localized descriptor families behind one admission
boundary over `AuthoritativeChemicalInput`.  The output retains the exact certified localized input
on which every family-specific P-92/P-93 proof depends.  It is deliberately named `Supported`:
admission currently covers the structurally localized closed-shell pair-bond domain, and the
scheduled family sum is not yet the complete IUPAC stereochemical vocabulary.
-/

/-- The finite default depth used by the scheduled localized analyzer. -/
def defaultLocalizedStereochemicalFuel (input : CertifiedLocalizedCIPInput) : Nat :=
  input.certified.input.molecule.atomCount + 1

/-- Proof-carrying output of the currently supported format-neutral localized pipeline. -/
structure SupportedAuthoritativeLocalizedStereochemicalAnalysis where
  input : CertifiedLocalizedCIPInput
  entries : List
    (input.LocalizedScheduledStereochemicalAnalysisEntry
      (defaultLocalizedStereochemicalFuel input))
  entries_eq : entries =
    input.analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries
      (defaultLocalizedStereochemicalFuel input)

namespace SupportedAuthoritativeLocalizedStereochemicalAnalysis

/-- Every public entry retained by a packaged analysis has its independent family meaning. -/
theorem member_conforms
    (analysis : SupportedAuthoritativeLocalizedStereochemicalAnalysis)
    (entry : analysis.input.LocalizedScheduledStereochemicalAnalysisEntry
      (defaultLocalizedStereochemicalFuel analysis.input))
    (present : entry ∈ analysis.entries) :
    analysis.input.DeclarativeLocalizedScheduledStereochemicalAnalysisEntry
      (defaultLocalizedStereochemicalFuel analysis.input) entry := by
  apply analysis.input.analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries_member_conforms
  simpa [analysis.entries_eq] using present

/-- In particular, every emitted descriptor assignment has the independent P-92/P-93 meaning of
its disjoint scheduled family. -/
theorem descriptorAssignment_member_conforms
    (analysis : SupportedAuthoritativeLocalizedStereochemicalAnalysis)
    (assignment : analysis.input.LocalizedScheduledStereochemicalAssignment
      (defaultLocalizedStereochemicalFuel analysis.input))
    (present :
      CertifiedLocalizedCIPInput.LocalizedScheduledStereochemicalAnalysisEntry.descriptorAssignment
          assignment ∈ analysis.entries) :
    analysis.input.DeclarativeLocalizedScheduledStereochemicalAssignment
      (defaultLocalizedStereochemicalFuel analysis.input) assignment := by
  have derived := analysis.member_conforms
    (CertifiedLocalizedCIPInput.LocalizedScheduledStereochemicalAnalysisEntry.descriptorAssignment
      assignment) present
  cases derived with
  | descriptorAssignment assignmentDerived => exact assignmentDerived

end SupportedAuthoritativeLocalizedStereochemicalAnalysis

/-- Admit a format-neutral source and run every currently integrated localized descriptor family.
Unsupported structural representations fail closed before any descriptor is returned. -/
noncomputable def AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry?
    (source : AuthoritativeChemicalInput) :
    Option SupportedAuthoritativeLocalizedStereochemicalAnalysis := do
  let certified ← source.certify?
  let localized ← certified.certifyLocalizedCIP?
  some
    { input := localized
      entries := localized.analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries
        (defaultLocalizedStereochemicalFuel localized)
      entries_eq := rfl }

/-- A successful packaged analysis retains exactly the source object admitted at its entry point. -/
theorem AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry?_source
    (source : AuthoritativeChemicalInput)
    (analysis : SupportedAuthoritativeLocalizedStereochemicalAnalysis)
    (computed : source.analyzeSupportedLocalizedStereochemistry? = some analysis) :
    analysis.input.certified.input = source := by
  unfold AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry? at computed
  cases certifiedEq : source.certify? with
  | none => simp [certifiedEq] at computed
  | some certified =>
      have sourceEq : certified.input = source := by
        unfold AuthoritativeChemicalInput.certify? at certifiedEq
        split at certifiedEq
        · cases certifiedEq
          rfl
        · simp at certifiedEq
      cases localizedEq : certified.certifyLocalizedCIP? with
      | none => simp [certifiedEq, localizedEq] at computed
      | some localized =>
          have localizedCertifiedEq : localized.certified = certified := by
            unfold CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP? at localizedEq
            split at localizedEq
            · cases localizedEq
              rfl
            · simp at localizedEq
          simp [certifiedEq, localizedEq] at computed
          subst analysis
          rw [localizedCertifiedEq]
          exact sourceEq

/-- End-to-end current-scope statement: every descriptor returned by a successful format-neutral
analysis is independently justified for the exact admitted source molecule. -/
theorem AuthoritativeChemicalInput.analyzeSupportedLocalizedStereochemistry?_descriptor_conforms
    (source : AuthoritativeChemicalInput)
    (analysis : SupportedAuthoritativeLocalizedStereochemicalAnalysis)
    (computed : source.analyzeSupportedLocalizedStereochemistry? = some analysis)
    (assignment : analysis.input.LocalizedScheduledStereochemicalAssignment
      (defaultLocalizedStereochemicalFuel analysis.input))
    (present :
      CertifiedLocalizedCIPInput.LocalizedScheduledStereochemicalAnalysisEntry.descriptorAssignment
          assignment ∈ analysis.entries) :
    analysis.input.certified.input = source ∧
      analysis.input.DeclarativeLocalizedScheduledStereochemicalAssignment
        (defaultLocalizedStereochemicalFuel analysis.input) assignment :=
  ⟨source.analyzeSupportedLocalizedStereochemistry?_source analysis computed,
    analysis.descriptorAssignment_member_conforms assignment present⟩

end TetraStereo.OneCenter
