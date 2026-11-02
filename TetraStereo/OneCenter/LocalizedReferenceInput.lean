import TetraStereo.OneCenter.LocalizedNoDoubleReferenceInput

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedReference

/-- Runtime input for the complete existing localized evaluator. Source certification and graph
readiness are checked by admission; no bond-order restriction or caller-supplied proof is required. -/
structure Input where
  certified : CertifiedLocalizedCIPInput

def Input.molecule (input : Input) : SemanticMolecule :=
  input.certified.certified.input.molecule

def admitSource? (source : AuthoritativeChemicalInput) : Option Input := do
  let certified ← source.certify?
  let localized ← certified.certifyLocalizedCIP?
  pure { certified := localized }

theorem admitSource?_exact (source : AuthoritativeChemicalInput) (input : Input)
    (accepted : admitSource? source = some input) :
    input.certified.certified.input = source := by
  unfold admitSource? at accepted
  cases hs : source.certify? with
  | none => simp [hs] at accepted
  | some certified =>
      cases hl : certified.certifyLocalizedCIP? with
      | none => simp [hs, hl] at accepted
      | some localized =>
          simp [hs, hl] at accepted
          subst input
          rw [LocalizedNoDoubleReference.certifyLocalizedCIP?_certified_eq hl]
          exact LocalizedNoDoubleReference.certify?_input_eq hs

def admitRawSpatial? (molecule : RawMolecule) (spatial : SpatialConfiguration) : Option Input :=
  (molecule.toAuthoritativeChemicalInputWithSpatial? spatial).bind admitSource?

theorem admitRawSpatial?_exact (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : Input) (accepted : admitRawSpatial? molecule spatial = some input) :
    molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
      input.certified.certified.input.spatial? = some spatial := by
  unfold admitRawSpatial? at accepted
  cases hs : molecule.toAuthoritativeChemicalInputWithSpatial? spatial with
  | none => simp [hs] at accepted
  | some source =>
      simp only [hs, Option.bind_some] at accepted
      rw [admitSource?_exact source input accepted]
      exact molecule.toAuthoritativeChemicalInputWithSpatial?_exact spatial source hs

/-- Coordinates are indexed by the hydrogen-expanded atom list, as in the existing intake. -/
def admitSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) : Except ParserError (Option Input) :=
  match parseAndNormalizeOpenSMILESCertified text cycles with
  | .error message => .error message
  | .ok certified =>
      if certified.result.expandedStereochemicalAdmissible? then
        .ok (admitRawSpatial? certified.result.parsed.withExplicitHydrogens spatial)
      else .error "hydrogen-expanded molecule failed structural stereochemical admission"

theorem admitSmilesSpatial?_exact (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle) (input : Input)
    (accepted : admitSmilesSpatial? text spatial cycles = .ok (some input)) :
    ∃ certified : CertifiedChemistryNormalizationResult,
      parseAndNormalizeOpenSMILESCertified text cycles = .ok certified ∧
        certified.result.expandedStereochemicalAdmissible? = true ∧
          certified.result.parsed.withExplicitHydrogens.AuthoritativeStructureAgreement
            input.certified.certified.input ∧
          input.certified.certified.input.spatial? = some spatial := by
  unfold admitSmilesSpatial? at accepted
  cases parsed : parseAndNormalizeOpenSMILESCertified text cycles with
  | error message => simp [parsed] at accepted
  | ok certified =>
      by_cases ready : certified.result.expandedStereochemicalAdmissible? = true
      · have rawAccepted : admitRawSpatial? certified.result.parsed.withExplicitHydrogens
            spatial = some input := by simpa [parsed, ready] using accepted
        exact ⟨certified, rfl, ready,
          admitRawSpatial?_exact _ spatial input rawAccepted⟩
      · simp [parsed, ready] at accepted

end TetraStereo.OneCenter.LocalizedReference
