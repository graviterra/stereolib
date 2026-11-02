import TetraStereo.OneCenter.AuthoritativeCIPGraph
import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.OneCenter.LocalizedNoDoubleRule3ChemicalCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter














































namespace LocalizedNoDoubleReference

/-- A checked runtime input for the localized no-double-bond reference evaluation.

The first component is the already certified authority input whose constitution lies in the exact
localized closed-shell pair-bond domain of the CIP graph; the second is the kernel proof, obtained
from the executable source-record test, that no extracted localized covalent source record has bond
order two.  No further proof obligation is imposed on callers. -/
structure Input where
  certified : CertifiedLocalizedCIPInput
  noDouble : certified.certified.input.molecule.NoLocalizedDoubleBondRecords

namespace Input

/-- The certified authority input consumed by the evaluation. -/
def authority (input : Input) : CertifiedAuthoritativeChemicalInput :=
  input.certified.certified

/-- The exact format-neutral semantic molecule consumed by the evaluation. -/
def molecule (input : Input) : SemanticMolecule :=
  input.certified.certified.input.molecule

/-- The source-record no-double-bond restriction of the admitted molecule, as a proposition.  This is
the type of the `noDouble` field, named so that it can be written as a statement. -/
def NoDoubleRecords (input : Input) : Prop :=
  input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords

/-- The admitted input carries the source-record no-double-bond restriction by construction. -/
theorem noDoubleRecords (input : Input) : input.NoDoubleRecords :=
  input.noDouble

/-- The admitted molecule lies in the exact localized CIP graph domain: a consumer of `Input` needs
no separate graph-readiness obligation. -/
theorem molecule_graphReady (input : Input) :
    input.certified.certified.input.molecule.LocalizedCIPGraphReady :=
  input.certified.graphReady

end Input

/-! ## Projection facts about the checked constructors -/

/-- A successful `certify?` on a source returns that very source: the certified wrapper adds a proof
but does not replace the input. -/
theorem certify?_input_eq {source : AuthoritativeChemicalInput}
    {certified : CertifiedAuthoritativeChemicalInput}
    (observed : source.certify? = some certified) : certified.input = source := by
  by_cases checked : source.structurallyWellFormed? = true
  · have reduced :
        (some { input := source
                structurallyWellFormed :=
                  source.structurallyWellFormed?_eq_true_iff.mp checked } :
                  Option CertifiedAuthoritativeChemicalInput) = some certified := by
      simpa [AuthoritativeChemicalInput.certify?, checked] using observed
    injection reduced with injected
    exact (congrArg CertifiedAuthoritativeChemicalInput.input injected).symm
  · simp [AuthoritativeChemicalInput.certify?, checked] at observed

/-- A successful `certifyLocalizedCIP?` returns the same certified authority input: the graph
readiness proof is added, the constitution is not changed. -/
theorem certifyLocalizedCIP?_certified_eq {certified : CertifiedAuthoritativeChemicalInput}
    {localized : CertifiedLocalizedCIPInput}
    (observed : certified.certifyLocalizedCIP? = some localized) :
    localized.certified = certified := by
  by_cases ready : certified.input.molecule.localizedCIPGraphReady? = true
  · have reduced :
        (some { certified := certified
                graphReady :=
                  (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff
                    certified.input.molecule).mp ready } :
                  Option CertifiedLocalizedCIPInput) = some localized := by
      simpa [CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?, ready] using observed
    injection reduced with injected
    exact (congrArg CertifiedLocalizedCIPInput.certified injected).symm
  · simp [CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?, ready] at observed

/-! ## Checked admission -/

/-- Fail-closed runtime admission of a complete authoritative source.

The source must pass structural well-formedness, must lie in the localized CIP graph domain, and its
extracted localized covalent source records must contain no bond order two.  Failure at any stage
yields `none`; no obligation is left to the caller and no descriptor is computed. -/
def admitSource? (source : AuthoritativeChemicalInput) : Option Input :=
  match source.certify? with
  | none => none
  | some certified =>
      match certified.certifyLocalizedCIP? with
      | none => none
      | some localized =>
          if accepted :
              localized.certified.input.molecule.noLocalizedDoubleBondRecords? = true then
            some { certified := localized
                   noDouble :=
                     (SemanticMolecule.noLocalizedDoubleBondRecords?_eq_true_iff
                       localized.certified.input.molecule).mp accepted }
          else
            none

/-- Every successfully admitted input is exactly the supplied source, and carries the source-record
no-double-bond restriction.  No hypothesis about the source is needed to run admission. -/
theorem admitSource?_exact (source : AuthoritativeChemicalInput) (input : Input)
    (admitted : admitSource? source = some input) :
    input.certified.certified.input = source ∧ input.NoDoubleRecords := by
  unfold admitSource? at admitted
  cases sourceObserved : source.certify? with
  | none => simp [sourceObserved] at admitted
  | some certified =>
      cases localizedObserved : certified.certifyLocalizedCIP? with
      | none => simp [sourceObserved, localizedObserved] at admitted
      | some localized =>
          by_cases accepted :
              localized.certified.input.molecule.noLocalizedDoubleBondRecords? = true
          · simp [sourceObserved, localizedObserved, accepted] at admitted
            obtain rfl : input =
                { certified := localized
                  noDouble :=
                    (SemanticMolecule.noLocalizedDoubleBondRecords?_eq_true_iff
                      localized.certified.input.molecule).mp accepted } := admitted.symm
            refine ⟨?_, ?_⟩
            · rw [certifyLocalizedCIP?_certified_eq localizedObserved]
              exact certify?_input_eq sourceObserved
            · exact (SemanticMolecule.noLocalizedDoubleBondRecords?_eq_true_iff
                localized.certified.input.molecule).mp accepted
          · simp [sourceObserved, localizedObserved, accepted] at admitted

/-- The source-record restriction holds for the molecule the source actually denotes. -/
theorem admitSource?_noDoubleRecords (source : AuthoritativeChemicalInput) (input : Input)
    (admitted : admitSource? source = some input) :
    source.molecule.NoLocalizedDoubleBondRecords := by
  have exact' := admitSource?_exact source input admitted
  exact exact'.1 ▸ exact'.2

/-- The admitted molecule is the supplied source's molecule, exactly. -/
theorem admitSource?_molecule (source : AuthoritativeChemicalInput) (input : Input)
    (admitted : admitSource? source = some input) :
    input.certified.certified.input.molecule = source.molecule :=
  congrArg AuthoritativeChemicalInput.molecule (admitSource?_exact source input admitted).1

/-- Successful admission preserves the structural certificate of the source. -/
theorem admitSource?_structurallyWellFormed (source : AuthoritativeChemicalInput) (input : Input)
    (admitted : admitSource? source = some input) :
    source.StructurallyWellFormed := by
  have exact' := admitSource?_exact source input admitted
  exact exact'.1 ▸ input.certified.certified.structurallyWellFormed

/-- Fail-closed runtime admission of a parsed molecule together with an independently supplied exact
spatial configuration, through `RawMolecule.toAuthoritativeChemicalInputWithSpatial?` and then
`admitSource?`.

The configuration is indexed by the atom list of `molecule` itself; when the caller reaches this
function with a hydrogen-expanded molecule (as `admitSmilesSpatial?` does), the coordinates therefore
refer to the expanded atom list. -/
def admitRawSpatial? (molecule : RawMolecule) (spatial : SpatialConfiguration) : Option Input :=
  match molecule.toAuthoritativeChemicalInputWithSpatial? spatial with
  | none => none
  | some source => admitSource? source

/-- Every successfully admitted raw input has the checked parser structure and the copied diagram
evidence of the source molecule, exactly the supplied spatial configuration, and the source-record
no-double-bond restriction. -/
theorem admitRawSpatial?_exact (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : Input) (admitted : admitRawSpatial? molecule spatial = some input) :
    molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
      input.certified.certified.input.spatial? = some spatial ∧
        input.NoDoubleRecords := by
  unfold admitRawSpatial? at admitted
  cases sourceObserved : molecule.toAuthoritativeChemicalInputWithSpatial? spatial with
  | none => simp [sourceObserved] at admitted
  | some source =>
      simp [sourceObserved] at admitted
      have converted :=
        molecule.toAuthoritativeChemicalInputWithSpatial?_exact spatial source sourceObserved
      have exact' := admitSource?_exact source input admitted
      exact ⟨exact'.1.symm ▸ converted.1, exact'.1.symm ▸ converted.2, exact'.2⟩

/-- The admitted molecule's extracted localized covalent source records contain no bond order two. -/
theorem admitRawSpatial?_noDoubleRecords (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (input : Input) (admitted : admitRawSpatial? molecule spatial = some input) :
    ∀ record ∈ input.certified.certified.input.molecule.localizedCovalentRecords,
      record.2 ≠ 2 :=
  (admitRawSpatial?_exact molecule spatial input admitted).2.2

/-! ## OpenSMILES-facing admission -/

/-- Fail-closed runtime admission from an OpenSMILES-style string and an exact spatial configuration.

This runs the parse/normalization admission of `parseAndNormalizeOpenSMILESCertified` and then the
same hydrogen-expansion admissibility gate and error message that `analyzeSmiles` uses, before
applying `admitRawSpatial?` to the hydrogen-expanded molecule.  No descriptor is produced.

`Except.error` reports a parse, normalization, or hydrogen-expanded admissibility failure.  The inner
`none` reports that the expanded molecule (or the supplied coordinates, which must be indexed by the
expanded atom list) failed the checked admission of `admitRawSpatial?`. -/
def admitSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) : Except ParserError (Option Input) :=
  match parseAndNormalizeOpenSMILESCertified text cycles with
  | Except.error message => Except.error message
  | Except.ok certified =>
      if certified.result.expandedStereochemicalAdmissible? then
        Except.ok (admitRawSpatial? certified.result.parsed.withExplicitHydrogens spatial)
      else
        Except.error "hydrogen-expanded molecule failed structural stereochemical admission"

/-- A successful OpenSMILES admission exposes the certified normalization result that produced it:
the same certified intake as `analyzeSmiles`, with the hydrogen-expanded admissibility gate passed,
the expanded molecule transported into the admitted authority input together with the supplied
coordinates, and the source-record no-double-bond restriction. -/
theorem admitSmilesSpatial?_ok_exact (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle) (input : Input)
    (admitted : admitSmilesSpatial? text spatial cycles = Except.ok (some input)) :
    ∃ certified : CertifiedChemistryNormalizationResult,
      parseAndNormalizeOpenSMILESCertified text cycles = Except.ok certified ∧
        certified.result.expandedStereochemicalAdmissible? = true ∧
          certified.result.parsed.withExplicitHydrogens.AuthoritativeStructureAgreement
            input.certified.certified.input ∧
            input.certified.certified.input.spatial? = some spatial ∧
              input.NoDoubleRecords := by
  unfold admitSmilesSpatial? at admitted
  cases observed : parseAndNormalizeOpenSMILESCertified text cycles with
  | error message => simp [observed] at admitted
  | ok certified =>
      by_cases admissible : certified.result.expandedStereochemicalAdmissible? = true
      · have rawAdmitted :
            admitRawSpatial? certified.result.parsed.withExplicitHydrogens spatial = some input := by
          simpa [observed, admissible] using admitted
        have exact' :=
          admitRawSpatial?_exact certified.result.parsed.withExplicitHydrogens spatial input
            rawAdmitted
        -- `cases … with` has already substituted the parsed result in this branch, so the parse
        -- equation is `rfl` here and the case split transports it back to the stated form.
        exact ⟨certified, rfl, admissible, exact'.1, exact'.2.1, exact'.2.2⟩
      · simp [observed, admissible] at admitted

/-- The admitted molecule's extracted localized covalent source records contain no bond order two. -/
theorem admitSmilesSpatial?_noDoubleRecords (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle) (input : Input)
    (admitted : admitSmilesSpatial? text spatial cycles = Except.ok (some input)) :
    input.NoDoubleRecords := by
  obtain ⟨_, _, _, _, _, noDouble⟩ := admitSmilesSpatial?_ok_exact text spatial cycles input admitted
  exact noDouble

/-! ## Fail-closed smoke test -/

/-- Admission rejects a structurally malformed source without any caller-side proof: an interaction
whose participant list is shorter than two cannot reach the certified constitution. -/
example :
    (admitSource? { molecule :=
        { atoms := []
          interactions := [{ participants := [0], kind := .ionic }] } }).isNone = true := by
  decide

end LocalizedNoDoubleReference

end TetraStereo.OneCenter
