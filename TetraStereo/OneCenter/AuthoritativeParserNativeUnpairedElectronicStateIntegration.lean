import TetraStereo.OneCenter.AuthoritativeParserMainGroupLewisGeneralHybridEvidence

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace RawMolecule

open AuthoritativeChemicalInput

/-!
# Native parser unpaired-electron integration

`SemanticAtom` has an `unpairedElectrons` field, but the current `AtomSpec` grammar has no radical
syntax and `AtomSpec.toSemanticAtom?` initializes that field to zero.  This is nevertheless the
native semantic datum produced by the parser conversion.  The definitions below transport that
datum into `ParserAtomElectronicStateAnnotation.unpairedElectronPositions`, prove that it is
exactly zero for the current parser, and refuse a sidecar whose unpaired-position count disagrees.

Implicit-protium, lone-pair, and vacancy counts remain sidecar observations.  Nothing here infers
them from connectivity or from the native closed-shell result.
-/

/-- Native unpaired-electron count at a raw atom index, transported through the proved
parser-to-semantic index conversion. -/
noncomputable def nativeParserUnpairedElectronPositions?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atomIndex : Nat) : Option Nat := by
  classical
  exact if valid : atomIndex < molecule.atomCount then
    some ((source.molecule.atoms.get
      (molecule.convertedAtomIndex source converted ⟨atomIndex, valid⟩)).unpairedElectrons)
  else none

/-- Exact transport theorem before specializing the current parser to its proved closed-shell
behavior. -/
theorem nativeParserUnpairedElectronPositions?_eq_some_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atomIndex count : Nat) :
    molecule.nativeParserUnpairedElectronPositions? source converted atomIndex = some count ↔
      ∃ valid : atomIndex < molecule.atomCount,
        count = (source.molecule.atoms.get
          (molecule.convertedAtomIndex source converted ⟨atomIndex, valid⟩)).unpairedElectrons := by
  classical
  unfold nativeParserUnpairedElectronPositions?
  split
  next valid =>
    constructor
    · intro computed
      refine ⟨valid, ?_⟩
      exact (Option.some.inj computed).symm
    · rintro ⟨_validAgain, countIdentity⟩
      simp [countIdentity]
  next invalid =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨valid, _countIdentity⟩
    exact invalid valid

/-- The strongest current native-parser specialization: a valid index returns exactly zero,
because `AtomSpec` has no radical syntax and conversion is proved closed-shell. -/
theorem nativeParserUnpairedElectronPositions?_eq_some_iff_valid_and_zero
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (atomIndex count : Nat) :
    molecule.nativeParserUnpairedElectronPositions? source converted atomIndex = some count ↔
      atomIndex < molecule.atomCount ∧ count = 0 := by
  constructor
  · intro computed
    rcases (molecule.nativeParserUnpairedElectronPositions?_eq_some_iff
      source converted atomIndex count).mp computed with ⟨valid, countIdentity⟩
    refine ⟨valid, countIdentity.trans ?_⟩
    exact molecule.toSemanticMolecule?_aromaticCanonicalAtomsClosedShell source converted
      (molecule.convertedAtomIndex source converted ⟨atomIndex, valid⟩)
  · rintro ⟨valid, countIdentity⟩
    apply (molecule.nativeParserUnpairedElectronPositions?_eq_some_iff
      source converted atomIndex count).mpr
    refine ⟨valid, countIdentity.trans ?_⟩
    exact (molecule.toSemanticMolecule?_aromaticCanonicalAtomsClosedShell source converted
      (molecule.convertedAtomIndex source converted ⟨atomIndex, valid⟩)).symm

/-- Independent semantic agreement predicate for a full parser sidecar.  The existential bound
witness ensures an out-of-range annotation is not called agreement. -/
def ParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation) : Prop :=
  ∃ valid : annotation.atomIndex < molecule.atomCount,
    annotation.unpairedElectronPositions =
      (source.molecule.atoms.get
        (molecule.convertedAtomIndex source converted
          ⟨annotation.atomIndex, valid⟩)).unpairedElectrons

theorem parserAtomElectronicStateAnnotation_agreesWithNative_iff_valid_and_zero
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation) :
    molecule.ParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
        source converted annotation ↔
      annotation.atomIndex < molecule.atomCount ∧
        annotation.unpairedElectronPositions = 0 := by
  constructor
  · rintro ⟨valid, countIdentity⟩
    refine ⟨valid, countIdentity.trans ?_⟩
    exact molecule.toSemanticMolecule?_aromaticCanonicalAtomsClosedShell source converted
      (molecule.convertedAtomIndex source converted ⟨annotation.atomIndex, valid⟩)
  · rintro ⟨valid, zero⟩
    refine ⟨valid, zero.trans ?_⟩
    exact (molecule.toSemanticMolecule?_aromaticCanonicalAtomsClosedShell source converted
      (molecule.convertedAtomIndex source converted ⟨annotation.atomIndex, valid⟩)).symm

/-- Replace only the sidecar unpaired-position field by the native parser conversion result.
All chemically distinct missing-position fields are preserved literally. -/
noncomputable def parserAtomElectronicStateAnnotationWithNativeUnpairedElectrons?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation) :
    Option ParserAtomElectronicStateAnnotation :=
  (molecule.nativeParserUnpairedElectronPositions?
    source converted annotation.atomIndex).map fun nativeCount => {
      atomIndex := annotation.atomIndex
      implicitProtia := annotation.implicitProtia
      lonePairs := annotation.lonePairs
      vacancies := annotation.vacancies
      unpairedElectronPositions := nativeCount
    }

/-- A sidecar is left unchanged by native refinement exactly when its raw index is valid and its
unpaired-position count agrees with the native semantic atom field. -/
theorem parserAtomElectronicStateAnnotationWithNativeUnpairedElectrons?_eq_some_self_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation) :
    molecule.parserAtomElectronicStateAnnotationWithNativeUnpairedElectrons?
        source converted annotation = some annotation ↔
      molecule.ParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
        source converted annotation := by
  classical
  rw [molecule.parserAtomElectronicStateAnnotation_agreesWithNative_iff_valid_and_zero
    source converted annotation]
  unfold parserAtomElectronicStateAnnotationWithNativeUnpairedElectrons?
  cases annotation with
  | mk atomIndex implicitProtia lonePairs vacancies unpairedElectronPositions =>
      cases observed : molecule.nativeParserUnpairedElectronPositions?
          source converted atomIndex with
      | none =>
          have invalid : ¬ atomIndex < molecule.atomCount := by
            intro valid
            have nativeZero :=
              (molecule.nativeParserUnpairedElectronPositions?_eq_some_iff_valid_and_zero
                source converted atomIndex 0).mpr ⟨valid, rfl⟩
            rw [observed] at nativeZero
            contradiction
          simp [invalid]
      | some count =>
          have native :=
            (molecule.nativeParserUnpairedElectronPositions?_eq_some_iff_valid_and_zero
              source converted atomIndex count).mp observed
          simp [native.1, native.2, eq_comm]

/-- List-level native refinement.  Invalid raw indices are dropped internally but are an explicit
public refusal case below. -/
noncomputable def parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    List ParserAtomElectronicStateAnnotation :=
  annotations.filterMap
    (molecule.parserAtomElectronicStateAnnotationWithNativeUnpairedElectrons?
      source converted)

def EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) : Prop :=
  ∀ annotation, annotation ∈ annotations →
    molecule.ParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
      source converted annotation

/-- A genuine contradiction: a valid raw annotation explicitly disagrees with the converted
semantic atom's native unpaired-electron count. -/
def HasParserAtomElectronicStateAnnotationNativeUnpairedMismatch
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) : Prop :=
  ∃ annotation ∈ annotations,
    ∃ valid : annotation.atomIndex < molecule.atomCount,
      annotation.unpairedElectronPositions ≠
        (source.molecule.atoms.get
          (molecule.convertedAtomIndex source converted
            ⟨annotation.atomIndex, valid⟩)).unpairedElectrons

/-- For the current parser grammar, native disagreement is exactly a valid sidecar carrying a
nonzero unpaired-position count. -/
theorem hasParserAtomElectronicStateAnnotationNativeUnpairedMismatch_iff_exists_valid_nonzero
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    molecule.HasParserAtomElectronicStateAnnotationNativeUnpairedMismatch
        source converted annotations ↔
      ∃ annotation ∈ annotations,
        annotation.atomIndex < molecule.atomCount ∧
          annotation.unpairedElectronPositions ≠ 0 := by
  constructor
  · rintro ⟨annotation, present, valid, mismatch⟩
    refine ⟨annotation, present, valid, ?_⟩
    intro countZero
    apply mismatch
    exact countZero.trans
      (molecule.toSemanticMolecule?_aromaticCanonicalAtomsClosedShell source converted
        (molecule.convertedAtomIndex source converted
          ⟨annotation.atomIndex, valid⟩)).symm
  · rintro ⟨annotation, present, valid, nonzero⟩
    refine ⟨annotation, present, valid, ?_⟩
    intro countIdentity
    exact nonzero (countIdentity.trans
      (molecule.toSemanticMolecule?_aromaticCanonicalAtomsClosedShell source converted
        (molecule.convertedAtomIndex source converted
          ⟨annotation.atomIndex, valid⟩)))

theorem not_everyParserAtomElectronicStateAnnotationAgreesWithNative_iff_mismatch_of_valid
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (valid : molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations) :
    ¬ molecule.EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
        source converted annotations ↔
      molecule.HasParserAtomElectronicStateAnnotationNativeUnpairedMismatch
        source converted annotations := by
  classical
  constructor
  · intro notEvery
    unfold EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons at notEvery
    push_neg at notEvery
    rcases notEvery with ⟨annotation, present, notAgree⟩
    have indexValid := valid annotation present
    refine ⟨annotation, present, indexValid, ?_⟩
    intro countIdentity
    exact notAgree ⟨indexValid, countIdentity⟩
  · rintro ⟨annotation, present, indexValid, mismatch⟩ everyAgree
    rcases everyAgree annotation present with ⟨_agreementValid, agreement⟩
    exact mismatch (by simpa using agreement)

/-- When every sidecar agrees, native refinement is extensionally the identity list. -/
theorem parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons_eq_self
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (agrees :
      molecule.EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
        source converted annotations) :
    molecule.parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons
        source converted annotations = annotations := by
  classical
  unfold parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons
  induction annotations with
  | nil => rfl
  | cons annotation rest inductionHypothesis =>
      have headAgrees := agrees annotation (by simp)
      have restAgrees :
          molecule.EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
            source converted rest := by
        intro candidate present
        exact agrees candidate (by simp [present])
      simp [
        (molecule.parserAtomElectronicStateAnnotationWithNativeUnpairedElectrons?_eq_some_self_iff
          source converted annotation).mpr headAgrees,
        inductionHypothesis restAgrees]

/-- Readiness for the native-refined hybrid path. -/
def ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) : Prop :=
  molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations ∧
  molecule.EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
    source converted annotations ∧
  source.MainGroupLewisGeneralHybridCertificationReady
    (molecule.parserAtomElectronicStateRecords source converted
      (molecule.parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons
        source converted annotations))

/-- Exact refusal: invalid raw index, native/sidecar contradiction, or a generalized-Lewis hybrid
refusal after automatic native refinement. -/
def ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) : Prop :=
  molecule.HasInvalidParserAtomElectronicStateAnnotationIndex annotations ∨
  molecule.HasParserAtomElectronicStateAnnotationNativeUnpairedMismatch
    source converted annotations ∨
  source.MainGroupLewisGeneralHybridCertificationRefusal
    (molecule.parserAtomElectronicStateRecords source converted
      (molecule.parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons
        source converted annotations))

theorem not_parserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady_iff_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    ¬ molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
        source converted annotations ↔
      molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  by_cases valid :
      molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations
  · have noInvalid :
        ¬ molecule.HasInvalidParserAtomElectronicStateAnnotationIndex annotations := by
      intro invalid
      exact ((molecule.not_everyParserAtomElectronicStateAnnotationIndexValid_iff_hasInvalid
        annotations).mpr invalid) valid
    unfold ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
      ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal
    simp only [valid, noInvalid, true_and, false_or]
    rw [not_and_or,
      molecule.not_everyParserAtomElectronicStateAnnotationAgreesWithNative_iff_mismatch_of_valid
        source converted annotations valid,
      source.not_mainGroupLewisGeneralHybridCertificationReady_iff_refusal]
  · have invalid :=
      (molecule.not_everyParserAtomElectronicStateAnnotationIndexValid_iff_hasInvalid
        annotations).mp valid
    simp [ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady,
      ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal, valid, invalid]

/-- Native refinement changes no accepted sidecar: readiness is exactly ordinary parser-hybrid
readiness plus agreement with the native semantic unpaired-electron field. -/
theorem parserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady_iff_parserReady_and_agrees
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
        source converted annotations ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationReady
          source converted annotations ∧
      molecule.EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
          source converted annotations := by
  constructor
  · rintro ⟨valid, agrees, ready⟩
    have refinedIdentity :=
      molecule.parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons_eq_self
        source converted annotations agrees
    rw [refinedIdentity] at ready
    exact ⟨⟨valid, ready⟩, agrees⟩
  · rintro ⟨⟨valid, ready⟩, agrees⟩
    have refinedIdentity :=
      molecule.parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons_eq_self
        source converted annotations agrees
    unfold ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
    rw [refinedIdentity]
    exact ⟨valid, agrees, ready⟩

/-- Fully expanded positive boundary, retaining generalized-Lewis validity as an independent
semantic predicate. -/
theorem parserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady_iff_exact_conditions
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
        source converted annotations ↔
      (molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations ∧
        source.StructurallyWellFormed ∧
        (annotations.map ParserAtomElectronicStateAnnotation.key).Nodup ∧
        (∀ annotation, annotation ∈ annotations →
          molecule.ParserAtomElectronicStateAnnotationSatisfiesMainGroupLewisGeneral
            source converted annotation) ∧
        source.EveryIndividualDoubleBondEndpointMainGroupLewisGeneralHybridResolved
          (molecule.parserAtomElectronicStateRecords source converted annotations)) ∧
      molecule.EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
        source converted annotations := by
  rw [molecule.parserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady_iff_parserReady_and_agrees
      source converted annotations,
    molecule.parserMainGroupLewisGeneralHybridCertificationReady_iff_exact_conditions
      source converted annotations]

/-- The new refusal is exactly the existing exhaustive parser refusal plus the new native mismatch
case. -/
theorem parserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal_iff_parserRefusal_or_mismatch
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
          source converted annotations ∨
      molecule.HasParserAtomElectronicStateAnnotationNativeUnpairedMismatch
          source converted annotations := by
  classical
  by_cases valid :
      molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations
  · have noInvalid :
        ¬ molecule.HasInvalidParserAtomElectronicStateAnnotationIndex annotations := by
      intro invalid
      exact ((molecule.not_everyParserAtomElectronicStateAnnotationIndexValid_iff_hasInvalid
        annotations).mpr invalid) valid
    by_cases agrees :
        molecule.EveryParserAtomElectronicStateAnnotationAgreesWithNativeUnpairedElectrons
          source converted annotations
    · have noMismatch :
          ¬ molecule.HasParserAtomElectronicStateAnnotationNativeUnpairedMismatch
            source converted annotations := by
        intro mismatch
        exact ((molecule.not_everyParserAtomElectronicStateAnnotationAgreesWithNative_iff_mismatch_of_valid
          source converted annotations valid).mpr mismatch) agrees
      have refinedIdentity :=
        molecule.parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons_eq_self
          source converted annotations agrees
      simp [ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal,
        ParserMainGroupLewisGeneralHybridCertificationRefusal,
        noInvalid, noMismatch, refinedIdentity]
    · have mismatch :=
        (molecule.not_everyParserAtomElectronicStateAnnotationAgreesWithNative_iff_mismatch_of_valid
          source converted annotations valid).mp agrees
      simp [ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal, mismatch]
  · have invalid :=
      (molecule.not_everyParserAtomElectronicStateAnnotationIndexValid_iff_hasInvalid
        annotations).mp valid
    simp [ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal,
      ParserMainGroupLewisGeneralHybridCertificationRefusal, invalid]

/-- Fully expanded negative boundary: the former parser refusal cases are preserved verbatim and
native unpaired-electron contradiction is the sole added case. -/
theorem parserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal_iff_exact_cases
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation) :
    molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations ↔
      (molecule.HasInvalidParserAtomElectronicStateAnnotationIndex annotations ∨
        ¬ source.StructurallyWellFormed ∨
        ¬ (annotations.map ParserAtomElectronicStateAnnotation.key).Nodup ∨
        (∃ annotation ∈ annotations,
          ¬ molecule.ParserAtomElectronicStateAnnotationSatisfiesMainGroupLewisGeneral
            source converted annotation) ∨
        (∃ endpoint partner,
          source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
          source.aromaticCanonicalAtomElectronicStateLookup?
              (molecule.parserAtomElectronicStateRecords source converted annotations)
              endpoint = none ∧
          ¬ ∃ inventory,
            source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory endpoint inventory)) ∨
      molecule.HasParserAtomElectronicStateAnnotationNativeUnpairedMismatch
        source converted annotations := by
  rw [
    molecule.parserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal_iff_parserRefusal_or_mismatch
      source converted annotations,
    molecule.parserMainGroupLewisGeneralHybridCertificationRefusal_iff_exact_cases
      source converted annotations]

/-- Certified hybrid evidence using the automatically native-refined annotations. -/
noncomputable def certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
      source converted annotations) :
    CertifiedAuthoritativeChemicalInputWithAtomElectronicStates :=
  source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
    (molecule.parserAtomElectronicStateRecords source converted
      (molecule.parserAtomElectronicStateAnnotationsWithNativeUnpairedElectrons
        source converted annotations)) ready.2.2

/-- Total analyzer guarded by native agreement and the existing generalized-Lewis checks. -/
noncomputable def analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    Option (List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) := by
  classical
  exact if ready : molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
      source converted annotations then
    some ((molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      source converted annotations ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt)
  else none

@[simp] theorem analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?_eq_none_iff_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    molecule.analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?
        source converted annotations carrierFuel viewAt = none ↔
      molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  rw [← molecule.not_parserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady_iff_refusal
    source converted annotations]
  simp [analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?]

theorem analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?_eq_some_of_ready
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    molecule.analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?
        source converted annotations carrierFuel viewAt =
      some ((molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
        source converted annotations ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt) := by
  classical
  simp [analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?, ready]

theorem analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?_some_nodup
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignments : List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (computed : molecule.analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence?
      source converted annotations carrierFuel viewAt = some assignments) :
    assignments.Nodup := by
  classical
  unfold analyzeOrdinaryDoubleBondsOfParserNativeUnpairedHybridEvidence? at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst assignments
    exact
      (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
        source converted annotations ready).analyzeOrdinaryDoubleBonds_nodup carrierFuel viewAt
  next notReady => contradiction

theorem mem_certifiedParserNativeUnpairedHybridAnalyzeOrdinaryDoubleBonds_iff_canonical
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈
        (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
          source converted annotations ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            source converted annotations ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) assignment := by
  exact
    (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      source converted annotations ready).mem_analyzeOrdinaryDoubleBonds_iff_canonical
        carrierFuel viewAt assignment

theorem every_certifiedParserNativeUnpairedHybridIndividualDoubleBond_exact_success_or_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserNativeUnpairedMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel
          (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            source converted annotations ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈
            (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
              source converted annotations ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt ∧
          assignment.bond = bond) ∨
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel
          (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            source converted annotations ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel
          (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            source converted annotations ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) = none) := by
  exact
    (molecule.certifiedParserNativeUnpairedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      source converted annotations ready).every_individualDoubleBond_exact_success_or_refusal
        carrierFuel viewAt

end RawMolecule
end TetraStereo.OneCenter
