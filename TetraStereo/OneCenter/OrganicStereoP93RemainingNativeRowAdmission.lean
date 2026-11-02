import TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission
import TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries
import TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Native source admission for the ten excluded P-93 production rows

`OrganicStereoP93StableRowAdmission` supports 46 of the 56 closed production rows directly.  The
ten remaining rows are the five general P-93.1 rows and the five molecule-specific relational
fullerene rows.  This module performs their native source admission with the actual closed
reference program and the actual green successor codecs.

The construction has four layers.

* **Classification.**  `rowFamily` is the semantic row split: the five general rows are
  `.general`, the three cage-handedness rows are `.handed`, `chiralSubstituents` is `.type4` and
  `superimposedStereogenicElements` is `.superimposed`.  The theorem
  `rowFamily_none_iff_stableSupported` identifies this split pointwise with the executable 46/10
  split of the stable adapter, and `rowFamily_excludedRows` gives the exact image of the ten
  excluded rows.  No count-only claim is made.

* **Source translation.**  `translateTo` maps the *actual* `(row.reference reviewed).Observation`
  of an excluded row onto the actual family carrier: the five `SourceGeneralObservation` tags, or
  the `.handed`, `.type4` and `.superimposed` tags of `SourceRelationalVariantObservation`.
  `translateTo_judged` derives each family's own validity from the *actual* closed
  `(row.reference reviewed).Judges` (the general `Judged`, `judged.2.1` for the three handed rows,
  and `judged` for Type-4 and superimposed).  `translateTo_boundedIn_of_judged` derives the
  representation bounds needed by the green encoders from that judgment and the one common
  physical-frame binding; nothing is assumed.  `translateTo_tag` keeps the row family tag exact.

* **Native representation.**  `packNativeRow` stores the original row tag, its family and a
  `NativeEntry` of the existing closed union `OrganicStereoAllAuthorityEntries`.  General rows use
  the existing `.general` native branch: the source-free `NativeSourceContext`, the native
  five-tag observation, and the actual `Judged` certificate at the reconstructed common source.
  Relational fullerene rows use the existing `.relationalVariants` branch: the native tagged
  observation and its decoded-side `ValidFor`.  No raw `P93…AuthorityObservation` and no
  `CertifiedAuthoritativeChemicalInput` is retained.  The source geometry and both optional
  channels live in the common core / native context, never in a source record.

* **Exact decode.**  `decodeNativeRow` is the existing `decodeEntry`, and
  `decodeNativeRow_packNativeRow` is the exact raw-entry inverse obtained from the already proven
  `decodeEntry_encodeEntry`; no inverse hypothesis is assumed.  The ten
  `decodeNativeRow_*` theorems expose, row by row, the exact original observation recovered from
  the native entry.  `NativeRowEntry.reconstructedSource` recovers the source: the general branch
  decodes its stored native context, while every variant branch reconstructs the common source.

## Closed-reference / variant-codec boundary

For the three handed fullerene rows the actual closed judgment is

`P93FullereneCageHandednessType chiralityType ∧ observation.ValidFor policy source ∧
observation.base.assignment.chiralityType = chiralityType`,

whereas `SourceRelationalVariantObservation.ValidFor (.handed observation)` is only
`observation.ValidFor policy source`.  The admission therefore translates the `ValidFor` conjunct
and relies on exact observation recovery for the other two: the decoded observation retains the
same `base`, hence the same `assignment.chiralityType`, and the preserved row tag fixes the row's
constant `chiralityType`.  The definitional boundary is exposed by
`closedHandedJudges_eq_validFor_with_extras`, `closedType4Judges_eq_validFor` and
`closedSuperimposedJudges_eq_validFor`.  Type-4 and superimposed closed judgments are exactly the
variant `ValidFor`; the five general closed judgments are exactly the corresponding
`SourceGeneralObservation.Judged`.  There is no arbitrary `RawMolecule` requirement for any
methodology row: only the actual fullerene observation carries its own provenance molecule, as
part of the approved variant codec.
-/

namespace TetraStereo.OneCenter

open IUPACNormativeProvision
open BlueBookP93.Cyclic
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoP93StableRowAdmission
open OrganicStereoAllAuthorityEntries
open OrganicStereoNativeP94SourceContext
open OrganicStereoP93GeneralAuthorityIngress
open OrganicStereoRelationalFullereneVariantIngress

namespace OrganicStereoP93RemainingNativeRowAdmission

variable {V : Type} [DecidableEq V] [Fintype V]
variable {LigandId LigandKind FragmentId FragmentKind : Type}
variable {State Framework : Type}
variable {BaseName Numbering Locant Prefix : Type}

/-! ## The policy bridge

`Remaining71ReviewedPolicies` owns the five reviewed policy families used by the closed production
rows, while the native union `OrganicStereoAllAuthorityEntries` consumes one `AllAuthorityPolicies`
record.  The bridge is a literal projection record: every relevant field is the same value, so the
general and relational policy fields are definitionally the reviewed ones. -/

/-- The closed-union policy record obtained from the reviewed policy record. -/
def policiesOfReviewed (reviewed : Remaining71ReviewedPolicies) : AllAuthorityPolicies where
  policy94 := reviewed.p94
  policy93 := reviewed.p93Acyclic
  noncarbonPolicy := reviewed.p93Noncarbon
  monocyclicPolicy := reviewed.p93Cyclic.monocyclic
  assemblyPolicy := reviewed.p93Cyclic.ringAssembly
  fusedPolicy := reviewed.p93Cyclic.fused
  vonBaeyerPolicy := reviewed.p93Cyclic.vonBaeyer
  cyclophanePolicy := reviewed.p93Cyclic.cyclophane
  spiroPolicy := reviewed.p93Cyclic.spiro
  generalPolicy := reviewed.p93General
  fullerenePolicy := reviewed.p93Cyclic.fullerene
  relationalPolicy := reviewed.p93Cyclic.relationalFullerene
  coupledPolicy := reviewed.p93Cyclic.coupledRingChain

@[simp] theorem policiesOfReviewed_generalPolicy (reviewed : Remaining71ReviewedPolicies) :
    (policiesOfReviewed reviewed).generalPolicy = reviewed.p93General := rfl

@[simp] theorem policiesOfReviewed_relationalPolicy (reviewed : Remaining71ReviewedPolicies) :
    (policiesOfReviewed reviewed).relationalPolicy =
      reviewed.p93Cyclic.relationalFullerene := rfl

/-! ## The row/family classification -/

/-- The four native destination families of the ten remaining rows. -/
inductive RemainingFamily where
  /-- The five P-93.1 general-configuration rows. -/
  | general
  /-- The three cage-handedness rows (P-93 fullerene Types 1--3). -/
  | handed
  /-- The Type-4 substituent-only row. -/
  | type4
  /-- The superimposed-stereogenic-elements row. -/
  | superimposed
  deriving DecidableEq, Repr

/-- The semantic family of every closed production row.  `none` is exactly the 46 rows already
admitted by the stable adapter. -/
def rowFamily : Remaining71P93ClosedProductionRow → Option RemainingFamily
  | .fullerene .generalMethodology => none
  | .fullerene .inherentParentChirality => some .handed
  | .fullerene .inherentSubstitutionChirality => some .handed
  | .fullerene .noninherentSubstitutionChirality => some .handed
  | .fullerene .chiralSubstituents => some .type4
  | .fullerene .superimposedStereogenicElements => some .superimposed
  | .general _ => some .general
  | .noncarbon _ => none
  | .monocyclic _ => none
  | .vonBaeyer _ => none
  | .ringAssembly _ => none
  | .acyclic _ => none
  | .spiro _ => none
  | .spiroNontetrahedral => none
  | .fusedCyclophane _ => none
  | .coupledRingChain _ => none

/-- The semantic family split agrees pointwise with the executable stable-adapter split: a row has
no remaining family exactly when the stable adapter supports it.  This is a pointwise
classification theorem, not a count. -/
theorem rowFamily_none_iff_stableSupported (row : Remaining71P93ClosedProductionRow) :
    rowFamily row = none ↔ stableSupported row = true := by
  cases row with
  | fullerene child => cases child <;> simp [rowFamily, stableSupported]
  | general _ => simp [rowFamily, stableSupported]
  | noncarbon _ => simp [rowFamily, stableSupported]
  | monocyclic _ => simp [rowFamily, stableSupported]
  | vonBaeyer _ => simp [rowFamily, stableSupported]
  | ringAssembly _ => simp [rowFamily, stableSupported]
  | acyclic _ => simp [rowFamily, stableSupported]
  | spiro _ => simp [rowFamily, stableSupported]
  | spiroNontetrahedral => simp [rowFamily, stableSupported]
  | fusedCyclophane _ => simp [rowFamily, stableSupported]
  | coupledRingChain _ => simp [rowFamily, stableSupported]

/-- Exact family image of the ten excluded rows, in the order of `excludedRows_exact`. -/
theorem rowFamily_excludedRows :
    excludedRows.map rowFamily =
      [ some .handed
      , some .handed
      , some .handed
      , some .type4
      , some .superimposed
      , some .general
      , some .general
      , some .general
      , some .general
      , some .general
      ] := by
  decide

/-! ## Translation of the actual row observation

`translateTo` is total in the row, the family and the exact `rowFamily` certificate.  Its ten real
branches wrap the *actual* observation record without copying or projecting any field.  The other
rows are impossible by the exact family certificate. -/

/-- Translate one closed general-row observation into its actual five-tag family constructor. -/
def generalTag (reviewed : Remaining71ReviewedPolicies) :
    (child : Remaining71P93GeneralAuthorityRow) →
      ((Remaining71P93ClosedProductionRow.general child).reference reviewed).Observation →
      SourceGeneralObservation reviewed.p93General
  | .absoluteConfiguration, observation => .absolute observation
  | .relativeConfiguration, observation => .relative observation
  | .mixedAbsoluteRelativeConfiguration, observation => .mixedAbsoluteRelative observation
  | .racemates, observation => .racemate observation
  | .ambo, observation => .ambo observation

/-- The source-side carrier of the ten remaining rows.  Each constructor stores the complete
actual upstream observation record; no field is abstracted away. -/
inductive SourceRemainingFamily (reviewed : Remaining71ReviewedPolicies) where
  /-- One of the five actual P-93.1 general observations. -/
  | general (observation : SourceGeneralObservation reviewed.p93General)
  /-- One actual cage-handedness observation (Types 1--3). -/
  | handed
      (observation : P93RelationalFullereneHandedAuthorityObservation
        reviewed.p93Cyclic.relationalFullerene)
  /-- One actual Type-4 observation. -/
  | type4
      (observation : P93RelationalFullereneType4AuthorityObservation
        reviewed.p93Cyclic.relationalFullerene)
  /-- One actual superimposed observation. -/
  | superimposed
      (observation : P93RelationalFullereneSuperimposedAuthorityObservation
        reviewed.p93Cyclic.relationalFullerene)

namespace SourceRemainingFamily

/-- The family tag of a translated observation. -/
def tag {reviewed : Remaining71ReviewedPolicies} :
    SourceRemainingFamily reviewed → RemainingFamily
  | .general _ => .general
  | .handed _ => .handed
  | .type4 _ => .type4
  | .superimposed _ => .superimposed

/-- The actual source validity of a translated observation.  For the general family this is the
actual reviewed `SourceGeneralObservation.Judged`; for the fullerene families it is the actual
tagged `SourceRelationalVariantObservation.ValidFor`. -/
def Judged {reviewed : Remaining71ReviewedPolicies}
    (observation : SourceRemainingFamily reviewed) (source : AuthoritativeChemicalInput) : Prop :=
  match observation with
  | .general o => SourceGeneralObservation.Judged reviewed.p93General source o
  | .handed o => (SourceRelationalVariantObservation.handed o).ValidFor source
  | .type4 o => (SourceRelationalVariantObservation.type4 o).ValidFor source
  | .superimposed o => (SourceRelationalVariantObservation.superimposed o).ValidFor source

/-- The representation bounds needed to write a translated observation into the finite atom type.
For the general family this is the actual `SourceGeneralObservation.BoundedIn`; for the fullerene
families it is the actual tagged `SourceRelationalVariantObservation.BoundedIn`. -/
def BoundedIn {reviewed : Remaining71ReviewedPolicies}
    (observation : SourceRemainingFamily reviewed) (n : Nat) : Prop :=
  match observation with
  | .general o => o.BoundedIn n
  | .handed o => (SourceRelationalVariantObservation.handed o).BoundedIn n
  | .type4 o => (SourceRelationalVariantObservation.type4 o).BoundedIn n
  | .superimposed o => (SourceRelationalVariantObservation.superimposed o).BoundedIn n

/-- The relational-fullerene view of a translated observation.  It is `none` exactly for the
general family. -/
def toVariant {reviewed : Remaining71ReviewedPolicies} :
    SourceRemainingFamily reviewed →
      Option (SourceRelationalVariantObservation reviewed.p93Cyclic.relationalFullerene)
  | .general _ => none
  | .handed o => some (.handed o)
  | .type4 o => some (.type4 o)
  | .superimposed o => some (.superimposed o)

/-- The optional spatial channel stored by the fullerene carriers.  The general family has no
observation-level spatial channel: its geometry is retained by the native source context. -/
def spatial? {reviewed : Remaining71ReviewedPolicies} :
    SourceRemainingFamily reviewed → Option SpatialConfiguration
  | .general _ => none
  | .handed o => (SourceRelationalVariantObservation.handed o).spatial?
  | .type4 o => (SourceRelationalVariantObservation.type4 o).spatial?
  | .superimposed o => (SourceRelationalVariantObservation.superimposed o).spatial?

/-- Assemble one translated observation and its actual judgment into the existing closed union.
General rows use the actual `.general` raw entry; the three fullerene tags use the actual
`.relationalVariants` raw entry.  No new native vocabulary is introduced. -/
def toRawEntry (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (translation : SourceRemainingFamily reviewed)
    (judged : translation.Judged (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration)) :
    RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix (policiesOfReviewed reviewed) core enumeration :=
  match translation with
  | .general observation => .general observation judged
  | .handed observation => .relationalVariants (.handed observation) judged
  | .type4 observation => .relationalVariants (.type4 observation) judged
  | .superimposed observation => .relationalVariants (.superimposed observation) judged

end SourceRemainingFamily

/-- Translate the actual observation of one remaining row into the correct family constructor.
The family certificate is exact; it simultaneously guarantees that the row is one of the ten. -/
def translateTo (reviewed : Remaining71ReviewedPolicies) :
    (row : Remaining71P93ClosedProductionRow) → (family : RemainingFamily) →
    rowFamily row = some family → (row.reference reviewed).Observation →
    SourceRemainingFamily reviewed
  | .fullerene .generalMethodology, _, hRow, _ => False.elim (by cases hRow)
  | .fullerene .inherentParentChirality, _, _, observation => .handed observation
  | .fullerene .inherentSubstitutionChirality, _, _, observation => .handed observation
  | .fullerene .noninherentSubstitutionChirality, _, _, observation => .handed observation
  | .fullerene .chiralSubstituents, _, _, observation => .type4 observation
  | .fullerene .superimposedStereogenicElements, _, _, observation =>
      .superimposed observation
  | .general child, _, _, observation => .general (generalTag reviewed child observation)
  | .noncarbon _, _, hRow, _ => False.elim (by cases hRow)
  | .monocyclic _, _, hRow, _ => False.elim (by cases hRow)
  | .vonBaeyer _, _, hRow, _ => False.elim (by cases hRow)
  | .ringAssembly _, _, hRow, _ => False.elim (by cases hRow)
  | .acyclic _, _, hRow, _ => False.elim (by cases hRow)
  | .spiro _, _, hRow, _ => False.elim (by cases hRow)
  | .spiroNontetrahedral, _, hRow, _ => False.elim (by cases hRow)
  | .fusedCyclophane _, _, hRow, _ => False.elim (by cases hRow)
  | .coupledRingChain _, _, hRow, _ => False.elim (by cases hRow)

/-- **Validity translation.**  The actual closed `(row.reference reviewed).Judges` of a remaining
row implies the translated family's own actual validity at the same source.  Each branch uses
exactly the corresponding conjunction projection; no inverse, normalization, agreement or
boundedness premise is assumed. -/
theorem translateTo_judged (reviewed : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family) (source : AuthoritativeChemicalInput)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges source observation) :
    (translateTo reviewed row family hRow observation).Judged source := by
  cases row with
  | fullerene child =>
      cases child with
      | generalMethodology => exact False.elim (by cases hRow)
      | inherentParentChirality => exact judged.2.1
      | inherentSubstitutionChirality => exact judged.2.1
      | noninherentSubstitutionChirality => exact judged.2.1
      | chiralSubstituents => exact judged
      | superimposedStereogenicElements => exact judged
  | general child =>
      cases child with
      | absoluteConfiguration => exact judged
      | relativeConfiguration => exact judged
      | mixedAbsoluteRelativeConfiguration => exact judged
      | racemates => exact judged
      | ambo => exact judged
  | noncarbon _ => exact False.elim (by cases hRow)
  | monocyclic _ => exact False.elim (by cases hRow)
  | vonBaeyer _ => exact False.elim (by cases hRow)
  | ringAssembly _ => exact False.elim (by cases hRow)
  | acyclic _ => exact False.elim (by cases hRow)
  | spiro _ => exact False.elim (by cases hRow)
  | spiroNontetrahedral => exact False.elim (by cases hRow)
  | fusedCyclophane _ => exact False.elim (by cases hRow)
  | coupledRingChain _ => exact False.elim (by cases hRow)

/-- The translation lands in the family certified by the row split. -/
theorem translateTo_tag (reviewed : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation) :
    (translateTo reviewed row family hRow observation).tag = family := by
  have rowFamily_some_eq {family' : RemainingFamily}
      (h : rowFamily row = some family') : family = family' := by
    have h' : some family = some family' := by
      rw [hRow] at h
      exact h
    exact (Option.some.injEq family family').mp h'
  cases row with
  | fullerene child =>
      cases child with
      | generalMethodology => exact False.elim (by cases hRow)
      | inherentParentChirality =>
          have hf : family = .handed := rowFamily_some_eq rfl
          subst hf
          rfl
      | inherentSubstitutionChirality =>
          have hf : family = .handed := rowFamily_some_eq rfl
          subst hf
          rfl
      | noninherentSubstitutionChirality =>
          have hf : family = .handed := rowFamily_some_eq rfl
          subst hf
          rfl
      | chiralSubstituents =>
          have hf : family = .type4 := rowFamily_some_eq rfl
          subst hf
          rfl
      | superimposedStereogenicElements =>
          have hf : family = .superimposed := rowFamily_some_eq rfl
          subst hf
          rfl
  | general child =>
      have hf : family = .general := rowFamily_some_eq rfl
      subst hf
      rfl
  | noncarbon _ => exact False.elim (by cases hRow)
  | monocyclic _ => exact False.elim (by cases hRow)
  | vonBaeyer _ => exact False.elim (by cases hRow)
  | ringAssembly _ => exact False.elim (by cases hRow)
  | acyclic _ => exact False.elim (by cases hRow)
  | spiro _ => exact False.elim (by cases hRow)
  | spiroNontetrahedral => exact False.elim (by cases hRow)
  | fusedCyclophane _ => exact False.elim (by cases hRow)
  | coupledRingChain _ => exact False.elim (by cases hRow)

/-- **Bounds translation.**  The representation bounds of the translated observation are derived
from the actual closed judgment and the one common physical-frame binding.  General rows use
`SourceGeneralObservation.boundedIn_of_judged` (through the existing `generalBounds`); the three
fullerene tags use `SourceRelationalVariantObservation.boundedIn_of_validFor`. -/
theorem translateTo_boundedIn_of_judged (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    (translateTo reviewed row family hRow observation).BoundedIn (Fintype.card V) := by
  cases row with
  | fullerene child =>
      cases child with
      | generalMethodology => exact False.elim (by cases hRow)
      | inherentParentChirality =>
          exact SourceRelationalVariantObservation.boundedIn_of_validFor
            (commonBinding core enumeration source_well_formed) (.handed observation) judged.2.1
      | inherentSubstitutionChirality =>
          exact SourceRelationalVariantObservation.boundedIn_of_validFor
            (commonBinding core enumeration source_well_formed) (.handed observation) judged.2.1
      | noninherentSubstitutionChirality =>
          exact SourceRelationalVariantObservation.boundedIn_of_validFor
            (commonBinding core enumeration source_well_formed) (.handed observation) judged.2.1
      | chiralSubstituents =>
          exact SourceRelationalVariantObservation.boundedIn_of_validFor
            (commonBinding core enumeration source_well_formed) (.type4 observation) judged
      | superimposedStereogenicElements =>
          exact SourceRelationalVariantObservation.boundedIn_of_validFor
            (commonBinding core enumeration source_well_formed) (.superimposed observation) judged
  | general child =>
      cases child with
      | absoluteConfiguration =>
          exact generalBounds (policies := policiesOfReviewed reviewed) core enumeration
            source_well_formed (.absolute observation) judged
      | relativeConfiguration =>
          exact generalBounds (policies := policiesOfReviewed reviewed) core enumeration
            source_well_formed (.relative observation) judged
      | mixedAbsoluteRelativeConfiguration =>
          exact generalBounds (policies := policiesOfReviewed reviewed) core enumeration
            source_well_formed (.mixedAbsoluteRelative observation) judged
      | racemates =>
          exact generalBounds (policies := policiesOfReviewed reviewed) core enumeration
            source_well_formed (.racemate observation) judged
      | ambo =>
          exact generalBounds (policies := policiesOfReviewed reviewed) core enumeration
            source_well_formed (.ambo observation) judged
  | noncarbon _ => exact False.elim (by cases hRow)
  | monocyclic _ => exact False.elim (by cases hRow)
  | vonBaeyer _ => exact False.elim (by cases hRow)
  | ringAssembly _ => exact False.elim (by cases hRow)
  | acyclic _ => exact False.elim (by cases hRow)
  | spiro _ => exact False.elim (by cases hRow)
  | spiroNontetrahedral => exact False.elim (by cases hRow)
  | fusedCyclophane _ => exact False.elim (by cases hRow)
  | coupledRingChain _ => exact False.elim (by cases hRow)

/-! ### Exact constructor of the translation

These ten lemmas expose the exact source constructor reached by `translateTo`: no field of the
actual observation is projected, copied or normalized.  They are the source-side half of the
exact observation recovery below. -/

theorem translateTo_general_absoluteConfiguration (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.general .absoluteConfiguration) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .absoluteConfiguration).reference reviewed).Observation) :
    translateTo reviewed (.general .absoluteConfiguration) .general hRow observation =
      .general (.absolute observation) := rfl

theorem translateTo_general_relativeConfiguration (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.general .relativeConfiguration) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .relativeConfiguration).reference reviewed).Observation) :
    translateTo reviewed (.general .relativeConfiguration) .general hRow observation =
      .general (.relative observation) := rfl

theorem translateTo_general_mixedAbsoluteRelativeConfiguration
    (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.general .mixedAbsoluteRelativeConfiguration) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .mixedAbsoluteRelativeConfiguration).reference reviewed).Observation) :
    translateTo reviewed (.general .mixedAbsoluteRelativeConfiguration) .general hRow observation =
      .general (.mixedAbsoluteRelative observation) := rfl

theorem translateTo_general_racemates (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.general .racemates) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .racemates).reference reviewed).Observation) :
    translateTo reviewed (.general .racemates) .general hRow observation =
      .general (.racemate observation) := rfl

theorem translateTo_general_ambo (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.general .ambo) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .ambo).reference reviewed).Observation) :
    translateTo reviewed (.general .ambo) .general hRow observation =
      .general (.ambo observation) := rfl

theorem translateTo_fullerene_inherentParentChirality
    (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.fullerene .inherentParentChirality) = some .handed)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .inherentParentChirality).reference reviewed).Observation) :
    translateTo reviewed (.fullerene .inherentParentChirality) .handed hRow observation =
      .handed observation := rfl

theorem translateTo_fullerene_inherentSubstitutionChirality
    (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.fullerene .inherentSubstitutionChirality) = some .handed)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .inherentSubstitutionChirality).reference reviewed).Observation) :
    translateTo reviewed (.fullerene .inherentSubstitutionChirality) .handed hRow observation =
      .handed observation := rfl

theorem translateTo_fullerene_noninherentSubstitutionChirality
    (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.fullerene .noninherentSubstitutionChirality) = some .handed)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .noninherentSubstitutionChirality).reference reviewed).Observation) :
    translateTo reviewed (.fullerene .noninherentSubstitutionChirality) .handed hRow observation =
      .handed observation := rfl

theorem translateTo_fullerene_chiralSubstituents
    (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.fullerene .chiralSubstituents) = some .type4)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .chiralSubstituents).reference reviewed).Observation) :
    translateTo reviewed (.fullerene .chiralSubstituents) .type4 hRow observation =
      .type4 observation := rfl

theorem translateTo_fullerene_superimposedStereogenicElements
    (reviewed : Remaining71ReviewedPolicies)
    (hRow : rowFamily (.fullerene .superimposedStereogenicElements) = some .superimposed)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .superimposedStereogenicElements).reference reviewed).Observation) :
    translateTo reviewed (.fullerene .superimposedStereogenicElements) .superimposed hRow
        observation =
      .superimposed observation := rfl

/-! ### Closed-reference / variant-codec boundary

The closed reference judgments are definitionally related to the family carriers below.  The
handed rows are the only place where the closed judgment is strictly stronger than the variant
`ValidFor`: the two extra conjuncts concern the constant row chirality type and the observation's
own chirality type.  Exact observation recovery retains the latter; the row tag retains the
former. -/

/-- The exact closed judgment of a handed fullerene row: the variant `ValidFor` together with the
cage-handedness class and the row chirality-type equality. -/
theorem closedHandedJudges_eq_validFor_with_extras
    (policy : P93RelationalFullereneAuthorityPolicy)
    (chiralityType : FullereneChiralityType) (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneHandedAuthorityObservation policy) :
    (p93RelationalFullereneTypeReference policy chiralityType).Judges source observation =
      (P93FullereneCageHandednessType chiralityType ∧
        (SourceRelationalVariantObservation.handed observation).ValidFor source ∧
        observation.base.assignment.chiralityType = chiralityType) := rfl

/-- The Type-4 closed judgment is exactly the tagged variant `ValidFor`. -/
theorem closedType4Judges_eq_validFor (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneType4AuthorityObservation policy) :
    (p93RelationalFullereneType4Reference policy).Judges source observation =
      (SourceRelationalVariantObservation.type4 observation).ValidFor source := rfl

/-- The superimposed closed judgment is exactly the tagged variant `ValidFor`. -/
theorem closedSuperimposedJudges_eq_validFor
    (policy : P93RelationalFullereneAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneSuperimposedAuthorityObservation policy) :
    (p93RelationalFullereneSuperimposedReference policy).Judges source observation =
      (SourceRelationalVariantObservation.superimposed observation).ValidFor source := rfl

/-- The three handed rows' extra chirality-type conjunct, exposed row by row. -/
theorem inherentParentChirality_judged_chiralityType
    (pol : P93RelationalFullereneAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneHandedAuthorityObservation pol)
    (judged : (p93RelationalFullereneTypeReference pol .inherentlyChiralParent).Judges
      source observation) :
    observation.base.assignment.chiralityType = .inherentlyChiralParent :=
  judged.2.2

theorem inherentSubstitutionChirality_judged_chiralityType
    (pol : P93RelationalFullereneAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneHandedAuthorityObservation pol)
    (judged : (p93RelationalFullereneTypeReference pol
      .inherentlyChiralSubstitutionPattern).Judges source observation) :
    observation.base.assignment.chiralityType = .inherentlyChiralSubstitutionPattern :=
  judged.2.2

theorem noninherentSubstitutionChirality_judged_chiralityType
    (pol : P93RelationalFullereneAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneHandedAuthorityObservation pol)
    (judged : (p93RelationalFullereneTypeReference pol
      .noninherentlyChiralSubstitutionPattern).Judges source observation) :
    observation.base.assignment.chiralityType = .noninherentlyChiralSubstitutionPattern :=
  judged.2.2

/-! ## Raw-entry assembly and family readback -/

/-- The raw-entry type of the closed union at the ambient ligand/frame parameters.  The union tags
of the ten remaining rows do not determine those parameters, so this abbreviation takes them
explicitly and keeps every downstream annotation determined. -/
abbrev RemainingRawEntry (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind State Framework BaseName Numbering Locant Prefix :
      Type)
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V)) :=
  RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix (policiesOfReviewed reviewed) core enumeration

/-- `RemainingRawEntry` applied at the ambient ligand/frame parameters. -/
local notation "RawAt" =>
  RemainingRawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix

/-- The native-entry type of the closed union at the ambient ligand/frame parameters. -/
abbrev RemainingNativeEntry (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind State Framework BaseName Numbering Locant Prefix :
      Type)
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V)) :=
  NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix (policiesOfReviewed reviewed) core enumeration

/-- `RemainingNativeEntry` applied at the ambient ligand/frame parameters. -/
local notation "NativeAt" =>
  RemainingNativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix

/-- Assemble the native raw entry of one remaining row from its actual observation and its actual
closed judgment.  The family-level validity is derived by `translateTo_judged`; the representation
bounds are derived inside the existing encoder from that validity. -/
def toRawEntry (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix (policiesOfReviewed reviewed) core enumeration :=
  SourceRemainingFamily.toRawEntry reviewed core enumeration
    (translateTo reviewed row family hRow observation)
    (translateTo_judged reviewed row family hRow
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation judged)

/-- Read the remaining-family observation back out of a raw entry.  It is `none` for every other
constructor of the closed union. -/
def rawEntryFamily? (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix (policiesOfReviewed reviewed) core enumeration →
    Option (SourceRemainingFamily reviewed)
  | .general observation _ => some (.general observation)
  | .relationalVariants (.handed observation) _ => some (.handed observation)
  | .relationalVariants (.type4 observation) _ => some (.type4 observation)
  | .relationalVariants (.superimposed observation) _ => some (.superimposed observation)
  | _ => none

/-- The assembled raw entry reads back to exactly the translated observation. -/
theorem rawEntryFamily?_toRawEntry (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (translation : SourceRemainingFamily reviewed)
    (judged : translation.Judged
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration)) :
    rawEntryFamily? reviewed core enumeration
      (SourceRemainingFamily.toRawEntry reviewed core enumeration translation judged :
        RawAt reviewed core enumeration) =
      some translation := by
  cases translation <;> rfl

/-! ## The native row entry -/

/-- One native admission record for a remaining row.  The row tag is retained literally next to
the family certificate and the existing closed-union native entry; the native entry itself stores
no raw observation and no certified source. -/
structure NativeRowEntry (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) where
  /-- The exact original closed production row. -/
  row : Remaining71P93ClosedProductionRow
  /-- The semantic family of that row. -/
  family : RemainingFamily
  /-- The exact family certificate. -/
  family_eq : rowFamily row = some family
  /-- The existing closed-union native entry (source-free native payload plus decoded validity). -/
  entry : NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix (policiesOfReviewed reviewed) core enumeration

/-- The fully applied native row entry type at the ambient ligand/frame parameters. -/
abbrev RemainingNativeRowEntry (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind State Framework BaseName Numbering Locant Prefix :
      Type)
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V)) :=
  NativeRowEntry (V := V) (LigandId := LigandId) (LigandKind := LigandKind)
    (FragmentId := FragmentId) (FragmentKind := FragmentKind) (State := State)
    (Framework := Framework) (BaseName := BaseName) (Numbering := Numbering)
    (Locant := Locant) (Prefix := Prefix) reviewed core enumeration

/-- `RemainingNativeRowEntry` applied at the ambient ligand/frame parameters. -/
local notation "NativeRowAt" =>
  RemainingNativeRowEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix

/-- Admit one remaining row: translate the actual observation, derive its actual family validity
from the actual closed judgment, encode it with the existing closed-union encoder, and retain the
row and family tags. -/
def packNativeRow (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    NativeRowAt reviewed core enumeration where
  row := row
  family := family
  family_eq := hRow
  entry := encodeEntry core enumeration source_well_formed
    (toRawEntry reviewed core enumeration row family hRow observation judged)

@[simp] theorem packNativeRow_row (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    ((packNativeRow reviewed core enumeration source_well_formed row family hRow observation
      judged : NativeRowAt reviewed core enumeration)).row = row := rfl

@[simp] theorem packNativeRow_family (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    ((packNativeRow reviewed core enumeration source_well_formed row family hRow observation
      judged : NativeRowAt reviewed core enumeration)).family = family := rfl

@[simp] theorem packNativeRow_family_eq (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    ((packNativeRow reviewed core enumeration source_well_formed row family hRow observation
      judged : NativeRowAt reviewed core enumeration)).family_eq = hRow := rfl

@[simp] theorem packNativeRow_entry (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    ((packNativeRow reviewed core enumeration source_well_formed row family hRow observation
      judged : NativeRowAt reviewed core enumeration)).entry =
      encodeEntry core enumeration source_well_formed
        (toRawEntry reviewed core enumeration row family hRow observation judged) := rfl

/-- An admitted row is an actual row excluded by the stable adapter.  The exclusion certificate is
derived from the exact family tag, not stored or assumed. -/
theorem packNativeRow_stableSupported_false_aux
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family) :
    stableSupported row = false := by
  have hnone : rowFamily row ≠ none := by
    rw [hRow]
    exact Option.some_ne_none family
  have hnotTrue : stableSupported row ≠ true := fun htrue =>
    hnone ((rowFamily_none_iff_stableSupported row).2 htrue)
  cases h : stableSupported row with
  | false => rfl
  | true => exact False.elim (hnotTrue h)

/-- The exclusion certificate of a packed row.  The conclusion is about the row that
`packNativeRow` stores (`packNativeRow_row`); the source certificate and the judgment only fix the
admission premises and are otherwise not consulted. -/
theorem packNativeRow_stableSupported_false (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (_source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (_judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    stableSupported row = false := by
  exact packNativeRow_stableSupported_false_aux row family hRow

/-! ## The source reconstructed by a native row entry

For the general family the source is reconstructed from the stored source-free native context; for
the three fullerene families the source is the common reconstructed source of the closed union
(the native variant entry stores no source record). -/

/-- Extract the general native source context, if the entry is the general branch. -/
def nativeGeneralContext? (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix (policiesOfReviewed reviewed) core enumeration →
    Option (NativeSourceContext core.graph enumeration)
  | .general context _ _ _ => some context
  | _ => none

/-- The source reconstructed from a native row entry.  General rows decode the stored source
context; every variant row reconstructs the common source from the core, enumeration and the
original optional geometry channels. -/
def NativeRowEntry.reconstructedSource {reviewed : Remaining71ReviewedPolicies}
    {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : NativeRowAt reviewed core enumeration) : AuthoritativeChemicalInput :=
  match entry.family, nativeGeneralContext? reviewed core enumeration entry.entry with
  | .general, some context => (decodeSourceContext core.graph enumeration context).input
  | _, _ => OrganicStereoAllAuthorityEntries.recoveredSource core enumeration

/-- The general branch stores exactly the common native context, which contains both optional
geometry channels of the reconstructed source. -/
theorem packNativeRow_generalContext? (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (child : Remaining71P93GeneralAuthorityRow)
    (hRow : rowFamily (.general child) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general child).reference
      reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.general child).reference
      reviewed).Judges (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration)
        observation) :
    nativeGeneralContext? reviewed core enumeration
      ((packNativeRow reviewed core enumeration source_well_formed
        (.general child) .general hRow observation judged :
          NativeRowAt reviewed core enumeration)).entry =
      some (generalContext core enumeration source_well_formed) := rfl

/-- The reconstructed source of a packed general row is exactly the common reconstructed source. -/
theorem packNativeRow_reconstructedSource_general
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (child : Remaining71P93GeneralAuthorityRow)
    (hRow : rowFamily (.general child) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general child).reference
      reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.general child).reference
      reviewed).Judges (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration)
        observation) :
    ((packNativeRow reviewed core enumeration source_well_formed
      (.general child) .general hRow observation judged :
        NativeRowAt reviewed core enumeration)).reconstructedSource =
      OrganicStereoAllAuthorityEntries.recoveredSource core enumeration := by
  have hctx : nativeGeneralContext? reviewed core enumeration
      ((packNativeRow reviewed core enumeration source_well_formed
        (.general child) .general hRow observation judged :
          NativeRowAt reviewed core enumeration)).entry =
      some (generalContext core enumeration source_well_formed) :=
    packNativeRow_generalContext? reviewed core enumeration source_well_formed
      child hRow observation judged
  simp only [NativeRowEntry.reconstructedSource, packNativeRow_family, hctx]
  exact decode_generalContext_source core enumeration source_well_formed

/-- The reconstructed source of a packed non-general (relational fullerene) row is the common
reconstructed source; no source record is stored in the native variant payload. -/
theorem packNativeRow_reconstructedSource_variant
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family) (hfamily : family ≠ .general)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    ((packNativeRow reviewed core enumeration source_well_formed row family hRow observation
      judged : NativeRowAt reviewed core enumeration)).reconstructedSource =
      OrganicStereoAllAuthorityEntries.recoveredSource core enumeration := by
  cases family with
  | general => exact False.elim (hfamily rfl)
  | handed => rfl
  | type4 => rfl
  | superimposed => rfl

/-! ## Native decode and exact recovery -/

/-- Decode a native row entry with the existing closed-union decoder.  The decoder consults only
the native entry and the common core/enumeration; it never sees the original request. -/
def decodeNativeRow (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : NativeRowAt reviewed core enumeration) :
    RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix (policiesOfReviewed reviewed) core enumeration :=
  decodeEntry core enumeration entry.entry

/-- **Exact raw-entry inverse.**  Decoding an admitted row returns exactly the raw entry assembled
from the original observation and its original closed judgment.  This is the already proven
`decodeEntry_encodeEntry`; no inverse is assumed. -/
theorem decodeNativeRow_packNativeRow (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    decodeNativeRow reviewed core enumeration
      (packNativeRow reviewed core enumeration source_well_formed row family hRow observation
        judged : NativeRowAt reviewed core enumeration) =
      toRawEntry reviewed core enumeration row family hRow observation judged :=
  decodeEntry_encodeEntry core enumeration source_well_formed
    (toRawEntry reviewed core enumeration row family hRow observation judged)

/-- The family observation recovered from the decoded native entry is exactly the translation of
the original observation. -/
theorem decodeNativeRow_packNativeRow_tag (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed row family hRow observation
          judged) : RawAt reviewed core enumeration)) =
      some (translateTo reviewed row family hRow observation) := by
  rw [decodeNativeRow_packNativeRow]
  exact rawEntryFamily?_toRawEntry reviewed core enumeration
    (translateTo reviewed row family hRow observation)
    (translateTo_judged reviewed row family hRow
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation judged)

/-! ### Exact original-observation recovery, row by row -/

theorem decodeNativeRow_general_absoluteConfiguration
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.general .absoluteConfiguration) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .absoluteConfiguration).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.general
      .absoluteConfiguration).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.general .absoluteConfiguration) .general hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.general (.absolute observation)) := by
  rw [decodeNativeRow_packNativeRow_tag, translateTo_general_absoluteConfiguration]

theorem decodeNativeRow_general_relativeConfiguration
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.general .relativeConfiguration) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .relativeConfiguration).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.general
      .relativeConfiguration).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.general .relativeConfiguration) .general hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.general (.relative observation)) := by
  rw [decodeNativeRow_packNativeRow_tag, translateTo_general_relativeConfiguration]

theorem decodeNativeRow_general_mixedAbsoluteRelativeConfiguration
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.general .mixedAbsoluteRelativeConfiguration) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .mixedAbsoluteRelativeConfiguration).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.general
      .mixedAbsoluteRelativeConfiguration).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.general .mixedAbsoluteRelativeConfiguration) .general hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.general (.mixedAbsoluteRelative observation)) := by
  rw [decodeNativeRow_packNativeRow_tag,
    translateTo_general_mixedAbsoluteRelativeConfiguration]

theorem decodeNativeRow_general_racemates
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.general .racemates) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .racemates).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.general
      .racemates).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.general .racemates) .general hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.general (.racemate observation)) := by
  rw [decodeNativeRow_packNativeRow_tag, translateTo_general_racemates]

theorem decodeNativeRow_general_ambo
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.general .ambo) = some .general)
    (observation : ((Remaining71P93ClosedProductionRow.general
      .ambo).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.general
      .ambo).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.general .ambo) .general hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.general (.ambo observation)) := by
  rw [decodeNativeRow_packNativeRow_tag, translateTo_general_ambo]

theorem decodeNativeRow_fullerene_inherentParentChirality
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.fullerene .inherentParentChirality) = some .handed)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .inherentParentChirality).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.fullerene
      .inherentParentChirality).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.fullerene .inherentParentChirality) .handed hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.handed observation) := by
  rw [decodeNativeRow_packNativeRow_tag, translateTo_fullerene_inherentParentChirality]

theorem decodeNativeRow_fullerene_inherentSubstitutionChirality
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.fullerene .inherentSubstitutionChirality) = some .handed)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .inherentSubstitutionChirality).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.fullerene
      .inherentSubstitutionChirality).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.fullerene .inherentSubstitutionChirality) .handed hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.handed observation) := by
  rw [decodeNativeRow_packNativeRow_tag, translateTo_fullerene_inherentSubstitutionChirality]

theorem decodeNativeRow_fullerene_noninherentSubstitutionChirality
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.fullerene .noninherentSubstitutionChirality) = some .handed)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .noninherentSubstitutionChirality).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.fullerene
      .noninherentSubstitutionChirality).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.fullerene .noninherentSubstitutionChirality) .handed hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.handed observation) := by
  rw [decodeNativeRow_packNativeRow_tag,
    translateTo_fullerene_noninherentSubstitutionChirality]

theorem decodeNativeRow_fullerene_chiralSubstituents
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.fullerene .chiralSubstituents) = some .type4)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .chiralSubstituents).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.fullerene
      .chiralSubstituents).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.fullerene .chiralSubstituents) .type4 hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.type4 observation) := by
  rw [decodeNativeRow_packNativeRow_tag, translateTo_fullerene_chiralSubstituents]

theorem decodeNativeRow_fullerene_superimposedStereogenicElements
    (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (hRow : rowFamily (.fullerene .superimposedStereogenicElements) = some .superimposed)
    (observation : ((Remaining71P93ClosedProductionRow.fullerene
      .superimposedStereogenicElements).reference reviewed).Observation)
    (judged : ((Remaining71P93ClosedProductionRow.fullerene
      .superimposedStereogenicElements).reference reviewed).Judges
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation) :
    rawEntryFamily? reviewed core enumeration
      ((decodeNativeRow reviewed core enumeration
        (packNativeRow reviewed core enumeration source_well_formed
          (.fullerene .superimposedStereogenicElements) .superimposed hRow observation judged) :
            RawAt reviewed core enumeration)) =
      some (.superimposed observation) := by
  rw [decodeNativeRow_packNativeRow_tag,
    translateTo_fullerene_superimposedStereogenicElements]

/-! ## Geometry preservation for the fullerene families -/

/-- A translated relational-fullerene observation carries the actual variant validity of the
family, recovered from its tagged source projection. -/
theorem SourceRemainingFamily.toVariant_judged (reviewed : Remaining71ReviewedPolicies)
    (translation : SourceRemainingFamily reviewed)
    (variant : SourceRelationalVariantObservation reviewed.p93Cyclic.relationalFullerene)
    (hvariant : translation.toVariant = some variant)
    (source : AuthoritativeChemicalInput)
    (judged : translation.Judged source) :
    variant.ValidFor source := by
  cases translation with
  | general o => simp [SourceRemainingFamily.toVariant] at hvariant
  | handed o =>
      simp only [SourceRemainingFamily.toVariant, Option.some.injEq] at hvariant
      cases hvariant
      exact judged
  | type4 o =>
      simp only [SourceRemainingFamily.toVariant, Option.some.injEq] at hvariant
      cases hvariant
      exact judged
  | superimposed o =>
      simp only [SourceRemainingFamily.toVariant, Option.some.injEq] at hvariant
      cases hvariant
      exact judged

/-- The spatial channel of a translated fullerene observation is exactly the encoded optional
spatial channel of the common reconstructed source.  This is derived from the actual tagged
`ValidFor` and the common physical-frame binding; absence and presence are both preserved. -/
theorem SourceRemainingFamily.spatial?_eq_common (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (translation : SourceRemainingFamily reviewed)
    (variant : SourceRelationalVariantObservation reviewed.p93Cyclic.relationalFullerene)
    (hvariant : translation.toVariant = some variant)
    (valid : variant.ValidFor
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration)) :
    translation.spatial? =
      OrganicFiniteSource.encodeSpatial? enumeration
        (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource core).spatial? := by
  cases translation with
  | general o => simp [SourceRemainingFamily.toVariant] at hvariant
  | handed o =>
      simp only [SourceRemainingFamily.toVariant, Option.some.injEq] at hvariant
      cases hvariant
      exact SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
        (commonBinding core enumeration source_well_formed) (.handed o) valid
  | type4 o =>
      simp only [SourceRemainingFamily.toVariant, Option.some.injEq] at hvariant
      cases hvariant
      exact SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
        (commonBinding core enumeration source_well_formed) (.type4 o) valid
  | superimposed o =>
      simp only [SourceRemainingFamily.toVariant, Option.some.injEq] at hvariant
      cases hvariant
      exact SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
        (commonBinding core enumeration source_well_formed) (.superimposed o) valid

/-- Geometry preservation for an admitted remaining row: the translated observation's spatial
channel is exactly the common source's encoded optional spatial channel. -/
theorem translateTo_spatial?_of_judged (reviewed : Remaining71ReviewedPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed :
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration).StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow) (family : RemainingFamily)
    (hRow : rowFamily row = some family)
    (observation : (row.reference reviewed).Observation)
    (judged : (row.reference reviewed).Judges
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation)
    (variant : SourceRelationalVariantObservation reviewed.p93Cyclic.relationalFullerene)
    (hvariant : (translateTo reviewed row family hRow observation).toVariant = some variant) :
    (translateTo reviewed row family hRow observation).spatial? =
      OrganicFiniteSource.encodeSpatial? enumeration
        (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource core).spatial? :=
  SourceRemainingFamily.spatial?_eq_common reviewed core enumeration source_well_formed
    (translateTo reviewed row family hRow observation) variant hvariant
    (SourceRemainingFamily.toVariant_judged reviewed
      (translateTo reviewed row family hRow observation) variant hvariant
      (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration)
      (translateTo_judged reviewed row family hRow
        (OrganicStereoAllAuthorityEntries.recoveredSource core enumeration) observation judged))

end OrganicStereoP93RemainingNativeRowAdmission

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.rowFamily_none_iff_stableSupported
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.rowFamily_excludedRows
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.translateTo_judged
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.translateTo_tag
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.translateTo_boundedIn_of_judged
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.rawEntryFamily?_toRawEntry
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_packNativeRow
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_packNativeRow_tag
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.packNativeRow_reconstructedSource_general
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.packNativeRow_reconstructedSource_variant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_general_absoluteConfiguration
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_general_relativeConfiguration
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_general_mixedAbsoluteRelativeConfiguration
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_general_racemates
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_general_ambo
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_fullerene_inherentParentChirality
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_fullerene_inherentSubstitutionChirality
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_fullerene_noninherentSubstitutionChirality
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_fullerene_chiralSubstituents
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93RemainingNativeRowAdmission.decodeNativeRow_fullerene_superimposedStereogenicElements
