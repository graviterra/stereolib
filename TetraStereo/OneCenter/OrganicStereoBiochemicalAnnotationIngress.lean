import TetraStereo.KernelOnly
import TetraStereo.OneCenter.AminoAcidPeptideStereochemistrySemantics
import TetraStereo.OneCenter.NucleicAcidStereochemistrySemantics
import TetraStereo.OneCenter.OrganicStereoSpecialistAnnotations
import TetraStereo.OneCenter.OrganicStereoResidueLinkAnnotations

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter

open AminoAcidPeptide1983
open NucleicAcid1970

/-!
# Biochemical per-instance source-record ingress

This module is the amino-acid/peptide and nucleic-acid leaf of the per-instance source-data
ingress.  It stores *actual* existing source payload types -- `AlphaConfiguration`,
`PartiallyKnownConfiguration`, `CenterDescriptor`, `ResidueConfiguration`,
`FischerRosanoffProjection`, `BaseKind`, `ExplicitNucleosideFacts` and directly supplied
`ResolvedNucleosideFacts` -- beside real `V` atom references.  It does not classify a molecule,
does not interpret names, and does not derive a desired stereochemical result.

The `V`-indexed datum below is the leaf's exact per-instance source channel.  Its shared-carrier
image is defined constructor for constructor (`toFragmentSourceData`), and it is attached to the
extended `FragmentAnnotation.sourceData` channel only by appending (`attachSourceData`).  The
fragment's support, ordered bindings and pre-existing source data are never replaced.

Key exactness properties proved here:

* `sourceView` is a source-independent readback of every original field and source locant;
  relabelling atoms does not change it.
* `atomReferences` contains only genuine `V` atoms; natural-number source locants are a separate
  channel (`sourceLocants`), never coerced to atoms.
* `BiochemicalSourceIngress.sourceData_supported` binds every atom reference to an actual atom of
  the carrying fragment's support, including every atom-bearing center.
* `ResidueConfiguration.ambo` and `.unknown` are kept distinct even though they expand to the same
  pair of enantiomers.
* A default nucleoside resolution retains the explicit fact record and `BaseKind`, and recovers
  `resolveNucleosideFacts` as a separate observable equation.  No explicit record is replaced by
  the default it induces.

## Completion scope: the ledger-bound output channel

The decisive lossless ingress is in `LedgerIngress` (`section OutputIngress`), not in the
provisional per-instance wrapper above.  There, the actual source locants are resolved through
the actual residue incidence ledger (`resolveAnchor?`), the payloads are emitted as ordered
`FragmentSourceDatum` lists on the isolated per-residue `sourceData` suffix of a
`ResidueLedgerAnnotation`, and the original payloads are recovered from the produced annotation
alone:

* `partialConfigurationReadback_encodePartialConfiguration` recovers the exact ordered
  `PartiallyKnownConfiguration.descriptors` list, preserving duplicates, order and the empty
  list.  The old `aminoPartialConfiguration -> []` wrapper image is *not* used for this claim.
* `peptideSequenceReadback_encodePeptideSequence` recovers the exact ordered
  `List ResidueConfiguration` from the ordered actual residue occurrences.
* `aminoAlphaReadback_encodeAminoAlpha`, `aminoCenterReadback_encodeAminoCenter` and
  `aminoFischerReadback_encodeAminoFischer` recover the exact source record, with the atom
  anchor obtained only by resolving the printed locant in the actual ledger.
* `nucleosideExplicitReadback_encodeNucleosideExplicit`,
  `nucleosideResolvedReadback_encodeNucleosideResolved` and
  `nucleosideDefaultResolutionReadback_encodeNucleosideDefaultResolution` recover the
  explicit/resolved records, and the default case recomputes `resolveNucleosideFacts` from the
  recovered explicit facts.
-/

namespace BiochemicalAnnotationIngress

/-! ## Amino-acid and peptide per-instance source records -/

/-- One alpha-carbon source record: its actual atom reference and the actual source
configuration. -/
structure AminoAlphaSourceRecord (V : Type*) where
  center : V
  configuration : AlphaConfiguration
  deriving DecidableEq, Repr

/-- One non-alpha (or uniformly described) center record.  `sourceLocant` is the source's own
natural-number locant; it is *not* an atom reference. -/
structure AminoCenterSourceRecord (V : Type*) where
  center : V
  sourceLocant : Nat
  descriptor : CenterDescriptor
  deriving DecidableEq, Repr

/-- A partially known configuration is preserved as its ordered descriptor list, with source
locants and ordered duplication exactly as supplied. -/
structure AminoPartialConfigurationSourceRecord where
  configuration : PartiallyKnownConfiguration
  deriving DecidableEq, Repr

/-- One peptide residue mark. -/
structure PeptideResidueSourceRecord where
  configuration : ResidueConfiguration
  deriving DecidableEq, Repr

/-- Ordered peptide residue marks.  Order, multiplicity and the distinction between adjacent
marks are retained because this is a genuine list. -/
structure PeptideSequenceSourceRecord where
  residues : List ResidueConfiguration
  deriving DecidableEq, Repr

/-- One alpha-center Fischer/Rosanoff projection, including non-canonical projections. -/
structure AminoFischerSourceRecord (V : Type*) where
  center : V
  projection : FischerRosanoffProjection
  deriving DecidableEq, Repr

/-! ## Nucleic-acid per-instance source records -/

/-- Explicitly supplied nucleoside facts together with the actual base kind used for defaults. -/
structure NucleosideExplicitSourceRecord where
  baseKind : BaseKind
  explicit : ExplicitNucleosideFacts
  deriving DecidableEq, Repr

/-- A directly supplied resolved nucleoside fact record.  This is source data, not a value
produced by this module. -/
structure NucleosideResolvedSourceRecord where
  resolved : ResolvedNucleosideFacts
  deriving DecidableEq, Repr

/-- The result of applying the source's field-by-field defaults while retaining the explicit
record that was supplied.  `resolved` is computed by `resolveNucleosideFacts`; the equation field
records that fact and is never an assumed desired output. -/
structure NucleosideDefaultResolution where
  baseKind : BaseKind
  explicit : ExplicitNucleosideFacts
  resolved : ResolvedNucleosideFacts
  resolved_eq : resolved = resolveNucleosideFacts baseKind explicit

/-- Build the default resolution of an explicit record.  This is the only constructor intended
for defaulting; the explicit record is passed through unchanged. -/
def canonicalDefaultResolution (baseKind : BaseKind) (explicit : ExplicitNucleosideFacts) :
    NucleosideDefaultResolution where
  baseKind := baseKind
  explicit := explicit
  resolved := resolveNucleosideFacts baseKind explicit
  resolved_eq := rfl

@[simp] theorem canonicalDefaultResolution_baseKind (baseKind : BaseKind)
    (explicit : ExplicitNucleosideFacts) :
    (canonicalDefaultResolution baseKind explicit).baseKind = baseKind := rfl

@[simp] theorem canonicalDefaultResolution_explicit (baseKind : BaseKind)
    (explicit : ExplicitNucleosideFacts) :
    (canonicalDefaultResolution baseKind explicit).explicit = explicit := rfl

@[simp] theorem canonicalDefaultResolution_resolved (baseKind : BaseKind)
    (explicit : ExplicitNucleosideFacts) :
    (canonicalDefaultResolution baseKind explicit).resolved =
      resolveNucleosideFacts baseKind explicit := rfl

/-! ## Source-independent readback views -/

/-- A `V`-independent view of one source datum.  Every original field and every source locant is
present; the arbitrary atom labels are deliberately absent. -/
inductive BiochemicalSourceView where
  | aminoAlpha (configuration : AlphaConfiguration)
  | aminoCenter (sourceLocant : Nat) (descriptor : CenterDescriptor)
  | aminoPartialConfiguration (configuration : PartiallyKnownConfiguration)
  | peptideResidue (configuration : ResidueConfiguration)
  | peptideSequence (residues : List ResidueConfiguration)
  | aminoFischer (projection : FischerRosanoffProjection)
  | nucleosideExplicit (baseKind : BaseKind) (explicit : ExplicitNucleosideFacts)
  | nucleosideResolved (resolved : ResolvedNucleosideFacts)
  | nucleosideDefaultResolution (baseKind : BaseKind) (explicit : ExplicitNucleosideFacts)
      (resolved : ResolvedNucleosideFacts)
  deriving DecidableEq, Repr

/-! ## The closed biochemical source datum -/

/-- One biochemical per-instance source datum, indexed only by the atom-reference type `V`. -/
inductive BiochemicalSourceDatum (V : Type*) where
  | aminoAlpha (record : AminoAlphaSourceRecord V)
  | aminoCenter (record : AminoCenterSourceRecord V)
  | aminoPartialConfiguration (record : AminoPartialConfigurationSourceRecord)
  | peptideResidue (record : PeptideResidueSourceRecord)
  | peptideSequence (record : PeptideSequenceSourceRecord)
  | aminoFischer (record : AminoFischerSourceRecord V)
  | nucleosideExplicit (record : NucleosideExplicitSourceRecord)
  | nucleosideResolved (record : NucleosideResolvedSourceRecord)
  | nucleosideDefaultResolution (record : NucleosideDefaultResolution)

namespace BiochemicalSourceDatum

variable {V W U : Type*}

/-! ### Atom references and source locants -/

/-- The genuine `V` atom references of a datum.  Natural-number source locants never occur here. -/
def atomReferences : BiochemicalSourceDatum V → List V
  | .aminoAlpha record => [record.center]
  | .aminoCenter record => [record.center]
  | .aminoPartialConfiguration _ => []
  | .peptideResidue _ => []
  | .peptideSequence _ => []
  | .aminoFischer record => [record.center]
  | .nucleosideExplicit _ => []
  | .nucleosideResolved _ => []
  | .nucleosideDefaultResolution _ => []

@[simp] theorem atomReferences_aminoAlpha (record : AminoAlphaSourceRecord V) :
    (aminoAlpha record).atomReferences = [record.center] := rfl

@[simp] theorem atomReferences_aminoCenter (record : AminoCenterSourceRecord V) :
    (aminoCenter record).atomReferences = [record.center] := rfl

@[simp] theorem atomReferences_aminoFischer (record : AminoFischerSourceRecord V) :
    (aminoFischer record).atomReferences = [record.center] := rfl

@[simp] theorem atomReferences_aminoPartialConfiguration
    (record : AminoPartialConfigurationSourceRecord) :
    (BiochemicalSourceDatum.aminoPartialConfiguration record : BiochemicalSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_peptideResidue (record : PeptideResidueSourceRecord) :
    (BiochemicalSourceDatum.peptideResidue record : BiochemicalSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_peptideSequence (record : PeptideSequenceSourceRecord) :
    (BiochemicalSourceDatum.peptideSequence record : BiochemicalSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_nucleosideExplicit
    (record : NucleosideExplicitSourceRecord) :
    (BiochemicalSourceDatum.nucleosideExplicit record : BiochemicalSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_nucleosideResolved
    (record : NucleosideResolvedSourceRecord) :
    (BiochemicalSourceDatum.nucleosideResolved record : BiochemicalSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_nucleosideDefaultResolution
    (record : NucleosideDefaultResolution) :
    (BiochemicalSourceDatum.nucleosideDefaultResolution record : BiochemicalSourceDatum V).atomReferences = [] := rfl

/-- The source's own ordered natural-number locants.  These are source metadata, not atoms. -/
def sourceLocants : BiochemicalSourceDatum V → List Nat
  | .aminoAlpha _ => []
  | .aminoCenter record => [record.sourceLocant]
  | .aminoPartialConfiguration record =>
      record.configuration.descriptors.map (fun entry => entry.1)
  | .peptideResidue _ => []
  | .peptideSequence _ => []
  | .aminoFischer _ => []
  | .nucleosideExplicit _ => []
  | .nucleosideResolved _ => []
  | .nucleosideDefaultResolution _ => []

@[simp] theorem sourceLocants_aminoCenter (record : AminoCenterSourceRecord V) :
    (aminoCenter record).sourceLocants = [record.sourceLocant] := rfl

@[simp] theorem sourceLocants_aminoPartialConfiguration
    (record : AminoPartialConfigurationSourceRecord) :
    (BiochemicalSourceDatum.aminoPartialConfiguration record : BiochemicalSourceDatum V).sourceLocants =
      record.configuration.descriptors.map (fun entry => entry.1) := rfl

@[simp] theorem sourceLocants_aminoAlpha (record : AminoAlphaSourceRecord V) :
    (aminoAlpha record).sourceLocants = [] := rfl

@[simp] theorem sourceLocants_aminoFischer (record : AminoFischerSourceRecord V) :
    (aminoFischer record).sourceLocants = [] := rfl

/-! ### Source-independent readback -/

/-- Read back every original field and locant, independently of `V`. -/
def sourceView : BiochemicalSourceDatum V → BiochemicalSourceView
  | .aminoAlpha record => .aminoAlpha record.configuration
  | .aminoCenter record => .aminoCenter record.sourceLocant record.descriptor
  | .aminoPartialConfiguration record => .aminoPartialConfiguration record.configuration
  | .peptideResidue record => .peptideResidue record.configuration
  | .peptideSequence record => .peptideSequence record.residues
  | .aminoFischer record => .aminoFischer record.projection
  | .nucleosideExplicit record => .nucleosideExplicit record.baseKind record.explicit
  | .nucleosideResolved record => .nucleosideResolved record.resolved
  | .nucleosideDefaultResolution record =>
      .nucleosideDefaultResolution record.baseKind record.explicit record.resolved

@[simp] theorem sourceView_aminoAlpha (record : AminoAlphaSourceRecord V) :
    (aminoAlpha record).sourceView = .aminoAlpha record.configuration := rfl

@[simp] theorem sourceView_aminoCenter (record : AminoCenterSourceRecord V) :
    (aminoCenter record).sourceView =
      .aminoCenter record.sourceLocant record.descriptor := rfl

@[simp] theorem sourceView_aminoPartialConfiguration
    (record : AminoPartialConfigurationSourceRecord) :
    (BiochemicalSourceDatum.aminoPartialConfiguration record : BiochemicalSourceDatum V).sourceView =
      .aminoPartialConfiguration record.configuration := rfl

@[simp] theorem sourceView_peptideResidue (record : PeptideResidueSourceRecord) :
    (BiochemicalSourceDatum.peptideResidue record : BiochemicalSourceDatum V).sourceView = .peptideResidue record.configuration := rfl

@[simp] theorem sourceView_peptideSequence (record : PeptideSequenceSourceRecord) :
    (BiochemicalSourceDatum.peptideSequence record : BiochemicalSourceDatum V).sourceView = .peptideSequence record.residues := rfl

@[simp] theorem sourceView_aminoFischer (record : AminoFischerSourceRecord V) :
    (aminoFischer record).sourceView = .aminoFischer record.projection := rfl

@[simp] theorem sourceView_nucleosideExplicit (record : NucleosideExplicitSourceRecord) :
    (BiochemicalSourceDatum.nucleosideExplicit record : BiochemicalSourceDatum V).sourceView =
      .nucleosideExplicit record.baseKind record.explicit := rfl

@[simp] theorem sourceView_nucleosideResolved (record : NucleosideResolvedSourceRecord) :
    (BiochemicalSourceDatum.nucleosideResolved record : BiochemicalSourceDatum V).sourceView = .nucleosideResolved record.resolved := rfl

@[simp] theorem sourceView_nucleosideDefaultResolution
    (record : NucleosideDefaultResolution) :
    (BiochemicalSourceDatum.nucleosideDefaultResolution record : BiochemicalSourceDatum V).sourceView =
      .nucleosideDefaultResolution record.baseKind record.explicit record.resolved := rfl

/-! ### Field accessors -/

def alphaConfiguration? : BiochemicalSourceDatum V → Option AlphaConfiguration
  | .aminoAlpha record => some record.configuration
  | _ => none

def aminoCenterSourceLocant? : BiochemicalSourceDatum V → Option Nat
  | .aminoCenter record => some record.sourceLocant
  | _ => none

def aminoCenterDescriptor? : BiochemicalSourceDatum V → Option CenterDescriptor
  | .aminoCenter record => some record.descriptor
  | _ => none

def partiallyKnownConfiguration? : BiochemicalSourceDatum V → Option PartiallyKnownConfiguration
  | .aminoPartialConfiguration record => some record.configuration
  | _ => none

def peptideMark? : BiochemicalSourceDatum V → Option ResidueConfiguration
  | .peptideResidue record => some record.configuration
  | _ => none

def peptideMarks? : BiochemicalSourceDatum V → Option (List ResidueConfiguration)
  | .peptideSequence record => some record.residues
  | _ => none

def fischerProjection? : BiochemicalSourceDatum V → Option FischerRosanoffProjection
  | .aminoFischer record => some record.projection
  | _ => none

def nucleosideExplicitFacts? :
    BiochemicalSourceDatum V → Option (BaseKind × ExplicitNucleosideFacts)
  | .nucleosideExplicit record => some (record.baseKind, record.explicit)
  | .nucleosideDefaultResolution record => some (record.baseKind, record.explicit)
  | _ => none

def nucleosideResolvedFacts? : BiochemicalSourceDatum V → Option ResolvedNucleosideFacts
  | .nucleosideResolved record => some record.resolved
  | .nucleosideDefaultResolution record => some record.resolved
  | _ => none

@[simp] theorem alphaConfiguration?_aminoAlpha (record : AminoAlphaSourceRecord V) :
    (aminoAlpha record).alphaConfiguration? = some record.configuration := rfl

@[simp] theorem aminoCenterSourceLocant?_aminoCenter
    (record : AminoCenterSourceRecord V) :
    (aminoCenter record).aminoCenterSourceLocant? = some record.sourceLocant := rfl

@[simp] theorem aminoCenterDescriptor?_aminoCenter (record : AminoCenterSourceRecord V) :
    (aminoCenter record).aminoCenterDescriptor? = some record.descriptor := rfl

@[simp] theorem partiallyKnownConfiguration?_aminoPartialConfiguration
    (record : AminoPartialConfigurationSourceRecord) :
    (BiochemicalSourceDatum.aminoPartialConfiguration record : BiochemicalSourceDatum V).partiallyKnownConfiguration? =
      some record.configuration := rfl

@[simp] theorem peptideMark?_peptideResidue (record : PeptideResidueSourceRecord) :
    (BiochemicalSourceDatum.peptideResidue record : BiochemicalSourceDatum V).peptideMark? = some record.configuration := rfl

@[simp] theorem peptideMarks?_peptideSequence (record : PeptideSequenceSourceRecord) :
    (BiochemicalSourceDatum.peptideSequence record : BiochemicalSourceDatum V).peptideMarks? = some record.residues := rfl

@[simp] theorem fischerProjection?_aminoFischer (record : AminoFischerSourceRecord V) :
    (aminoFischer record).fischerProjection? = some record.projection := rfl

@[simp] theorem nucleosideExplicitFacts?_nucleosideExplicit
    (record : NucleosideExplicitSourceRecord) :
    (BiochemicalSourceDatum.nucleosideExplicit record : BiochemicalSourceDatum V).nucleosideExplicitFacts? =
      some (record.baseKind, record.explicit) := rfl

@[simp] theorem nucleosideExplicitFacts?_nucleosideDefaultResolution
    (record : NucleosideDefaultResolution) :
    (BiochemicalSourceDatum.nucleosideDefaultResolution record : BiochemicalSourceDatum V).nucleosideExplicitFacts? =
      some (record.baseKind, record.explicit) := rfl

@[simp] theorem nucleosideResolvedFacts?_nucleosideResolved
    (record : NucleosideResolvedSourceRecord) :
    (BiochemicalSourceDatum.nucleosideResolved record : BiochemicalSourceDatum V).nucleosideResolvedFacts? = some record.resolved := rfl

@[simp] theorem nucleosideResolvedFacts?_nucleosideDefaultResolution
    (record : NucleosideDefaultResolution) :
    (BiochemicalSourceDatum.nucleosideDefaultResolution record : BiochemicalSourceDatum V).nucleosideResolvedFacts? = some record.resolved := rfl

/-! ### Atom relabelling -/

/-- Relabel only the `V` atom references; every source field and locant is copied verbatim. -/
def relabel (f : V ≃ W) : BiochemicalSourceDatum V → BiochemicalSourceDatum W
  | .aminoAlpha record => .aminoAlpha ⟨f record.center, record.configuration⟩
  | .aminoCenter record => .aminoCenter ⟨f record.center, record.sourceLocant, record.descriptor⟩
  | .aminoPartialConfiguration record => .aminoPartialConfiguration record
  | .peptideResidue record => .peptideResidue record
  | .peptideSequence record => .peptideSequence record
  | .aminoFischer record => .aminoFischer ⟨f record.center, record.projection⟩
  | .nucleosideExplicit record => .nucleosideExplicit record
  | .nucleosideResolved record => .nucleosideResolved record
  | .nucleosideDefaultResolution record => .nucleosideDefaultResolution record

@[simp] theorem atomReferences_relabel (f : V ≃ W) (datum : BiochemicalSourceDatum V) :
    (datum.relabel f).atomReferences = datum.atomReferences.map f := by
  cases datum <;> simp [BiochemicalSourceDatum.relabel, atomReferences]

@[simp] theorem sourceLocants_relabel (f : V ≃ W) (datum : BiochemicalSourceDatum V) :
    (datum.relabel f).sourceLocants = datum.sourceLocants := by
  cases datum <;> rfl

/-- Relabelling atoms does not change the source-independent readback. -/
@[simp] theorem sourceView_relabel (f : V ≃ W) (datum : BiochemicalSourceDatum V) :
    (datum.relabel f).sourceView = datum.sourceView := by
  cases datum <;> rfl

@[simp] theorem relabel_refl (datum : BiochemicalSourceDatum V) :
    datum.relabel (Equiv.refl V) = datum := by
  cases datum <;> simp [BiochemicalSourceDatum.relabel]

theorem relabel_trans (f : V ≃ W) (g : W ≃ U) (datum : BiochemicalSourceDatum V) :
    (datum.relabel f).relabel g = datum.relabel (f.trans g) := by
  cases datum <;> simp [BiochemicalSourceDatum.relabel, Equiv.trans_apply]

@[simp] theorem relabel_symm_relabel (f : V ≃ W) (datum : BiochemicalSourceDatum V) :
    (datum.relabel f).relabel f.symm = datum := by
  rw [relabel_trans]
  rw [show f.trans f.symm = Equiv.refl V from by ext atom; simp]
  exact relabel_refl datum

theorem relabel_injective (f : V ≃ W) :
    Function.Injective (fun datum : BiochemicalSourceDatum V => datum.relabel f) := by
  intro first second equal
  have inject := congrArg
    (fun datum : BiochemicalSourceDatum W => datum.relabel f.symm) equal
  simpa [relabel_symm_relabel] using inject

/-! ### Consolidated readback theorems -/

/-- Complete readback of an alpha configuration: the source configuration, the accessor and the
actual center reference are all recovered exactly. -/
theorem aminoAlpha_readback (record : AminoAlphaSourceRecord V) :
    (aminoAlpha record).sourceView = .aminoAlpha record.configuration ∧
      (aminoAlpha record).alphaConfiguration? = some record.configuration ∧
      (aminoAlpha record).atomReferences = [record.center] :=
  ⟨rfl, rfl, rfl⟩

/-- Complete readback of a center record: ordered source locant and descriptor are recovered, and
the source locant is kept out of the atom-reference channel. -/
theorem aminoCenter_readback (record : AminoCenterSourceRecord V) :
    (aminoCenter record).sourceView =
        .aminoCenter record.sourceLocant record.descriptor ∧
      (aminoCenter record).aminoCenterSourceLocant? = some record.sourceLocant ∧
      (aminoCenter record).aminoCenterDescriptor? = some record.descriptor ∧
      (aminoCenter record).sourceLocants = [record.sourceLocant] ∧
      (aminoCenter record).atomReferences = [record.center] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Complete readback of an ordered partially-known configuration: the whole descriptor list and
its locant order are recovered verbatim. -/
theorem aminoPartialConfiguration_readback
    (record : AminoPartialConfigurationSourceRecord) :
    (BiochemicalSourceDatum.aminoPartialConfiguration record : BiochemicalSourceDatum V).sourceView =
        .aminoPartialConfiguration record.configuration ∧
      (BiochemicalSourceDatum.aminoPartialConfiguration record : BiochemicalSourceDatum V).partiallyKnownConfiguration? =
        some record.configuration ∧
      (BiochemicalSourceDatum.aminoPartialConfiguration record : BiochemicalSourceDatum V).sourceLocants =
        record.configuration.descriptors.map (fun entry => entry.1) ∧
      (BiochemicalSourceDatum.aminoPartialConfiguration record : BiochemicalSourceDatum V).atomReferences = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Readback of one peptide residue mark. -/
theorem peptideResidue_readback (record : PeptideResidueSourceRecord) :
    (BiochemicalSourceDatum.peptideResidue record : BiochemicalSourceDatum V).sourceView = .peptideResidue record.configuration ∧
      (BiochemicalSourceDatum.peptideResidue record : BiochemicalSourceDatum V).peptideMark? = some record.configuration :=
  ⟨rfl, rfl⟩

/-- Readback of ordered peptide marks: the list is recovered with the same order and
multiplicity. -/
theorem peptideSequence_readback (record : PeptideSequenceSourceRecord) :
    (BiochemicalSourceDatum.peptideSequence record : BiochemicalSourceDatum V).sourceView = .peptideSequence record.residues ∧
      (BiochemicalSourceDatum.peptideSequence record : BiochemicalSourceDatum V).peptideMarks? = some record.residues :=
  ⟨rfl, rfl⟩

/-- Readback of a Fischer/Rosanoff projection, including a non-canonical one. -/
theorem aminoFischer_readback (record : AminoFischerSourceRecord V) :
    (aminoFischer record).sourceView = .aminoFischer record.projection ∧
      (aminoFischer record).fischerProjection? = some record.projection ∧
      (aminoFischer record).atomReferences = [record.center] :=
  ⟨rfl, rfl, rfl⟩

/-- Readback of explicit nucleoside facts together with their actual `BaseKind`. -/
theorem nucleosideExplicit_readback (record : NucleosideExplicitSourceRecord) :
    (BiochemicalSourceDatum.nucleosideExplicit record : BiochemicalSourceDatum V).sourceView =
        .nucleosideExplicit record.baseKind record.explicit ∧
      (BiochemicalSourceDatum.nucleosideExplicit record : BiochemicalSourceDatum V).nucleosideExplicitFacts? =
        some (record.baseKind, record.explicit) ∧
      (BiochemicalSourceDatum.nucleosideExplicit record : BiochemicalSourceDatum V).nucleosideResolvedFacts? = none :=
  ⟨rfl, rfl, rfl⟩

/-- Readback of directly supplied resolved facts. -/
theorem nucleosideResolved_readback (record : NucleosideResolvedSourceRecord) :
    (BiochemicalSourceDatum.nucleosideResolved record : BiochemicalSourceDatum V).sourceView = .nucleosideResolved record.resolved ∧
      (BiochemicalSourceDatum.nucleosideResolved record : BiochemicalSourceDatum V).nucleosideResolvedFacts? = some record.resolved ∧
      (BiochemicalSourceDatum.nucleosideResolved record : BiochemicalSourceDatum V).nucleosideExplicitFacts? = none :=
  ⟨rfl, rfl, rfl⟩

/-- Readback of a default resolution: explicit facts and `BaseKind` remain readable, the resolved
record is readable separately, and the resolved record is exactly the forward
`resolveNucleosideFacts` result. -/
theorem nucleosideDefaultResolution_readback (record : NucleosideDefaultResolution) :
    (BiochemicalSourceDatum.nucleosideDefaultResolution record : BiochemicalSourceDatum V).nucleosideExplicitFacts? =
        some (record.baseKind, record.explicit) ∧
      (BiochemicalSourceDatum.nucleosideDefaultResolution record : BiochemicalSourceDatum V).nucleosideResolvedFacts? =
        some record.resolved ∧
      record.resolved = resolveNucleosideFacts record.baseKind record.explicit :=
  ⟨rfl, rfl, record.resolved_eq⟩

/-! ### Distinct constructor payloads -/

/-- Whether the datum carries a directly supplied resolved record. -/
def isDirectlyResolved : BiochemicalSourceDatum V → Bool
  | .nucleosideResolved _ => true
  | _ => false

@[simp] theorem isDirectlyResolved_nucleosideExplicit
    (record : NucleosideExplicitSourceRecord) :
    (BiochemicalSourceDatum.nucleosideExplicit record : BiochemicalSourceDatum V).isDirectlyResolved = false := rfl

@[simp] theorem isDirectlyResolved_nucleosideResolved
    (record : NucleosideResolvedSourceRecord) :
    (BiochemicalSourceDatum.nucleosideResolved record : BiochemicalSourceDatum V).isDirectlyResolved = true := rfl

/-- A directly supplied resolution and an explicit record are different source-data cases even if
their resolved fields happen to agree. -/
theorem explicit_and_resolved_payloads_remain_distinct
    (explicitRecord : NucleosideExplicitSourceRecord)
    (resolvedRecord : NucleosideResolvedSourceRecord) :
    (BiochemicalSourceDatum.nucleosideExplicit explicitRecord : BiochemicalSourceDatum V).isDirectlyResolved ≠
      (BiochemicalSourceDatum.nucleosideResolved resolvedRecord : BiochemicalSourceDatum V).isDirectlyResolved := by
  simp

/-! ### Binding to the shared closed carrier

`FragmentSourceDatum V` is the shared carrier owned by `OrganicStereoFragmentSourceData`.  The
constructs that have an exact shared constructor are mapped constructor for constructor.  An
ordered peptide sequence maps to the ordered list of shared `peptideResidue` data, so order,
multiplicity and adjacent marks are retained.

`PartiallyKnownConfiguration` has no shared constructor: its entries retain source locants but no
resolved atom centers, so a conversion would have to invent `V` anchors.  It therefore stays in
this leaf's own source channel and maps to `[]`.  A default nucleoside resolution attaches only the
actual explicit record; the derived `resolveNucleosideFacts` result stays in
`NucleosideDefaultResolution` and is never retyped as source data. -/

/-- The shared-carrier image of one biochemical source datum. -/
def toFragmentSourceData : BiochemicalSourceDatum V → List (FragmentSourceDatum V)
  | .aminoAlpha record => [FragmentSourceDatum.aminoAlpha record.center record.configuration]
  | .aminoCenter record =>
      [FragmentSourceDatum.aminoCenter record.center record.sourceLocant record.descriptor]
  | .aminoPartialConfiguration _ => []
  | .peptideResidue record => [FragmentSourceDatum.peptideResidue record.configuration]
  | .peptideSequence record => record.residues.map FragmentSourceDatum.peptideResidue
  | .aminoFischer record => [FragmentSourceDatum.aminoFischer record.center record.projection]
  | .nucleosideExplicit record =>
      [FragmentSourceDatum.nucleosideExplicit record.baseKind record.explicit]
  | .nucleosideResolved record => [FragmentSourceDatum.nucleosideResolved record.resolved]
  | .nucleosideDefaultResolution record =>
      [FragmentSourceDatum.nucleosideExplicit record.baseKind record.explicit]

@[simp] theorem toFragmentSourceData_aminoAlpha (record : AminoAlphaSourceRecord V) :
    (aminoAlpha record).toFragmentSourceData =
      [FragmentSourceDatum.aminoAlpha record.center record.configuration] := rfl

@[simp] theorem toFragmentSourceData_aminoCenter (record : AminoCenterSourceRecord V) :
    (aminoCenter record).toFragmentSourceData =
      [FragmentSourceDatum.aminoCenter record.center record.sourceLocant record.descriptor] := rfl

@[simp] theorem toFragmentSourceData_aminoPartialConfiguration {V : Type*}
    (record : AminoPartialConfigurationSourceRecord) :
    (BiochemicalSourceDatum.aminoPartialConfiguration record :
        BiochemicalSourceDatum V).toFragmentSourceData = [] := rfl

@[simp] theorem toFragmentSourceData_peptideResidue {V : Type*}
    (record : PeptideResidueSourceRecord) :
    (BiochemicalSourceDatum.peptideResidue record :
        BiochemicalSourceDatum V).toFragmentSourceData =
      [FragmentSourceDatum.peptideResidue record.configuration] := rfl

@[simp] theorem toFragmentSourceData_peptideSequence {V : Type*}
    (record : PeptideSequenceSourceRecord) :
    (BiochemicalSourceDatum.peptideSequence record :
        BiochemicalSourceDatum V).toFragmentSourceData =
      record.residues.map FragmentSourceDatum.peptideResidue := rfl

@[simp] theorem toFragmentSourceData_aminoFischer (record : AminoFischerSourceRecord V) :
    (aminoFischer record).toFragmentSourceData =
      [FragmentSourceDatum.aminoFischer record.center record.projection] := rfl

@[simp] theorem toFragmentSourceData_nucleosideExplicit {V : Type*}
    (record : NucleosideExplicitSourceRecord) :
    (BiochemicalSourceDatum.nucleosideExplicit record :
        BiochemicalSourceDatum V).toFragmentSourceData =
      [FragmentSourceDatum.nucleosideExplicit record.baseKind record.explicit] := rfl

@[simp] theorem toFragmentSourceData_nucleosideResolved {V : Type*}
    (record : NucleosideResolvedSourceRecord) :
    (BiochemicalSourceDatum.nucleosideResolved record :
        BiochemicalSourceDatum V).toFragmentSourceData =
      [FragmentSourceDatum.nucleosideResolved record.resolved] := rfl

/-- A default resolution contributes its actual explicit source record, not its derived
resolution. -/
@[simp] theorem toFragmentSourceData_nucleosideDefaultResolution {V : Type*}
    (record : NucleosideDefaultResolution) :
    (BiochemicalSourceDatum.nucleosideDefaultResolution record :
        BiochemicalSourceDatum V).toFragmentSourceData =
      [FragmentSourceDatum.nucleosideExplicit record.baseKind record.explicit] := rfl

/-- Conversion to the shared carrier never manufactures an atom reference: every anchor of a
produced shared datum was already an anchor of the original leaf datum. -/
theorem atomReferences_subset_of_mem_toFragmentSourceData
    (original : BiochemicalSourceDatum V) {shared : FragmentSourceDatum V}
    (member : shared ∈ original.toFragmentSourceData) :
    shared.atomReferences ⊆ original.atomReferences := by
  cases original with
  | aminoAlpha record =>
      rw [toFragmentSourceData_aminoAlpha, List.mem_singleton] at member
      subst shared
      intro atom found
      simpa using found
  | aminoCenter record =>
      rw [toFragmentSourceData_aminoCenter, List.mem_singleton] at member
      subst shared
      intro atom found
      simpa using found
  | aminoPartialConfiguration record =>
      rw [toFragmentSourceData_aminoPartialConfiguration] at member
      simp at member
  | peptideResidue record =>
      rw [toFragmentSourceData_peptideResidue, List.mem_singleton] at member
      subst shared
      intro atom found
      simp at found
  | peptideSequence record =>
      rw [toFragmentSourceData_peptideSequence] at member
      obtain ⟨residue, _residueMember, rfl⟩ := List.mem_map.mp member
      intro atom found
      simp at found
  | aminoFischer record =>
      rw [toFragmentSourceData_aminoFischer, List.mem_singleton] at member
      subst shared
      intro atom found
      simpa using found
  | nucleosideExplicit record =>
      rw [toFragmentSourceData_nucleosideExplicit, List.mem_singleton] at member
      subst shared
      intro atom found
      simp at found
  | nucleosideResolved record =>
      rw [toFragmentSourceData_nucleosideResolved, List.mem_singleton] at member
      subst shared
      intro atom found
      simp at found
  | nucleosideDefaultResolution record =>
      rw [toFragmentSourceData_nucleosideDefaultResolution, List.mem_singleton] at member
      subst shared
      intro atom found
      simp at found

end BiochemicalSourceDatum

/-! ## The ingress wrapper preserves the common-core fragment channels -/

/-- A fragment annotation plus ordered biochemical source data.  The existing `FragmentAnnotation`
is carried unchanged; the support invariant is an explicit proof obligation, not an assumed
result. -/
structure BiochemicalSourceIngress (V : Type*) where
  annotation : FragmentAnnotation V
  sourceData : List (BiochemicalSourceDatum V)
  sourceData_supported :
    ∀ datum ∈ sourceData, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support

namespace BiochemicalSourceIngress

variable {V W U : Type*}

/-- Wrap an existing fragment annotation and supplied source data. -/
def ofAnnotation (annotation : FragmentAnnotation V)
    (sourceData : List (BiochemicalSourceDatum V))
    (supported : ∀ datum ∈ sourceData,
      ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    BiochemicalSourceIngress V :=
  ⟨annotation, sourceData, supported⟩

@[simp] theorem ofAnnotation_annotation (annotation : FragmentAnnotation V)
    (sourceData : List (BiochemicalSourceDatum V))
    (supported : ∀ datum ∈ sourceData,
      ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    (ofAnnotation annotation sourceData supported).annotation = annotation := rfl

@[simp] theorem ofAnnotation_sourceData (annotation : FragmentAnnotation V)
    (sourceData : List (BiochemicalSourceDatum V))
    (supported : ∀ datum ∈ sourceData,
      ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    (ofAnnotation annotation sourceData supported).sourceData = sourceData := rfl

@[simp] theorem ofAnnotation_support (annotation : FragmentAnnotation V)
    (sourceData : List (BiochemicalSourceDatum V))
    (supported : ∀ datum ∈ sourceData,
      ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    (ofAnnotation annotation sourceData supported).annotation.support = annotation.support := rfl

@[simp] theorem ofAnnotation_bindings (annotation : FragmentAnnotation V)
    (sourceData : List (BiochemicalSourceDatum V))
    (supported : ∀ datum ∈ sourceData,
      ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    (ofAnnotation annotation sourceData supported).annotation.bindings =
      annotation.bindings := rfl

/-- Every source atom reference is an actual atom of the carrying fragment support. -/
theorem atomReferences_mem_support (ingress : BiochemicalSourceIngress V)
    {datum : BiochemicalSourceDatum V} (member : datum ∈ ingress.sourceData)
    {atom : V} (found : atom ∈ datum.atomReferences) :
    atom ∈ ingress.annotation.support :=
  ingress.sourceData_supported datum member atom found

/-- An amino-alpha center is an actual support atom of the carrying fragment. -/
theorem aminoAlpha_center_mem_support (ingress : BiochemicalSourceIngress V)
    (record : AminoAlphaSourceRecord V)
    (member : BiochemicalSourceDatum.aminoAlpha record ∈ ingress.sourceData) :
    record.center ∈ ingress.annotation.support :=
  ingress.atomReferences_mem_support member (by simp)

/-- A center record's atom reference (not its numeric source locant) is an actual support atom. -/
theorem aminoCenter_center_mem_support (ingress : BiochemicalSourceIngress V)
    (record : AminoCenterSourceRecord V)
    (member : BiochemicalSourceDatum.aminoCenter record ∈ ingress.sourceData) :
    record.center ∈ ingress.annotation.support :=
  ingress.atomReferences_mem_support member (by simp)

/-- A Fischer-projection center is an actual support atom. -/
theorem aminoFischer_center_mem_support (ingress : BiochemicalSourceIngress V)
    (record : AminoFischerSourceRecord V)
    (member : BiochemicalSourceDatum.aminoFischer record ∈ ingress.sourceData) :
    record.center ∈ ingress.annotation.support :=
  ingress.atomReferences_mem_support member (by simp)

/-- The ordered, source-independent readback of all source data. -/
def sourceViews (ingress : BiochemicalSourceIngress V) : List BiochemicalSourceView :=
  ingress.sourceData.map BiochemicalSourceDatum.sourceView

@[simp] theorem sourceViews_eq (ingress : BiochemicalSourceIngress V) :
    ingress.sourceViews = ingress.sourceData.map BiochemicalSourceDatum.sourceView := rfl

/-- Relabel only atom references.  Support and scoped bindings of the common core move along the
same equivalence, exactly as `FragmentAnnotation.relabel` dictates. -/
def relabel (f : V ≃ W) (ingress : BiochemicalSourceIngress V) :
    BiochemicalSourceIngress W where
  annotation := ingress.annotation.relabel f
  sourceData := ingress.sourceData.map (BiochemicalSourceDatum.relabel f)
  sourceData_supported := by
    intro datum member atom found
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    have mappedReferences : atom ∈ original.atomReferences.map f := by
      simpa using found
    obtain ⟨sourceAtom, sourceMember, sourceEq⟩ := List.mem_map.mp mappedReferences
    have sourceSupported : sourceAtom ∈ ingress.annotation.support :=
      ingress.sourceData_supported original originalMember sourceAtom sourceMember
    exact Finset.mem_map.mpr ⟨sourceAtom, sourceSupported, by simpa using sourceEq⟩

@[simp] theorem relabel_annotation (f : V ≃ W) (ingress : BiochemicalSourceIngress V) :
    (ingress.relabel f).annotation = ingress.annotation.relabel f := rfl

@[simp] theorem relabel_sourceData (f : V ≃ W) (ingress : BiochemicalSourceIngress V) :
    (ingress.relabel f).sourceData =
      ingress.sourceData.map (BiochemicalSourceDatum.relabel f) := rfl

@[simp] theorem relabel_support (f : V ≃ W) (ingress : BiochemicalSourceIngress V) :
    (ingress.relabel f).annotation.support =
      ingress.annotation.support.map f.toEmbedding := rfl

@[simp] theorem relabel_bindings (f : V ≃ W) (ingress : BiochemicalSourceIngress V) :
    (ingress.relabel f).annotation.bindings =
      ingress.annotation.bindings.map fun binding => (binding.1, binding.2.map f) := rfl

private theorem map_relabel_refl (data : List (BiochemicalSourceDatum V)) :
    data.map (BiochemicalSourceDatum.relabel (Equiv.refl V)) = data := by
  induction data with
  | nil => rfl
  | cons head tail hypothesis =>
      simp [BiochemicalSourceDatum.relabel_refl, hypothesis]

private theorem map_relabel_trans (f : V ≃ W) (g : W ≃ U)
    (data : List (BiochemicalSourceDatum V)) :
    (data.map (BiochemicalSourceDatum.relabel f)).map
        (BiochemicalSourceDatum.relabel g) =
      data.map (BiochemicalSourceDatum.relabel (f.trans g)) := by
  induction data with
  | nil => rfl
  | cons head tail hypothesis =>
      simp only [List.map_cons]
      rw [hypothesis]
      rw [BiochemicalSourceDatum.relabel_trans]

private theorem map_sourceView_relabel (f : V ≃ W)
    (data : List (BiochemicalSourceDatum V)) :
    (data.map (BiochemicalSourceDatum.relabel f)).map
        BiochemicalSourceDatum.sourceView =
      data.map BiochemicalSourceDatum.sourceView := by
  induction data with
  | nil => rfl
  | cons head tail hypothesis =>
      simp [BiochemicalSourceDatum.sourceView_relabel, hypothesis]

/-- Source-independent readback is invariant under atom relabelling. -/
@[simp] theorem sourceViews_relabel (f : V ≃ W) (ingress : BiochemicalSourceIngress V) :
    (ingress.relabel f).sourceViews = ingress.sourceViews := by
  simp only [sourceViews, relabel_sourceData]
  induction ingress.sourceData with
  | nil => rfl
  | cons head tail hypothesis =>
      simp [BiochemicalSourceDatum.sourceView_relabel, hypothesis]

@[ext] theorem ext {first second : BiochemicalSourceIngress V}
    (annotation : first.annotation = second.annotation)
    (sourceData : first.sourceData = second.sourceData) : first = second := by
  obtain ⟨a, d, h⟩ := first
  obtain ⟨a', d', h'⟩ := second
  simp only at annotation sourceData
  subst annotation
  subst sourceData
  rw [show h = h' from Subsingleton.elim h h']

@[simp] theorem relabel_refl (ingress : BiochemicalSourceIngress V) :
    ingress.relabel (Equiv.refl V) = ingress := by
  apply BiochemicalSourceIngress.ext
  · exact FragmentAnnotation.relabel_refl ingress.annotation
  · simp only [relabel_sourceData]
    exact map_relabel_refl ingress.sourceData

theorem relabel_trans (f : V ≃ W) (g : W ≃ U) (ingress : BiochemicalSourceIngress V) :
    (ingress.relabel f).relabel g = ingress.relabel (f.trans g) := by
  apply BiochemicalSourceIngress.ext
  · simp only [relabel_annotation]
    exact FragmentAnnotation.relabel_trans f g ingress.annotation
  · simp only [relabel_sourceData]
    exact map_relabel_trans f g ingress.sourceData

@[simp] theorem relabel_symm_relabel (f : V ≃ W) (ingress : BiochemicalSourceIngress V) :
    (ingress.relabel f).relabel f.symm = ingress := by
  rw [relabel_trans]
  rw [show f.trans f.symm = Equiv.refl V from by ext atom; simp]
  exact relabel_refl ingress

theorem relabel_injective (f : V ≃ W) :
    Function.Injective
      (fun ingress : BiochemicalSourceIngress V => ingress.relabel f) := by
  intro first second equal
  have inject := congrArg
    (fun ingress : BiochemicalSourceIngress W => ingress.relabel f.symm) equal
  simpa [relabel_symm_relabel] using inject

/-! ### Attachment to the shared fragment-annotation carrier

The shared owner's `FragmentAnnotation` carries a `sourceData : List (FragmentSourceDatum V)`
channel.  Attachment below appends the leaf's shared-carrier image after any data the fragment
already carried, so all common-core channels coexist. -/

/-- The shared-carrier data contributed by one ingress: the ordered flat map of the leaf source
data.  A peptide sequence contributes all of its residue marks in order. -/
def sharedSourceData (ingress : BiochemicalSourceIngress V) : List (FragmentSourceDatum V) :=
  ingress.sourceData.flatMap BiochemicalSourceDatum.toFragmentSourceData

/-- Attach the leaf's shared-carrier image to a fragment annotation by appending.

The fragment's support, ordered bindings, pre-existing source data and support invariants are
unchanged.  The shared invariant is discharged from the leaf invariant because conversion never
manufactures an anchor (`atomReferences_subset_of_mem_toFragmentSourceData`). -/
def attachSourceData (ingress : BiochemicalSourceIngress V) : FragmentAnnotation V :=
  ingress.annotation.withSourceData ingress.sharedSourceData (by
    intro datum member atom found
    simp only [sharedSourceData, List.mem_flatMap] at member
    obtain ⟨original, originalMember, datumMember⟩ := member
    exact ingress.sourceData_supported original originalMember atom
      (BiochemicalSourceDatum.atomReferences_subset_of_mem_toFragmentSourceData
        original datumMember found))

@[simp] theorem attachSourceData_support (ingress : BiochemicalSourceIngress V) :
    (attachSourceData ingress).support = ingress.annotation.support := by
  simp [attachSourceData]

@[simp] theorem attachSourceData_bindings (ingress : BiochemicalSourceIngress V) :
    (attachSourceData ingress).bindings = ingress.annotation.bindings := by
  simp [attachSourceData]

@[simp] theorem attachSourceData_sourceData (ingress : BiochemicalSourceIngress V) :
    (attachSourceData ingress).sourceData =
      ingress.annotation.sourceData ++ ingress.sharedSourceData := by
  simp [attachSourceData]

/-- Attachment never overwrites the common core: all pre-existing source data remain, in order, as
a prefix of the attached channel. -/
theorem attachSourceData_preserves_existing (ingress : BiochemicalSourceIngress V) :
    ∃ suffix : List (FragmentSourceDatum V),
      (attachSourceData ingress).sourceData =
        ingress.annotation.sourceData ++ suffix :=
  ⟨ingress.sharedSourceData, attachSourceData_sourceData ingress⟩

/-- The physical channels of the carrying fragment are literally unchanged by attachment. -/
theorem attachSourceData_preserves_physical_channels
    (ingress : BiochemicalSourceIngress V) :
    (attachSourceData ingress).support = ingress.annotation.support ∧
      (attachSourceData ingress).bindings = ingress.annotation.bindings :=
  ⟨attachSourceData_support ingress, attachSourceData_bindings ingress⟩

end BiochemicalSourceIngress

/-! ## Exact semantic distinctions -/

/-- `ambo` and `unknown` have the same finite expansion set. -/
@[simp] theorem ambo_expands_like_unknown :
    expandResidueConfiguration .ambo = expandResidueConfiguration .unknown := rfl

/-- They remain distinct source marks. -/
theorem ambo_ne_unknown : ResidueConfiguration.ambo ≠ ResidueConfiguration.unknown := by
  decide

/-- Equality of expansion sets therefore cannot determine the source mark. -/
theorem expansion_does_not_determine_ambiguity :
    ¬ Function.Injective
      (fun configuration : ResidueConfiguration =>
        expandResidueConfiguration configuration) := by
  intro injective
  exact ambo_ne_unknown (injective ambo_expands_like_unknown)

/-- A direct Boolean discriminator for the two equally expanding marks. -/
def residueMarkIsAmbo : ResidueConfiguration → Bool
  | .ambo => true
  | _ => false

@[simp] theorem residueMarkIsAmbo_ambo : residueMarkIsAmbo .ambo = true := rfl

@[simp] theorem residueMarkIsAmbo_unknown : residueMarkIsAmbo .unknown = false := rfl

/-- The exact distinction is observable even though the expansion sets coincide. -/
theorem ambo_distinguished_even_with_equal_expansion :
    residueMarkIsAmbo .ambo ≠ residueMarkIsAmbo .unknown ∧
      expandResidueConfiguration .ambo = expandResidueConfiguration .unknown :=
  ⟨by decide, rfl⟩

/-- A concrete non-canonical Fischer/Rosanoff projection. -/
def noncanonicalFischerExample : FischerRosanoffProjection :=
  ⟨false, true, true, .left⟩

@[simp] theorem noncanonicalFischerExample_not_canonical :
    noncanonicalFischerExample.isCanonical = false := rfl

/-- A non-canonical projection does not determine a series; it is still retained as source data. -/
theorem noncanonicalFischerExample_has_no_series :
    seriesFromCanonicalFischer noncanonicalFischerExample = none := by
  unfold seriesFromCanonicalFischer
  rw [noncanonicalFischerExample_not_canonical]
  simp

/-- A supplied non-canonical projection is readable back exactly and is not silently assigned a
series. -/
theorem fischer_projection_readback_includes_noncanonical {V : Type*}
    (record : AminoFischerSourceRecord V) (noncanonical : record.projection.isCanonical = false) :
    (BiochemicalSourceDatum.aminoFischer record).sourceView =
        BiochemicalSourceView.aminoFischer record.projection ∧
      seriesFromCanonicalFischer record.projection = none := by
  refine ⟨rfl, ?_⟩
  unfold seriesFromCanonicalFischer
  rw [noncanonical]
  simp

/-- Canonical projections that do determine a series retain that positive reading. -/
@[simp] theorem canonical_left_projection_still_reads_L :
    seriesFromCanonicalFischer ⟨true, true, true, .left⟩ = some .L := rfl

/-! ### Default nucleoside resolution retains the explicit record -/

/-- The resolved record of a default resolution is exactly the forward default computation. -/
@[simp] theorem nucleosideDefaultResolution_resolved_is_default
    (record : NucleosideDefaultResolution) :
    record.resolved = resolveNucleosideFacts record.baseKind record.explicit :=
  record.resolved_eq

/-- Building a default resolution passes the explicit record and the base kind through unchanged,
and recovers `resolveNucleosideFacts` separately. -/
theorem default_resolution_retains_explicit_and_separately_recovers {V : Type*}
    (baseKind : BaseKind) (explicit : ExplicitNucleosideFacts) :
    let record := canonicalDefaultResolution baseKind explicit
    (BiochemicalSourceDatum.nucleosideDefaultResolution record :
        BiochemicalSourceDatum V).nucleosideExplicitFacts? =
        some (baseKind, explicit) ∧
      (BiochemicalSourceDatum.nucleosideDefaultResolution record :
        BiochemicalSourceDatum V).nucleosideResolvedFacts? =
        some (resolveNucleosideFacts baseKind explicit) := by
  refine ⟨rfl, ?_⟩
  simp [canonicalDefaultResolution]

/-- The default computation never replaces the explicit record itself. -/
theorem default_does_not_replace_explicit
    (baseKind : BaseKind) (explicit : ExplicitNucleosideFacts) :
    (canonicalDefaultResolution baseKind explicit).explicit = explicit := rfl

/-- An absent explicit symbol is not the explicit beta symbol. -/
theorem explicit_absence_is_not_the_explicit_beta_symbol :
    ({} : ExplicitNucleosideFacts) ≠
      ({ anomer? := some .beta } : ExplicitNucleosideFacts) := by
  decide

/-- Equal resolved records do not identify the explicit records that produced them: the beta
default and an explicit beta resolve equally, while the supplied records differ. -/
theorem equal_resolution_does_not_identify_explicit_records (baseKind : BaseKind) :
    resolveNucleosideFacts baseKind {} =
        resolveNucleosideFacts baseKind { anomer? := some .beta } ∧
      ({} : ExplicitNucleosideFacts) ≠
        ({ anomer? := some .beta } : ExplicitNucleosideFacts) :=
  ⟨rfl, explicit_absence_is_not_the_explicit_beta_symbol⟩

/-- The same exactness for the D-series default: an explicit D symbol and an absent symbol
resolve equally, but the explicit record is retained distinctly. -/
theorem explicit_D_symbol_retained_despite_default (baseKind : BaseKind) :
    resolveNucleosideFacts baseKind { sugarSeries? := some .D } =
        resolveNucleosideFacts baseKind {} ∧
      ({ sugarSeries? := some .D } : ExplicitNucleosideFacts) ≠ {} := by
  refine ⟨rfl, ?_⟩
  decide

/-- A directly supplied resolution is read back exactly and is a different case from an explicit
record with the same resolved content. -/
theorem directly_supplied_resolution_is_recovered {V : Type*}
    (facts : ResolvedNucleosideFacts) :
    (BiochemicalSourceDatum.nucleosideResolved ⟨facts⟩ :
        BiochemicalSourceDatum V).nucleosideResolvedFacts? = some facts ∧
      (BiochemicalSourceDatum.nucleosideResolved ⟨facts⟩ :
        BiochemicalSourceDatum V).nucleosideExplicitFacts? = none :=
  ⟨rfl, rfl⟩

/-! ## Source-specific ledger ties for atom-anchored biochemical records

The biochemical subset has no ordered-bond constructor: its atom-bearing records are centers
(`aminoAlpha`, `aminoCenter`, `aminoFischer`).  For those records the source-specific tie is not
"some support atom": the printed natural-number locant must resolve through the actual residue
incidence ledger, and the resulting atom is then certified to lie in the actual encoded fragment
support.  Scope-level records (peptide marks and nucleoside facts) have no locant to resolve; their
tie is the actual ledger residue occurrence, and they are recovered through the full annotation
channel, not through the ordinary view that deliberately omits source data. -/

section LedgerBound

variable {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}

/-- A source locant resolved by the actual ledger incidence denotes an atom of the actual encoded
residue support.  This is the certificate used by every atom-anchored record below. -/
theorem resolvedAnchor_mem_encodeFragment_support
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (anchor : V) (cover : List Nat)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    anchor ∈ (encodeFragment codec e (ledger.residue index) cover).support := by
  rw [encodeFragment_support]
  exact resolveAnchor?_mem_support e ledger index locant resolved

/-- An alpha-center record whose atom anchor is the ledger's resolution of its printed locant. -/
def aminoAlphaSourceRecordOfLedger
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (configuration : AlphaConfiguration) (anchor : V)
    (_resolved : resolveAnchor? e ledger index locant = some anchor) :
    AminoAlphaSourceRecord V :=
  { center := anchor, configuration := configuration }

/-- The alpha-center record's atom is tied to the actual encoded residue support. -/
theorem aminoAlphaSourceRecordOfLedger_center_mem
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (configuration : AlphaConfiguration) (anchor : V) (cover : List Nat)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    (aminoAlphaSourceRecordOfLedger e ledger index locant configuration anchor resolved).center ∈
      (encodeFragment codec e (ledger.residue index) cover).support :=
  resolvedAnchor_mem_encodeFragment_support codec e ledger index locant anchor cover resolved

/-- A center record whose atom anchor is the ledger's resolution of its printed locant.  The
natural-number locant itself is retained unchanged. -/
def aminoCenterSourceRecordOfLedger
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (descriptor : CenterDescriptor) (anchor : V)
    (_resolved : resolveAnchor? e ledger index locant = some anchor) :
    AminoCenterSourceRecord V :=
  { center := anchor, sourceLocant := locant, descriptor := descriptor }

/-- The center record's atom is tied to the actual encoded residue support; its source locant is
not retyped as an atom. -/
theorem aminoCenterSourceRecordOfLedger_center_mem
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (descriptor : CenterDescriptor) (anchor : V) (cover : List Nat)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    (aminoCenterSourceRecordOfLedger e ledger index locant descriptor anchor resolved).center ∈
      (encodeFragment codec e (ledger.residue index) cover).support :=
  resolvedAnchor_mem_encodeFragment_support codec e ledger index locant anchor cover resolved

/-- A Fischer/Rosanoff record whose atom anchor is the ledger's resolution of its printed
locant. -/
def aminoFischerSourceRecordOfLedger
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (projection : FischerRosanoffProjection) (anchor : V)
    (_resolved : resolveAnchor? e ledger index locant = some anchor) :
    AminoFischerSourceRecord V :=
  { center := anchor, projection := projection }

/-- The Fischer record's atom is tied to the actual encoded residue support, including when the
projection is non-canonical. -/
theorem aminoFischerSourceRecordOfLedger_center_mem
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (projection : FischerRosanoffProjection) (anchor : V) (cover : List Nat)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    (aminoFischerSourceRecordOfLedger e ledger index locant projection anchor resolved).center ∈
      (encodeFragment codec e (ledger.residue index) cover).support :=
  resolvedAnchor_mem_encodeFragment_support codec e ledger index locant anchor cover resolved

/-- The shared-carrier image of a ledger-bound alpha record satisfies the actual encoded-support
invariant required by `withSourceData`/`encodeWithSourceData`. -/
theorem aminoAlphaSourceRecordOfLedger_sharedData_supported
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (configuration : AlphaConfiguration) (anchor : V) (cover : List Nat)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    ∀ datum ∈ (BiochemicalSourceDatum.aminoAlpha
        (aminoAlphaSourceRecordOfLedger e ledger index locant configuration anchor resolved)).toFragmentSourceData,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (encodeFragment codec e (ledger.residue index) cover).support := by
  intro datum member atom found
  rw [BiochemicalSourceDatum.toFragmentSourceData_aminoAlpha, List.mem_singleton] at member
  subst datum
  simp only [FragmentSourceDatum.atomReferences_aminoAlpha, List.mem_singleton] at found
  subst atom
  exact aminoAlphaSourceRecordOfLedger_center_mem
    codec e ledger index locant configuration anchor cover resolved

/-- The shared-carrier image of a ledger-bound center record satisfies the actual encoded-support
invariant required by `withSourceData`/`encodeWithSourceData`. -/
theorem aminoCenterSourceRecordOfLedger_sharedData_supported
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (descriptor : CenterDescriptor) (anchor : V) (cover : List Nat)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    ∀ datum ∈ (BiochemicalSourceDatum.aminoCenter
        (aminoCenterSourceRecordOfLedger e ledger index locant descriptor anchor resolved)).toFragmentSourceData,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (encodeFragment codec e (ledger.residue index) cover).support := by
  intro datum member atom found
  rw [BiochemicalSourceDatum.toFragmentSourceData_aminoCenter, List.mem_singleton] at member
  subst datum
  simp only [FragmentSourceDatum.atomReferences_aminoCenter, List.mem_singleton] at found
  subst atom
  exact aminoCenterSourceRecordOfLedger_center_mem
    codec e ledger index locant descriptor anchor cover resolved

/-- The shared-carrier image of a ledger-bound Fischer record satisfies the actual encoded-support
invariant required by `withSourceData`/`encodeWithSourceData`, non-canonical projections included. -/
theorem aminoFischerSourceRecordOfLedger_sharedData_supported
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (projection : FischerRosanoffProjection) (anchor : V) (cover : List Nat)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    ∀ datum ∈ (BiochemicalSourceDatum.aminoFischer
        (aminoFischerSourceRecordOfLedger e ledger index locant projection anchor resolved)).toFragmentSourceData,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (encodeFragment codec e (ledger.residue index) cover).support := by
  intro datum member atom found
  rw [BiochemicalSourceDatum.toFragmentSourceData_aminoFischer, List.mem_singleton] at member
  subst datum
  simp only [FragmentSourceDatum.atomReferences_aminoFischer, List.mem_singleton] at found
  subst atom
  exact aminoFischerSourceRecordOfLedger_center_mem
    codec e ledger index locant projection anchor cover resolved

/-- Scope-level biochemical source data have no locant to resolve.  Their source-specific tie is
the actual ledger residue occurrence, and the full annotation/core channel recovers exactly the
data attached at that index.  The ordinary `decodeView?` intentionally omits source data and is not
used here. -/
theorem scopeLevelData_recovered_at_ledger_index
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding)
    (index : Fin ledger.residueCount) :
    ((encodeWithSourceData codec e ledger cover sourceData supported).residue index).sourceData =
      sourceData index :=
  encodeWithSourceData_residue_sourceData codec e ledger cover sourceData supported index

end LedgerBound

/-! ## Output-channel source ingress and output-only readback

The codecs in `LedgerIngress` are stated directly on the shared output type
`ResidueLedgerAnnotation` (the common-graph full annotated ledger used by the shared
source-data/residue-assembly endpoint).  Every record is attached at an *actual* ledger residue
occurrence, and every atom anchor is the ledger resolution of an actual source locant.  Each codec
has an accessor that reads only the produced `ResidueLedgerAnnotation` and recovers the exact source
payload.  These are the completed ingress results of this module; the input-wrapper views in the
sections above are provisional helpers and are never used to claim completion.

In particular:

* an ordered `PartiallyKnownConfiguration` is no longer dropped.  Every `(locant, descriptor)`
  entry is resolved through the actual residue incidence and emitted in order as `.aminoCenter`;
  the output-only accessor recovers the whole ordered list, including duplicates and the empty
  list;
* a peptide sequence is attached one mark per actual ledger residue occurrence in source order;
  the output-only accessor reconstructs the sequence from the ordered occurrences;
* alpha, center and Fischer records resolve their actual printed source locants through the
  ledger; the accessor reads the exact anchor and payload back from the output;
* nucleoside explicit records retain their actual facts, and a default resolution is recomputed
  from the recovered explicit facts by the forward `resolveNucleosideFacts`, not assumed. -/

section OutputIngress

variable {V : Type*} {input : CertifiedAuthoritativeChemicalInput}

namespace LedgerIngress

/-! ### A whole ordered source-data list at one actual residue occurrence -/

/-- Attach a whole ordered source-data list to one actual ledger residue occurrence, leaving every
other occurrence empty.  This is the isolated source-data channel used by the lossless codecs
below: the attached list is exactly the source-data content of that residue, so nothing else can be
confused with it. -/
def residueSourceDataAt {residueCount : Nat} (index : Fin residueCount)
    (data : List (FragmentSourceDatum V)) :
    Fin residueCount → List (FragmentSourceDatum V) :=
  fun other => if other = index then data else []

@[simp] theorem residueSourceDataAt_self {residueCount : Nat} (index : Fin residueCount)
    (data : List (FragmentSourceDatum V)) :
    residueSourceDataAt index data index = data := by
  simp [residueSourceDataAt]

theorem residueSourceDataAt_of_ne {residueCount : Nat} {index other : Fin residueCount}
    (data : List (FragmentSourceDatum V)) (different : other ≠ index) :
    residueSourceDataAt index data other = [] := by
  simp [residueSourceDataAt, different]

/-- The support invariant for the isolated channel: if every anchor of the data belongs to the
actual support of residue `index`, every anchor of the data attached at `index` belongs to the
support of whichever residue occurrence it is read at. -/
theorem residueSourceDataAt_supported
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (index : Fin ledger.residueCount) (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    ∀ other, ∀ datum ∈ residueSourceDataAt index data other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding := by
  intro other datum member atom atomMem
  by_cases h : other = index
  · subst other
    rw [residueSourceDataAt_self] at member
    exact supported datum member atom atomMem
  · rw [residueSourceDataAt_of_ne data h] at member
    simp at member

/-- Encode one already-resolved shared source datum at one actual ledger residue occurrence.  The
caller supplies the anchor-membership certificate for the actual residue support; it is discharged,
never assumed. -/
def encodeSingleDatum (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (datum : FragmentSourceDatum V)
    (supported : ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeWithSourceData codec e ledger cover (residueSourceDataAt index [datum])
    (residueSourceDataAt_supported e ledger index [datum] (by
      intro otherDatum member atom atomMem
      rw [List.mem_singleton] at member
      subst otherDatum
      exact supported atom atomMem))

/-- The encoded residue occurrence carries exactly the one supplied datum. -/
@[simp] theorem encodeSingleDatum_residue_sourceData
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (datum : FragmentSourceDatum V)
    (supported : ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    ((encodeSingleDatum codec e ledger cover index datum supported).residue index).sourceData =
      [datum] := by
  unfold encodeSingleDatum
  rw [encodeWithSourceData_residue_sourceData]
  simp [residueSourceDataAt]

/-! ### Lossless ordered partial configurations

A source `PartiallyKnownConfiguration` is an ordered list of `(Nat locant, CenterDescriptor)`
entries.  The dedicated codec below resolves *every* entry at one actual ledger residue through
`resolveAnchor?` and emits the ordered `.aminoCenter` list as the isolated source-data content of
that residue.  Nothing is dropped: order, multiplicity and the empty list are all preserved, and
the output-only accessor recovers the exact original descriptor list. -/

/-- Resolve every ordered `(locant, descriptor)` entry of a source `PartiallyKnownConfiguration`
through one actual ledger residue, preserving order and multiplicity.  `none` means at least one
printed locant does not resolve at that residue; no anchor is manufactured from a number that is
not an actual ledger entry. -/
def resolvePartialDescriptors? (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount) :
    List (Nat × CenterDescriptor) → Option (List (FragmentSourceDatum V))
  | [] => some []
  | (locant, descriptor) :: rest =>
      match resolveAnchor? e ledger index locant with
      | none => none
      | some center =>
          Option.map
            (fun tail => FragmentSourceDatum.aminoCenter center locant descriptor :: tail)
            (resolvePartialDescriptors? e ledger index rest)

@[simp] theorem resolvePartialDescriptors?_nil
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount) :
    resolvePartialDescriptors? e ledger index [] = some [] := rfl

theorem resolvePartialDescriptors?_cons_none
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (descriptor : CenterDescriptor)
    (rest : List (Nat × CenterDescriptor))
    (unresolved : resolveAnchor? e ledger index locant = none) :
    resolvePartialDescriptors? e ledger index ((locant, descriptor) :: rest) = none := by
  simp [resolvePartialDescriptors?, unresolved]

theorem resolvePartialDescriptors?_cons_some
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount)
    (locant : Nat) (descriptor : CenterDescriptor)
    (rest : List (Nat × CenterDescriptor)) (center : V)
    (resolvedAnchor : resolveAnchor? e ledger index locant = some center)
    (tailData : List (FragmentSourceDatum V))
    (resolvedTail : resolvePartialDescriptors? e ledger index rest = some tailData) :
    resolvePartialDescriptors? e ledger index ((locant, descriptor) :: rest) =
      some (FragmentSourceDatum.aminoCenter center locant descriptor :: tailData) := by
  simp [resolvePartialDescriptors?, resolvedAnchor, resolvedTail]

/-- Every emitted `.aminoCenter` anchor resolves at the actual residue, so it belongs to the actual
encoded residue support. -/
theorem resolvePartialDescriptors?_mem_support
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount) :
    ∀ (entries : List (Nat × CenterDescriptor)) {data : List (FragmentSourceDatum V)},
      resolvePartialDescriptors? e ledger index entries = some data →
      ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue index).support.map e.symm.toEmbedding := by
  intro entries
  induction entries with
  | nil =>
      intro data resolved datum member
      have dataEq : ([] : List (FragmentSourceDatum V)) = data :=
        Option.some.inj (by simpa using resolved)
      rw [← dataEq] at member
      simp at member
  | cons head tail ih =>
      intro data resolved datum member atom atomMem
      obtain ⟨locant, descriptor⟩ := head
      cases resolvedAnchor : resolveAnchor? e ledger index locant with
      | none =>
          rw [resolvePartialDescriptors?_cons_none e ledger index locant descriptor tail
            resolvedAnchor] at resolved
          simp at resolved
      | some center =>
          cases resolvedTail : resolvePartialDescriptors? e ledger index tail with
          | none =>
              simp [resolvePartialDescriptors?, resolvedAnchor, resolvedTail] at resolved
          | some tailData =>
              have dataEq :
                  FragmentSourceDatum.aminoCenter center locant descriptor :: tailData = data :=
                Option.some.inj (by
                  simpa [resolvePartialDescriptors?, resolvedAnchor, resolvedTail] using resolved)
              rw [← dataEq] at member
              simp only [List.mem_cons] at member
              rcases member with same | member
              · subst datum
                simp only [FragmentSourceDatum.atomReferences_aminoCenter,
                  List.mem_singleton] at atomMem
                subst atom
                exact resolveAnchor?_mem_support e ledger index locant resolvedAnchor
              · exact ih resolvedTail datum member atom atomMem

/-- Output-only readback of an ordered partial configuration from a residue's source-data channel.
The list is recovered positionally, so order, duplicates and the empty list are exact.  `none`
means the channel is not an ordered `.aminoCenter` list. -/
def partialConfigurationOfSourceData :
    List (FragmentSourceDatum V) → Option (List (Nat × CenterDescriptor))
  | [] => some []
  | FragmentSourceDatum.aminoCenter _ locant descriptor :: rest =>
      Option.map (fun tail => (locant, descriptor) :: tail)
        (partialConfigurationOfSourceData rest)
  | _ :: _ => none

@[simp] theorem partialConfigurationOfSourceData_nil :
    partialConfigurationOfSourceData ([] : List (FragmentSourceDatum V)) = some [] := rfl

@[simp] theorem partialConfigurationOfSourceData_cons_aminoCenter
    (center : V) (locant : Nat) (descriptor : CenterDescriptor)
    (rest : List (FragmentSourceDatum V)) :
    partialConfigurationOfSourceData
        (FragmentSourceDatum.aminoCenter center locant descriptor :: rest) =
      Option.map (fun tail => (locant, descriptor) :: tail)
        (partialConfigurationOfSourceData rest) := rfl

/-- The output-only accessor strictly inverts the resolution of an ordered partial configuration. -/
theorem partialConfigurationOfSourceData_resolvePartialDescriptors?
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (index : Fin ledger.residueCount) :
    ∀ (entries : List (Nat × CenterDescriptor)) {data : List (FragmentSourceDatum V)},
      resolvePartialDescriptors? e ledger index entries = some data →
      partialConfigurationOfSourceData data = some entries := by
  intro entries
  induction entries with
  | nil =>
      intro data resolved
      have dataEq : ([] : List (FragmentSourceDatum V)) = data :=
        Option.some.inj (by simpa using resolved)
      rw [← dataEq]
      rfl
  | cons head tail ih =>
      intro data resolved
      obtain ⟨locant, descriptor⟩ := head
      cases resolvedAnchor : resolveAnchor? e ledger index locant with
      | none =>
          rw [resolvePartialDescriptors?_cons_none e ledger index locant descriptor tail
            resolvedAnchor] at resolved
          simp at resolved
      | some center =>
          cases resolvedTail : resolvePartialDescriptors? e ledger index tail with
          | none =>
              simp [resolvePartialDescriptors?, resolvedAnchor, resolvedTail] at resolved
          | some tailData =>
              have dataEq :
                  FragmentSourceDatum.aminoCenter center locant descriptor :: tailData = data :=
                Option.some.inj (by
                  simpa [resolvePartialDescriptors?, resolvedAnchor, resolvedTail] using resolved)
              rw [← dataEq]
              rw [partialConfigurationOfSourceData_cons_aminoCenter, ih resolvedTail]
              rfl

/-- The dedicated ledger-bound partial-list ingress.  Every ordered `(locant, descriptor)` entry
is resolved at the actual residue `index` and emitted as a shared `.aminoCenter` datum, in source
order, as the whole isolated source-data content of that residue.  `resolved` is the actual
resolution certificate: an entry whose printed locant does not resolve cannot be encoded, and no
anchor is invented. -/
def encodePartialConfiguration (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (configuration : PartiallyKnownConfiguration)
    (data : List (FragmentSourceDatum V))
    (resolved : resolvePartialDescriptors? e ledger index configuration.descriptors = some data) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeWithSourceData codec e ledger cover (residueSourceDataAt index data)
    (residueSourceDataAt_supported e ledger index data
      (resolvePartialDescriptors?_mem_support e ledger index configuration.descriptors resolved))

/-- The partial-configuration codec emits exactly the resolved ordered list, whole and unaltered. -/
@[simp] theorem encodePartialConfiguration_residue_sourceData
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (configuration : PartiallyKnownConfiguration)
    (data : List (FragmentSourceDatum V))
    (resolved : resolvePartialDescriptors? e ledger index configuration.descriptors = some data) :
    ((encodePartialConfiguration codec e ledger cover index configuration data resolved).residue
      index).sourceData = data := by
  unfold encodePartialConfiguration
  rw [encodeWithSourceData_residue_sourceData]
  simp [residueSourceDataAt]

/-- Output-only readback of an ordered partial configuration: it reads a produced annotation and
nothing from the source side. -/
def partialConfigurationReadback {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option (List (Nat × CenterDescriptor)) :=
  partialConfigurationOfSourceData (annotation.residue index).sourceData

/-- The completed lossless partial-configuration result: every ordered entry, duplicates and the
empty list included, is recovered exactly from the output annotation. -/
@[simp] theorem partialConfigurationReadback_encodePartialConfiguration
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (configuration : PartiallyKnownConfiguration)
    (data : List (FragmentSourceDatum V))
    (resolved : resolvePartialDescriptors? e ledger index configuration.descriptors = some data) :
    partialConfigurationReadback
        (encodePartialConfiguration codec e ledger cover index configuration data resolved)
        index = some configuration.descriptors := by
  unfold partialConfigurationReadback
  rw [encodePartialConfiguration_residue_sourceData]
  exact partialConfigurationOfSourceData_resolvePartialDescriptors? e ledger index
    configuration.descriptors resolved

/-! ### Peptide sequences: one mark per actual residue occurrence -/

/-- The per-occurrence attachment of an ordered peptide sequence: mark `i` is attached at actual
ledger residue occurrence `i`, and every other occurrence is empty.  The bound
`sequence.length ≤ residueCount` is the explicit source-sequence-to-occurrence indexing: each
source mark has its own actual residue occurrence, and no mark is duplicated onto an arbitrary
fragment. -/
def peptideSequenceSourceData (sequence : List ResidueConfiguration)
    {residueCount : Nat} (_bound : sequence.length ≤ residueCount) :
    Fin residueCount → List (FragmentSourceDatum V) :=
  fun index =>
    match sequence[index.val]? with
    | some configuration => [FragmentSourceDatum.peptideResidue configuration]
    | none => []

/-- At a residue occurrence that indexes a source mark, the isolated channel carries exactly that
mark. -/
theorem peptideSequenceSourceData_at
    (sequence : List ResidueConfiguration) {residueCount : Nat}
    (bound : sequence.length ≤ residueCount) (index : Fin residueCount)
    {configuration : ResidueConfiguration} (found : sequence[index.val]? = some configuration) :
    (peptideSequenceSourceData sequence bound index : List (FragmentSourceDatum V)) =
      ([FragmentSourceDatum.peptideResidue configuration] : List (FragmentSourceDatum V)) := by
  unfold peptideSequenceSourceData
  rw [found]

/-- At a residue occurrence beyond the source sequence, the isolated channel is empty. -/
theorem peptideSequenceSourceData_beyond
    (sequence : List ResidueConfiguration) {residueCount : Nat}
    (bound : sequence.length ≤ residueCount) (index : Fin residueCount)
    (beyond : sequence[index.val]? = none) :
    (peptideSequenceSourceData sequence bound index : List (FragmentSourceDatum V)) = [] := by
  unfold peptideSequenceSourceData
  rw [beyond]

/-- The ledger-bound peptide-sequence ingress: mark `i` is attached at the actual residue
occurrence `i`. -/
def encodePeptideSequence (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (sequence : List ResidueConfiguration) (bound : sequence.length ≤ ledger.residueCount) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeWithSourceData codec e ledger cover (peptideSequenceSourceData sequence bound)
    (by
      intro index datum member atom atomMem
      unfold peptideSequenceSourceData at member
      split at member
      · rw [List.mem_singleton] at member
        subst datum
        simp at atomMem
      · simp at member)

/-- The residue marks carried by one source-data channel, in order. -/
def peptideMarksOfSourceData : List (FragmentSourceDatum V) → List ResidueConfiguration
  | [] => []
  | FragmentSourceDatum.peptideResidue configuration :: rest =>
      configuration :: peptideMarksOfSourceData rest
  | _ :: rest => peptideMarksOfSourceData rest

/-- The marks of the ordered source sequence at one natural-number position, as an ordinary
named function so that the codec and the readback lemma share one definition. -/
def peptideMarksAt? (sequence : List ResidueConfiguration) (index : Nat) :
    List ResidueConfiguration :=
  match sequence[index]? with
  | some configuration => [configuration]
  | none => []

@[simp] theorem peptideMarksOfSourceData_peptideSequenceSourceData
    (sequence : List ResidueConfiguration) {residueCount : Nat}
    (bound : sequence.length ≤ residueCount) (index : Fin residueCount) :
    peptideMarksOfSourceData
        (peptideSequenceSourceData sequence bound index : List (FragmentSourceDatum V)) =
      peptideMarksAt? sequence index.val := by
  unfold peptideSequenceSourceData
  cases h : sequence[index.val]? <;> simp [peptideMarksOfSourceData, peptideMarksAt?, h]

/-- Output-only readback: the sequence is reconstructed from the ordered actual residue
occurrences of a produced annotation, never from a single arbitrary fragment. -/
def peptideSequenceReadback {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount) :
    List ResidueConfiguration :=
  (List.finRange residueCount).flatMap fun index =>
    peptideMarksOfSourceData (annotation.residue index).sourceData

/-- Ordered prefix flattening: reading the marks of the first `sequence.length` occurrences of
`finRange n` in order returns the original sequence. -/
theorem finRange_flatMap_peptideMarksAt? (sequence : List ResidueConfiguration) :
    ∀ (n : Nat), sequence.length ≤ n →
      (List.finRange n).flatMap
        (fun index : Fin n => peptideMarksAt? sequence index.val) = sequence := by
  induction sequence with
  | nil =>
      intro n _
      simp [peptideMarksAt?]
  | cons head tail ih =>
      intro n bound
      cases n with
      | zero => exact absurd bound (by simp)
      | succ n =>
          rw [List.finRange_succ]
          rw [List.flatMap_cons, List.flatMap_map]
          have hzero : peptideMarksAt? (head :: tail) (0 : Fin (n + 1)).val = [head] := rfl
          rw [hzero]
          have hshift :
              (fun i : Fin n => peptideMarksAt? (head :: tail) (Fin.succ i).val) =
              (fun i : Fin n => peptideMarksAt? tail i.val) := by
            funext i
            simp only [Fin.val_succ]
            simp [peptideMarksAt?, List.getElem?_cons_succ]
          rw [hshift]
          rw [ih n (by simpa using bound)]
          simp

/-- The completed peptide-sequence result: the exact ordered source sequence is recovered from the
emitted per-occurrence marks. -/
@[simp] theorem peptideSequenceReadback_encodePeptideSequence
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (sequence : List ResidueConfiguration) (bound : sequence.length ≤ ledger.residueCount) :
    peptideSequenceReadback (encodePeptideSequence codec e ledger cover sequence bound) =
      sequence := by
  unfold peptideSequenceReadback encodePeptideSequence
  simp only [encodeWithSourceData_residue_sourceData,
    peptideMarksOfSourceData_peptideSequenceSourceData]
  exact finRange_flatMap_peptideMarksAt? sequence ledger.residueCount bound

/-! ### Alpha, center and Fischer records: resolved source locants and exact readback -/

def aminoAlphaOfSourceData :
    List (FragmentSourceDatum V) → Option (AminoAlphaSourceRecord V)
  | [FragmentSourceDatum.aminoAlpha center configuration] =>
      some ⟨center, configuration⟩
  | _ => none

def aminoCenterOfSourceData :
    List (FragmentSourceDatum V) → Option (AminoCenterSourceRecord V)
  | [FragmentSourceDatum.aminoCenter center locant descriptor] =>
      some ⟨center, locant, descriptor⟩
  | _ => none

def aminoFischerOfSourceData :
    List (FragmentSourceDatum V) → Option (AminoFischerSourceRecord V)
  | [FragmentSourceDatum.aminoFischer center projection] =>
      some ⟨center, projection⟩
  | _ => none

/-- Alpha record whose atom anchor is the actual ledger resolution of the printed source locant. -/
def encodeAminoAlpha (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (locant : Nat)
    (configuration : AlphaConfiguration) (anchor : V)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeSingleDatum codec e ledger cover index
    (FragmentSourceDatum.aminoAlpha anchor configuration)
    (by
      intro atom atomMem
      simp only [FragmentSourceDatum.atomReferences_aminoAlpha, List.mem_singleton] at atomMem
      subst atom
      exact resolveAnchor?_mem_support e ledger index locant resolved)

def aminoAlphaReadback {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option (AminoAlphaSourceRecord V) :=
  aminoAlphaOfSourceData (annotation.residue index).sourceData

@[simp] theorem aminoAlphaReadback_encodeAminoAlpha
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (locant : Nat)
    (configuration : AlphaConfiguration) (anchor : V)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    aminoAlphaReadback
        (encodeAminoAlpha codec e ledger cover index locant configuration anchor resolved)
        index = some ⟨anchor, configuration⟩ := by
  unfold aminoAlphaReadback encodeAminoAlpha
  rw [encodeSingleDatum_residue_sourceData]
  rfl

/-- Center record whose atom anchor is the actual ledger resolution of its printed source locant;
the locant itself remains natural-number source metadata. -/
def encodeAminoCenter (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (locant : Nat)
    (descriptor : CenterDescriptor) (anchor : V)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeSingleDatum codec e ledger cover index
    (FragmentSourceDatum.aminoCenter anchor locant descriptor)
    (by
      intro atom atomMem
      simp only [FragmentSourceDatum.atomReferences_aminoCenter, List.mem_singleton] at atomMem
      subst atom
      exact resolveAnchor?_mem_support e ledger index locant resolved)

def aminoCenterReadback {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option (AminoCenterSourceRecord V) :=
  aminoCenterOfSourceData (annotation.residue index).sourceData

@[simp] theorem aminoCenterReadback_encodeAminoCenter
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (locant : Nat)
    (descriptor : CenterDescriptor) (anchor : V)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    aminoCenterReadback
        (encodeAminoCenter codec e ledger cover index locant descriptor anchor resolved)
        index = some ⟨anchor, locant, descriptor⟩ := by
  unfold aminoCenterReadback encodeAminoCenter
  rw [encodeSingleDatum_residue_sourceData]
  rfl

/-- Fischer/Rosanoff record whose atom anchor is the actual ledger resolution of its printed
source locant.  Non-canonical projections are encoded and recovered without a canonicality
premise. -/
def encodeAminoFischer (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (locant : Nat)
    (projection : FischerRosanoffProjection) (anchor : V)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeSingleDatum codec e ledger cover index
    (FragmentSourceDatum.aminoFischer anchor projection)
    (by
      intro atom atomMem
      simp only [FragmentSourceDatum.atomReferences_aminoFischer, List.mem_singleton] at atomMem
      subst atom
      exact resolveAnchor?_mem_support e ledger index locant resolved)

def aminoFischerReadback {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option (AminoFischerSourceRecord V) :=
  aminoFischerOfSourceData (annotation.residue index).sourceData

@[simp] theorem aminoFischerReadback_encodeAminoFischer
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (locant : Nat)
    (projection : FischerRosanoffProjection) (anchor : V)
    (resolved : resolveAnchor? e ledger index locant = some anchor) :
    aminoFischerReadback
        (encodeAminoFischer codec e ledger cover index locant projection anchor resolved)
        index = some ⟨anchor, projection⟩ := by
  unfold aminoFischerReadback encodeAminoFischer
  rw [encodeSingleDatum_residue_sourceData]
  rfl

/-! ### Nucleoside records: actual facts retained, default resolution recomputed -/

def nucleosideExplicitOfSourceData :
    List (FragmentSourceDatum V) → Option NucleosideExplicitSourceRecord
  | [FragmentSourceDatum.nucleosideExplicit baseKind explicit] =>
      some ⟨baseKind, explicit⟩
  | _ => none

def nucleosideResolvedOfSourceData :
    List (FragmentSourceDatum V) → Option NucleosideResolvedSourceRecord
  | [FragmentSourceDatum.nucleosideResolved resolved] => some ⟨resolved⟩
  | _ => none

/-- Readback of a default resolution: the explicit facts are recovered from the output and the
resolved record is recomputed by the forward `resolveNucleosideFacts`, never assumed. -/
def nucleosideDefaultResolutionOfSourceData :
    List (FragmentSourceDatum V) → Option NucleosideDefaultResolution
  | [FragmentSourceDatum.nucleosideExplicit baseKind explicit] =>
      some (canonicalDefaultResolution baseKind explicit)
  | _ => none

def encodeNucleosideExplicit (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (record : NucleosideExplicitSourceRecord) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeSingleDatum codec e ledger cover index
    (FragmentSourceDatum.nucleosideExplicit record.baseKind record.explicit)
    (by
      intro atom atomMem
      simp at atomMem)

def nucleosideExplicitReadback {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option NucleosideExplicitSourceRecord :=
  nucleosideExplicitOfSourceData (annotation.residue index).sourceData

@[simp] theorem nucleosideExplicitReadback_encodeNucleosideExplicit
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (record : NucleosideExplicitSourceRecord) :
    nucleosideExplicitReadback
        (encodeNucleosideExplicit codec e ledger cover index record) index = some record := by
  unfold nucleosideExplicitReadback encodeNucleosideExplicit
  rw [encodeSingleDatum_residue_sourceData]
  rfl

def encodeNucleosideResolved (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (record : NucleosideResolvedSourceRecord) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeSingleDatum codec e ledger cover index
    (FragmentSourceDatum.nucleosideResolved record.resolved)
    (by
      intro atom atomMem
      simp at atomMem)

def nucleosideResolvedReadback {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option NucleosideResolvedSourceRecord :=
  nucleosideResolvedOfSourceData (annotation.residue index).sourceData

@[simp] theorem nucleosideResolvedReadback_encodeNucleosideResolved
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (record : NucleosideResolvedSourceRecord) :
    nucleosideResolvedReadback
        (encodeNucleosideResolved codec e ledger cover index record) index = some record := by
  unfold nucleosideResolvedReadback encodeNucleosideResolved
  rw [encodeSingleDatum_residue_sourceData]
  rfl

/-- The source default-resolution record is the canonical default of its own explicit facts. -/
@[simp] theorem canonicalDefaultResolution_eta (record : NucleosideDefaultResolution) :
    canonicalDefaultResolution record.baseKind record.explicit = record := by
  obtain ⟨baseKind, explicit, resolved, resolvedEq⟩ := record
  cases resolvedEq
  rfl

/-- The default-resolution ingress attaches only the actual explicit record; the derived
resolution is not retyped as source chemistry. -/
def encodeNucleosideDefaultResolution (codec : LocantCodec Nat)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (record : NucleosideDefaultResolution) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeSingleDatum codec e ledger cover index
    (FragmentSourceDatum.nucleosideExplicit record.baseKind record.explicit)
    (by
      intro atom atomMem
      simp at atomMem)

def nucleosideDefaultResolutionReadback {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option NucleosideDefaultResolution :=
  nucleosideDefaultResolutionOfSourceData (annotation.residue index).sourceData

/-- The completed default-resolution result: the explicit facts are recovered exactly and the
resolved record is the forward default recomputation. -/
@[simp] theorem nucleosideDefaultResolutionReadback_encodeNucleosideDefaultResolution
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (record : NucleosideDefaultResolution) :
    nucleosideDefaultResolutionReadback
        (encodeNucleosideDefaultResolution codec e ledger cover index record) index =
      some record := by
  unfold nucleosideDefaultResolutionReadback encodeNucleosideDefaultResolution
  rw [encodeSingleDatum_residue_sourceData]
  simp only [nucleosideDefaultResolutionOfSourceData]
  rw [canonicalDefaultResolution_eta]

end LedgerIngress

end OutputIngress

end BiochemicalAnnotationIngress

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the decisive readback and distinction results -/

assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.aminoAlpha_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.aminoCenter_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.aminoPartialConfiguration_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.peptideResidue_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.peptideSequence_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.aminoFischer_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.nucleosideExplicit_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.nucleosideResolved_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.nucleosideDefaultResolution_readback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.sourceView_relabel
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.ambo_ne_unknown
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.ambo_distinguished_even_with_equal_expansion
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.expansion_does_not_determine_ambiguity
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.noncanonicalFischerExample_has_no_series
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.fischer_projection_readback_includes_noncanonical
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.default_resolution_retains_explicit_and_separately_recovers
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.default_does_not_replace_explicit
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.equal_resolution_does_not_identify_explicit_records
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.explicit_D_symbol_retained_despite_default
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.aminoAlpha_center_mem_support
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.aminoCenter_center_mem_support
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.aminoFischer_center_mem_support
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.sourceViews_relabel
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.relabel_injective
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.atomReferences_subset_of_mem_toFragmentSourceData
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.toFragmentSourceData_aminoPartialConfiguration
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.toFragmentSourceData_peptideSequence
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.toFragmentSourceData_nucleosideExplicit
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceDatum.toFragmentSourceData_nucleosideDefaultResolution
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.attachSourceData_support
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.attachSourceData_bindings
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.attachSourceData_sourceData
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.attachSourceData_preserves_existing
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.BiochemicalSourceIngress.attachSourceData_preserves_physical_channels
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.resolvedAnchor_mem_encodeFragment_support
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.aminoAlphaSourceRecordOfLedger_center_mem
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.aminoCenterSourceRecordOfLedger_center_mem
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.aminoFischerSourceRecordOfLedger_center_mem
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.aminoAlphaSourceRecordOfLedger_sharedData_supported
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.aminoCenterSourceRecordOfLedger_sharedData_supported
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.aminoFischerSourceRecordOfLedger_sharedData_supported
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.scopeLevelData_recovered_at_ledger_index

/-! ### Ledger-bound output-channel ingress: lossless payload readbacks -/

assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.residueSourceDataAt_self
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.residueSourceDataAt_of_ne
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.residueSourceDataAt_supported
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.encodeSingleDatum_residue_sourceData
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.resolvePartialDescriptors?_nil
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.resolvePartialDescriptors?_cons_none
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.resolvePartialDescriptors?_cons_some
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.resolvePartialDescriptors?_mem_support
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.partialConfigurationOfSourceData_nil
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.partialConfigurationOfSourceData_cons_aminoCenter
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.partialConfigurationOfSourceData_resolvePartialDescriptors?
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.partialConfigurationReadback
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.encodePartialConfiguration_residue_sourceData
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.partialConfigurationReadback_encodePartialConfiguration
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.peptideSequenceSourceData_at
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.peptideSequenceSourceData_beyond
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.peptideMarksOfSourceData_peptideSequenceSourceData
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.finRange_flatMap_peptideMarksAt?
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.peptideSequenceReadback_encodePeptideSequence
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.aminoAlphaReadback_encodeAminoAlpha
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.aminoCenterReadback_encodeAminoCenter
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.aminoFischerReadback_encodeAminoFischer
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.nucleosideExplicitReadback_encodeNucleosideExplicit
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.nucleosideResolvedReadback_encodeNucleosideResolved
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.nucleosideDefaultResolutionReadback_encodeNucleosideDefaultResolution
assert_kernel_only TetraStereo.OneCenter.BiochemicalAnnotationIngress.LedgerIngress.canonicalDefaultResolution_eta
