import TetraStereo.OneCenter.AminoAcidPeptideStereochemistrySemantics
import TetraStereo.OneCenter.NucleicAcidStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateFoundationStereochemistrySemantics
import TetraStereo.OneCenter.LipidStereochemistrySemantics
import TetraStereo.OneCenter.GlycolipidStereochemistrySemantics
import TetraStereo.OneCenter.Retinoid1981ExplicitCenterLabelCatalog
import TetraStereo.OneCenter.Retinoid1981FigureGraphTranscription

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter

/-!
# Closed source-data payloads for organic fragment annotations

This module defines `FragmentSourceDatum V`: the exact, typed representation of the source-level
stereochemical data that specialist recommendations attach to a residue, fragment or named
structure.  `V` is used **only** for atom references into the finite atom language of an existing
fragment/cycle annotation.  Every other field is either an *actual* existing source record from the
independently audited authority-semantics modules, or a natural-number source locant/ID retained as
metadata.

This is a representation of supplied data.  It is not a classifier, it derives no descriptor, it
has no "authorization" or "approval" premise, and no constructor recovers chemistry from a name.
In particular:

* every atom-bearing constructor carries explicit center anchors of type `V`, or ordered bond
  anchors (`source`, `target`) of type `V`;
* source locants and atom IDs stay `Nat` metadata and are never retyped as `V`;
* the payload of a constructor is the literal record already defined by the relevant authority
  module, with all of its own fields (including optional `Option` fields) preserved;
* constructors with no atom anchors have `atomReferences = []`; such a datum is still attached to a
  fragment and inherits the fragment support as its scope.

The constructor groups follow the specialist authorities in scope for the organic assembly:
amino acids/peptides (1983), nucleic acids (1970), carbohydrates (1996), natural/retinoid
configured centers and double bonds (1981), lipids (1976), and glycolipids (1997).

`relabel` moves atom anchors only.  Locants, IDs, payload records, ordering and duplication are
copied verbatim, so relabelling cannot invent or destroy source data.  The relabelling laws
(`refl`, `trans`, both inverse directions and injectivity) are proved below; they are the API the
fragment-annotation layer reuses.

Import discipline: this module depends only on the existing low-level authority-semantics
modules, never on `OrganicStereoSpecialistAnnotations`, `OrganicStereoResidueIncidence` or any
other `OrganicStereo*` module, so it cannot introduce an import cycle.
-/















/-- The horizontal side of a Fischer substituent.  Independent closed copy of the source
enumeration. -/
inductive CarbohydrateFischerHorizontalSide where
  | left | right
  deriving DecidableEq, Repr

/-- The oxygen group at a Fischer substituent.  Independent closed copy of the source
enumeration. -/
inductive CarbohydrateFischerOxygenSubstituent where
  | hydroxy | methoxy | acetoxy
  deriving DecidableEq, Repr

/-- One listed Fischer-chain substituent: printed source locant, oxygen group and horizontal
side.  `locant` is natural-number source metadata, never an atom anchor. -/
structure CarbohydrateFischerSubstituent where
  /-- The printed source locant of the substituent. -/
  locant : Nat
  /-- The oxygen group at that locant. -/
  oxygenGroup : CarbohydrateFischerOxygenSubstituent
  /-- The horizontal side on which the group is drawn. -/
  horizontalSide : CarbohydrateFischerHorizontalSide
  deriving DecidableEq, Repr

/-- A complete supplied Fischer-chain projection record.  Hydrogens opposite the listed horizontal
oxygen groups are implicit.  The fields, their defaults and the ordering/duplication of
`substituents` are retained literally. -/
structure CarbohydrateFischerChainData where
  /-- The number of carbons in the chain. -/
  carbonCount : Nat
  /-- The optional carbonyl locant; `none` records its absence. -/
  carbonylLocant? : Option Nat := none
  /-- The ordered, possibly duplicated, substituent list. -/
  substituents : List CarbohydrateFischerSubstituent
  /-- Whether the chain has hydroxymethyl termini. -/
  hydroxymethylTermini : Bool := true
  deriving DecidableEq, Repr

namespace CarbohydrateFischerSubstituent

/-- The source well-formedness predicate for one substituent, mirrored exactly. -/
def wellFormedFor (substituent : CarbohydrateFischerSubstituent) (carbonCount : Nat) : Bool :=
  1 < substituent.locant && substituent.locant < carbonCount

end CarbohydrateFischerSubstituent

namespace CarbohydrateFischerChainData

/-- The source well-formedness predicate for a whole chain, mirrored exactly. -/
def wellFormed (projection : CarbohydrateFischerChainData) : Bool :=
  decide (2 ≤ projection.carbonCount) &&
    projection.substituents.all
      (CarbohydrateFischerSubstituent.wellFormedFor · projection.carbonCount) &&
    decide (projection.substituents.map CarbohydrateFischerSubstituent.locant).Nodup &&
    match projection.carbonylLocant? with
    | none => true
    | some locant =>
        0 < locant && locant ≤ projection.carbonCount &&
          decide (locant ∉ projection.substituents.map
            CarbohydrateFischerSubstituent.locant)

end CarbohydrateFischerChainData







inductive FragmentSourceDatum (V : Type*) where
  /-- An alpha-carbon D/L (or unknown) configuration.  Anchored at the alpha carbon. -/
  | aminoAlpha (center : V)
      (configuration : AminoAcidPeptide1983.AlphaConfiguration)
  /-- A non-alpha amino-acid center descriptor, with its printed source locant. -/
  | aminoCenter (center : V) (sourceLocant : Nat)
      (descriptor : AminoAcidPeptide1983.CenterDescriptor)
  /-- A residue-local peptide configuration (`exact`, `ambo`, `unknown`).  Scope-level: it names
  no atom, and inherits the enclosing fragment support. -/
  | peptideResidue (configuration : AminoAcidPeptide1983.ResidueConfiguration)
  /-- A Fischer–Rosanoff projection statement, anchored at the projected center. -/
  | aminoFischer (center : V)
      (projection : AminoAcidPeptide1983.FischerRosanoffProjection)
  /-- Explicit (possibly partial) nucleoside facts under a base kind.  Scope-level. -/
  | nucleosideExplicit (base : NucleicAcid1970.BaseKind)
      (facts : NucleicAcid1970.ExplicitNucleosideFacts)
  /-- Resolved nucleoside facts.  Scope-level. -/
  | nucleosideResolved (facts : NucleicAcid1970.ResolvedNucleosideFacts)
  /-- A carbohydrate D/L series statement.  Scope-level. -/
  | carbohydrateSeries (series : Carbohydrate1996Foundation.DLSeries)
  /-- A carbohydrate series-plus-optical-rotation reading.  Scope-level. -/
  | carbohydrateRotation (reading : Carbohydrate1996Foundation.SeriesAndRotation)
  /-- An anomeric knowledge statement.  Scope-level. -/
  | carbohydrateAnomerKnowledge (knowledge : Carbohydrate1996Foundation.AnomerKnowledge)
  /-- An anomeric descriptor with ordered anchors `(anomeric, reference)` and both printed source
  locants retained as metadata. -/
  | carbohydrateAnomer (anomeric : V) (reference : V)
      (anomericSourceLocant : Nat) (referenceSourceLocant : Nat)
      (descriptor : Carbohydrate1996Foundation.AnomerDescriptor)
  /-- A complete 1996 Fischer-chain projection statement with the ordered list of its chain carbon
  anchors.  Unlike the single-centre Fischer constructors, this retains the whole supplied record:
  carbon count, optional carbonyl locant, the ordered (and possibly duplicated) substituent list,
  and the hydroxymethyl-termini flag.  `carbons` is an ordered list, not a set. -/
  | carbohydrateFischerChain (carbons : List V)
      (projection : CarbohydrateFischerChainData)
  /-- An explicit natural-product center label, anchored at the labeled atom.  The source
  `atomId` inside the payload is metadata, not a `V` anchor. -/
  | naturalCenter (center : V)
      (label : Retinoid1981.ExplicitCenterLabelCatalog.LocatedSourceCenterLabel)
  /-- A natural-product double-bond configuration with ordered bond anchors
  `(source, target)`; the claim's own `low`/`high` source IDs are metadata. -/
  | naturalDoubleBond (source : V) (target : V)
      (claim : Retinoid1981.FigureGraphTranscription.DoubleBondConfigurationClaim)
  /-- A lipid reference Fischer projection, anchored at the projected center. -/
  | lipidFischer (center : V) (projection : Lipid1976.ReferenceFischerProjection)
  /-- A lipid knowledge state (`sn` / `rac` / unknown).  Scope-level. -/
  | lipidKnowledge (knowledge : Lipid1976.KnowledgeState)
  /-- A glycerol substitution pattern with ordered anchors `(sn-1, sn-2, sn-3)`. -/
  | lipidGlycerol (first : V) (second : V) (third : V)
      (substitution : Lipid1976.SnGlycerolSubstitution)
  /-- A glycerol CIP reading, anchored at the center; the fixed `sn` locant in the payload is
  metadata. -/
  | lipidCIP (center : V) (reading : Lipid1976.GlycerolCIPReading)
  /-- A full sphingoid configuration record.  Scope-level. -/
  | glycolipidSphingoid (configuration : Glycolipid1997.SphingoidConfiguration)
  /-- A glycolipid center descriptor with its printed source locant. -/
  | glycolipidCenter (center : V) (sourceLocant : Nat) (descriptor : Glycolipid1997.RS)
  /-- A glycolipid double-bond descriptor with ordered bond anchors `(source, target)` and its
  printed source locant metadata. -/
  | glycolipidDoubleBond (source : V) (target : V) (sourceLocant : Nat)
      (descriptor : Glycolipid1997.EZ)
  deriving DecidableEq, Repr

namespace FragmentSourceDatum

variable {V W U : Type*}

/-! ## Atom anchors -/

/-- The atom anchors of one datum, in constructor order.  This is a list, not a set: ordered bond
anchors stay ordered and repeated anchors are not silently deduplicated.  Constructors with no
atom anchors return the empty list; they are scoped by the enclosing fragment support. -/
def atomReferences : FragmentSourceDatum V → List V
  | aminoAlpha center _ => [center]
  | aminoCenter center _ _ => [center]
  | peptideResidue _ => []
  | aminoFischer center _ => [center]
  | nucleosideExplicit _ _ => []
  | nucleosideResolved _ => []
  | carbohydrateSeries _ => []
  | carbohydrateRotation _ => []
  | carbohydrateAnomerKnowledge _ => []
  | carbohydrateAnomer anomeric reference _ _ _ => [anomeric, reference]
  | carbohydrateFischerChain carbons _ => carbons
  | naturalCenter center _ => [center]
  | naturalDoubleBond source target _ => [source, target]
  | lipidFischer center _ => [center]
  | lipidKnowledge _ => []
  | lipidGlycerol first second third _ => [first, second, third]
  | lipidCIP center _ => [center]
  | glycolipidSphingoid _ => []
  | glycolipidCenter center _ _ => [center]
  | glycolipidDoubleBond source target _ _ => [source, target]

/-! ### Exact anchor lists, one equation per constructor -/

@[simp] theorem atomReferences_aminoAlpha (center : V)
    (configuration : AminoAcidPeptide1983.AlphaConfiguration) :
    (aminoAlpha center configuration).atomReferences = [center] := rfl

@[simp] theorem atomReferences_aminoCenter (center : V) (sourceLocant : Nat)
    (descriptor : AminoAcidPeptide1983.CenterDescriptor) :
    (aminoCenter center sourceLocant descriptor).atomReferences = [center] := rfl

@[simp] theorem atomReferences_peptideResidue
    (configuration : AminoAcidPeptide1983.ResidueConfiguration) :
    (peptideResidue configuration : FragmentSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_aminoFischer (center : V)
    (projection : AminoAcidPeptide1983.FischerRosanoffProjection) :
    (aminoFischer center projection).atomReferences = [center] := rfl

@[simp] theorem atomReferences_nucleosideExplicit (base : NucleicAcid1970.BaseKind)
    (facts : NucleicAcid1970.ExplicitNucleosideFacts) :
    (nucleosideExplicit base facts : FragmentSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_nucleosideResolved
    (facts : NucleicAcid1970.ResolvedNucleosideFacts) :
    (nucleosideResolved facts : FragmentSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_carbohydrateSeries
    (series : Carbohydrate1996Foundation.DLSeries) :
    (carbohydrateSeries series : FragmentSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_carbohydrateRotation
    (reading : Carbohydrate1996Foundation.SeriesAndRotation) :
    (carbohydrateRotation reading : FragmentSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_carbohydrateAnomerKnowledge
    (knowledge : Carbohydrate1996Foundation.AnomerKnowledge) :
    (carbohydrateAnomerKnowledge knowledge : FragmentSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_carbohydrateAnomer (anomeric reference : V)
    (anomericSourceLocant referenceSourceLocant : Nat)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor) :
    (carbohydrateAnomer anomeric reference anomericSourceLocant referenceSourceLocant
      descriptor).atomReferences = [anomeric, reference] := rfl

@[simp] theorem atomReferences_carbohydrateFischerChain (carbons : List V)
    (projection : CarbohydrateFischerChainData) :
    (carbohydrateFischerChain carbons projection).atomReferences = carbons := rfl

@[simp] theorem atomReferences_naturalCenter (center : V)
    (label : Retinoid1981.ExplicitCenterLabelCatalog.LocatedSourceCenterLabel) :
    (naturalCenter center label).atomReferences = [center] := rfl

@[simp] theorem atomReferences_naturalDoubleBond (source target : V)
    (claim : Retinoid1981.FigureGraphTranscription.DoubleBondConfigurationClaim) :
    (naturalDoubleBond source target claim).atomReferences = [source, target] := rfl

@[simp] theorem atomReferences_lipidFischer (center : V)
    (projection : Lipid1976.ReferenceFischerProjection) :
    (lipidFischer center projection).atomReferences = [center] := rfl

@[simp] theorem atomReferences_lipidKnowledge (knowledge : Lipid1976.KnowledgeState) :
    (lipidKnowledge knowledge : FragmentSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_lipidGlycerol (first second third : V)
    (substitution : Lipid1976.SnGlycerolSubstitution) :
    (lipidGlycerol first second third substitution).atomReferences = [first, second, third] := rfl

@[simp] theorem atomReferences_lipidCIP (center : V)
    (reading : Lipid1976.GlycerolCIPReading) :
    (lipidCIP center reading).atomReferences = [center] := rfl

@[simp] theorem atomReferences_glycolipidSphingoid
    (configuration : Glycolipid1997.SphingoidConfiguration) :
    (glycolipidSphingoid configuration : FragmentSourceDatum V).atomReferences = [] := rfl

@[simp] theorem atomReferences_glycolipidCenter (center : V) (sourceLocant : Nat)
    (descriptor : Glycolipid1997.RS) :
    (glycolipidCenter center sourceLocant descriptor).atomReferences = [center] := rfl

@[simp] theorem atomReferences_glycolipidDoubleBond (source target : V) (sourceLocant : Nat)
    (descriptor : Glycolipid1997.EZ) :
    (glycolipidDoubleBond source target sourceLocant descriptor).atomReferences =
      [source, target] := rfl

/-! ## Atom relabelling -/

/-- Relabel the atom anchors of a datum along an external equivalence.  Every payload record,
locant, ID, option and ordering is copied verbatim. -/
def relabel (f : V ≃ W) : FragmentSourceDatum V → FragmentSourceDatum W
  | aminoAlpha center configuration => aminoAlpha (f center) configuration
  | aminoCenter center sourceLocant descriptor =>
      aminoCenter (f center) sourceLocant descriptor
  | peptideResidue configuration => peptideResidue configuration
  | aminoFischer center projection => aminoFischer (f center) projection
  | nucleosideExplicit base facts => nucleosideExplicit base facts
  | nucleosideResolved facts => nucleosideResolved facts
  | carbohydrateSeries series => carbohydrateSeries series
  | carbohydrateRotation reading => carbohydrateRotation reading
  | carbohydrateAnomerKnowledge knowledge => carbohydrateAnomerKnowledge knowledge
  | carbohydrateAnomer anomeric reference anomericSourceLocant referenceSourceLocant descriptor =>
      carbohydrateAnomer (f anomeric) (f reference) anomericSourceLocant referenceSourceLocant
        descriptor
  | carbohydrateFischerChain carbons projection =>
      carbohydrateFischerChain (carbons.map f) projection
  | naturalCenter center label => naturalCenter (f center) label
  | naturalDoubleBond source target claim => naturalDoubleBond (f source) (f target) claim
  | lipidFischer center projection => lipidFischer (f center) projection
  | lipidKnowledge knowledge => lipidKnowledge knowledge
  | lipidGlycerol first second third substitution =>
      lipidGlycerol (f first) (f second) (f third) substitution
  | lipidCIP center reading => lipidCIP (f center) reading
  | glycolipidSphingoid configuration => glycolipidSphingoid configuration
  | glycolipidCenter center sourceLocant descriptor =>
      glycolipidCenter (f center) sourceLocant descriptor
  | glycolipidDoubleBond source target sourceLocant descriptor =>
      glycolipidDoubleBond (f source) (f target) sourceLocant descriptor

/-! ### Exact relabelling, one equation per constructor -/

@[simp] theorem relabel_aminoAlpha (f : V ≃ W) (center : V)
    (configuration : AminoAcidPeptide1983.AlphaConfiguration) :
    (aminoAlpha center configuration).relabel f = aminoAlpha (f center) configuration := rfl

@[simp] theorem relabel_aminoCenter (f : V ≃ W) (center : V) (sourceLocant : Nat)
    (descriptor : AminoAcidPeptide1983.CenterDescriptor) :
    (aminoCenter center sourceLocant descriptor).relabel f =
      aminoCenter (f center) sourceLocant descriptor := rfl

@[simp] theorem relabel_peptideResidue (f : V ≃ W)
    (configuration : AminoAcidPeptide1983.ResidueConfiguration) :
    (peptideResidue configuration).relabel f = peptideResidue configuration := rfl

@[simp] theorem relabel_aminoFischer (f : V ≃ W) (center : V)
    (projection : AminoAcidPeptide1983.FischerRosanoffProjection) :
    (aminoFischer center projection).relabel f = aminoFischer (f center) projection := rfl

@[simp] theorem relabel_nucleosideExplicit (f : V ≃ W) (base : NucleicAcid1970.BaseKind)
    (facts : NucleicAcid1970.ExplicitNucleosideFacts) :
    (nucleosideExplicit base facts).relabel f = nucleosideExplicit base facts := rfl

@[simp] theorem relabel_nucleosideResolved (f : V ≃ W)
    (facts : NucleicAcid1970.ResolvedNucleosideFacts) :
    (nucleosideResolved facts).relabel f = nucleosideResolved facts := rfl

@[simp] theorem relabel_carbohydrateSeries (f : V ≃ W)
    (series : Carbohydrate1996Foundation.DLSeries) :
    (carbohydrateSeries series).relabel f = carbohydrateSeries series := rfl

@[simp] theorem relabel_carbohydrateRotation (f : V ≃ W)
    (reading : Carbohydrate1996Foundation.SeriesAndRotation) :
    (carbohydrateRotation reading).relabel f = carbohydrateRotation reading := rfl

@[simp] theorem relabel_carbohydrateAnomerKnowledge (f : V ≃ W)
    (knowledge : Carbohydrate1996Foundation.AnomerKnowledge) :
    (carbohydrateAnomerKnowledge knowledge).relabel f =
      carbohydrateAnomerKnowledge knowledge := rfl

@[simp] theorem relabel_carbohydrateAnomer (f : V ≃ W) (anomeric reference : V)
    (anomericSourceLocant referenceSourceLocant : Nat)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor) :
    (carbohydrateAnomer anomeric reference anomericSourceLocant referenceSourceLocant
      descriptor).relabel f =
      carbohydrateAnomer (f anomeric) (f reference) anomericSourceLocant referenceSourceLocant
        descriptor := rfl

@[simp] theorem relabel_carbohydrateFischerChain (f : V ≃ W) (carbons : List V)
    (projection : CarbohydrateFischerChainData) :
    (carbohydrateFischerChain carbons projection).relabel f =
      carbohydrateFischerChain (carbons.map f) projection := rfl

@[simp] theorem relabel_naturalCenter (f : V ≃ W) (center : V)
    (label : Retinoid1981.ExplicitCenterLabelCatalog.LocatedSourceCenterLabel) :
    (naturalCenter center label).relabel f = naturalCenter (f center) label := rfl

@[simp] theorem relabel_naturalDoubleBond (f : V ≃ W) (source target : V)
    (claim : Retinoid1981.FigureGraphTranscription.DoubleBondConfigurationClaim) :
    (naturalDoubleBond source target claim).relabel f =
      naturalDoubleBond (f source) (f target) claim := rfl

@[simp] theorem relabel_lipidFischer (f : V ≃ W) (center : V)
    (projection : Lipid1976.ReferenceFischerProjection) :
    (lipidFischer center projection).relabel f = lipidFischer (f center) projection := rfl

@[simp] theorem relabel_lipidKnowledge (f : V ≃ W) (knowledge : Lipid1976.KnowledgeState) :
    (lipidKnowledge knowledge).relabel f = lipidKnowledge knowledge := rfl

@[simp] theorem relabel_lipidGlycerol (f : V ≃ W) (first second third : V)
    (substitution : Lipid1976.SnGlycerolSubstitution) :
    (lipidGlycerol first second third substitution).relabel f =
      lipidGlycerol (f first) (f second) (f third) substitution := rfl

@[simp] theorem relabel_lipidCIP (f : V ≃ W) (center : V)
    (reading : Lipid1976.GlycerolCIPReading) :
    (lipidCIP center reading).relabel f = lipidCIP (f center) reading := rfl

@[simp] theorem relabel_glycolipidSphingoid (f : V ≃ W)
    (configuration : Glycolipid1997.SphingoidConfiguration) :
    (glycolipidSphingoid configuration).relabel f =
      glycolipidSphingoid configuration := rfl

@[simp] theorem relabel_glycolipidCenter (f : V ≃ W) (center : V) (sourceLocant : Nat)
    (descriptor : Glycolipid1997.RS) :
    (glycolipidCenter center sourceLocant descriptor).relabel f =
      glycolipidCenter (f center) sourceLocant descriptor := rfl

@[simp] theorem relabel_glycolipidDoubleBond (f : V ≃ W) (source target : V)
    (sourceLocant : Nat) (descriptor : Glycolipid1997.EZ) :
    (glycolipidDoubleBond source target sourceLocant descriptor).relabel f =
      glycolipidDoubleBond (f source) (f target) sourceLocant descriptor := rfl

/-- Relabelling moves atom anchors and nothing else: the anchor list of a relabelled datum is the
image of its anchor list, in the same order. -/
@[simp] theorem atomReferences_relabel (f : V ≃ W) (datum : FragmentSourceDatum V) :
    (datum.relabel f).atomReferences = datum.atomReferences.map f := by
  cases datum <;> rfl

/-- Membership characterisation of relabelled anchors: an atom is an anchor of the relabelled
datum exactly when it is the image of an original anchor. -/
theorem mem_atomReferences_relabel_iff (f : V ≃ W) (datum : FragmentSourceDatum V) (atom : W) :
    atom ∈ (datum.relabel f).atomReferences ↔
      ∃ original ∈ datum.atomReferences, f original = atom := by
  rw [atomReferences_relabel, List.mem_map]

/-! ### Relabelling laws -/

/-- Relabelling by the identity equivalence is the identity. -/
@[simp] theorem relabel_refl (datum : FragmentSourceDatum V) :
    datum.relabel (Equiv.refl V) = datum := by
  cases datum <;> simp [relabel]

/-- Relabelling composes along equivalence composition. -/
theorem relabel_trans (f : V ≃ W) (g : W ≃ U) (datum : FragmentSourceDatum V) :
    (datum.relabel f).relabel g = datum.relabel (f.trans g) := by
  cases datum <;> simp [relabel]

/-- Pointwise-equal equivalences relabel identically. -/
theorem relabel_congr {f g : V ≃ W} (agree : ∀ atom, f atom = g atom)
    (datum : FragmentSourceDatum V) : datum.relabel f = datum.relabel g := by
  cases datum with
  | carbohydrateFischerChain carbons projection =>
      simp only [relabel]
      rw [List.map_congr_left (fun atom _ => agree atom)]
  | aminoAlpha center configuration => simp [relabel, agree]
  | aminoCenter center sourceLocant descriptor => simp [relabel, agree]
  | peptideResidue configuration => simp [relabel]
  | aminoFischer center projection => simp [relabel, agree]
  | nucleosideExplicit base facts => simp [relabel]
  | nucleosideResolved facts => simp [relabel]
  | carbohydrateSeries series => simp [relabel]
  | carbohydrateRotation reading => simp [relabel]
  | carbohydrateAnomerKnowledge knowledge => simp [relabel]
  | carbohydrateAnomer anomeric reference anomericSourceLocant referenceSourceLocant
      descriptor =>
      simp [relabel, agree]
  | naturalCenter center label => simp [relabel, agree]
  | naturalDoubleBond source target claim => simp [relabel, agree]
  | lipidFischer center projection => simp [relabel, agree]
  | lipidKnowledge knowledge => simp [relabel]
  | lipidGlycerol first second third substitution => simp [relabel, agree]
  | lipidCIP center reading => simp [relabel, agree]
  | glycolipidSphingoid configuration => simp [relabel]
  | glycolipidCenter center sourceLocant descriptor => simp [relabel, agree]
  | glycolipidDoubleBond source target sourceLocant descriptor => simp [relabel, agree]

/-- Relabelling by an equivalence and then by its inverse is the identity. -/
theorem relabel_relabel_symm (f : V ≃ W) (datum : FragmentSourceDatum V) :
    (datum.relabel f).relabel f.symm = datum := by
  rw [relabel_trans]
  rw [show f.trans f.symm = Equiv.refl V from by ext atom; simp]
  exact relabel_refl datum

/-- Relabelling by an inverse and then by the equivalence is the identity. -/
theorem relabel_symm_relabel (f : V ≃ W) (datum : FragmentSourceDatum W) :
    (datum.relabel f.symm).relabel f = datum := by
  rw [relabel_trans]
  rw [show f.symm.trans f = Equiv.refl W from by ext atom; simp]
  exact relabel_refl datum

/-- Relabelling by an equivalence is injective: a datum contains no atom reference outside its
declared `V` anchors. -/
theorem relabel_injective (f : V ≃ W) :
    Function.Injective (fun datum : FragmentSourceDatum V => datum.relabel f) := by
  intro first second equal
  have injected := congrArg
    (fun datum : FragmentSourceDatum W => datum.relabel f.symm) equal
  simpa [relabel_relabel_symm] using injected

end FragmentSourceDatum

end TetraStereo.OneCenter
