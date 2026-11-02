import TetraStereo.OneCenter.P10NormativeAudit
import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.RS

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent Blue Book P-103--P-107 biochemical stereochemical semantics

This module covers the configuration-bearing rules for amino acids and peptides, cyclitols,
nucleosides/nucleotides, and lipids.  Specialist tables and retained structures remain explicit
authority boundaries; the definitions here state how their configurations are used by P-10.
-/

namespace BlueBookP103to107

/-! ## P-103 amino acids and peptides -/

inductive AminoAcidSeries where
  | D
  | L
  | xi
  deriving DecidableEq, Repr

inductive AlphaAminoAcidKind where
  | ordinary
  | cysteine
  | cystine
  deriving DecidableEq, Repr

/-- The stated L/CIP correspondence.  It is intentionally not generalized to D/L carbohydrates
or to non-alpha centres. -/
def cipOfLAminoAcid : AlphaAminoAcidKind → RS
  | .ordinary => .S
  | .cysteine | .cystine => .R

@[simp] theorem ordinary_L_is_S : cipOfLAminoAcid .ordinary = .S := rfl
@[simp] theorem cysteine_L_is_R : cipOfLAminoAcid .cysteine = .R := rfl

inductive AminoAcidMixtureNotation where
  | DL
  | rac
  deriving DecidableEq, Repr

def AminoAcidMixtureNotation.preferred : AminoAcidMixtureNotation → Bool
  | .DL => true
  | .rac => false

inductive AminoAcidCenterKind where
  | alphaCarbon
  | otherCenter
  deriving DecidableEq, Repr

inductive AminoAcidCenterDescriptorKind where
  | seriesDL
  | cipRS
  deriving DecidableEq, Repr

def descriptorKindForAminoAcidCenter :
    AminoAcidCenterKind → AminoAcidCenterDescriptorKind
  | .alphaCarbon => .seriesDL
  | .otherCenter => .cipRS

inductive AlloParent where
  | isoleucine
  | threonine
  deriving DecidableEq, Repr

structure AlloSemantics where
  parent : AlloParent
  alphaCarbonUnchanged : Prop
  carbonThreeInverted : Prop

def AlloParent.symbol : AlloParent → String
  | .isoleucine => "aIle"
  | .threonine => "aThr"

inductive PeptideResidueSeries where
  | standardL
  | D
  | xi
  | ambo
  deriving DecidableEq, Repr

def PeptideResidueSeries.mustBeCited : PeptideResidueSeries → Bool
  | .standardL => false
  | .D | .xi | .ambo => true

inductive PeptideMixtureNotation where
  | DL
  | ambo
  deriving DecidableEq, Repr

/-- `DL` is not allowed in a peptide because it generally denotes diastereomers in unspecified
proportions; `ambo` states that both configurations occur. -/
def PeptideMixtureNotation.allowed : PeptideMixtureNotation → Bool
  | .DL => false
  | .ambo => true

inductive PeptideWholeNameScope where
  | ordinary
  | ent
  deriving DecidableEq, Repr

structure EnantiomericResidueReplacement where
  residuePosition : Nat
  replacementSeries : PeptideResidueSeries
  singleEnantiomerUsesD : Prop
  mixtureUsesAmbo : Prop

/-! ## P-104 cyclitols -/

inductive CyclitolKind where
  | inositol
  | otherCyclitol
  deriving DecidableEq, Repr

inductive CyclitolConfigurationSystem where
  | inositolRetainedDL
  | systematicCIP
  deriving DecidableEq, Repr

def cyclitolConfigurationSystem : CyclitolKind → CyclitolConfigurationSystem
  | .inositol => .inositolRetainedDL
  | .otherCyclitol => .systematicCIP

inductive InositolStereoprefix where
  | cis
  | epi
  | allo
  | myo
  | muco
  | neo
  | scyllo
  | chiro
  deriving DecidableEq, Repr

namespace InositolStereoprefix

def all : List InositolStereoprefix :=
  [.cis, .epi, .allo, .myo, .muco, .neo, .scyllo, .chiro]

@[simp] theorem mem_all (stereoprefix : InositolStereoprefix) : stereoprefix ∈ all := by
  cases stereoprefix <;> simp [all]

theorem all_nodup : all.Nodup := by decide

end InositolStereoprefix

inductive RingNumberingSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

inductive CyclitolSeries where
  | D
  | L
  deriving DecidableEq, Repr

/-- With OH-1 above the planar ring, clockwise numbering is L and anticlockwise is D. -/
def cyclitolSeriesOfNumbering : RingNumberingSense → CyclitolSeries
  | .clockwise => .L
  | .counterclockwise => .D

@[simp] theorem clockwise_cyclitol_is_L :
    cyclitolSeriesOfNumbering .clockwise = .L := rfl

@[simp] theorem counterclockwise_cyclitol_is_D :
    cyclitolSeriesOfNumbering .counterclockwise = .D := rfl

inductive CyclitolNumberingCriterion where
  | lowestNumericalSeriesIgnoringConfiguration
  | moreNumerousFaceSet
  | lowerNumberableFaceSet
  | modifiedHydroxySubstituents
  | alphabeticallyFirstSubstituent
  | LBeforeDForMeso
  deriving DecidableEq, Repr

def CyclitolNumberingCriterion.rank : CyclitolNumberingCriterion → Nat
  | .lowestNumericalSeriesIgnoringConfiguration => 0
  | .moreNumerousFaceSet => 1
  | .lowerNumberableFaceSet => 2
  | .modifiedHydroxySubstituents => 3
  | .alphabeticallyFirstSubstituent => 4
  | .LBeforeDForMeso => 5

theorem cyclitolNumberingCriterion_ordered (criterion : CyclitolNumberingCriterion) :
    criterion.rank < 6 := by
  cases criterion <;> decide

inductive InositolDerivativeNaming where
  | carbohydrateStylePreserveNumberingAndDL
  | fullySubstitutiveForGroupSeniorToHydroxy
  deriving DecidableEq, Repr

def inositolDerivativeNaming (introducesGroupSeniorToHydroxy : Bool) :
    InositolDerivativeNaming :=
  if introducesGroupSeniorToHydroxy then .fullySubstitutiveForGroupSeniorToHydroxy
  else .carbohydrateStylePreserveNumberingAndDL

def otherCyclitolDerivativeUsesSystematicCIP : Prop := True

/-! ## P-105 and P-106 nucleosides and nucleotides -/

inductive RetainedNucleoside where
  | adenosine
  | guanosine
  | inosine
  | xanthosine
  | cytidine
  | thymidine
  | uridine
  deriving DecidableEq, Repr

namespace RetainedNucleoside

def all : List RetainedNucleoside :=
  [.adenosine, .guanosine, .inosine, .xanthosine, .cytidine, .thymidine, .uridine]

@[simp] theorem mem_all (nucleoside : RetainedNucleoside) : nucleoside ∈ all := by
  cases nucleoside <;> simp [all]

theorem all_nodup : all.Nodup := by decide

end RetainedNucleoside

/-- Retained structures must be supplied from the source figures; a retained name fixes the
complete nucleoside configuration through this independent table. -/
structure NucleosideConfigurationTable (Configuration : Type*) where
  configurationOf : RetainedNucleoside → Configuration

inductive NucleosideModificationSite where
  | purineOrPyrimidineRing
  | ribofuranosylComponent
  deriving DecidableEq, Repr

inductive NucleosideModificationAuthority where
  | generalSubstitution
  | carbohydrateP102
  deriving DecidableEq, Repr

def modificationAuthority : NucleosideModificationSite → NucleosideModificationAuthority
  | .purineOrPyrimidineRing => .generalSubstitution
  | .ribofuranosylComponent => .carbohydrateP102

inductive RetainedNucleotide where
  | adenylicAcid5Prime
  | thymidylicAcid5Prime
  | guanylicAcid5Prime
  | inosinicAcid5Prime
  | xanthylicAcid3Prime
  | cytidylicAcid5Prime
  | uridylicAcid5Prime
  deriving DecidableEq, Repr

namespace RetainedNucleotide

def all : List RetainedNucleotide :=
  [ .adenylicAcid5Prime, .thymidylicAcid5Prime, .guanylicAcid5Prime
  , .inosinicAcid5Prime, .xanthylicAcid3Prime, .cytidylicAcid5Prime
  , .uridylicAcid5Prime
  ]

@[simp] theorem mem_all (nucleotide : RetainedNucleotide) : nucleotide ∈ all := by
  cases nucleotide <;> simp [all]

theorem all_nodup : all.Nodup := by decide

end RetainedNucleotide

structure NucleotideDerivativeSemantics where
  purineOrPyrimidineFullySubstitutable : Prop
  ribofuranosylUsesP102 : Prop
  twoAndThreeDeoxyModificationsAllowed : Prop

/-! ## P-107 lipids -/

structure SphinganineConfiguration where
  carbonTwo : RS
  carbonThree : RS

def retainedSphinganineConfiguration : SphinganineConfiguration :=
  { carbonTwo := .S, carbonThree := .R }

@[simp] theorem retained_sphinganine_is_2S3R :
    retainedSphinganineConfiguration.carbonTwo = .S ∧
      retainedSphinganineConfiguration.carbonThree = .R := by
  constructor <;> rfl

inductive GlycerolStereochemicalScope where
  | sn
  | rac
  | unknownXi
  deriving DecidableEq, Repr

structure StereospecificGlycerolNumbering where
  fischerChainVertical : Prop
  carbonTwoHydroxyLeft : Prop
  topCarbonIsOne : Prop

def StereospecificGlycerolNumbering.Normative
    (numbering : StereospecificGlycerolNumbering) : Prop :=
  numbering.fischerChainVertical ∧ numbering.carbonTwoHydroxyLeft ∧ numbering.topCarbonIsOne

inductive PhosphatidylHeadGroupConfiguration where
  | usuallyLSerine
  | configuredInositol
  deriving DecidableEq, Repr

structure PhosphatidylserineSemantics where
  serineUsuallyL : Prop
  semisystematicNameUsesSubstitutiveRules : Prop

structure PhosphatidylinositolSemantics where
  inositolConfigurationExplicit : Prop
  semisystematicNameUsesSubstitutiveRules : Prop

structure GlycoglycerolipidSemantics where
  parentIsGlycerol : Prop
  glycerolIsStereospecificallyNumbered : Prop
  glycosylAnomerExplicit : Prop

inductive SphinganineDerivativeKind where
  | unsaturated
  | NSubstituted
  | OSubstituted
  | differentChainLength
  | additionalHydroxyOxoOrAmino
  | otherDiastereoisomer
  deriving DecidableEq, Repr

def mayRetainSphinganineName : SphinganineDerivativeKind → Bool
  | .unsaturated | .NSubstituted | .OSubstituted => true
  | .differentChainLength | .additionalHydroxyOxoOrAmino | .otherDiastereoisomer => false

@[simp] theorem sphinganine_otherDiastereomer_systematic :
    mayRetainSphinganineName .otherDiastereoisomer = false := rfl

/-! ## Clause-to-semantics ownership -/

inductive SemanticDomain where
  | aminoAcid
  | peptide
  | cyclitol
  | nucleoside
  | nucleotide
  | lipid
  deriving DecidableEq, Repr

def provisionSemanticDomain : BlueBookP10Audit.Provision → Option SemanticDomain
  | .p103AlphaAminoAcidConfiguration | .p103NonalphaCenterConfiguration
  | .p103AlloInversion => some .aminoAcid
  | .p103PeptideComponentConfiguration | .p103PeptideMixtureUnknownAndEnantiomer
  | .p103ResidueEnantiomerReplacement => some .peptide
  | .p104InositolAndOtherCyclitolDomainSplit | .p104InositolStereoprefixes
  | .p104CyclitolDAndLOrientation | .p104OtherCyclitolsCIP
  | .p104ConfigurationSensitiveNumbering | .p104InositolDerivativeConfiguration
  | .p104OtherCyclitolDerivativeConfiguration => some .cyclitol
  | .p105RetainedNucleosideStereoparents | .p105CarbohydrateMoietyModification =>
      some .nucleoside
  | .p106RetainedNucleotideStereoparents | .p106NucleotideDerivativeConfiguration =>
      some .nucleotide
  | .p107RetainedSphinganineConfiguration | .p107StereospecificGlycerolNumbering
  | .p107SnRacAndUnknownDescriptors | .p107PhosphatidylserineConfiguration
  | .p107PhosphatidylinositolConfiguration | .p107GlycoglycerolipidConfiguration
  | .p107SphinganineDerivativeConfiguration => some .lipid
  | _ => none

def p103to107Provisions : List BlueBookP10Audit.Provision :=
  [ .p103AlphaAminoAcidConfiguration
  , .p103NonalphaCenterConfiguration
  , .p103AlloInversion
  , .p103PeptideComponentConfiguration
  , .p103PeptideMixtureUnknownAndEnantiomer
  , .p103ResidueEnantiomerReplacement
  , .p104InositolAndOtherCyclitolDomainSplit
  , .p104InositolStereoprefixes
  , .p104CyclitolDAndLOrientation
  , .p104OtherCyclitolsCIP
  , .p104ConfigurationSensitiveNumbering
  , .p104InositolDerivativeConfiguration
  , .p104OtherCyclitolDerivativeConfiguration
  , .p105RetainedNucleosideStereoparents
  , .p105CarbohydrateMoietyModification
  , .p106RetainedNucleotideStereoparents
  , .p106NucleotideDerivativeConfiguration
  , .p107RetainedSphinganineConfiguration
  , .p107StereospecificGlycerolNumbering
  , .p107SnRacAndUnknownDescriptors
  , .p107PhosphatidylserineConfiguration
  , .p107PhosphatidylinositolConfiguration
  , .p107GlycoglycerolipidConfiguration
  , .p107SphinganineDerivativeConfiguration
  ]

@[simp] theorem p103to107Provisions_length : p103to107Provisions.length = 24 := by
  rfl

theorem every_p103to107_provision_has_semantic_domain :
    ∀ provision ∈ p103to107Provisions, (provisionSemanticDomain provision).isSome := by
  intro provision member
  cases provision <;>
    simp [p103to107Provisions, provisionSemanticDomain] at member ⊢

end BlueBookP103to107

end TetraStereo.OneCenter
