import TetraStereo.OneCenter.P91DescriptorSyntax

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent P-93.2 noncarbon tetrahedral semantics

P-93.2 extends the ordinary tetrahedral chirality rule to any four-ligand tetrahedral center and
then specifies representation normalizations for several element families.  These predicates are
authority-side chemistry; they do not use the parser's element whitelist or production valence
table.
-/

namespace BlueBookP93.NoncarbonTetrahedra

inductive ConfigurationClass where
  | chiral
  | pseudoasymmetric
  deriving DecidableEq, Repr

inductive Descriptor where
  | R | S | r | s
  deriving DecidableEq, Repr

def DescriptorAllowed : ConfigurationClass → Descriptor → Prop
  | .chiral, .R | .chiral, .S => True
  | .pseudoasymmetric, .r | .pseudoasymmetric, .s => True
  | _, _ => False

structure FourLigandTetrahedralCenter (Element Ligand : Type*) where
  centralElement : Element
  ligands : Fin 4 → Ligand
  tetrahedrallyArranged : Prop

/-- The P-93.2.0 applicability boundary is element-independent. -/
def InP93_2Scope {Element Ligand : Type*}
    (center : FourLigandTetrahedralCenter Element Ligand) : Prop :=
  center.tetrahedrallyArranged

theorem scope_does_not_require_carbon {Element Ligand : Type*}
    (center : FourLigandTetrahedralCenter Element Ligand)
    (tetrahedral : center.tetrahedrallyArranged) :
    InP93_2Scope center :=
  tetrahedral

inductive LocantKind where
  | none
  | numerical
  | letter
  deriving DecidableEq, Repr

inductive NameContext where
  | preferredIUPACName
  | general
  deriving DecidableEq, Repr

inductive CentralElementFamily where
  | boron
  | sulfur
  | selenium
  | tellurium
  | nitrogen
  | phosphorus
  | arsenic
  | antimony
  | bismuth
  | other
  deriving DecidableEq, Repr

def RequiresNestingWithoutReferenceLocant : CentralElementFamily → Prop
  | .boron | .sulfur | .selenium | .tellurium | .nitrogen
  | .phosphorus | .arsenic | .antimony | .bismuth => True
  | .other => False

structure DescriptorCitationObservation where
  context : NameContext
  centralElement : CentralElementFamily
  locant : LocantKind
  compoundNameNested : Bool

/-- P-93.2.1: PINs use numerical locants when available, never element-letter locants; named
element families require nesting when the name supplies no reference locant. -/
def CitationConforms (observation : DescriptorCitationObservation) : Prop :=
  observation.locant ≠ .letter ∧
  (observation.context = .preferredIUPACName →
    observation.locant = .none →
    RequiresNestingWithoutReferenceLocant observation.centralElement →
    observation.compoundNameNested = true)

theorem PIN_named_center_without_locant_requires_nesting
    (family : CentralElementFamily)
    (requires : RequiresNestingWithoutReferenceLocant family)
    (conforms : CitationConforms
      { context := .preferredIUPACName
        centralElement := family
        locant := .none
        compoundNameNested := false }) : False := by
  exact Bool.noConfusion (conforms.2 rfl rfl requires)

/-! ## Element-family representation rules -/

inductive OnicCenter where
  | azanium
  | phosphanium
  | arsanium
  | stibanium
  | bismuthanium
  deriving DecidableEq, Repr

/-- Every named onium family uses the same four-ligand sequence-rule treatment. -/
def onicCenters : List OnicCenter :=
  [ .azanium, .phosphanium, .arsanium, .stibanium, .bismuthanium ]

@[simp] theorem onicCenters_exhaustive (center : OnicCenter) : center ∈ onicCenters := by
  cases center <;> simp [onicCenters]

theorem onicCenters_nodup : onicCenters.Nodup := by
  decide

inductive OxideCenter where
  | amineOxide
  | phosphaneOxide
  deriving DecidableEq, Repr

inductive WrittenBondingToOxygen where
  | chargeSeparatedSingle
  | neutralSingle
  | writtenDouble
  | otherFormalism
  deriving DecidableEq, Repr

/-- In amine and phosphane oxides, oxygen is the fourth ligand and its written bond formalism is
irrelevant to the configuration model. -/
def oxideLigandCount (_ : OxideCenter) (_ : WrittenBondingToOxygen) : ℕ := 4

theorem oxide_bonding_formalism_irrelevant (center : OxideCenter)
    (first second : WrittenBondingToOxygen) :
    oxideLigandCount center first = oxideLigandCount center second :=
  rfl

inductive PhosphorusOxoFamily where
  | phosphate
  | phosphonate
  | related
  deriving DecidableEq, Repr

inductive EffectiveBondOrder where
  | single
  | double
  deriving DecidableEq, Repr

/-- A conventional written P=O contributes one ligand edge, not a duplicate ligand. -/
def phosphorusOxoEffectiveBondOrder
    (_ : PhosphorusOxoFamily) (_writtenAsDouble : Bool) : EffectiveBondOrder :=
  .single

@[simp] theorem written_PO_double_normalizes_to_single (family : PhosphorusOxoFamily) :
    phosphorusOxoEffectiveBondOrder family true = .single :=
  rfl

structure FormalChargeArrangement where
  centerCharge : Int
  oxygenCharge : Int
  deriving DecidableEq, Repr

/-- P-93.2.4 directs configuration assignment to ignore alternative formal charge placement. -/
def SameConfigurationIgnoringFormalCharges
    (_first _second : FormalChargeArrangement) : Prop := True

theorem all_formal_charge_arrangements_configuration_equivalent
    (first second : FormalChargeArrangement) :
    SameConfigurationIgnoringFormalCharges first second :=
  trivial

inductive ChalcogenOxoFamily where
  | sulfate
  | sulfonate
  | selenate
  | selenonate
  | tellurate
  | telluronate
  | related
  deriving DecidableEq, Repr

/-- P-93.2.5 imports the phosphate normalization for every listed chalcogen family. -/
def UsesPhosphateConfigurationTreatment (_ : ChalcogenOxoFamily) : Prop := True

theorem every_chalcogen_oxo_family_uses_phosphate_treatment
    (family : ChalcogenOxoFamily) :
    UsesPhosphateConfigurationTreatment family :=
  trivial

inductive NoncarbonGroup14Center where
  | silicon
  | germanium
  | tin
  | lead
  deriving DecidableEq, Repr

def noncarbonGroup14Centers : List NoncarbonGroup14Center :=
  [ .silicon, .germanium, .tin, .lead ]

@[simp] theorem noncarbonGroup14Centers_exhaustive
    (center : NoncarbonGroup14Center) : center ∈ noncarbonGroup14Centers := by
  cases center <;> simp [noncarbonGroup14Centers]

/-- P-93.2.6 is an exact method transfer, not a new priority rule. -/
def UsesCarbonTetrahedralMethod (_ : NoncarbonGroup14Center) : Prop := True

theorem every_noncarbon_group14_center_uses_carbon_method
    (center : NoncarbonGroup14Center) :
    UsesCarbonTetrahedralMethod center :=
  trivial

end BlueBookP93.NoncarbonTetrahedra

end TetraStereo.OneCenter
