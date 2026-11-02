import TetraStereo.OneCenter.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent P-90 scope semantics

P-90 distinguishes the stereochemistry-free name skeleton from stereodescriptor annotations,
retained names that already imply configuration, preferred descriptors used in PINs, and other
appropriate descriptors admitted in general nomenclature.  These small definitions make those
scope distinctions explicit before any later descriptor algorithm is connected to naming.
-/

namespace BlueBookP90

inductive NameConfigurationMode where
  | descriptorAnnotated
  | retainedNameImpliesConfiguration
  deriving DecidableEq, Repr

inductive NomenclatureContext where
  | preferredIUPACName
  | general
  deriving DecidableEq, Repr

inductive RecommendationStatus where
  | preferred
  | appropriateGeneral
  | notAdmitted
  deriving DecidableEq, Repr

/-- P-90's distinction between the descriptor-free name and affixes that specify configuration or
conformation. -/
structure StereochemicallyAnnotatedName (CoreName Descriptor : Type*) where
  core : CoreName
  descriptors : List Descriptor

def sameNameApartFromDescriptors {CoreName Descriptor : Type*}
    (first second : StereochemicallyAnnotatedName CoreName Descriptor) : Prop :=
  first.core = second.core

@[simp] theorem descriptor_replacement_preserves_core
    {CoreName Descriptor : Type*}
    (name : StereochemicallyAnnotatedName CoreName Descriptor)
    (descriptors : List Descriptor) :
    ({ name with descriptors := descriptors }).core = name.core :=
  rfl

/-- Preferred nomenclature accepts the selected preferred descriptor; general nomenclature also
accepts other appropriate systems. -/
def DescriptorAdmitted :
    NomenclatureContext → RecommendationStatus → Prop
  | .preferredIUPACName, .preferred => True
  | .general, .preferred => True
  | .general, .appropriateGeneral => True
  | _, _ => False

theorem preferred_descriptor_admitted_everywhere (context : NomenclatureContext) :
    DescriptorAdmitted context .preferred := by
  cases context <;> trivial

theorem general_only_descriptor_not_admitted_in_PIN :
    ¬DescriptorAdmitted .preferredIUPACName .appropriateGeneral := by
  simp [DescriptorAdmitted]

/-- The P-90 role of the sequence rules: establish ligand seniority, which later configuration
rules consume.  No particular encoded comparator is used in this authority-side signature. -/
structure CIPPrioritySystem (Ligand : Type*) where
  precedes : Ligand → Ligand → Prop
  derivedBySequenceRules : Prop

/-- P-90 routes synthetic compounds to P-93 and natural products to P-10. -/
inductive ApplicationDomain where
  | syntheticCompound
  | naturalProduct
  deriving DecidableEq, Repr

inductive ConfigurationAuthority where
  | chapterP93
  | chapterP10
  deriving DecidableEq, Repr

def configurationAuthority : ApplicationDomain → ConfigurationAuthority
  | .syntheticCompound => .chapterP93
  | .naturalProduct => .chapterP10

@[simp] theorem synthetic_routes_to_P93 :
    configurationAuthority .syntheticCompound = .chapterP93 :=
  rfl

@[simp] theorem natural_product_routes_to_P10 :
    configurationAuthority .naturalProduct = .chapterP10 :=
  rfl

end BlueBookP90

end TetraStereo.OneCenter
