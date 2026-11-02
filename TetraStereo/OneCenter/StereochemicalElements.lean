import TetraStereo.OneCenter.ChemistrySemantics

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Stereochemical elements beyond tetrahedral centers.

  This module adds formal descriptor types for the stereochemical primitives needed by a
  production stereochemistry engine:

  * axial chirality (`Rₐ/Sₐ`),
  * planar chirality (`Rₚ/Sₚ`),
  * helical chirality (`P/M`),
  * alkene and cumulene-like `E/Z`,
  * conformational stereochemistry,
  * ensemble stereochemistry.

  The key proof pattern is uniform: orientation-reversing mirror operations swap chiral descriptor
  pairs, while `E/Z` is mirror-invariant because both sides of the double bond are reflected
  together.  The conformational layer connects this descriptor algebra to the existing Euclidean
  conformation and ensemble predicates from `CIPFrontier`.
-/

/-! ### Descriptor senses -/

/-- Abstract two-valued orientation sense for chiral stereochemical elements. -/
inductive StereoSense where
  | positive
  | negative
  deriving DecidableEq, Repr

namespace StereoSense

/-- Mirror reflection reverses an orientation sense. -/
def mirror : StereoSense → StereoSense
  | positive => negative
  | negative => positive

@[simp] theorem mirror_positive :
    mirror positive = negative :=
  rfl

@[simp] theorem mirror_negative :
    mirror negative = positive :=
  rfl

@[simp] theorem mirror_mirror (sense : StereoSense) :
    mirror (mirror sense) = sense := by
  cases sense <;> rfl

theorem mirror_ne_self (sense : StereoSense) :
    mirror sense ≠ sense := by
  cases sense <;> decide

end StereoSense

/-- Axial descriptors, usually written `Rₐ` and `Sₐ`. -/
inductive AxialDescriptor where
  | Ra
  | Sa
  deriving DecidableEq, Repr

namespace AxialDescriptor

def mirror : AxialDescriptor → AxialDescriptor
  | Ra => Sa
  | Sa => Ra

def ofSense : StereoSense → AxialDescriptor
  | StereoSense.positive => Ra
  | StereoSense.negative => Sa

@[simp] theorem mirror_Ra : mirror Ra = Sa := rfl

@[simp] theorem mirror_Sa : mirror Sa = Ra := rfl

@[simp] theorem mirror_mirror (descriptor : AxialDescriptor) :
    mirror (mirror descriptor) = descriptor := by
  cases descriptor <;> rfl

@[simp] theorem ofSense_mirror (sense : StereoSense) :
    ofSense sense.mirror = mirror (ofSense sense) := by
  cases sense <;> rfl

theorem mirror_ne_self (descriptor : AxialDescriptor) :
    mirror descriptor ≠ descriptor := by
  cases descriptor <;> decide

end AxialDescriptor

/-- Planar descriptors, usually written `Rₚ` and `Sₚ`. -/
inductive PlanarDescriptor where
  | Rp
  | Sp
  deriving DecidableEq, Repr

namespace PlanarDescriptor

def mirror : PlanarDescriptor → PlanarDescriptor
  | Rp => Sp
  | Sp => Rp

def ofSense : StereoSense → PlanarDescriptor
  | StereoSense.positive => Rp
  | StereoSense.negative => Sp

@[simp] theorem mirror_Rp : mirror Rp = Sp := rfl

@[simp] theorem mirror_Sp : mirror Sp = Rp := rfl

@[simp] theorem mirror_mirror (descriptor : PlanarDescriptor) :
    mirror (mirror descriptor) = descriptor := by
  cases descriptor <;> rfl

@[simp] theorem ofSense_mirror (sense : StereoSense) :
    ofSense sense.mirror = mirror (ofSense sense) := by
  cases sense <;> rfl

theorem mirror_ne_self (descriptor : PlanarDescriptor) :
    mirror descriptor ≠ descriptor := by
  cases descriptor <;> decide

end PlanarDescriptor

/-- Helical descriptors: plus/right-handed `P` and minus/left-handed `M`. -/
inductive HelicalDescriptor where
  | P
  | M
  deriving DecidableEq, Repr

namespace HelicalDescriptor

def mirror : HelicalDescriptor → HelicalDescriptor
  | P => M
  | M => P

def ofSense : StereoSense → HelicalDescriptor
  | StereoSense.positive => P
  | StereoSense.negative => M

@[simp] theorem mirror_P : mirror P = M := rfl

@[simp] theorem mirror_M : mirror M = P := rfl

@[simp] theorem mirror_mirror (descriptor : HelicalDescriptor) :
    mirror (mirror descriptor) = descriptor := by
  cases descriptor <;> rfl

@[simp] theorem ofSense_mirror (sense : StereoSense) :
    ofSense sense.mirror = mirror (ofSense sense) := by
  cases sense <;> rfl

theorem mirror_ne_self (descriptor : HelicalDescriptor) :
    mirror descriptor ≠ descriptor := by
  cases descriptor <;> decide

/-- Map helical `M/P` descriptors into the official Rule 5 descriptor layer. -/
def toRule5Descriptor : HelicalDescriptor → OfficialRule5Descriptor
  | M => OfficialRule5Descriptor.descriptorM
  | P => OfficialRule5Descriptor.descriptorP

/-- Official-rule context for a helical descriptor. -/
def toOfficialLigandRuleContext (descriptor : HelicalDescriptor) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor descriptor.toRule5Descriptor

@[simp] theorem toRule5Descriptor_M :
    toRule5Descriptor M = OfficialRule5Descriptor.descriptorM :=
  rfl

@[simp] theorem toRule5Descriptor_P :
    toRule5Descriptor P = OfficialRule5Descriptor.descriptorP :=
  rfl

@[simp] theorem officialContextTrace_M_P :
    cipTraceOutcome
      (CIPRuleEngine.compareOfficialContextTrace
        M.toOfficialLigandRuleContext P.toOfficialLigandRuleContext) = Ordering.gt :=
  rfl

end HelicalDescriptor

/-! ### Alkene `E/Z` -/

/-- Two sides of an alkene/double-bond reference plane. -/
inductive AlkeneSide where
  | above
  | below
  deriving DecidableEq, Repr

namespace AlkeneSide

/-- A mirror reflection flips both sides of the double-bond reference plane. -/
def mirror : AlkeneSide → AlkeneSide
  | above => below
  | below => above

@[simp] theorem mirror_above :
    mirror above = below :=
  rfl

@[simp] theorem mirror_below :
    mirror below = above :=
  rfl

@[simp] theorem mirror_mirror (side : AlkeneSide) :
    mirror (mirror side) = side := by
  cases side <;> rfl

end AlkeneSide

/-- Alkene descriptor: high-priority substituents opposite (`E`) or together (`Z`). -/
inductive AlkeneEZ where
  | E
  | Z
  deriving DecidableEq, Repr

namespace AlkeneEZ

/-- `E/Z` itself is mirror-invariant: a mirror flips both substituent sides simultaneously. -/
def mirror (descriptor : AlkeneEZ) : AlkeneEZ :=
  descriptor

/-- Assign `E/Z` from the two high-priority substituent sides. -/
def ofHighPrioritySides (left right : AlkeneSide) : AlkeneEZ :=
  if left = right then Z else E

/-- Map alkene `E/Z` into the official Rule-3 geometry layer. -/
def toRule3Geometry : AlkeneEZ → OfficialRule3Geometry
  | Z => OfficialRule3Geometry.seqcis
  | E => OfficialRule3Geometry.seqtrans

/-- Official-rule context for alkene/cumulene `E/Z` geometry. -/
def toOfficialLigandRuleContext (descriptor : AlkeneEZ) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  CIPRuleEngine.OfficialLigandRuleContext.ofRule3Geometry descriptor.toRule3Geometry

@[simp] theorem mirror_E :
    mirror E = E :=
  rfl

@[simp] theorem mirror_Z :
    mirror Z = Z :=
  rfl

@[simp] theorem mirror_mirror (descriptor : AlkeneEZ) :
    mirror (mirror descriptor) = descriptor := by
  cases descriptor <;> rfl

@[simp] theorem ofHighPrioritySides_same (side : AlkeneSide) :
    ofHighPrioritySides side side = Z := by
  simp [ofHighPrioritySides]

theorem ofHighPrioritySides_mirror (left right : AlkeneSide) :
    ofHighPrioritySides left.mirror right.mirror = ofHighPrioritySides left right := by
  cases left <;> cases right <;> rfl

@[simp] theorem rule3_Z_precedes_E :
    iupacSequenceRuleSystem.rule3Compare Z.toRule3Geometry E.toRule3Geometry = Ordering.gt :=
  rfl

@[simp] theorem toOfficialLigandRuleContext_Z_rule3 :
    Z.toOfficialLigandRuleContext.rule3Geometry? = some OfficialRule3Geometry.seqcis :=
  rfl

@[simp] theorem toOfficialLigandRuleContext_E_rule3 :
    E.toOfficialLigandRuleContext.rule3Geometry? = some OfficialRule3Geometry.seqtrans :=
  rfl

@[simp] theorem officialContextTrace_Z_E :
    cipTraceOutcome
      (CIPRuleEngine.compareOfficialContextTrace
        Z.toOfficialLigandRuleContext E.toOfficialLigandRuleContext) = Ordering.gt :=
  rfl

end AlkeneEZ

/-! ### Stereogenic units and descriptor assignments -/

/-- An axial stereogenic unit: an oriented axis and the high/low ligand references at each end. -/
structure AxialUnit (V : Type*) where
  axisStart : V
  axisEnd : V
  startHigh : V
  startLow : V
  endHigh : V
  endLow : V
  deriving Repr

/-- A planar stereogenic unit: a stereogenic plane plus a pilot/reference atom. -/
structure PlanarUnit (V : Type*) where
  planeAtoms : List V
  pilotAtom : V
  highReference : V
  lowReference : V
  deriving Repr

/-- A helical stereogenic unit: an ordered atom path or axis witness for a helix. -/
structure HelicalUnit (V : Type*) where
  helixPath : List V
  frontReference : V
  backReference : V
  deriving Repr

/-- An alkene/cumulene stereogenic unit with the two high/low substituents already identified. -/
structure AlkeneUnit (V : Type*) where
  leftAtom : V
  rightAtom : V
  leftHigh : V
  leftLow : V
  rightHigh : V
  rightLow : V
  deriving Repr

/-- Descriptor attached to an axial stereogenic unit. -/
structure AxialAssignment (V : Type*) where
  unit : AxialUnit V
  descriptor : AxialDescriptor

namespace AxialAssignment

variable {V : Type*}

def mirror (assignment : AxialAssignment V) : AxialAssignment V where
  unit := assignment.unit
  descriptor := assignment.descriptor.mirror

@[simp] theorem mirror_mirror (assignment : AxialAssignment V) :
    mirror (mirror assignment) = assignment := by
  cases assignment
  simp [mirror]

end AxialAssignment

/-- Descriptor attached to a planar stereogenic unit. -/
structure PlanarAssignment (V : Type*) where
  unit : PlanarUnit V
  descriptor : PlanarDescriptor

namespace PlanarAssignment

variable {V : Type*}

def mirror (assignment : PlanarAssignment V) : PlanarAssignment V where
  unit := assignment.unit
  descriptor := assignment.descriptor.mirror

@[simp] theorem mirror_mirror (assignment : PlanarAssignment V) :
    mirror (mirror assignment) = assignment := by
  cases assignment
  simp [mirror]

end PlanarAssignment

/-- Descriptor attached to a helical stereogenic unit. -/
structure HelicalAssignment (V : Type*) where
  unit : HelicalUnit V
  descriptor : HelicalDescriptor

namespace HelicalAssignment

variable {V : Type*}

def mirror (assignment : HelicalAssignment V) : HelicalAssignment V where
  unit := assignment.unit
  descriptor := assignment.descriptor.mirror

@[simp] theorem mirror_mirror (assignment : HelicalAssignment V) :
    mirror (mirror assignment) = assignment := by
  cases assignment
  simp [mirror]

end HelicalAssignment

/-- Descriptor attached to an alkene/cumulene stereogenic unit. -/
structure AlkeneAssignment (V : Type*) where
  unit : AlkeneUnit V
  descriptor : AlkeneEZ

namespace AlkeneAssignment

variable {V : Type*}

def mirror (assignment : AlkeneAssignment V) : AlkeneAssignment V where
  unit := assignment.unit
  descriptor := assignment.descriptor.mirror

@[simp] theorem mirror_mirror (assignment : AlkeneAssignment V) :
    mirror (mirror assignment) = assignment := by
  cases assignment
  simp [mirror]

end AlkeneAssignment

/-- List-map form of an involution. -/
theorem list_map_involutive {α : Type*} (f : α → α) (hf : ∀ x, f (f x) = x) :
    ∀ xs : List α, (xs.map f).map f = xs
  | [] => rfl
  | x :: xs => by
      simp [hf x, list_map_involutive f hf xs]

/-- A molecule-level stereochemical profile covering all non-tetrahedral element families added
in this module. -/
structure StereoElementProfile (V : Type*) where
  axial : List (AxialAssignment V) := []
  planar : List (PlanarAssignment V) := []
  helical : List (HelicalAssignment V) := []
  alkene : List (AlkeneAssignment V) := []

namespace StereoElementProfile

variable {V : Type*}

/-- Mirror a stereochemical profile: chiral element descriptors are swapped; `E/Z` is preserved. -/
def mirror (profile : StereoElementProfile V) : StereoElementProfile V where
  axial := profile.axial.map AxialAssignment.mirror
  planar := profile.planar.map PlanarAssignment.mirror
  helical := profile.helical.map HelicalAssignment.mirror
  alkene := profile.alkene.map AlkeneAssignment.mirror

@[simp] theorem mirror_mirror (profile : StereoElementProfile V) :
    mirror (mirror profile) = profile := by
  cases profile
  simp [mirror, list_map_involutive AxialAssignment.mirror AxialAssignment.mirror_mirror,
    list_map_involutive PlanarAssignment.mirror PlanarAssignment.mirror_mirror,
    list_map_involutive HelicalAssignment.mirror HelicalAssignment.mirror_mirror,
    list_map_involutive AlkeneAssignment.mirror AlkeneAssignment.mirror_mirror]

/-- A profile is descriptor-achiral when it is fixed by mirror. -/
def DescriptorAchiral (profile : StereoElementProfile V) : Prop :=
  profile.mirror = profile

/-- A profile is descriptor-chiral when mirror changes it. -/
def DescriptorChiral (profile : StereoElementProfile V) : Prop :=
  profile.mirror ≠ profile

theorem descriptorChiral_iff_not_descriptorAchiral (profile : StereoElementProfile V) :
    profile.DescriptorChiral ↔ ¬ profile.DescriptorAchiral := by
  rfl

theorem not_descriptorChiral_of_descriptorAchiral {profile : StereoElementProfile V}
    (h : profile.DescriptorAchiral) :
    ¬ profile.DescriptorChiral := by
  intro hchiral
  exact hchiral h

end StereoElementProfile

/-! ### Conformational and ensemble stereochemistry -/

/-- A conformational stereochemistry system assigns a stereochemical element profile to every
allowed molecular conformation, invariant under proper rigid motion and mirror-compatible under
improper rigid motion. -/
structure ConformationalStereoSystem (V : Type*) where
  ensemble : MolecularConformation.Ensemble V
  profile : MolecularConformation V → StereoElementProfile V
  properInvariant :
    ∀ {c d : MolecularConformation V}, MolecularConformation.ProperEquivalent c d →
      profile c = profile d
  improperMirror :
    ∀ {c d : MolecularConformation V}, MolecularConformation.ImproperImage c d →
      profile d = (profile c).mirror

namespace ConformationalStereoSystem

variable {V : Type*}

/-- A conformation has a chiral descriptor profile if mirror changes its profile. -/
def ProfileChiralAt (system : ConformationalStereoSystem V)
    (c : MolecularConformation V) : Prop :=
  (system.profile c).DescriptorChiral

/-- A conformation has an achiral descriptor profile if mirror fixes its profile. -/
def ProfileAchiralAt (system : ConformationalStereoSystem V)
    (c : MolecularConformation V) : Prop :=
  (system.profile c).DescriptorAchiral

/-- If a conformation is ensemble-achiral, its descriptor profile must be mirror-fixed. -/
theorem profile_fixed_of_achiralWithin (system : ConformationalStereoSystem V)
    {c : MolecularConformation V}
    (h : system.ensemble.AchiralWithin c) :
    system.ProfileAchiralAt c := by
  rcases h with ⟨_hc, d, _hd, himproper, hproper⟩
  have hProper : system.profile c = system.profile d :=
    system.properInvariant hproper
  have hImproper : system.profile d = (system.profile c).mirror :=
    system.improperMirror himproper
  exact (hProper.trans hImproper).symm

/-- A mirror-changing descriptor profile rules out ensemble achirality. -/
theorem not_achiralWithin_of_profileChiral (system : ConformationalStereoSystem V)
    {c : MolecularConformation V}
    (hprofile : system.ProfileChiralAt c) :
    ¬ system.ensemble.AchiralWithin c := by
  intro hachiral
  exact hprofile (system.profile_fixed_of_achiralWithin hachiral)

/-- An allowed conformation with a mirror-changing descriptor profile is chiral within the
ensemble. -/
theorem chiralWithin_of_profileChiral (system : ConformationalStereoSystem V)
    {c : MolecularConformation V} (hc : c ∈ system.ensemble.allowed)
    (hprofile : system.ProfileChiralAt c) :
    system.ensemble.ChiralWithin c :=
  ⟨hc, system.not_achiralWithin_of_profileChiral hprofile⟩

/-- Ensemble-level existence of a chiral conformer. -/
def HasChiralConformer (system : ConformationalStereoSystem V) : Prop :=
  ∃ c, system.ensemble.ChiralWithin c

/-- A profile-chiral allowed conformation witnesses a chiral conformer in the ensemble. -/
theorem hasChiralConformer_of_profileChiral (system : ConformationalStereoSystem V)
    {c : MolecularConformation V} (hc : c ∈ system.ensemble.allowed)
    (hprofile : system.ProfileChiralAt c) :
    system.HasChiralConformer :=
  ⟨c, system.chiralWithin_of_profileChiral hc hprofile⟩

/-- Ensemble-level descriptor achirality: every allowed conformer has a mirror-fixed profile. -/
def DescriptorAchiralEnsemble (system : ConformationalStereoSystem V) : Prop :=
  ∀ c, c ∈ system.ensemble.allowed → system.ProfileAchiralAt c

/-- Ensemble-level descriptor chirality: some allowed conformer has a mirror-changing profile. -/
def DescriptorChiralEnsemble (system : ConformationalStereoSystem V) : Prop :=
  ∃ c, c ∈ system.ensemble.allowed ∧ system.ProfileChiralAt c

theorem not_descriptorAchiralEnsemble_of_descriptorChiralEnsemble
    (system : ConformationalStereoSystem V)
    (h : system.DescriptorChiralEnsemble) :
    ¬ system.DescriptorAchiralEnsemble := by
  intro hachiral
  rcases h with ⟨c, hc, hchiral⟩
  exact hchiral (hachiral c hc)

end ConformationalStereoSystem

end
end OneCenter
end TetraStereo
