import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

/-!
# Authority carrier for the five spiro P-93 rows

One local spiro frame consists of the shared atom and two otherwise disjoint closed constitutional
cycles. This identifies a represented local ring frame even inside a dispiro or polyspiro
graph. Stereogenicity requires separate ligand-pattern, ranking and geometry evidence.
Ligand-pattern recognition, occurrence-sensitive ranking, ring assignment,
polyhedral coordination, and center/axis descriptor correspondence remain source-indexed audited
relations.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Cyclic

structure P93AuthoritySpiroSystem where
  center : Nat
  firstRingInternal : List Nat
  secondRingInternal : List Nat
  deriving DecidableEq, Repr

namespace P93AuthoritySpiroSystem

def atoms (system : P93AuthoritySpiroSystem) : List Nat :=
  system.center :: system.firstRingInternal ++ system.secondRingInternal

def firstRing (system : P93AuthoritySpiroSystem) : List Nat :=
  system.center :: system.firstRingInternal

def secondRing (system : P93AuthoritySpiroSystem) : List Nat :=
  system.center :: system.secondRingInternal

def closedPath (system : P93AuthoritySpiroSystem)
    (internal : List Nat) : List Nat :=
  system.center :: internal ++ [system.center]

def MechanicallyValidFor
    (source : AuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) : Prop :=
  system.atoms.Nodup ∧
    P93AuthorityAtomsBounded source system.atoms ∧
    2 ≤ system.firstRingInternal.length ∧
    2 ≤ system.secondRingInternal.length ∧
    P93AuthorityConnectedPath source
      (system.closedPath system.firstRingInternal) ∧
    P93AuthorityConnectedPath source
      (system.closedPath system.secondRingInternal)

/-! ## Coupled cyclic-unit consequences of mechanical validity

The module docstring calls a spiro system "two otherwise disjoint closed constitutional cycles".
That is a *proof obligation on the representation*, not a convention: the `Nodup` clause of
`MechanicallyValidFor` is exactly what forces the two ring interiors to be disjoint and the shared
center to be their only common atom.  Occurrence-sensitive ranking, ring assignment, and the
center/axis correspondence all consume this coupling, so its consequences are recorded here once
instead of being re-derived (or silently assumed) downstream. -/

theorem atoms_eq_center_cons_append (system : P93AuthoritySpiroSystem) :
    system.atoms =
      system.center ::
        (system.firstRingInternal ++ system.secondRingInternal) := rfl

theorem mem_atoms_iff (system : P93AuthoritySpiroSystem) (atom : Nat) :
    atom ∈ system.atoms ↔
      atom = system.center ∨ atom ∈ system.firstRingInternal ∨
        atom ∈ system.secondRingInternal := by
  unfold atoms
  simp only [List.mem_append, List.mem_cons, or_assoc]

theorem atoms_nodup_of_mechanicallyValid
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) : system.atoms.Nodup := valid.1

theorem firstInternal_length_of_mechanicallyValid
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) :
    2 ≤ system.firstRingInternal.length := valid.2.2.1

theorem secondInternal_length_of_mechanicallyValid
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) :
    2 ≤ system.secondRingInternal.length := valid.2.2.2.1

/-- The two ring interiors share no atom.  This is the "otherwise disjoint" clause of the module
docstring, derived rather than assumed. -/
theorem firstInternal_disjoint_secondInternal
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) :
    List.Disjoint system.firstRingInternal system.secondRingInternal := by
  have nodup : (system.center ::
      (system.firstRingInternal ++ system.secondRingInternal)).Nodup := valid.1
  exact List.disjoint_of_nodup_append (List.nodup_cons.mp nodup).2

theorem center_not_mem_firstInternal
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) :
    system.center ∉ system.firstRingInternal := by
  have nodup : (system.center ::
      (system.firstRingInternal ++ system.secondRingInternal)).Nodup := valid.1
  have avoids := (List.nodup_cons.mp nodup).1
  intro member
  exact avoids (List.mem_append.mpr (Or.inl member))

theorem center_not_mem_secondInternal
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) :
    system.center ∉ system.secondRingInternal := by
  have nodup : (system.center ::
      (system.firstRingInternal ++ system.secondRingInternal)).Nodup := valid.1
  have avoids := (List.nodup_cons.mp nodup).1
  intro member
  exact avoids (List.mem_append.mpr (Or.inr member))

theorem firstRing_subset_atoms (system : P93AuthoritySpiroSystem) :
    system.firstRing ⊆ system.atoms := by
  intro atom member
  rw [mem_atoms_iff system atom]
  unfold firstRing at member
  simp only [List.mem_cons] at member
  rcases member with hcenter | hfirst
  · exact Or.inl hcenter
  · exact Or.inr (Or.inl hfirst)

theorem secondRing_subset_atoms (system : P93AuthoritySpiroSystem) :
    system.secondRing ⊆ system.atoms := by
  intro atom member
  rw [mem_atoms_iff system atom]
  unfold secondRing at member
  simp only [List.mem_cons] at member
  rcases member with hcenter | hsecond
  · exact Or.inl hcenter
  · exact Or.inr (Or.inr hsecond)

/-- The two closed cycles of a spiro system are coupled at exactly one atom, the shared center. -/
theorem rings_inter_center
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source)
    {atom : Nat} (first : atom ∈ system.firstRing) (second : atom ∈ system.secondRing) :
    atom = system.center := by
  unfold firstRing at first
  unfold secondRing at second
  simp only [List.mem_cons] at first second
  rcases first with hcenter | hfirst
  · exact hcenter
  · rcases second with hcenter | hsecond
    · exact hcenter
    · exact False.elim
        ((List.disjoint_left.mp (firstInternal_disjoint_secondInternal valid))
          hfirst hsecond)

/-- A represented frame with shared ring interiors fails mechanical validity. This conditional
obstruction is separate from a closed graph regression and from the topology of the whole molecule. -/
theorem not_mechanicallyValid_of_shared_internal
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (shared : ∃ atom, atom ∈ system.firstRingInternal ∧
      atom ∈ system.secondRingInternal) :
    ¬ system.MechanicallyValidFor source := by
  rintro valid
  obtain ⟨atom, firstMember, secondMember⟩ := shared
  exact (List.disjoint_left.mp (firstInternal_disjoint_secondInternal valid))
    firstMember secondMember

end P93AuthoritySpiroSystem

structure P93SpiroAuthorityPolicy where
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  SystemObserved :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem → Prop
  UnitInSystemObserved :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      P93AuthorityPhysicalUnit → Prop
  CitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCitationToken →
      P93AuthorityPhysicalUnit → Prop
  SpiroPatternObserved :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      SpiroLigandPattern → Prop
  CenterDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      SpiroLigandPattern → SpiroDescriptorFamily →
        BlueBookP93.Acyclic.Descriptor → Prop
  XababOccurrenceOrderObserved :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      XababOccurrenceOrder → Prop
  DoubleBondRingObserved :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      P93AuthorityPhysicalUnit → List Nat → Prop
  DoubleBondGeometryObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      MonocyclicSeniorLigandGeometry → Prop
  DoubleBondNamingAuthorized :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      P93AuthorityPhysicalUnit → BlueBookP93.Acyclic.NomenclatureContext →
        Option BlueBookP93.Acyclic.Descriptor → Prop
  CoordinationObserved :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      Finset Nat → SpiroCenterCoordination → Prop
  PolyhedralDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      Finset Nat → ConfigurationKnowledge →
        PolyhedralChiralitySymbol → Prop
  AxialCenterDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      BlueBookP93.Acyclic.Descriptor → Prop
  AxialDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthoritySpiroSystem →
      BlueBookP93.Acyclic.Descriptor → Prop

def P93AuthoritySpiroSystem.ValidFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) : Prop :=
  system.MechanicallyValidFor source ∧
    policy.SystemObserved source system

def P93SpiroUnitSupported
    (system : P93AuthoritySpiroSystem) : P93AuthorityPhysicalUnit → Prop
  | .atomCenter center => center ∈ system.atoms
  | .bond first second => first ∈ system.atoms ∧ second ∈ system.atoms
  | .polyhedron center _positions =>
      center = system.center
  | .axis _ | .plane _ | .helix _ => False

def P93SpiroCenterDescriptorMatchesFamily
    (family : SpiroDescriptorFamily)
    (descriptor : BlueBookP93.Acyclic.Descriptor) : Prop :=
  match family with
  | .centerRS => descriptor = .R ∨ descriptor = .S
  | .centerRrSs => descriptor = .r ∨ descriptor = .s
  | .axialMP => descriptor = .M ∨ descriptor = .P
  | .polyhedralAC => False

structure P93SpiroXabcdAuthorityObservation
    (policy : P93SpiroAuthorityPolicy) where
  system : P93AuthoritySpiroSystem
  citation : P93AuthorityCitationToken
  descriptor : BlueBookP93.Acyclic.Descriptor

def P93SpiroXabcdAuthorityObservation.ValidFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroXabcdAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    (P93AuthorityPhysicalUnit.atomCenter observation.system.center).ValidFor
      policy.physicalObservation source ∧
    policy.UnitInSystemObserved source observation.system
      (P93AuthorityPhysicalUnit.atomCenter observation.system.center) ∧
    policy.SpiroPatternObserved source observation.system .Xabcd ∧
    SpiroFamilySupported .Xabcd .centerRS ∧
    P93SpiroCenterDescriptorMatchesFamily .centerRS observation.descriptor ∧
    policy.CenterDescriptorAuthorized source observation.system
      .Xabcd .centerRS observation.descriptor ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation
      (P93AuthorityPhysicalUnit.atomCenter observation.system.center)

/-- Source-case coverage: a valid `Xabcd` spiro observation inherits the exact cyclic coupling of
its mechanical skeleton, so no downstream ranking step has to re-open the `Nodup` hypothesis. -/
theorem P93SpiroXabcdAuthorityObservation.system_rings_share_only_center
    {policy : P93SpiroAuthorityPolicy} {source : AuthoritativeChemicalInput}
    {observation : P93SpiroXabcdAuthorityObservation policy}
    (valid : observation.ValidFor policy source)
    {atom : Nat} (first : atom ∈ observation.system.firstRing)
    (second : atom ∈ observation.system.secondRing) :
    atom = observation.system.center :=
  P93AuthoritySpiroSystem.rings_inter_center valid.1.1 first second

structure P93SpiroXababAuthorityObservation
    (policy : P93SpiroAuthorityPolicy) where
  system : P93AuthoritySpiroSystem
  citation : P93AuthorityCitationToken
  family : SpiroDescriptorFamily
  occurrenceOrder : XababOccurrenceOrder
  descriptor : BlueBookP93.Acyclic.Descriptor

def P93SpiroXababAuthorityObservation.ValidFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroXababAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    (P93AuthorityPhysicalUnit.atomCenter observation.system.center).ValidFor
      policy.physicalObservation source ∧
    policy.UnitInSystemObserved source observation.system
      (P93AuthorityPhysicalUnit.atomCenter observation.system.center) ∧
    policy.SpiroPatternObserved source observation.system .Xabab ∧
    SpiroFamilySupported .Xabab observation.family ∧
    (observation.family = .centerRS ∨
      observation.family = .centerRrSs) ∧
    ValidXababOccurrenceOrder observation.occurrenceOrder ∧
    policy.XababOccurrenceOrderObserved source observation.system
      observation.occurrenceOrder ∧
    P93SpiroCenterDescriptorMatchesFamily observation.family
      observation.descriptor ∧
    policy.CenterDescriptorAuthorized source observation.system
      .Xabab observation.family observation.descriptor ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation
      (P93AuthorityPhysicalUnit.atomCenter observation.system.center)

def P93SpiroRingBelongsToSystem
    (system : P93AuthoritySpiroSystem) (ring : List Nat) : Prop :=
  ring = system.firstRing ∨ ring = system.secondRing

def P93SpiroDoubleBondExpected
    (ringSize : Nat) (geometry : MonocyclicSeniorLigandGeometry) :
    Option BlueBookP93.Acyclic.Descriptor :=
  if SpiroDoubleBondDescriptorRequired ringSize = true then
    match geometry with
    | .together => some .Z
    | .opposite => some .E
  else
    none

def P93SpiroGeneralDoubleBondDescriptorAllowed :
    Option BlueBookP93.Acyclic.Descriptor → Prop
  | none => True
  | some descriptor =>
      BlueBookP93.Acyclic.DescriptorApplies .ordinaryDoubleBond descriptor

structure P93SpiroDoubleBondAuthorityObservation
    (policy : P93SpiroAuthorityPolicy) where
  system : P93AuthoritySpiroSystem
  unit : P93AuthorityPhysicalUnit
  ring : List Nat
  citation : P93AuthorityCitationToken
  geometry : MonocyclicSeniorLigandGeometry
  context : BlueBookP93.Acyclic.NomenclatureContext
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

def P93SpiroDoubleBondAuthorityObservation.ValidFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroDoubleBondAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    observation.unit.ValidFor policy.physicalObservation source ∧
    P93SpiroUnitSupported observation.system observation.unit ∧
    (∃ first second, observation.unit = .bond first second ∧
      first ∈ observation.ring ∧ second ∈ observation.ring) ∧
    P93SpiroRingBelongsToSystem observation.system observation.ring ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    policy.DoubleBondRingObserved source observation.system observation.unit
      observation.ring ∧
    policy.DoubleBondGeometryObserved source observation.unit observation.geometry ∧
    policy.DoubleBondNamingAuthorized source observation.system observation.unit
      observation.context observation.descriptor? ∧
    P93SpiroGeneralDoubleBondDescriptorAllowed observation.descriptor? ∧
    (observation.context = .preferredIUPACName →
      observation.descriptor? =
        P93SpiroDoubleBondExpected observation.ring.length observation.geometry) ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit

structure P93SpiroPolyhedralAuthorityObservation
    (policy : P93SpiroAuthorityPolicy) where
  system : P93AuthoritySpiroSystem
  unit : P93AuthorityPhysicalUnit
  citation : P93AuthorityCitationToken
  coordination : SpiroCenterCoordination
  knowledge : ConfigurationKnowledge
  descriptor : PolyhedralChiralitySymbol

def P93SpiroPolyhedralAuthorityObservation.ValidFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroPolyhedralAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    observation.unit.ValidFor policy.physicalObservation source ∧
    P93SpiroUnitSupported observation.system observation.unit ∧
    (∃ positions,
      observation.unit = .polyhedron observation.system.center positions ∧
        policy.CoordinationObserved source observation.system positions
          observation.coordination ∧
        policy.PolyhedralDescriptorAuthorized source observation.system positions
          observation.knowledge observation.descriptor) ∧
    PolyhedralACApplicable observation.coordination ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit

def P93SpiroCenterAxialCorrespondence
    (centerDescriptor axialDescriptor : BlueBookP93.Acyclic.Descriptor) : Prop :=
  match centerDescriptor, axialDescriptor with
  | .R, .M | .S, .P => True
  | _, _ => False

structure P93SpiroAxialAuthorityObservation
    (policy : P93SpiroAuthorityPolicy) where
  system : P93AuthoritySpiroSystem
  citation : P93AuthorityCitationToken
  centerDescriptor : BlueBookP93.Acyclic.Descriptor
  axialDescriptor : BlueBookP93.Acyclic.Descriptor

def P93SpiroAxialAuthorityObservation.ValidFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroAxialAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    (P93AuthorityPhysicalUnit.atomCenter observation.system.center).ValidFor
      policy.physicalObservation source ∧
    policy.UnitInSystemObserved source observation.system
      (P93AuthorityPhysicalUnit.atomCenter observation.system.center) ∧
    policy.SpiroPatternObserved source observation.system .Xaabb ∧
    SpiroFamilySupported .Xaabb .centerRS ∧
    SpiroFamilySupported .Xaabb .axialMP ∧
    P93SpiroCenterDescriptorMatchesFamily .centerRS
      observation.centerDescriptor ∧
    P93SpiroCenterDescriptorMatchesFamily .axialMP
      observation.axialDescriptor ∧
    P93SpiroCenterAxialCorrespondence observation.centerDescriptor
      observation.axialDescriptor ∧
    policy.AxialCenterDescriptorAuthorized source observation.system
      observation.centerDescriptor ∧
    policy.AxialDescriptorAuthorized source observation.system
      observation.axialDescriptor ∧
    BlueBookP93.Acyclic.DescriptorRecommended .preferredIUPACName
      .chiralCenter observation.centerDescriptor ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation
      (P93AuthorityPhysicalUnit.atomCenter observation.system.center)







theorem P93SpiroXababAuthorityObservation.system_rings_share_only_center
    {policy : P93SpiroAuthorityPolicy} {source : AuthoritativeChemicalInput}
    {observation : P93SpiroXababAuthorityObservation policy}
    (valid : observation.ValidFor policy source)
    {atom : Nat} (first : atom ∈ observation.system.firstRing)
    (second : atom ∈ observation.system.secondRing) :
    atom = observation.system.center :=
  P93AuthoritySpiroSystem.rings_inter_center valid.1.1 first second

theorem P93SpiroDoubleBondAuthorityObservation.system_rings_share_only_center
    {policy : P93SpiroAuthorityPolicy} {source : AuthoritativeChemicalInput}
    {observation : P93SpiroDoubleBondAuthorityObservation policy}
    (valid : observation.ValidFor policy source)
    {atom : Nat} (first : atom ∈ observation.system.firstRing)
    (second : atom ∈ observation.system.secondRing) :
    atom = observation.system.center :=
  P93AuthoritySpiroSystem.rings_inter_center valid.1.1 first second

theorem P93SpiroPolyhedralAuthorityObservation.system_rings_share_only_center
    {policy : P93SpiroAuthorityPolicy} {source : AuthoritativeChemicalInput}
    {observation : P93SpiroPolyhedralAuthorityObservation policy}
    (valid : observation.ValidFor policy source)
    {atom : Nat} (first : atom ∈ observation.system.firstRing)
    (second : atom ∈ observation.system.secondRing) :
    atom = observation.system.center :=
  P93AuthoritySpiroSystem.rings_inter_center valid.1.1 first second

theorem P93SpiroAxialAuthorityObservation.system_rings_share_only_center
    {policy : P93SpiroAuthorityPolicy} {source : AuthoritativeChemicalInput}
    {observation : P93SpiroAxialAuthorityObservation policy}
    (valid : observation.ValidFor policy source)
    {atom : Nat} (first : atom ∈ observation.system.firstRing)
    (second : atom ∈ observation.system.secondRing) :
    atom = observation.system.center :=
  P93AuthoritySpiroSystem.rings_inter_center valid.1.1 first second

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93AuthoritySpiroSystem.MechanicallyValidFor
assert_kernel_only TetraStereo.OneCenter.P93SpiroXabcdAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93SpiroXababAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93SpiroDoubleBondAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93SpiroPolyhedralAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93SpiroAxialAuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93AuthoritySpiroSystem.firstInternal_disjoint_secondInternal
assert_kernel_only
  TetraStereo.OneCenter.P93AuthoritySpiroSystem.rings_inter_center
assert_kernel_only
  TetraStereo.OneCenter.P93AuthoritySpiroSystem.not_mechanicallyValid_of_shared_internal
assert_kernel_only
  TetraStereo.OneCenter.P93SpiroXabcdAuthorityObservation.system_rings_share_only_center
assert_kernel_only
  TetraStereo.OneCenter.P93SpiroXababAuthorityObservation.system_rings_share_only_center
assert_kernel_only
  TetraStereo.OneCenter.P93SpiroDoubleBondAuthorityObservation.system_rings_share_only_center
assert_kernel_only
  TetraStereo.OneCenter.P93SpiroPolyhedralAuthorityObservation.system_rings_share_only_center
assert_kernel_only
  TetraStereo.OneCenter.P93SpiroAxialAuthorityObservation.system_rings_share_only_center
