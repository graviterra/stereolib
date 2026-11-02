import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedOpenCumuleneAnalysis
import TetraStereo.OneCenter.AuthoritativeSemanticCyclicCumuleneComponentPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Unified source analysis with the fully cyclic P-31 authority branch

Fully cyclic all-double components do not receive an invented open-terminal cumulene descriptor.
They are nevertheless retained in the public source result as explicit P-31 parent-hydride
authority records.  This module appends those records to the four descriptor-bearing families and
proves exact membership, authority soundness, and literal exactly-once component retention.
-/

/-- Public source result through tetrahedral, ordinary-double-bond, both open-cumulene parity
routes, and the fully cyclic P-31 authority boundary. -/
inductive AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes
    (source : AuthoritativeChemicalInput) where
  | prior : source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes →
      source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes
  | fullyCyclicCumuleneParent : source.AromaticCanonicalCyclicCumuleneComponent →
      source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes
  deriving DecidableEq

/-- Deterministic five-branch source result. The cyclic branch reports authority topology rather
than a descriptor because P-93 open-terminal descriptors are proved inapplicable there. -/
noncomputable def analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes :=
  (source.analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes
      carrierFuel ruleFuel).map
    AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ++
  source.aromaticCanonicalCyclicCumuleneComponents.map
    AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent

/-- Exact family boundary for the five-branch source result. -/
def AromaticCanonicalConcreteStereochemicalWithCyclicCumulenesExecutableMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) : Prop :=
  match result with
  | .prior prior =>
      source.AromaticCanonicalConcreteStereochemicalWithOpenCumulenesExecutableMember
        carrierFuel ruleFuel prior
  | .fullyCyclicCumuleneParent component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component

/-- The five-branch result contains exactly the prior executable descriptor assignments and the
independently recognized fully cyclic source components. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) :
    result ∈ source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
        carrierFuel ruleFuel ↔
      source.AromaticCanonicalConcreteStereochemicalWithCyclicCumulenesExecutableMember
        carrierFuel ruleFuel result := by
  cases result with
  | prior prior =>
      unfold AromaticCanonicalConcreteStereochemicalWithCyclicCumulenesExecutableMember
      constructor
      · intro present
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
          List.mem_append] at present
        rcases present with priorPresent | cyclicPresent
        · obtain ⟨other, otherPresent, equal⟩ := List.mem_map.mp priorPresent
          cases equal
          exact
            (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_iff_executableMember
              carrierFuel ruleFuel prior).mp otherPresent
        · obtain ⟨_other, _otherPresent, equal⟩ := List.mem_map.mp cyclicPresent
          contradiction
      · intro executable
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
          List.mem_append]
        left
        exact List.mem_map.mpr ⟨prior,
          (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_iff_executableMember
            carrierFuel ruleFuel prior).mpr executable, rfl⟩
  | fullyCyclicCumuleneParent component =>
      unfold AromaticCanonicalConcreteStereochemicalWithCyclicCumulenesExecutableMember
      constructor
      · intro present
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
          List.mem_append] at present
        rcases present with priorPresent | cyclicPresent
        · obtain ⟨_other, _otherPresent, equal⟩ := List.mem_map.mp priorPresent
          contradiction
        · obtain ⟨other, otherPresent, equal⟩ := List.mem_map.mp cyclicPresent
          cases equal
          exact
            (source.mem_aromaticCanonicalCyclicCumuleneComponents_iff component).mp
              otherPresent
      · intro derived
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
          List.mem_append]
        right
        exact List.mem_map.mpr ⟨component,
          (source.mem_aromaticCanonicalCyclicCumuleneComponents_iff component).mpr derived,
          rfl⟩

/-- Independent meaning of a five-branch result. The cyclic case includes both positive P-31
authority and negative exclusion of the P-93 open-terminal schema. -/
def DeclarativeAromaticCanonicalConcreteStereochemicalWithCyclicCumulenesMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) : Prop :=
  match result with
  | .prior prior =>
      source.DeclarativeAromaticCanonicalConcreteStereochemicalWithOpenCumulenesMember
        carrierFuel ruleFuel prior
  | .fullyCyclicCumuleneParent component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
        BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
        ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene

/-- Every five-branch result has its independent descriptor judgment or, for a fully cyclic
component, its exact P-31 authority and open-terminal exclusion proof. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes)
    (present : result ∈
      source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
        carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalConcreteStereochemicalWithCyclicCumulenesMember
      carrierFuel ruleFuel result := by
  cases result with
  | prior prior =>
      have executable :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
          carrierFuel ruleFuel (.prior prior)).mp present
      exact
        source.analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_member_sound
          carrierFuel ruleFuel prior
          ((source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_iff_executableMember
            carrierFuel ruleFuel prior).mpr executable)
  | fullyCyclicCumuleneParent component =>
      have derived :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
          carrierFuel ruleFuel (.fullyCyclicCumuleneParent component)).mp present
      exact ⟨derived, derived.authority_topology.1, derived.authority_topology.2⟩

/-- Every independently recognized fully cyclic component is literally retained once, not only
present under set-like list membership. -/
theorem count_fullyCyclicCumuleneParent_in_analyzeAromaticCanonicalConcreteStereochemistry_eq_one
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent)
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
      carrierFuel ruleFuel).count (.fullyCyclicCumuleneParent component) = 1 := by
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
    List.count_append]
  have priorZero :
      ((source.analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes
          carrierFuel ruleFuel).map
        AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior).count
          (.fullyCyclicCumuleneParent component) = 0 :=
    List.count_eq_zero.mpr (by simp)
  rw [priorZero, zero_add]
  have cyclicNodup :
      (source.aromaticCanonicalCyclicCumuleneComponents.map
        AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent).Nodup :=
    source.aromaticCanonicalCyclicCumuleneComponents_nodup.map (by
      intro left right equal
      exact AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent.inj
        equal)
  rw [cyclicNodup.count]
  simp [(source.mem_aromaticCanonicalCyclicCumuleneComponents_iff component).mpr derived]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
