import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6FuelCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRule3Through6GeometrySoundness
import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondWholeMoleculeAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Concrete source-canonical tetrahedral and ordinary-double-bond analysis

This module removes the remaining abstract `AromaticCanonicalRuleSemantics` parameter from the
exact molecule-level Rules-3--6 totality boundary.  The same unique source-canonical auxiliary
fixed point is then used to supply the endpoint dependency views of the ordinary-double-bond
analyzer.  The final sum is a single source-indexed analysis result with an exact executable
membership boundary and an independent soundness theorem for both represented families.
-/

/-! ## Parameter-free exact tetrahedral endpoint -/

/-- Exact executable meaning of the parameter-free concrete tetrahedral endpoint. -/
def AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) : Prop :=
  source.AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center descriptor

/-- The concrete no-callback endpoint emits exactly its complete executable judgment. -/
theorem aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) :
    source.aromaticCanonicalConcreteRule3Through6Descriptor?
        carrierFuel ruleFuel center = some descriptor ↔
      source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
        carrierFuel ruleFuel center descriptor := by
  exact source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_some_iff_executableJudgment
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center descriptor

/-- Descriptor-independent readiness of the parameter-free concrete endpoint. -/
def AromaticCanonicalConcreteRule3Through6Ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  ∃ descriptor,
    source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
      carrierFuel ruleFuel center descriptor

/-- Concrete readiness is exactly existence of an emitted descriptor. -/
theorem aromaticCanonicalConcreteRule3Through6Ready_iff_exists_descriptor
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalConcreteRule3Through6Ready carrierFuel ruleFuel center ↔
      ∃ descriptor,
        source.aromaticCanonicalConcreteRule3Through6Descriptor?
          carrierFuel ruleFuel center = some descriptor := by
  unfold AromaticCanonicalConcreteRule3Through6Ready
  constructor <;> rintro ⟨descriptor, witnessed⟩
  · exact ⟨descriptor,
      (source.aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
        carrierFuel ruleFuel center descriptor).mpr witnessed⟩
  · exact ⟨descriptor,
      (source.aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
        carrierFuel ruleFuel center descriptor).mp witnessed⟩

/-- The concrete endpoint refuses exactly the centers that are not completely ready. -/
theorem aromaticCanonicalConcreteRule3Through6Descriptor?_eq_none_iff_not_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalConcreteRule3Through6Descriptor?
        carrierFuel ruleFuel center = none ↔
      ¬ source.AromaticCanonicalConcreteRule3Through6Ready
        carrierFuel ruleFuel center := by
  rw [source.aromaticCanonicalConcreteRule3Through6Ready_iff_exists_descriptor]
  cases computed : source.aromaticCanonicalConcreteRule3Through6Descriptor?
      carrierFuel ruleFuel center <;> simp

/-- Exact whole-molecule membership for the parameter-free concrete analyzer. -/
theorem mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment) :
    assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
        carrierFuel ruleFuel ↔
      source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
        carrierFuel ruleFuel assignment.center assignment.descriptor := by
  unfold analyzeAromaticCanonicalConcreteRule3Through6
  unfold AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
  rw [source.mem_analyzeAromaticCanonicalScheduledRule3Through6_iff]
  exact source.aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
    carrierFuel ruleFuel assignment.center assignment.descriptor

/-- Every executable concrete result entails the earlier independent complete judgment. -/
theorem AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment.complete
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS)
    (judged : source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
      carrierFuel ruleFuel center descriptor) :
    source.AromaticCanonicalConcreteRule3Through6DescriptorJudgment
      carrierFuel ruleFuel center descriptor := by
  unfold AromaticCanonicalConcreteRule3Through6DescriptorJudgment
  exact ⟨
    AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment.complete
      source
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel) ruleFuel center descriptor judged,
    source.aromaticCanonicalScheduledAuxiliaryState_cipModel
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)⟩

/-- Chemical readiness at the proved uniform reroot bound, specialized to the concrete
source-canonical auxiliary semantics. -/
def AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  source.AromaticCanonicalScheduledRule3Through6ChemicallyReadyAtBound
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel (2 * (carrierFuel + 1))) center

/-- Concrete finite-fuel completeness: every chemically ready source center emits at the proved
uniform bound, with no semantic callback or recursive-builder-success premise. -/
theorem exists_aromaticCanonicalConcreteRule3Through6Descriptor?_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound
      carrierFuel center) :
    ∃ descriptor,
      source.aromaticCanonicalConcreteRule3Through6Descriptor?
        carrierFuel (2 * (carrierFuel + 1)) center = some descriptor := by
  exact source.exists_aromaticCanonicalScheduledRule3Through6Descriptor?_at_bound
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel (2 * (carrierFuel + 1))) center ready

/-- Concrete completeness and independent correctness for the same emitted descriptor. -/
theorem exists_aromaticCanonicalConcreteRule3Through6Descriptor_and_judgment_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound
      carrierFuel center) :
    ∃ descriptor,
      source.aromaticCanonicalConcreteRule3Through6Descriptor?
          carrierFuel (2 * (carrierFuel + 1)) center = some descriptor ∧
        source.AromaticCanonicalConcreteRule3Through6DescriptorJudgment
          carrierFuel (2 * (carrierFuel + 1)) center descriptor := by
  obtain ⟨descriptor, computed⟩ :=
    source.exists_aromaticCanonicalConcreteRule3Through6Descriptor?_at_bound
      carrierFuel center ready
  have executable :=
    (source.aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
      carrierFuel (2 * (carrierFuel + 1)) center descriptor).mp computed
  exact ⟨descriptor, computed, executable.complete⟩

/-! ## The same fixed point supplies ordinary-double-bond dependency views -/

/-- The unique concrete auxiliary state used by every represented stereogenic family below. -/
noncomputable def aromaticCanonicalConcreteAuxiliaryState
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  source.aromaticCanonicalScheduledAuxiliaryState
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel)

/-- Source-derived dependency view at one canonical atom, with no caller callback. -/
noncomputable def aromaticCanonicalConcreteDependencyViewAt
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (atom : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel atom) :=
  source.aromaticCanonicalDependencyView
    (source.aromaticCanonicalConcreteAuxiliaryState carrierFuel ruleFuel)
    (source.aromaticCanonicalRootOccurrence carrierFuel atom)

/-- Parameter-free whole-molecule ordinary-double-bond analyzer driven by the same fixed point as
the concrete tetrahedral analyzer. -/
noncomputable def analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial carrierFuel
    (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)

/-- Exact executable membership of the parameter-free ordinary-double-bond analyzer. -/
theorem mem_analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_iff
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈
        source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
          carrierFuel ruleFuel ↔
      ∃ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
          carrierFuel bond
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel bond.left)
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel bond.right) = some assignment := by
  exact source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff
    carrierFuel
    (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)
    assignment

/-- Every parameter-free ordinary-double-bond emission has the independent Rules-1a--5,
Rule-5-parity, exact-coordinate, rational-geometry, and final descriptor derivation. -/
theorem analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (present : assignment ∈
      source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
        carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialMember
      carrierFuel
      (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)
      assignment := by
  exact source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_member_sound
    carrierFuel
    (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)
    assignment present

/-- The parameter-free ordinary-double-bond output contains no duplicate assignments. -/
theorem analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
      carrierFuel ruleFuel).Nodup := by
  exact source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_nodup
    carrierFuel
    (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)

/-! ## One combined source scheduler result -/

/-- Disjoint output type for the source-canonical families scheduled in this module. -/
inductive AromaticCanonicalConcreteStereochemicalAssignment
    (source : AuthoritativeChemicalInput) where
  | tetrahedral : source.AromaticCanonicalScheduledRule3Through6Assignment →
      source.AromaticCanonicalConcreteStereochemicalAssignment
  | ordinaryDoubleBond : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment →
      source.AromaticCanonicalConcreteStereochemicalAssignment
  deriving DecidableEq

/-- A single deterministic result list for concrete tetrahedral Rules-1a--6 assignments and
canonical individual ordinary-double-bond assignments. -/
noncomputable def analyzeAromaticCanonicalConcreteStereochemistry
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalConcreteStereochemicalAssignment :=
  (source.analyzeAromaticCanonicalConcreteRule3Through6 carrierFuel ruleFuel).map
      AromaticCanonicalConcreteStereochemicalAssignment.tetrahedral ++
    (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
      carrierFuel ruleFuel).map
      AromaticCanonicalConcreteStereochemicalAssignment.ordinaryDoubleBond

/-- Exact executable boundary for membership in the combined result. -/
def AromaticCanonicalConcreteStereochemicalExecutableMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalConcreteStereochemicalAssignment) : Prop :=
  match assignment with
  | .tetrahedral tetrahedral =>
      source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
        carrierFuel ruleFuel tetrahedral.center tetrahedral.descriptor
  | .ordinaryDoubleBond ordinaryDoubleBond =>
      ∃ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
          carrierFuel bond
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel bond.left)
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel bond.right) = some ordinaryDoubleBond

/-- The combined source scheduler contains exactly the results admitted by its executable
family judgments. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistry_iff_executableMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalConcreteStereochemicalAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalConcreteStereochemistry
        carrierFuel ruleFuel ↔
      source.AromaticCanonicalConcreteStereochemicalExecutableMember
        carrierFuel ruleFuel assignment := by
  cases assignment with
  | tetrahedral tetrahedral =>
      unfold AromaticCanonicalConcreteStereochemicalExecutableMember
      constructor
      · intro present
        rw [analyzeAromaticCanonicalConcreteStereochemistry,
          List.mem_append] at present
        rcases present with tetrahedralPresent | ordinaryPresent
        · obtain ⟨other, otherPresent, equal⟩ :=
            (List.mem_map.mp tetrahedralPresent)
          cases equal
          exact
            (source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
              carrierFuel ruleFuel tetrahedral).mp otherPresent
        · obtain ⟨other, _otherPresent, equal⟩ :=
            (List.mem_map.mp ordinaryPresent)
          contradiction
      · intro executable
        rw [analyzeAromaticCanonicalConcreteStereochemistry,
          List.mem_append]
        left
        exact List.mem_map.mpr ⟨tetrahedral,
          (source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
            carrierFuel ruleFuel tetrahedral).mpr executable, rfl⟩
  | ordinaryDoubleBond ordinaryDoubleBond =>
      unfold AromaticCanonicalConcreteStereochemicalExecutableMember
      constructor
      · intro present
        rw [analyzeAromaticCanonicalConcreteStereochemistry,
          List.mem_append] at present
        rcases present with tetrahedralPresent | ordinaryPresent
        · obtain ⟨other, _otherPresent, equal⟩ :=
            (List.mem_map.mp tetrahedralPresent)
          contradiction
        · obtain ⟨other, otherPresent, equal⟩ :=
            (List.mem_map.mp ordinaryPresent)
          cases equal
          exact
            (source.mem_analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_iff
              carrierFuel ruleFuel ordinaryDoubleBond).mp otherPresent
      · intro executable
        rw [analyzeAromaticCanonicalConcreteStereochemistry,
          List.mem_append]
        right
        exact List.mem_map.mpr ⟨ordinaryDoubleBond,
          (source.mem_analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_iff
            carrierFuel ruleFuel ordinaryDoubleBond).mpr executable, rfl⟩

/-- Independent chemical meaning of every combined output. -/
def DeclarativeAromaticCanonicalConcreteStereochemicalMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalConcreteStereochemicalAssignment) : Prop :=
  match assignment with
  | .tetrahedral tetrahedral =>
      source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel) ruleFuel tetrahedral.center tetrahedral.descriptor
  | .ordinaryDoubleBond ordinaryDoubleBond =>
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialMember
        carrierFuel
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)
        ordinaryDoubleBond

/-- Every descriptor emitted by the combined source scheduler satisfies its independent
Rules-1a--6 or ordinary-double-bond Rules-1a--5 plus exact-geometry judgment. -/
theorem analyzeAromaticCanonicalConcreteStereochemistry_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalConcreteStereochemicalAssignment)
    (present : assignment ∈
      source.analyzeAromaticCanonicalConcreteStereochemistry carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalConcreteStereochemicalMember
      carrierFuel ruleFuel assignment := by
  cases assignment with
  | tetrahedral tetrahedral =>
      have executable :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistry_iff_executableMember
          carrierFuel ruleFuel (.tetrahedral tetrahedral)).mp present
      exact source.aromaticCanonicalConcreteRule3Through6Descriptor?_geometry_sound
        carrierFuel ruleFuel tetrahedral.center tetrahedral.descriptor
        ((source.aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
          carrierFuel ruleFuel tetrahedral.center tetrahedral.descriptor).mpr executable)
  | ordinaryDoubleBond ordinaryDoubleBond =>
      have executable :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistry_iff_executableMember
          carrierFuel ruleFuel (.ordinaryDoubleBond ordinaryDoubleBond)).mp present
      exact source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_member_sound
        carrierFuel ruleFuel ordinaryDoubleBond
        ((source.mem_analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_iff
          carrierFuel ruleFuel ordinaryDoubleBond).mpr executable)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
