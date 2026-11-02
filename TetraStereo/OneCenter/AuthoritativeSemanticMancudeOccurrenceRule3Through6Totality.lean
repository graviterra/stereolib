import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Scheduler
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6InitialPartitionTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact totality boundary for the source-canonical Rules 1a--6 scheduler

This module characterizes every successful and unsuccessful result of the one-shot scheduler.
The readiness proposition exposes the actual chemical obligations at this boundary: four roots,
a completely constructed Rules-1a--5 partition, admissible Rule-6 topology, and one independently
stated P-92 branch descriptor judgment.
-/

/-- Exact non-wrapper meaning of one executable Rules-1a--6 descriptor.  The initial partition is
recorded by its construction equation; all later applicability and descriptor claims are stated
by the independent declarative relations. -/
def AromaticCanonicalRule3Through6ExecutableDescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS) : Prop :=
  ∃ (rootsLength : roots.length = 4)
      (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel),
    source.buildAromaticCanonicalRule3Through5InitialPartition?
        target view fuel roots = some partition ∧
      source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition ∧
      source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
        target view fuel roots partition parity descriptor

/-- The one-shot scheduler is complete as well as sound at its explicit construction boundary:
it emits exactly the descriptors satisfying the executable-partition and independent chemical
judgments above. -/
theorem aromaticCanonicalRule3Through6Descriptor?_eq_some_iff_executableJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS) :
    source.aromaticCanonicalRule3Through6Descriptor?
        center target view fuel roots parity = some descriptor ↔
      source.AromaticCanonicalRule3Through6ExecutableDescriptorJudgment
        center target view fuel roots parity descriptor := by
  unfold aromaticCanonicalRule3Through6Descriptor?
    AromaticCanonicalRule3Through6ExecutableDescriptorJudgment
  constructor
  · intro computed
    by_cases rootsLength : roots.length = 4
    · cases partitionComputed :
          source.buildAromaticCanonicalRule3Through5InitialPartition?
            target view fuel roots with
      | none => simp [rootsLength, partitionComputed] at computed
      | some partition =>
          have checked :
              source.aromaticCanonicalRule3Through6DescriptorForPartitionChecked?
                  center target view fuel roots rootsLength partition parity =
                some descriptor := by
            simpa [rootsLength, partitionComputed] using computed
          have exactMeaning :=
            (source.aromaticCanonicalRule3Through6DescriptorForPartitionChecked?_eq_some_iff
              center target view fuel roots rootsLength partition parity descriptor).mp checked
          exact ⟨rootsLength, partition, rfl, exactMeaning.1, exactMeaning.2⟩
    · simp [rootsLength] at computed
  · rintro ⟨rootsLength, partition, partitionComputed, applicable, judged⟩
    have checked :
        source.aromaticCanonicalRule3Through6DescriptorForPartitionChecked?
            center target view fuel roots rootsLength partition parity = some descriptor :=
      (source.aromaticCanonicalRule3Through6DescriptorForPartitionChecked?_eq_some_iff
        center target view fuel roots rootsLength partition parity descriptor).mpr
          ⟨applicable, judged⟩
    simpa [rootsLength, partitionComputed] using checked

/-- All evidence needed for this scheduler to assign some descriptor, without preselecting which
descriptor it must be. -/
def AromaticCanonicalRule3Through6Ready
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) : Prop :=
  ∃ descriptor,
    source.AromaticCanonicalRule3Through6ExecutableDescriptorJudgment
      center target view fuel roots parity descriptor

/-- Readiness is exactly existence of a successful descriptor computation. -/
theorem aromaticCanonicalRule3Through6Ready_iff_exists_descriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) :
    source.AromaticCanonicalRule3Through6Ready center target view fuel roots parity ↔
      ∃ descriptor,
        source.aromaticCanonicalRule3Through6Descriptor?
          center target view fuel roots parity = some descriptor := by
  unfold AromaticCanonicalRule3Through6Ready
  constructor <;> rintro ⟨descriptor, witnessed⟩
  · exact ⟨descriptor,
      (source.aromaticCanonicalRule3Through6Descriptor?_eq_some_iff_executableJudgment
        center target view fuel roots parity descriptor).mpr witnessed⟩
  · exact ⟨descriptor,
      (source.aromaticCanonicalRule3Through6Descriptor?_eq_some_iff_executableJudgment
        center target view fuel roots parity descriptor).mp witnessed⟩

/-- Equivalently, the scheduler returns `none` exactly when its full readiness proposition is
false.  There is no additional hidden failure branch at the one-shot scheduler layer. -/
theorem aromaticCanonicalRule3Through6Descriptor?_eq_none_iff_not_ready
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) :
    source.aromaticCanonicalRule3Through6Descriptor?
        center target view fuel roots parity = none ↔
      ¬ source.AromaticCanonicalRule3Through6Ready center target view fuel roots parity := by
  rw [source.aromaticCanonicalRule3Through6Ready_iff_exists_descriptor]
  cases computed : source.aromaticCanonicalRule3Through6Descriptor?
      center target view fuel roots parity with
  | none => simp
  | some descriptor => simp

/-- The exact executable judgment implies the earlier wholly declarative soundness judgment;
the construction equation cannot weaken the chemical meaning of a successful result. -/
theorem AromaticCanonicalRule3Through6ExecutableDescriptorJudgment.complete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS)
    (judged : source.AromaticCanonicalRule3Through6ExecutableDescriptorJudgment
      center target view fuel roots parity descriptor) :
    source.AromaticCanonicalRule3Through6CompleteDescriptorJudgment
      center target view fuel roots parity descriptor := by
  rcases judged with
    ⟨rootsLength, partition, partitionComputed, applicable, branchJudgment⟩
  exact ⟨rootsLength, partition,
    source.buildAromaticCanonicalRule3Through5InitialPartition?_sound
      target view fuel roots partition partitionComputed,
    applicable, branchJudgment⟩

/-- Descriptor-independent readiness stated one construction layer lower.  The root inputs are
resolved, and the uniquely constructed canonical partition is chemically admissible and has a
P-92 branch descriptor.  Universal quantification prevents the definition from selecting a
convenient noncanonical partition. -/
def AromaticCanonicalRule3Through6ChemicallyReady
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) : Prop :=
  ∃ rootsLength : roots.length = 4,
    source.AromaticCanonicalRule3Through5RootInputsResolved target view fuel roots ∧
      ∀ partition,
        source.buildAromaticCanonicalRule3Through5InitialPartition?
            target view fuel roots = some partition →
          source.AromaticCanonicalRule6TopologyAdmissible
              center roots rootsLength partition ∧
            ∃ descriptor,
              source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
                target view fuel roots partition parity descriptor

/-- Lower-level chemical readiness is exactly the scheduler readiness relation. -/
theorem aromaticCanonicalRule3Through6ChemicallyReady_iff_ready
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) :
    source.AromaticCanonicalRule3Through6ChemicallyReady
        center target view fuel roots parity ↔
      source.AromaticCanonicalRule3Through6Ready
        center target view fuel roots parity := by
  constructor
  · rintro ⟨rootsLength, inputsResolved, everyPartition⟩
    obtain ⟨partition, partitionComputed⟩ :=
      (source.exists_buildAromaticCanonicalRule3Through5InitialPartition_iff_inputsResolved
        target view fuel roots).mpr inputsResolved
    obtain ⟨applicable, descriptor, judged⟩ :=
      everyPartition partition partitionComputed
    exact ⟨descriptor, rootsLength, partition, partitionComputed, applicable, judged⟩
  · rintro ⟨descriptor, rootsLength, partition, partitionComputed, applicable, judged⟩
    have inputsResolved :
        source.AromaticCanonicalRule3Through5RootInputsResolved target view fuel roots :=
      (source.exists_buildAromaticCanonicalRule3Through5InitialPartition_iff_inputsResolved
        target view fuel roots).mp ⟨partition, partitionComputed⟩
    refine ⟨rootsLength, inputsResolved, ?_⟩
    intro otherPartition otherComputed
    have partitionEq : otherPartition = partition := by
      apply Option.some.inj
      exact otherComputed.symm.trans partitionComputed
    subst otherPartition
    exact ⟨applicable, descriptor, judged⟩

/-- Final exact refusal theorem at the lower chemical-readiness boundary. -/
theorem aromaticCanonicalRule3Through6Descriptor?_eq_none_iff_not_chemicallyReady
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) :
    source.aromaticCanonicalRule3Through6Descriptor?
        center target view fuel roots parity = none ↔
      ¬ source.AromaticCanonicalRule3Through6ChemicallyReady
        center target view fuel roots parity := by
  rw [source.aromaticCanonicalRule3Through6ChemicallyReady_iff_ready,
    source.aromaticCanonicalRule3Through6Descriptor?_eq_none_iff_not_ready]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
