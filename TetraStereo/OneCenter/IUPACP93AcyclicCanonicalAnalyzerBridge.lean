import TetraStereo.OneCenter.IUPACP93AcyclicDescriptorCore
import TetraStereo.OneCenter.AuthoritativeLocalizedApplicability
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAnalysis
import TetraStereo.OneCenter.LocalizedOddCumuleneAnalysis

set_option autoImplicit false

/-!
# Canonical localized-analyzer bridge to the policy-free acyclic P-93 core

This file projects actual scheduled open-cumulene assignments into the physical descriptor core.
The projection contains no citation, name component, nomenclature context, or authority-policy
field.  Analyzer membership proves both core validity for the exact admitted source and the
existing independent declarative meaning of the retained production assignment.

Only soundness is asserted.  A perceived axis can still fail closed because of unresolved or tied
endpoint priorities, absent or degenerate spatial evidence, or insufficient traversal fuel.
Consequently source/core readiness does not yet imply analyzer emission, and no reverse
completeness theorem or membership-defined reference relation appears here.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Acyclic

namespace CertifiedLocalizedCIPInput

namespace LocalizedEvenAxialSpatialAssignment

/-- Project a scheduled even-cumulene result to its preferred P-93 `M/P` physical descriptor
core.  The underlying proved production `Rₐ/Sₐ` assignment remains in the source value. -/
def toP93AcyclicDescriptorCore
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel) :
    P93AcyclicDescriptorCore :=
  { kind := .evenCumulene
    unit := .axis (assignment.axis.1.path.map fun atom => atom.1)
    descriptor := assignment.result.assignment.descriptor.toPreferredP93 }

end LocalizedEvenAxialSpatialAssignment

namespace LocalizedOddCumuleneEZSpatialAssignment

/-- Project a scheduled odd-cumulene result to its emitted `E/Z` physical descriptor core. -/
def toP93AcyclicDescriptorCore
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel) :
    P93AcyclicDescriptorCore :=
  { kind := .oddCumulene
    unit := .axis (assignment.axis.1.path.map fun atom => atom.1)
    descriptor := assignment.result.descriptor }

end LocalizedOddCumuleneEZSpatialAssignment

/-- A retained even-axis assignment already supplies canonical source perception, and its exact
production axial descriptor has an independently proved preferred-P93 conversion. -/
theorem LocalizedEvenAxialSpatialAssignment.toP93AcyclicDescriptorCore_validFor
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel) :
    assignment.toP93AcyclicDescriptorCore.ValidFor input.certified.input := by
  refine ⟨?_, trivial, ?_⟩
  · exact assignment.axis.p93AuthorityEvenAxisPerceived input
  · exact assignment.result.assignment.descriptor.toPreferredP93_recommended.1

/-- Scheduled even-cumulene membership yields the policy-free core and preserves the stronger
independent topology, Rules-1a--5 priority, rational geometry, and descriptor meaning. -/
theorem analyzeLocalizedEvenCumuleneAxial_member_toP93Core_validFor_and_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedEvenCumuleneAxial fuel) :
    assignment.toP93AcyclicDescriptorCore.ValidFor input.certified.input ∧
      input.DeclarativeLocalizedEvenAxialSpatialAssignment fuel assignment :=
  ⟨assignment.toP93AcyclicDescriptorCore_validFor input fuel,
    input.analyzeLocalizedEvenCumuleneAxial_member_conforms fuel assignment present⟩

/-- Independent scheduled odd-cumulene meaning supplies descriptor applicability in addition to
the canonical perceived physical axis retained by the assignment. -/
theorem LocalizedOddCumuleneEZSpatialAssignment.toP93AcyclicDescriptorCore_validFor_of_declarative
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (derived : input.DeclarativeLocalizedOddCumuleneEZSpatialAssignment fuel assignment) :
    assignment.toP93AcyclicDescriptorCore.ValidFor input.certified.input := by
  dsimp [DeclarativeLocalizedOddCumuleneEZSpatialAssignment,
    DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState,
    DeclarativeLocalizedRule3OddCumuleneEZWith] at derived
  obtain ⟨terminalGeometry, _refines, assigned, _recommended⟩ := derived.2.2
  refine ⟨?_, trivial, ?_⟩
  · exact assignment.axis.p93AuthorityOddAxisPerceived input
  · exact (oddCumuleneEZDescriptor?_recommended terminalGeometry
      assignment.result.descriptor
      ((oddCumuleneEZDescriptor?_eq_some_iff terminalGeometry
        assignment.result.descriptor).mpr assigned)).1

/-- Scheduled odd-cumulene membership yields a valid policy-free core and the complete independent
maximal-chain, endpoint-priority, rational-geometry, and P-93 `E/Z` meaning. -/
theorem analyzeLocalizedOddCumuleneEZ_member_toP93Core_validFor_and_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedOddCumuleneEZ fuel) :
    assignment.toP93AcyclicDescriptorCore.ValidFor input.certified.input ∧
      input.DeclarativeLocalizedOddCumuleneEZSpatialAssignment fuel assignment := by
  have derived :=
    input.analyzeLocalizedOddCumuleneEZ_member_conforms fuel assignment present
  exact ⟨assignment.toP93AcyclicDescriptorCore_validFor_of_declarative
      input fuel derived, derived⟩

end CertifiedLocalizedCIPInput

namespace CertifiedLocalizedCIPApplicableInput

/-- Exact-source form of the even-cumulene bridge for a format-neutral admitted input. -/
theorem analyzeLocalizedEvenCumuleneAxial_member_toP93Core_validFor_for_admitted_source
    (admitted : CertifiedLocalizedCIPApplicableInput) (fuel : Nat)
    (assignment : admitted.toCertifiedLocalizedCIPInput.LocalizedEvenAxialSpatialAssignment fuel)
    (present : assignment ∈
      admitted.toCertifiedLocalizedCIPInput.analyzeLocalizedEvenCumuleneAxial fuel) :
    assignment.toP93AcyclicDescriptorCore.ValidFor admitted.source ∧
      admitted.toCertifiedLocalizedCIPInput.DeclarativeLocalizedEvenAxialSpatialAssignment
        fuel assignment := by
  exact admitted.toCertifiedLocalizedCIPInput
    |>.analyzeLocalizedEvenCumuleneAxial_member_toP93Core_validFor_and_conforms
      fuel assignment present

/-- Exact-source form of the odd-cumulene bridge for a format-neutral admitted input. -/
theorem analyzeLocalizedOddCumuleneEZ_member_toP93Core_validFor_for_admitted_source
    (admitted : CertifiedLocalizedCIPApplicableInput) (fuel : Nat)
    (assignment : admitted.toCertifiedLocalizedCIPInput.LocalizedOddCumuleneEZSpatialAssignment
      fuel)
    (present : assignment ∈
      admitted.toCertifiedLocalizedCIPInput.analyzeLocalizedOddCumuleneEZ fuel) :
    assignment.toP93AcyclicDescriptorCore.ValidFor admitted.source ∧
      admitted.toCertifiedLocalizedCIPInput.DeclarativeLocalizedOddCumuleneEZSpatialAssignment
        fuel assignment := by
  exact admitted.toCertifiedLocalizedCIPInput
    |>.analyzeLocalizedOddCumuleneEZ_member_toP93Core_validFor_and_conforms
      fuel assignment present

end CertifiedLocalizedCIPApplicableInput

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedEvenAxialSpatialAssignment.toP93AcyclicDescriptorCore_validFor
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.analyzeLocalizedEvenCumuleneAxial_member_toP93Core_validFor_and_conforms
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedOddCumuleneEZSpatialAssignment.toP93AcyclicDescriptorCore_validFor_of_declarative
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.analyzeLocalizedOddCumuleneEZ_member_toP93Core_validFor_and_conforms
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPApplicableInput.analyzeLocalizedEvenCumuleneAxial_member_toP93Core_validFor_for_admitted_source
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPApplicableInput.analyzeLocalizedOddCumuleneEZ_member_toP93Core_validFor_for_admitted_source
