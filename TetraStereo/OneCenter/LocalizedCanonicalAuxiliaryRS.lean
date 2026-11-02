import TetraStereo.OneCenter.LocalizedOuterRootPhysicalPriority
import TetraStereo.OneCenter.LocalizedIndependentAuxiliaryRSClosure
import TetraStereo.KernelOnly

set_option autoImplicit false

noncomputable section

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-!
# Actual auxiliary letters against canonical physical incoming-cut priority

The priority below quantifies over graph-only full incoming-cut trees. It does not select an
executed expansion or depend on a successful comparison. The original outer root is retained.
The domain supplies the actual graph, degree-four centre, physical geometry and configuration;
its rigid/twin restrictions are unchanged. Correspondence, highest-first order and the returned
auxiliary letter are derived rather than supplied.

This is the independent absolute-letter connection for rigid auxiliary centres in the declared
outer-digraph distance profile. It does not establish the final pseudoasymmetric root's absolute
letter, all molecular domains, or equivalence of that profile with normative 2013 chemistry.
-/

namespace DomainPhysicalContext

variable {input : LocalizedUniversalReference.Input}

/-- Graph-only canonical priority, using the physical incoming cuts named by the actual frame.
The frame fixes which molecular neighbours the four slots denote; no key or sorted tree enters
the priority relation. -/
def canonicalPriority (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) (left right : Fin 4) : Prop :=
  PhysicalTreeCanonicalOutcome input.certified.moleculeGraph context.target.1.root
    (((context.frame branch).cursorAt left).previous?.bind (fun p => p.1.node.current?))
    (((context.frame branch).cursorAt right).previous?.bind (fun p => p.1.node.current?))
    (cursorAtom context.singleBonded context.acyclic ((context.frame branch).cursorAt left))
    (cursorAtom context.singleBonded context.acyclic ((context.frame branch).cursorAt right))
    Ordering.gt

/-- The actual four-slot comparison agrees with canonical physical priority. Both successful
key builds are obtained from the derived actual frame; neither is a hypothesis. -/
theorem canonicalPriority_correspondence (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ConstitutionalPriorityCorrespondence input.certified context.target context.view
      (context.frame branch) (context.derived branch) (context.canonicalPriority branch) := by
  intro left right _different
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    change input.certified.certified.input.molecule.atomCount ≤
      input.certified.certified.input.molecule.atomCount + 1
    omega
  have rootAt (index : Fin 4) :
      ((context.frame branch).cursorAt index).occurrence.1.root = context.target.1.root := by
    have root := frameSlotBranchTree_root input.certified context.target context.view
      (context.frame branch) (context.derived branch) index
    rwa [frameSlotBranchTree_source] at root
  exact (physicalTreeCanonicalOutcome_iff_actualComparison enough context.singleBonded
    context.acyclic .rule4a context.target context.view context.target.1.root
    ((context.frame branch).cursorAt left) ((context.frame branch).cursorAt right)
    ((context.frame branch).cursorAt_valid input.certified context.target
      (context.derived branch) left)
    ((context.frame branch).cursorAt_valid input.certified context.target
      (context.derived branch) right)
    (rootAt left) (rootAt right)
    (((context.frame branch).compoundKeyAt input.certified context.target context.view
      (context.derived branch) left).prior.rule4aKey)
    (((context.frame branch).compoundKeyAt input.certified context.target context.view
      (context.derived branch) right).prior.rule4aKey)
    (buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame input.certified context.target
      context.view (context.frame branch) (context.derived branch) left)
    (buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame input.certified context.target
      context.view (context.frame branch) (context.derived branch) right)
    Ordering.gt).symm

/-- The existing derived order is highest-first for the independent canonical relation. -/
theorem order_canonical (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    IndependentHighestFirstFor (context.canonicalPriority branch) (context.order branch) :=
  context.order_independent_of_correspondence branch (context.canonicalPriority branch)
    (context.canonicalPriority_correspondence branch)

/-- Independent physical descriptor: some complete highest-first physical order has the stated
orientation. The definition mentions neither the runtime key nor its returned descriptor. -/
def CanonicalPhysicalDescriptor (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) (rs : RS) : Prop :=
  ∃ order : List (Fin 4),
    IndependentHighestFirstFor (context.canonicalPriority branch) order ∧
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        (order.map (context.pointsAt branch)) rs

/-- Actual generated auxiliary letter iff the canonical physical descriptor, with no supplied
priority correspondence, successful build, sorting order or desired letter. -/
theorem referenceState_iff_canonicalPhysicalDescriptor
    (context : DomainPhysicalContext input) (branch : DomainPhysicalRigidBranch context)
    (rs : RS) :
    LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ↔
      context.CanonicalPhysicalDescriptor branch rs := by
  constructor
  · intro actual
    refine ⟨context.order branch, context.order_canonical branch, ?_⟩
    exact (referenceState_eq_chiral_iff_domainPriorityDescriptor input context branch
      (context.canonicalPriority branch) (context.canonicalPriority_correspondence branch)
      rs).mp actual
  · rintro ⟨order, highestFirst, descriptor⟩
    exact (referenceState_eq_chiral_iff_domainCanonicalPriorityDescriptor input context branch
      (context.canonicalPriority branch) (context.canonicalPriority_correspondence branch)
      order highestFirst rs).mpr descriptor

/-- Every rigid auxiliary centre in this physical domain actually produces its independent
canonical physical letter. -/
theorem exists_referenceState_canonicalPhysicalDescriptor
    (context : DomainPhysicalContext input) (branch : DomainPhysicalRigidBranch context) :
    ∃ rs : RS,
      LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ∧
        context.CanonicalPhysicalDescriptor branch rs := by
  obtain ⟨rs, actual⟩ := context.exists_chiral branch
  exact ⟨rs, actual, (context.referenceState_iff_canonicalPhysicalDescriptor branch rs).mp actual⟩

/-- The physical criterion determines at most one absolute auxiliary letter. -/
theorem canonicalPhysicalDescriptor_unique
    (context : DomainPhysicalContext input) (branch : DomainPhysicalRigidBranch context)
    {first second : RS}
    (left : context.CanonicalPhysicalDescriptor branch first)
    (right : context.CanonicalPhysicalDescriptor branch second) : first = second := by
  have leftState := (context.referenceState_iff_canonicalPhysicalDescriptor branch first).mpr left
  have rightState := (context.referenceState_iff_canonicalPhysicalDescriptor branch second).mpr right
  have same := leftState.symm.trans rightState
  cases same
  rfl

/-- Both physical branches: terminal twins read none; every non-twin has the independently
characterized chiral letter. The underlying physical domain supplies the rigid alternative. -/
theorem referenceState_canonicalPhysicalClassification
    (context : DomainPhysicalContext input) :
    (ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule context.center →
      LocalizedUniversalReference.referenceState input context.target = none) ∧
    (∀ notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule context.center,
      ∃ rs : RS,
        LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ∧
          context.CanonicalPhysicalDescriptor ⟨notTwin⟩ rs) := by
  exact ⟨fun twin => referenceState_eq_none_of_domainPhysicalTwin input context twin,
    fun notTwin => context.exists_referenceState_canonicalPhysicalDescriptor ⟨notTwin⟩⟩

end DomainPhysicalContext

assert_kernel_only DomainPhysicalContext.canonicalPriority
assert_kernel_only DomainPhysicalContext.canonicalPriority_correspondence
assert_kernel_only DomainPhysicalContext.order_canonical
assert_kernel_only DomainPhysicalContext.CanonicalPhysicalDescriptor
assert_kernel_only DomainPhysicalContext.referenceState_iff_canonicalPhysicalDescriptor
assert_kernel_only DomainPhysicalContext.exists_referenceState_canonicalPhysicalDescriptor
assert_kernel_only DomainPhysicalContext.canonicalPhysicalDescriptor_unique
assert_kernel_only DomainPhysicalContext.referenceState_canonicalPhysicalClassification

end TetraStereo.OneCenter
