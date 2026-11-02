import TetraStereo.OneCenter.IUPACRemaining71P93AcyclicReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for three acyclic P-93 rows

This module closes the heteroatom-double-bond, even-cumulene, and odd-cumulene rows as one
dependent family.  The shared production envelope spells out the physical, source-policy,
component, descriptor-authorization, and citation facts carried by an acyclic assignment.  It
deliberately omits `DescriptorApplies`: that mathematical fact is recovered from the row's local
descriptor evaluator.

The even and odd cumulene rows use the exact executable evaluators
`preferredEvenCumuleneAxialDescriptor?` and `oddCumuleneEZDescriptor?`.  The heteroatom row uses
the finite independent `HeteroDoubleBondDescriptorRecommended` relation, whose two admitted
outputs are proved to belong to the heteroatom-double-bond descriptor family; it is not a geometry
evaluator.  No production definition calls a reviewed `Judges` relation.  For the bond and axis
branches reachable by these three rows, physical validity is expanded directly into source graph
and canonical-axis evidence; the unused plane, helix, and polyhedron cases retain their lower
frame-validity predicates solely to keep the shared factorization extensionally exact.

The theorem is uniform in `P93AcyclicAuthorityPolicy`.  It therefore closes production/reference
agreement relative to an explicit policy, but it does not choose a canonical policy or manufacture
raw molecular observations satisfying that policy.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93.Acyclic

/-- Two acyclic rows with exact local descriptor evaluators and one row with an exact finite
descriptor-family relation. -/
inductive Remaining71P93AcyclicReadyAuthorityRow where
  | heteroatomDoubleBonds
  | evenCumulenes
  | oddCumulenes
  deriving DecidableEq, Repr

namespace Remaining71P93AcyclicReadyAuthorityRow

def all : List Remaining71P93AcyclicReadyAuthorityRow :=
  [ .heteroatomDoubleBonds
  , .evenCumulenes
  , .oddCumulenes
  ]

def toAuthorityRow : Remaining71P93AcyclicReadyAuthorityRow →
    Remaining71P93AcyclicAuthorityRow
  | .heteroatomDoubleBonds => .heteroatomDoubleBonds
  | .evenCumulenes => .evenCumulenes
  | .oddCumulenes => .oddCumulenes

def provision (row : Remaining71P93AcyclicReadyAuthorityRow) :
    IUPACNormativeProvision :=
  row.toAuthorityRow.provision

def reference
    (policy : P93AcyclicAuthorityPolicy)
    (row : Remaining71P93AcyclicReadyAuthorityRow) : ProvisionReference :=
  row.toAuthorityRow.reference policy

def provisions : List IUPACNormativeProvision :=
  all.map provision

@[simp] theorem all_length : all.length = 3 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem provisions_length : provisions.length = 3 := by
  rfl

@[simp] theorem provisions_exact :
    provisions =
      [ .p93HeteroatomDoubleBonds
      , .p93EvenCumulenes
      , .p93OddCumulenes
      ] := by
  rfl

@[simp] theorem toAuthorityRow_provision
    (row : Remaining71P93AcyclicReadyAuthorityRow) :
    row.toAuthorityRow.provision = row.provision := by
  rfl

@[simp] theorem toAuthorityRow_reference
    (policy : P93AcyclicAuthorityPolicy)
    (row : Remaining71P93AcyclicReadyAuthorityRow) :
    row.toAuthorityRow.reference policy = row.reference policy := by
  rfl

end Remaining71P93AcyclicReadyAuthorityRow

/-- Source evidence for a physical unit, with the authority carrier's `ValidFor` definition
expanded rather than used as a production premise.  The three rows below reach only the `bond`
and `axis` cases; the remaining cases are retained so the shared assignment factorization is
extensionally exact for every well-typed assignment. -/
def P93AcyclicPhysicalUnitSourceEnvelope
    (policy : P93AuthorityPhysicalObservationPolicy)
    (source : AuthoritativeChemicalInput) : P93AuthorityPhysicalUnit → Prop
  | .atomCenter center =>
      center < source.molecule.atomCount ∧
        ∃ neighbors : List Nat,
          3 ≤ neighbors.length ∧ neighbors.Nodup ∧
            P93AuthorityAtomsBounded source neighbors ∧
            ∀ neighbor ∈ neighbors,
              P93AuthorityBinaryBond source center neighbor ∨
                P93AuthorityMulticenterIncidence source center neighbor
  | .bond first second =>
      first < source.molecule.atomCount ∧
        second < source.molecule.atomCount ∧
        first < second ∧
        P93AuthorityBinaryBond source first second
  | .axis path => P93AuthorityCanonicalCumuleneAxisPerceived source path
  | .plane members =>
      ∃ frame : P93AuthorityPlaneFrame,
        frame.ValidFor source members ∧
          policy.PlanarRestrictionAndAsymmetryObserved source members frame
  | .helix path =>
      ∃ frame : P93AuthorityHelixFrame,
        frame.ValidFor source path ∧ policy.HelixIdentified source path frame
  | .polyhedron center positions =>
      ∃ geometry frame,
        P93AuthorityPolyhedralFrame.ValidFor source center positions geometry frame ∧
          policy.PolyhedralQualitativeFrameObserved
            source center positions geometry frame

theorem p93AcyclicPhysicalUnit_sourceEnvelope_iff_validFor
    (policy : P93AuthorityPhysicalObservationPolicy)
    (source : AuthoritativeChemicalInput)
    (unit : P93AuthorityPhysicalUnit) :
    P93AcyclicPhysicalUnitSourceEnvelope policy source unit ↔
      unit.ValidFor policy source := by
  cases unit <;> rfl

/-- Source and policy facts shared by the three production rows.  Descriptor-family applicability
is intentionally absent and must be supplied by the local evaluator. -/
def P93AcyclicAssignmentSourceEnvelope
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy) : Prop :=
  P93AcyclicPhysicalUnitSourceEnvelope
      policy.physicalObservation source assignment.unit ∧
    P93AcyclicUnitKindMatchesPhysical assignment.kind assignment.unit ∧
    policy.AcyclicUnitObserved source assignment.unit ∧
    policy.UnitKindObserved source assignment.unit assignment.kind ∧
    policy.DescriptorAuthorized source assignment.unit assignment.descriptor ∧
    policy.ComponentAuthorized source assignment.component assignment.unit ∧
    assignment.CitationValidFor policy source

theorem p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy) :
    assignment.ValidFor policy source ↔
      P93AcyclicAssignmentSourceEnvelope policy source assignment ∧
        DescriptorApplies assignment.kind assignment.descriptor := by
  rw [P93AcyclicAuthorityAssignment.ValidFor,
    P93AcyclicAssignmentSourceEnvelope,
    p93AcyclicPhysicalUnit_sourceEnvelope_iff_validFor]
  aesop

theorem heteroDoubleBondDescriptorRecommended_implies_applies
    (context : NomenclatureContext)
    (descriptor : Descriptor)
    (recommended : HeteroDoubleBondDescriptorRecommended context descriptor) :
    DescriptorApplies .heteroatomDoubleBond descriptor := by
  cases context <;> cases descriptor <;>
    simp_all [HeteroDoubleBondDescriptorRecommended, DescriptorApplies]

theorem evenCumuleneEvaluator_descriptor_facts
    (context : NomenclatureContext)
    (generalDescriptor preferredDescriptor assignmentDescriptor : Descriptor)
    (computed : preferredEvenCumuleneAxialDescriptor? generalDescriptor =
      some preferredDescriptor)
    (selected : assignmentDescriptor =
      match context with
      | .preferredIUPACName => preferredDescriptor
      | .general => generalDescriptor) :
    DescriptorApplies .evenDoubleBondCumulene assignmentDescriptor ∧
      DescriptorRecommended context .evenDoubleBondCumulene assignmentDescriptor := by
  cases context with
  | preferredIUPACName =>
      simp only at selected
      subst assignmentDescriptor
      exact preferredEvenCumuleneAxialDescriptor?_recommended
        generalDescriptor preferredDescriptor computed
  | general =>
      simp only at selected
      subst assignmentDescriptor
      have correspondence :=
        (preferredEvenCumuleneAxialDescriptor?_eq_some_iff
          generalDescriptor preferredDescriptor).mp computed
      cases generalDescriptor <;> cases preferredDescriptor <;>
        simp_all [EvenCumuleneAxialDescriptorCorrespondence,
          DescriptorApplies, DescriptorRecommended]

theorem oddCumuleneEvaluator_descriptor_applies
    (geometry : OddCumuleneTerminalGeometry)
    (descriptor : Descriptor)
    (computed : oddCumuleneEZDescriptor? geometry = some descriptor) :
    DescriptorApplies .oddDoubleBondCumulene descriptor :=
  (oddCumuleneEZDescriptor?_recommended geometry descriptor computed).1

namespace Remaining71P93AcyclicReadyAuthorityRow

/-- One source-bound production relation for the two evaluator rows and the finite-relation row. -/
def ProductionJudges
    (policy : P93AcyclicAuthorityPolicy) :
    (row : Remaining71P93AcyclicReadyAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .heteroatomDoubleBonds, source, observation =>
      P93AcyclicAssignmentSourceEnvelope policy source observation.assignment ∧
        observation.assignment.kind = .heteroatomDoubleBond ∧
        HeteroDoubleBondDescriptorRecommended observation.context
          observation.assignment.descriptor
  | .evenCumulenes, source, observation =>
      P93AcyclicAssignmentSourceEnvelope policy source observation.assignment ∧
        observation.assignment.kind = .evenDoubleBondCumulene ∧
        preferredEvenCumuleneAxialDescriptor? observation.generalDescriptor =
          some observation.preferredDescriptor ∧
        observation.assignment.descriptor =
          match observation.context with
          | .preferredIUPACName => observation.preferredDescriptor
          | .general => observation.generalDescriptor
  | .oddCumulenes, source, observation =>
      P93AcyclicAssignmentSourceEnvelope policy source observation.assignment ∧
        observation.assignment.kind = .oddDoubleBondCumulene ∧
        (∃ path, observation.assignment.unit = .axis path ∧
          policy.OddCumuleneTerminalGeometryObserved source path observation.geometry) ∧
        oddCumuleneEZDescriptor? observation.geometry =
          some observation.assignment.descriptor

/-- The three source-bound producer cases are exactly their independently reviewed judgments. -/
theorem production_eq_reference
    (policy : P93AcyclicAuthorityPolicy)
    (row : Remaining71P93AcyclicReadyAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row with
  | heteroatomDoubleBonds =>
      change
        (P93AcyclicAssignmentSourceEnvelope policy source observation.assignment ∧
          observation.assignment.kind = .heteroatomDoubleBond ∧
          HeteroDoubleBondDescriptorRecommended observation.context
            observation.assignment.descriptor) ↔
        ((observation.assignment.ValidFor policy source ∧
          observation.assignment.kind = .heteroatomDoubleBond) ∧
          HeteroDoubleBondDescriptorRecommended observation.context
            observation.assignment.descriptor)
      constructor
      · rintro ⟨sourceEnvelope, kind, recommended⟩
        have applies : DescriptorApplies observation.assignment.kind
            observation.assignment.descriptor := by
          rw [kind]
          exact heteroDoubleBondDescriptorRecommended_implies_applies
            observation.context observation.assignment.descriptor recommended
        exact ⟨⟨
          (p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
            policy source observation.assignment).2 ⟨sourceEnvelope, applies⟩,
          kind⟩, recommended⟩
      · rintro ⟨⟨valid, kind⟩, recommended⟩
        exact ⟨
          (p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
            policy source observation.assignment).1 valid |>.1,
          kind, recommended⟩
  | evenCumulenes =>
      change
        (P93AcyclicAssignmentSourceEnvelope policy source observation.assignment ∧
          observation.assignment.kind = .evenDoubleBondCumulene ∧
          preferredEvenCumuleneAxialDescriptor? observation.generalDescriptor =
            some observation.preferredDescriptor ∧
          observation.assignment.descriptor =
            (match observation.context with
            | .preferredIUPACName => observation.preferredDescriptor
            | .general => observation.generalDescriptor)) ↔
        (observation.assignment.ValidFor policy source ∧
          observation.assignment.kind = .evenDoubleBondCumulene ∧
          EvenCumuleneAxialDescriptorCorrespondence observation.generalDescriptor
            observation.preferredDescriptor ∧
          observation.assignment.descriptor =
            (match observation.context with
            | .preferredIUPACName => observation.preferredDescriptor
            | .general => observation.generalDescriptor) ∧
          DescriptorRecommended observation.context .evenDoubleBondCumulene
            observation.assignment.descriptor)
      constructor
      · rintro ⟨sourceEnvelope, kind, computed, selected⟩
        have descriptorFacts := evenCumuleneEvaluator_descriptor_facts
          observation.context observation.generalDescriptor observation.preferredDescriptor
          observation.assignment.descriptor computed selected
        have applies : DescriptorApplies observation.assignment.kind
            observation.assignment.descriptor := by
          rw [kind]
          exact descriptorFacts.1
        exact ⟨
          (p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
            policy source observation.assignment).2 ⟨sourceEnvelope, applies⟩,
          kind,
          (preferredEvenCumuleneAxialDescriptor?_eq_some_iff
            observation.generalDescriptor observation.preferredDescriptor).mp computed,
          selected,
          descriptorFacts.2⟩
      · rintro ⟨valid, kind, correspondence, selected, _recommended⟩
        exact ⟨
          (p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
            policy source observation.assignment).1 valid |>.1,
          kind,
          (preferredEvenCumuleneAxialDescriptor?_eq_some_iff
            observation.generalDescriptor observation.preferredDescriptor).mpr correspondence,
          selected⟩
  | oddCumulenes =>
      change
        (P93AcyclicAssignmentSourceEnvelope policy source observation.assignment ∧
          observation.assignment.kind = .oddDoubleBondCumulene ∧
          (∃ path, observation.assignment.unit = .axis path ∧
            policy.OddCumuleneTerminalGeometryObserved source path observation.geometry) ∧
          oddCumuleneEZDescriptor? observation.geometry =
            some observation.assignment.descriptor) ↔
        (observation.assignment.ValidFor policy source ∧
          observation.assignment.kind = .oddDoubleBondCumulene ∧
          (∃ path, observation.assignment.unit = .axis path ∧
            policy.OddCumuleneTerminalGeometryObserved source path observation.geometry) ∧
          OddCumuleneEZAssignment observation.geometry observation.assignment.descriptor)
      constructor
      · rintro ⟨sourceEnvelope, kind, geometryObserved, computed⟩
        have applies : DescriptorApplies observation.assignment.kind
            observation.assignment.descriptor := by
          rw [kind]
          exact oddCumuleneEvaluator_descriptor_applies
            observation.geometry observation.assignment.descriptor computed
        exact ⟨
          (p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
            policy source observation.assignment).2 ⟨sourceEnvelope, applies⟩,
          kind, geometryObserved,
          (oddCumuleneEZDescriptor?_eq_some_iff
            observation.geometry observation.assignment.descriptor).mp computed⟩
      · rintro ⟨valid, kind, geometryObserved, assigned⟩
        exact ⟨
          (p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
            policy source observation.assignment).1 valid |>.1,
          kind, geometryObserved,
          (oddCumuleneEZDescriptor?_eq_some_iff
            observation.geometry observation.assignment.descriptor).mpr assigned⟩

theorem reference_applicable_of_judged
    (policy : P93AcyclicAuthorityPolicy)
    (row : Remaining71P93AcyclicReadyAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row with
  | heteroatomDoubleBonds =>
      exact ⟨observation, judged.1⟩
  | evenCumulenes =>
      exact ⟨observation, judged⟩
  | oddCumulenes =>
      exact ⟨observation, judged⟩

end Remaining71P93AcyclicReadyAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93AcyclicReadyAuthorityRow.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93AcyclicPhysicalUnit_sourceEnvelope_iff_validFor
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.evenCumuleneEvaluator_descriptor_facts
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93AcyclicReadyAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93AcyclicReadyAuthorityRow.reference_applicable_of_judged
