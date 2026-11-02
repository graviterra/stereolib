
































import TetraStereo.OneCenter.Rule1bRepresentedAtomObservation
import TetraStereo.OneCenter.CIPAuthoritativeRule1bObservation
import TetraStereo.OneCenter.Rule1bSourceProfileFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity

/-- The explicit BB2013 represented-distance observation.

For a real atom the node's own sphere (`depth`) is read; for a multiple-bond or ring-closure
duplicate the sphere at which the represented atom occurs on the actual root-to-node path is read
from `node.history`; for a phantom the stored root distance is read.  Only `node.atom` and
`node.history` are inspected for duplicate nodes, so stored provenance and attachment distances are
never consulted or overwritten. -/
def representedRule1bObservation (node : RawMolecule.CanonicalBranchNode) : Option ℕ :=
  match node.provenance with
  | RawMolecule.CanonicalNodeProvenance.realAtom => some node.depth
  | RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate _ =>
      Rule1bRepresentedAtomObservation.canonicalRepresentedSphere? node
  | RawMolecule.CanonicalNodeProvenance.ringDuplicate _ =>
      Rule1bRepresentedAtomObservation.canonicalRepresentedSphere? node
  | RawMolecule.CanonicalNodeProvenance.phantom distance => some distance

/-- The BB2013 observer totalizes to exactly the source 2013 observation: its only use of the
shared `node.depth` fallback coincides with the source's own totalization convention. -/
theorem representedRule1bObservation_getD_eq_source (node : RawMolecule.CanonicalBranchNode) :
    (representedRule1bObservation node).getD node.depth =
      Rule1bRepresentedAtomObservation.canonicalSourceObservation2013 node := by
  unfold representedRule1bObservation
    Rule1bRepresentedAtomObservation.canonicalSourceObservation2013
  cases node.provenance <;>
    simp [Rule1bRepresentedAtomObservation.canonicalRepresentedSphere_eq_getD]

/-- Outside the multiple-bond case the BB2013 observer and the legacy stored-distance observer
read the same distance.  Real-atom occurrences are unchanged. -/
theorem representedRule1bObservation_realAtom_eq_legacy (node : RawMolecule.CanonicalBranchNode) :
    representedRule1bObservation
        { node with provenance := RawMolecule.CanonicalNodeProvenance.realAtom } =
      RawMolecule.rule1bRootDistanceObservation
        { node with provenance := RawMolecule.CanonicalNodeProvenance.realAtom } := by
  simp [representedRule1bObservation, RawMolecule.rule1bRootDistanceObservation,
    RawMolecule.CanonicalBranchNode.rule1bRootDistance, RawMolecule.CanonicalBranchNode.depth]

/-- Phantom occurrences are unchanged: both observers read the stored phantom distance. -/
theorem representedRule1bObservation_phantom_eq_legacy
    (node : RawMolecule.CanonicalBranchNode) (distance : ℕ) :
    representedRule1bObservation
        { node with provenance := RawMolecule.CanonicalNodeProvenance.phantom distance } =
      RawMolecule.rule1bRootDistanceObservation
        { node with provenance := RawMolecule.CanonicalNodeProvenance.phantom distance } := by
  simp [representedRule1bObservation, RawMolecule.rule1bRootDistanceObservation,
    RawMolecule.CanonicalBranchNode.rule1bRootDistance]

/-! ## Pinned P-92.2.2 duplicate pair -/

/-- The BB2013 observer reads the represented C2 sphere (3) for the pinned P-92.2.2 multiple-bond
duplicate, exactly as the source 2013 equation declares. -/
theorem duplicatepair_bb2013_observation_eq_represented :
    representedRule1bObservation Rule1bSourceProfile.P92.duplicateNode = some 3 := by
  decide

/-- The stored/legacy observer reads the attached C3 sphere (2) for the same duplicate. -/
theorem duplicatepair_legacy_observation_eq_stored :
    RawMolecule.rule1bRootDistanceObservation Rule1bSourceProfile.P92.duplicateNode = some 2 := by
  decide

/-- The compiled Rule-1b comparison through the BB2013 observer ties the pinned duplicate with its
represented real copy under the explicit mixed-node totalization convention. The 2013
source observation is established for the duplicate; no normative real-node Rule-1b claim is made. -/
theorem duplicatepair_compiled_rule1b_bb2013_eq (mol : RawMolecule) :
    RawMolecule.compareCanonicalNodeRuleAuthoritativeWithRule1b? mol representedRule1bObservation
        RawMolecule.CanonicalRuleStage.rule1b Rule1bSourceProfile.P92.realCopyNode
        Rule1bSourceProfile.P92.duplicateNode = some Ordering.eq := by
  rfl



theorem duplicatepair_compiled_rule1b_legacy_lt (mol : RawMolecule) :
    RawMolecule.compareCanonicalNodeRuleAuthoritativeWithRule1b? mol
        RawMolecule.rule1bRootDistanceObservation RawMolecule.CanonicalRuleStage.rule1b
        Rule1bSourceProfile.P92.realCopyNode Rule1bSourceProfile.P92.duplicateNode =
      some Ordering.lt := by
  rfl

/-- Source-faithful compiled duplicate-pair observation: the 2013 observer reads the represented
sphere (3) and the stored observer reads the attached sphere (2), exactly the two source-profile
equations on the pinned P-92.2.2 duplicate. -/
theorem duplicatepair_comparison_sourcefaithful :
    representedRule1bObservation Rule1bSourceProfile.P92.duplicateNode =
        some (Rule1bSourceProfile.bb2013Observation
          Rule1bSourceProfile.NodeKind.multipleBondDuplicate
          Rule1bSourceProfile.P92.duplicateSpheres) ∧
      RawMolecule.rule1bRootDistanceObservation Rule1bSourceProfile.P92.duplicateNode =
        some (Rule1bSourceProfile.hanson2018Observation
          Rule1bSourceProfile.NodeKind.multipleBondDuplicate
          Rule1bSourceProfile.P92.duplicateSpheres) := by
  constructor
  · rw [Rule1bSourceProfile.P92.bb2013_observation_eq_three]
    exact duplicatepair_bb2013_observation_eq_represented
  · rw [Rule1bSourceProfile.P92.hanson2018_observation_eq_two]
    exact duplicatepair_legacy_observation_eq_stored

end TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity.representedRule1bObservation_getD_eq_source
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity.representedRule1bObservation_realAtom_eq_legacy
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity.representedRule1bObservation_phantom_eq_legacy
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity.duplicatepair_bb2013_observation_eq_represented
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity.duplicatepair_legacy_observation_eq_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity.duplicatepair_compiled_rule1b_bb2013_eq
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity.duplicatepair_compiled_rule1b_legacy_lt
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedProfileFidelity.duplicatepair_comparison_sourcefaithful
