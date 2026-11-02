import TetraStereo.OneCenter.DeclarativeCIPCanonicalAddressing
import TetraStereo.OneCenter.LocalizedOuterRootPhysicalPriority
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Observer-parametric constitutional vector keys for retained outer-root contexts

The recursive key construction is generalized over its three node-observation columns.  A
contextual observer can therefore use physical graph distance from a retained outer root without
changing the established canonical-addressing key.  Real nodes use `(Z, dist outerRoot atom,
mass)`; non-real Rule 1b observations retain the existing totalized positional profile.  No
runtime key, comparator, or ring-duplicate semantics are changed here.
-/

namespace TetraStereo.OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (Key assemble sortDesc)
universe u

noncomputable section
open scoped Classical

section ParametricKey

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
variable (graph : RootedDigraph Atom)
local instance contextualKeyNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- One component at a node, with an explicitly selected observation and the same child-key
projection/assembly used by the established rule-major key. -/
def ruleComponentWithObservations (W D : ℕ)
    (observe : ConstitutionalRule → graph.Node → ℤ)
    (rule : ConstitutionalRule) (node : graph.Node) (ranked : List (List (Key ℤ))) : Key ℤ :=
  assemble W D (observe rule node)
    (ranked.map fun key => key.getD (ruleIndex rule) [])

/-- Recursive three-column rule-major key over any node-observation family.  Siblings are sorted
by the same complete vector key, then every rule component is assembled over that one order. -/
noncomputable def ruleKeyWithObservations (W D : ℕ)
    (observe : ConstitutionalRule → graph.Node → ℤ) (node : graph.Node) : List (Key ℤ) :=
  let ranked := sortDesc ((graph.childList node).attach.map
    fun child => ruleKeyWithObservations W D observe child.1)
  [ruleComponentWithObservations graph W D observe .rule1aAtomicNumber node ranked,
   ruleComponentWithObservations graph W D observe .rule1bDuplicateNodeProximity node ranked,
   ruleComponentWithObservations graph W D observe .rule2AtomicMass node ranked]
termination_by graph.height + 1 - graph.depth node
decreasing_by
  have hchild := (graph.mem_childList).1 child.2
  have hdepth := graph.child_depth hchild
  have hle := graph.depth_le_height child.1
  omega

omit [Fintype Atom] [DecidableEq Atom] in
/-- Equation with the un-attached child list, for proof-facing recursive arguments. -/
theorem ruleKeyWithObservations_eq (W D : ℕ)
    (observe : ConstitutionalRule → graph.Node → ℤ) (node : graph.Node) :
    ruleKeyWithObservations (graph := graph) W D observe node =
      let ranked := sortDesc ((graph.childList node).map
        (ruleKeyWithObservations (graph := graph) W D observe))
      [ruleComponentWithObservations graph W D observe .rule1aAtomicNumber node ranked,
       ruleComponentWithObservations graph W D observe .rule1bDuplicateNodeProximity node ranked,
       ruleComponentWithObservations graph W D observe .rule2AtomicMass node ranked] := by
  rw [ruleKeyWithObservations]
  simp only [List.attach_map_val]

omit [Fintype Atom] [DecidableEq Atom] in
/-- Reading the requested rule component from the generic vector key. -/
theorem ruleKeyWithObservations_getD (W D : ℕ)
    (observe : ConstitutionalRule → graph.Node → ℤ) (rule : ConstitutionalRule)
    (node : graph.Node) :
    (ruleKeyWithObservations (graph := graph) W D observe node).getD (ruleIndex rule) [] =
      ruleComponentWithObservations graph W D observe rule node
        (sortDesc ((graph.childList node).map
          (ruleKeyWithObservations (graph := graph) W D observe))) := by
  rw [ruleKeyWithObservations_eq]
  cases rule <;> rfl

omit [Fintype Atom] [DecidableEq Atom] in
/-- The observer-parametric key is well shaped at every node and for every component. -/
theorem ruleKeyWithObservations_wellShaped (W D : ℕ)
    (observe : ConstitutionalRule → graph.Node → ℤ) (rule : ConstitutionalRule) :
    ∀ node, Certificate.CanonicalSphereKey.WellShaped W D
      ((ruleKeyWithObservations (graph := graph) W D observe node).getD (ruleIndex rule) []) := by
  intro node
  refine node_induction graph (motive := fun node => ∀ rule, Certificate.CanonicalSphereKey.WellShaped W D
    ((ruleKeyWithObservations (graph := graph) W D observe node).getD (ruleIndex rule) [])) ?_ node rule
  intro node ih component
  rw [ruleKeyWithObservations_getD]
  apply Certificate.CanonicalSphereKey.assemble_wellShaped
  intro key hkey
  obtain ⟨childKey, hchildKey, rfl⟩ := List.mem_map.1 hkey
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.1
    (Certificate.CanonicalSphereKey.sortDesc_mem hchildKey)
  exact ih child ((graph.mem_childList).1 hchild) component

omit [Fintype Atom] [DecidableEq Atom] in
/-- Extensionality: pointwise-equal observations produce identical recursive vector keys. -/
theorem ruleKeyWithObservations_congr (W D : ℕ)
    (left right : ConstitutionalRule → graph.Node → ℤ)
    (observed : ∀ rule node, left rule node = right rule node) :
    ∀ node, ruleKeyWithObservations (graph := graph) W D left node =
      ruleKeyWithObservations (graph := graph) W D right node := by
  refine node_induction graph (motive := fun node =>
    ruleKeyWithObservations (graph := graph) W D left node =
      ruleKeyWithObservations (graph := graph) W D right node) ?_
  intro node ih
  rw [ruleKeyWithObservations_eq, ruleKeyWithObservations_eq]
  have hchildren :
      sortDesc ((graph.childList node).map (ruleKeyWithObservations (graph := graph) W D left)) =
        sortDesc ((graph.childList node).map (ruleKeyWithObservations (graph := graph) W D right)) := by
    congr 1
    apply List.map_congr_left
    intro child hchild
    exact ih child ((graph.mem_childList).1 hchild)
  simp only [ruleComponentWithObservations, observed, hchildren]

/-- The existing `ruleKey` is the parametric construction at its established observations. -/
theorem ruleKeyWithObservations_eq_ruleKey (molecule : MoleculeGraph Atom) (W D : ℕ)
    (node : graph.Node) :
    ruleKeyWithObservations (graph := graph) W D (nodeObservation molecule graph) node =
      ruleKey molecule graph W D node := by
  refine node_induction graph (motive := fun node =>
    ruleKeyWithObservations (graph := graph) W D (nodeObservation molecule graph) node =
      ruleKey molecule graph W D node) ?_ node
  intro current ih
  rw [ruleKeyWithObservations_eq, ruleKey_eq]
  have hchildren :
      sortDesc ((graph.childList current).map
          (ruleKeyWithObservations (graph := graph) W D (nodeObservation molecule graph))) =
        sortDesc ((graph.childList current).map (ruleKey molecule graph W D)) := by
    congr 1
    apply List.map_congr_left
    intro child hchild
    exact ih child ((graph.mem_childList).1 hchild)
  simp [ruleComponentWithObservations, ruleComponent, hchildren]

end ParametricKey

section ContextualObservation

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
local instance contextualObservationNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Contextual natural-number observation.  Only a real represented atom changes Rule 1b: it
uses physical distance from the fixed outer root.  Non-real Rule 1b entries preserve the existing
position/provenance totalization; Rule 1a and Rule 2 always use the established observation. -/
def contextualRuleValue (outerRoot : Atom) : ConstitutionalRule → graph.Node → ℕ
  | .rule1aAtomicNumber, node =>
      ruleValue molecule .rule1aAtomicNumber (List.replicate (graph.depth node) 0)
        (some (graph.label node))
  | .rule1bDuplicateNodeProximity, node =>
      match graph.label node with
      | ⟨some atom, .realAtom⟩ => molecule.underlyingSimpleGraph.dist outerRoot atom
      | label => ruleValue molecule .rule1bDuplicateNodeProximity
          (List.replicate (graph.depth node) 0) (some label)
  | .rule2AtomicMass, node =>
      ruleValue molecule .rule2AtomicMass (List.replicate (graph.depth node) 0)
        (some (graph.label node))

/-- Priority-oriented contextual observation for the retained outer-root profile. -/
def contextualNodeObservation (outerRoot : Atom) (rule : ConstitutionalRule)
    (node : graph.Node) : ℤ :=
  priorityValue rule (contextualRuleValue molecule graph outerRoot rule node)

/-- Contextual rule-major vector key.  It is the same generic constructor as `ruleKey`, with only
the node observations supplied by the fixed outer-root context. -/
noncomputable def contextualRuleKey (outerRoot : Atom) (W D : ℕ) (node : graph.Node) :
    List (Key ℤ) :=
  ruleKeyWithObservations graph W D (contextualNodeObservation molecule graph outerRoot) node

/-- At a real node, the contextual Rule 1b root value is exactly the molecular graph distance
from `outerRoot`. -/
theorem contextualRuleValue_rule1b_real (outerRoot : Atom) (node : graph.Node) (atom : Atom)
    (label : graph.label node = ⟨some atom, .realAtom⟩) :
    contextualRuleValue molecule graph outerRoot .rule1bDuplicateNodeProximity node =
      molecule.underlyingSimpleGraph.dist outerRoot atom := by
  simp [contextualRuleValue, label]

/-- Contextual Rule 1a remains the established atomic-number observation. -/
theorem contextualNodeObservation_rule1a (outerRoot : Atom) (node : graph.Node) :
    contextualNodeObservation molecule graph outerRoot .rule1aAtomicNumber node =
      nodeObservation molecule graph .rule1aAtomicNumber node := rfl

/-- Contextual Rule 2 remains the established atomic-mass observation. -/
theorem contextualNodeObservation_rule2 (outerRoot : Atom) (node : graph.Node) :
    contextualNodeObservation molecule graph outerRoot .rule2AtomicMass node =
      nodeObservation molecule graph .rule2AtomicMass node := rfl

/-- The priority-oriented Rule 1b value at a real node is negative distance from the retained
outer root. -/
theorem contextualNodeObservation_rule1b_real (outerRoot : Atom) (node : graph.Node)
    (atom : Atom) (label : graph.label node = ⟨some atom, .realAtom⟩) :
    contextualNodeObservation molecule graph outerRoot .rule1bDuplicateNodeProximity node =
      -(molecule.underlyingSimpleGraph.dist outerRoot atom : ℤ) := by
  simp [contextualNodeObservation, contextualRuleValue, priorityValue, label]

/-- If every real node's retained outer-root distance is its old represented depth plus one,
contextual observations agree exactly with the established canonical observations.  This is the
specialization needed for original-root ligand digraphs; it is not asserted for rerooted contexts. -/
theorem contextualNodeObservation_eq_nodeObservation_of_depth (outerRoot : Atom)
    (distanceProfile : ∀ node atom,
      graph.label node = ⟨some atom, .realAtom⟩ →
        molecule.underlyingSimpleGraph.dist outerRoot atom = graph.depth node + 1) :
    ∀ rule node, contextualNodeObservation molecule graph outerRoot rule node =
      nodeObservation molecule graph rule node := by
  intro rule node
  cases rule with
  | rule1aAtomicNumber => rfl
  | rule2AtomicMass => rfl
  | rule1bDuplicateNodeProximity =>
      cases hlabel : graph.label node with
      | mk atom? provenance =>
        cases atom? with
        | none =>
          simp [contextualNodeObservation, contextualRuleValue, nodeObservation,
            ruleValue, nodeRule1bRootDistance, hlabel]
        | some atom =>
          cases provenance with
          | realAtom =>
              have hd := distanceProfile node atom hlabel
              simp only [contextualNodeObservation, nodeObservation, contextualRuleValue, hlabel]
              rw [hd]
              simp [priorityValue, ruleValue, nodeRule1bRootDistance]
          | multipleBondDuplicate _ =>
              simp [contextualNodeObservation, contextualRuleValue, nodeObservation,
                ruleValue, hlabel]
          | ringDuplicate _ =>
              simp [contextualNodeObservation, contextualRuleValue, nodeObservation,
                ruleValue, hlabel]
          | phantom _ =>
              simp [contextualNodeObservation, contextualRuleValue, nodeObservation,
                ruleValue, hlabel]
          | lonePair _ =>
              simp [contextualNodeObservation, contextualRuleValue, nodeObservation,
                ruleValue, hlabel]
          | auxiliary _ =>
              simp [contextualNodeObservation, contextualRuleValue, nodeObservation,
                ruleValue, hlabel]

/-- The contextual vector key specializes to the established canonical key under the same
depth-plus-one real-node distance profile. -/
theorem contextualRuleKey_eq_ruleKey_of_depth (outerRoot : Atom) (W D : ℕ)
    (distanceProfile : ∀ node atom,
      graph.label node = ⟨some atom, .realAtom⟩ →
        molecule.underlyingSimpleGraph.dist outerRoot atom = graph.depth node + 1)
    (node : graph.Node) :
    contextualRuleKey molecule graph outerRoot W D node = ruleKey molecule graph W D node := by
  change ruleKeyWithObservations (graph := graph) W D
    (contextualNodeObservation molecule graph outerRoot) node =
      ruleKey molecule graph W D node
  have hobs := contextualNodeObservation_eq_nodeObservation_of_depth molecule graph outerRoot
    distanceProfile
  rw [ruleKeyWithObservations_congr graph W D
    (contextualNodeObservation molecule graph outerRoot) (nodeObservation molecule graph)
    hobs node]
  exact ruleKeyWithObservations_eq_ruleKey graph molecule W D node

end ContextualObservation

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKeyWithObservations_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKeyWithObservations_getD
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKeyWithObservations_wellShaped
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKeyWithObservations_congr
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKeyWithObservations_eq_ruleKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualRuleValue_rule1b_real
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualNodeObservation_rule1a
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualNodeObservation_rule2
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualNodeObservation_rule1b_real
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualNodeObservation_eq_nodeObservation_of_depth
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualRuleKey_eq_ruleKey_of_depth
