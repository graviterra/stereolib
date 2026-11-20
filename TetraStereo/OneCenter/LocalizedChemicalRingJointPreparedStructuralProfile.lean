import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! One stable context/geometry profile for every reached molecular occurrence.
At the source's structural budget, each generated descendant label is evaluated at exactly
that descendant's own structural budget. There is no caller-dependent remaining fuel in the
resulting profile equation. Strict canonical descent decreases this measure, regardless of
how the reference context or geometry changes. This is the concrete recursion connection;
it does not assert that the profile satisfies the independent chemical source equations yet.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile

open CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedTerminalReferenceScope (Descends StrictDescendant descendant_reached)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointPreparedLabelExecution
open LocalizedMarkedRetainedStateReader (factLabel)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Every reached nonterminal occurrence has a duplicate-free in-range molecular history. -/
theorem reached_good (mol : RawMolecule) (wellFormed : WellFormedBonds mol)
    {node : Node} (reached : Reached mol node) (real : node.forcedLeaf = false) :
    GoodNode mol node := by
  obtain ⟨root, valid, path⟩ := reached
  induction path with
  | refl =>
      refine ⟨List.nodup_singleton _, ?_⟩
      intro atom member
      have equal : atom = root := by simpa only [canonicalCenterRoot, List.mem_singleton] using member
      exact equal ▸ valid
  | @tail parent child path edge ih =>
      have parentReal : parent.forcedLeaf = false := by
        cases leaf : parent.forcedLeaf with
        | false => rfl
        | true =>
            rw [canonicalChildren_forcedLeaf mol parent leaf] at edge
            simp at edge
      exact (ih parentReal).child wellFormed edge real

/-- A terminal duplicate can add at most one atom to a valid simple history. -/
theorem reached_history_bound (mol : RawMolecule) (wellFormed : WellFormedBonds mol)
    {node : Node} (reached : Reached mol node) :
    node.history.length ≤ mol.atomCount + 1 := by
  obtain ⟨root, valid, path⟩ := reached
  rcases path.cases_tail with same | ⟨parent, parentPath, edge⟩
  · subst node
    simp only [canonicalCenterRoot, List.length_singleton]
    omega
  · have parentReal : parent.forcedLeaf = false := by
      cases leaf : parent.forcedLeaf with
      | false => rfl
      | true =>
          rw [canonicalChildren_forcedLeaf mol parent leaf] at edge
          simp at edge
    have bound := (reached_good mol wellFormed ⟨root, valid, parentPath⟩ parentReal).length_le
    rw [mol.canonicalChildren_history parent node edge, List.length_cons]
    omega

/-- Structural budgeting has an exact residual, not merely a sufficient bound. -/
theorem residual_eq_structuralDepth (mol : RawMolecule) (wellFormed : WellFormedBonds mol)
    {source : Node} (reached : Reached mol source) (query : Node) :
    structuralDepth mol source + source.history.length - query.history.length =
      structuralDepth mol query := by
  have bound := reached_history_bound mol wellFormed reached
  unfold structuralDepth
  omega

/-- Every reached descendant is inside its source's structural budget. -/
theorem descendant_within_structuralDepth (mol : RawMolecule)
    (wellFormed : WellFormedBonds mol) {source query : Node}
    (reached : Reached mol source) (path : StrictDescendant mol source query) :
    query.history.length ≤ structuralDepth mol source + source.history.length := by
  obtain ⟨child, edge, rest⟩ := path
  have queryReached := descendant_reached (reached_child mol source child reached edge) rest
  have sourceBound := reached_history_bound mol wellFormed reached
  have queryBound := reached_history_bound mol wellFormed queryReached
  unfold structuralDepth
  omega

/-- Strict canonical descent decreases the actual structural budget, rings included. -/
theorem structuralDepth_lt (mol : RawMolecule) (wellFormed : WellFormedBonds mol)
    {source query : Node} (reached : Reached mol source)
    (path : StrictDescendant mol source query) :
    structuralDepth mol query < structuralDepth mol source := by
  rw [← residual_eq_structuralDepth mol wellFormed reached query]
  exact residual_depth_lt _ path (descendant_within_structuralDepth mol wellFormed reached path)

/-- Context changes do not affect well-foundedness: only strict molecular descent matters. -/
theorem contextDependency_wellFounded {Context : Type*} (mol : RawMolecule)
    (wellFormed : WellFormedBonds mol) :
    WellFounded (fun (query source : Context × {node : Node // Reached mol node}) =>
      StrictDescendant mol source.2.1 query.2.1) := by
  exact Subrelation.wf
    (fun {query source : Context × {node : Node // Reached mol node}} path =>
      structuralDepth_lt mol wellFormed source.2.2 path)
    (measure (fun query : Context × {node : Node // Reached mol node} =>
      structuralDepth mol query.2.1)).wf

/-- The actual evaluator's stable optional profile, indexed by geometry, full context and node.
This is the executable candidate whose independent-model theorem must be established separately. -/
def stableProfile (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (geom : Geometry) (references : List input.Atom) (query : Node) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol query)
    geom [] (references.map Fin.val) query

/-- Actual generated reads at structural depth are the same global optional profile at every
strict descendant. Includes refused/missing labels, all ordered contexts and either geometry. -/
theorem generated_label_eq_stableProfile (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (references : List input.Atom)
    {source query : Node} (reached : Reached mol source)
    (path : StrictDescendant mol source query) :
    ((generated input mol (structuralDepth mol source) geom source references).factAt? query).map
        factLabel = stableProfile input mol geom references query := by
  rw [generated_label_eq_descriptor input mol (structuralDepth mol source) geom source query
    references reached (by exact path) (descendant_within_structuralDepth mol wellFormed reached path),
    residual_eq_structuralDepth mol wellFormed reached query]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.reached_good
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.reached_history_bound
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.residual_eq_structuralDepth
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.descendant_within_structuralDepth
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.structuralDepth_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.contextDependency_wellFounded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.generated_label_eq_stableProfile
