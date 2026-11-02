import TetraStereo.OneCenter.LocalizedMarkedOperationSimulation
import TetraStereo.OneCenter.LocalizedMarkedUncappedOperations
import TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# A carried reference cannot be a descendant center's terminal neighbor

A reference selected in an ancestor's actual frame cannot be a terminal neighbor of a distinct
descendant center: a terminal atom has only one molecular neighbor. Real canonical descendants
cannot revisit the ancestor atom. The statement applies to arbitrary finite single-bond rings,
without rigidity, reference-count, geometry or label assumptions.

The snapshot theorem applies this fact to the evaluator's actual generated promotion snapshot.
It rules out externally carried promotion of one member of a descendant's terminal-twin pair.
The final theorem also proves that generated facts never label a terminal atom itself.
It does not yet prove that the center's own reference consensus refuses, or that its generated
descriptor is independent of terminal-twin geometry.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope

open LocalizedMarkedOperationEvaluator LocalizedMarkedOperationSimulation
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedUncappedOperations
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? factOf)

abbrev Node := RawMolecule.CanonicalBranchNode

abbrev Descends (mol : RawMolecule) (source target : Node) : Prop :=
  Relation.ReflTransGen (fun parent child => child ∈ mol.canonicalChildren parent) source target

/-- At least one actual canonical child step, followed by any number of further steps. -/
def StrictDescendant (mol : RawMolecule) (source target : Node) : Prop :=
  ∃ child, child ∈ mol.canonicalChildren source ∧ Descends mol child target

/-- Molecular terminality, stated independently of occurrence expansion and comparisons. -/
def TerminalNeighbor (mol : RawMolecule) (center atom : Nat) : Prop :=
  0 < mol.bondOrder center atom ∧ ∀ other, 0 < mol.bondOrder atom other → other = center

theorem history_mono {mol : RawMolecule} {source target : Node}
    (path : Descends mol source target) : source.history ⊆ target.history := by
  induction path with
  | refl => exact fun _ member => member
  | tail path edge ih =>
      intro atom member
      rw [mol.canonicalChildren_history _ _ edge]
      exact List.mem_cons_of_mem _ (ih member)

theorem descendant_reached {mol : RawMolecule} {source target : Node}
    (reached : Reached mol source) (path : Descends mol source target) : Reached mol target := by
  induction path with
  | refl => exact reached
  | tail path edge ih => exact reached_child mol _ _ ih edge

theorem strictDescendant_atom_ne {mol : RawMolecule} {source target : Node}
    (reached : Reached mol source) (path : StrictDescendant mol source target)
    (real : target.forcedLeaf = false) : target.atom ≠ source.atom := by
  obtain ⟨center, valid, generated⟩ := reached
  have head := (generated_of_reachedFrom mol center source generated).history_head
  have sourceMember : source.atom ∈ source.history := List.mem_of_head?_eq_some head
  obtain ⟨child, first, rest⟩ := path
  have childMember : source.atom ∈ child.history := by
    rw [mol.canonicalChildren_history source child first]
    exact List.mem_cons_of_mem _ sourceMember
  induction rest with
  | refl =>
      intro same
      exact (LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol source child first).2.1
        real (same ▸ sourceMember)
  | @tail parent target path edge ih =>
      intro same
      have member := history_mono path childMember
      exact (LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol parent target edge).2.1
        real (same ▸ member)

theorem frame_member_bond (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (source : Node) (reached : Reached mol source)
    (atoms : List Nat) (frame : frameAtoms? mol source = some atoms)
    (mark : Nat) (member : mark ∈ atoms) (valid : mark < mol.atomCount) :
    0 < mol.bondOrder source.atom mark := by
  apply (mol.mem_canonicalIncidentNeighbors_iff source.atom wellFormed mark).mp
  rcases frame_atoms_perm_neighbors mol wellFormed single source reached atoms frame with
    ⟨_, perm⟩ | ⟨_, perm⟩
  · exact perm.mem_iff.mp member
  · have choices := perm.mem_iff.mp member
    simpa [Nat.ne_of_lt valid] using choices

/-- An actual ancestor frame cannot carry a terminal-neighbor reference into a real descendant. -/
theorem carried_not_terminal (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (source target : Node) (reached : Reached mol source)
    (path : StrictDescendant mol source target) (real : target.forcedLeaf = false)
    (atoms : List Nat) (frame : frameAtoms? mol source = some atoms)
    (mark : Nat) (member : mark ∈ atoms) : ¬ TerminalNeighbor mol target.atom mark := by
  intro terminal
  have valid := (mol.bondOrder_pos_endpoint_lt wellFormed terminal.1).2
  have sourceBond := frame_member_bond mol wellFormed single source reached atoms frame
    mark member valid
  have same := terminal.2 source.atom (by simpa [RawMolecule.bondOrder_symm] using sourceBond)
  exact strictDescendant_atom_ne reached path real same.symm

/-- Each emitted fact comes from a successfully framed occurrence in the actual child closure. -/
theorem fact_source (mol : RawMolecule) (ops : Operations) (depth : Nat) :
    ∀ geom state ctx source fact, fact ∈ facts mol ops depth geom state ctx source →
      ∃ target descriptor atoms, Descends mol source target ∧
        frameAtoms? mol target = some atoms ∧ fact = factOf target descriptor := by
  induction depth with
  | zero => simp [facts]
  | succ depth ih =>
      intro geom state ctx source fact member
      rw [facts_succ] at member
      rcases List.mem_append.mp member with own | deeper
      · obtain ⟨descriptor, present, rfl⟩ := List.mem_map.mp own
        have someDescriptor := Option.mem_toList.mp present
        cases frame : frameAtoms? mol source with
        | none =>
            have absent := descriptor_none_of_frame mol ops geom state ctx source
              (facts mol ops depth) frame
            change descriptorWith? mol ops geom state ctx source (facts mol ops depth) =
              some descriptor at someDescriptor
            rw [absent] at someDescriptor
            cases someDescriptor
        | some atoms => exact ⟨source, descriptor, atoms, .refl, frame, rfl⟩
      · obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp deeper
        obtain ⟨target, descriptor, atoms, path, frame, value⟩ :=
          ih geom state ctx child fact member
        exact ⟨target, descriptor, atoms, (Relation.ReflTransGen.single edge).trans path,
          frame, value⟩

/-- No fact actually passed upward under an ancestor's selected reference is at a center for
which that reference is terminal. This includes all recursion depths and both mirrored runs. -/
theorem generated_snapshot_no_terminal_reference (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (source : Node) (reached : Reached mol source)
    (atoms : List Nat) (frame : frameAtoms? mol source = some atoms)
    (mark : Nat) (selected : mark ∈ atoms) (fact : OccurrenceAuxFact)
    (member : fact ∈ underWith mol ops geom state source (facts mol ops depth) mark) :
    ¬ TerminalNeighbor mol fact.atom mark := by
  obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp member
  have actual := mem_tiedChildren_actual mol ops state source child edge
  obtain ⟨target, descriptor, targetAtoms, path, targetFrame, rfl⟩ :=
    fact_source mol ops depth geom state (some mark) child fact member
  have real : target.forcedLeaf = false := by
    cases leaf : target.forcedLeaf with
    | false => rfl
    | true => simp [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol target leaf]
        at targetFrame
  have exclude := carried_not_terminal mol wellFormed single source target reached
    ⟨child, actual, path⟩ real atoms frame mark selected
  cases descriptor with
  | chiral letter => exact exclude
  | pseudoasymmetric letter => cases letter <;> exact exclude

/-- A terminal atom cannot acquire an occurrence frame by cutting a ring. -/
theorem terminal_no_frame (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (node : Node) (reached : Reached mol node) (center : Nat)
    (terminal : TerminalNeighbor mol center node.atom) : frameAtoms? mol node = none := by
  have length : (mol.canonicalIncidentNeighbors node.atom).length ≤ 1 := by
    rw [← List.toFinset_card_of_nodup (mol.canonicalIncidentNeighbors_nodup node.atom unique)]
    have subset : (mol.canonicalIncidentNeighbors node.atom).toFinset ⊆ {center} := by
      intro other member
      apply Finset.mem_singleton.mpr
      exact terminal.2 other
        ((mol.mem_canonicalIncidentNeighbors_iff node.atom wellFormed other).mp
          (List.mem_toFinset.mp member))
    simpa using Finset.card_le_card subset
  cases frame : frameAtoms? mol node with
  | none => rfl
  | some atoms =>
      rcases frame_atoms_perm_neighbors mol wellFormed single node reached atoms frame with
        ⟨four, _⟩ | ⟨three, _⟩ <;> omega

/-- Terminal atoms receive no internally generated auxiliary facts, on every actual subtree.
This holds independently of geometry, comparison operations and carried context. -/
theorem generated_facts_no_terminal_atom (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (source : Node) (reached : Reached mol source) (fact : OccurrenceAuxFact)
    (member : fact ∈ facts mol ops depth geom state ctx source) (center : Nat) :
    ¬ TerminalNeighbor mol center fact.atom := by
  obtain ⟨target, descriptor, atoms, path, frame, rfl⟩ :=
    fact_source mol ops depth geom state ctx source fact member
  have atom : (factOf target descriptor).atom = target.atom := by
    cases descriptor with
    | chiral letter => rfl
    | pseudoasymmetric letter => cases letter <;> rfl
  rw [atom]
  intro terminal
  have absent := terminal_no_frame mol wellFormed single unique target
    (descendant_reached reached path) center terminal
  rw [absent] at frame
  cases frame

/-- The actual occurrence-key lookup cannot read an internally generated label at a terminal
atom. Equality of full occurrence keys is used; matching atom numbers alone is insufficient. -/
theorem generated_factAt_terminal_none (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (source : Node) (reached : Reached mol source) (query : Node) (queryReached : Reached mol query)
    (center : Nat) (terminal : TerminalNeighbor mol center query.atom) :
    (facts mol ops depth geom state ctx source).factAt? query = none := by
  unfold OccurrenceAuxState.factAt?
  apply List.find?_eq_none.mpr
  intro fact member key
  have keys : fact.key = canonicalOccurrenceKey query := by simpa using key
  have exclude := generated_facts_no_terminal_atom mol ops wellFormed single unique depth
    geom state ctx source reached fact member center
  obtain ⟨target, descriptor, atoms, path, frame, value⟩ :=
    fact_source mol ops depth geom state ctx source fact member
  have targetReached := descendant_reached reached path
  obtain ⟨root, _, targetPath⟩ := targetReached
  obtain ⟨queryRoot, _, queryPath⟩ := queryReached
  have targetHead := (generated_of_reachedFrom mol root target targetPath).history_head
  have queryHead := (generated_of_reachedFrom mol queryRoot query queryPath).history_head
  have histories : target.history = query.history := by
    rw [value, LocalizedMarkedGeneratedFactUniqueness.factOf_key] at keys
    exact congrArg CanonicalOccurrenceKey.history keys
  have same : target.atom = query.atom :=
    Option.some.inj (targetHead.symm.trans ((congrArg List.head? histories).trans queryHead))
  have factAtom : fact.atom = query.atom := by
    rw [value]
    cases descriptor with
    | chiral letter => exact same
    | pseudoasymmetric letter => cases letter <;> exact same
  exact exclude (factAtom ▸ terminal)

end TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope.strictDescendant_atom_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope.frame_member_bond
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope.carried_not_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope.fact_source
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope.generated_snapshot_no_terminal_reference
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope.terminal_no_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope.generated_facts_no_terminal_atom
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope.generated_factAt_terminal_none
