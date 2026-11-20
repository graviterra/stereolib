import TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion
import TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness
import TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Full-history uniqueness of the prepared-context recursion

This module proves that the actual prepared-context recursion emits no duplicate occurrence
key, at every depth, geometry, incoming state and inherited mark context. The argument is the
ring-safe history argument of `LocalizedChemicalRingCompletenessGeneratedFacts`: every fact
emitted below an occurrence retains the occurrence history as a suffix, while canonical
children have distinct atoms and hence disjoint history suffixes. No child-level `Nodup`
assumption and no append success is assumed.

Consequently `appendFacts? []` succeeds on every prepared child state, both at the comparison
context `M` and at every fallback context `M ++ [s]`. These are exactly the incoming states
used by the concrete recursion rooted at `preparedAssignCenter?`, whose incoming state is `[]`.

The assumptions are the existing raw-molecule ones: `WellFormed`, `SingleBonded` and
`BondRecordsUnique`. They are derived from authoritative/admissible certified input at the end.
No orientation, Rule-6 source faithfulness or chemical-meaning claim is made.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts

open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations markedReadingJoint?)
open LocalizedGenericMarkedRecalculation (Geometry appendFacts? factOf frameAtoms?)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded)
open LocalizedMarkedGeneratedFactUniqueness (factOf_key child_atoms_nodup appendFacts_of_nodup)

/-- Every fact emitted by the prepared recursion at an occurrence retains that occurrence's
actual history as a suffix. This holds for an arbitrary prepared step and needs no
well-formedness hypothesis. -/
theorem history_suffix (step : PreparedStep) (mol : RawMolecule) (depth : Nat) :
    ∀ geom state M node fact, fact ∈ factsOfStep step mol depth geom state M node →
      node.history <:+ fact.key.history := by
  induction depth with
  | zero => simp [factsOfStep]
  | succ depth ih =>
      intro geom state M node fact member
      rw [factsOfStep_succ] at member
      rcases List.mem_append.mp member with own | descendant
      · obtain ⟨descriptor, _, rfl⟩ := List.mem_map.mp own
        simp [factOf_key, canonicalOccurrenceKey]
      · obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp descendant
        have suffix := ih geom state M child fact member
        have stepSuffix : node.history <:+ child.history := by
          rw [mol.canonicalChildren_history node child edge]
          exact List.suffix_cons _ _
        exact stepSuffix.trans suffix

private theorem child_history_disjoint (step : PreparedStep) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext)
    (node left right : Node) (leftEdge : left ∈ mol.canonicalChildren node)
    (rightEdge : right ∈ mol.canonicalChildren node) (different : left.atom ≠ right.atom) :
    List.Disjoint
      ((factsOfStep step mol depth geom state M left).map (fun fact => fact.key.history))
      ((factsOfStep step mol depth geom state M right).map (fun fact => fact.key.history)) := by
  intro history leftMember rightMember
  obtain ⟨leftFact, leftMem, leftEq⟩ := List.mem_map.mp leftMember
  obtain ⟨rightFact, rightMem, rightEq⟩ := List.mem_map.mp rightMember
  have leftSuffix := history_suffix step mol depth geom state M left leftFact leftMem
  have rightSuffix := history_suffix step mol depth geom state M right rightFact rightMem
  rw [leftEq] at leftSuffix
  rw [rightEq] at rightSuffix
  have length : left.history.length = right.history.length := by
    rw [mol.canonicalChildren_history node left leftEdge,
      mol.canonicalChildren_history node right rightEdge]
    rfl
  have same :=
    (List.suffix_of_suffix_length_le leftSuffix rightSuffix (Nat.le_of_eq length)).eq_of_length length
  rw [mol.canonicalChildren_history node left leftEdge,
    mol.canonicalChildren_history node right rightEdge] at same
  exact different (List.cons.inj same).1

private theorem forest_histories_nodup (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (children : ∀ child ∈ mol.canonicalChildren node,
      ((factsOfStep step mol depth geom state M child).map
        (fun fact => fact.key.history)).Nodup) :
    (((mol.canonicalChildren node).flatMap (factsOfStep step mol depth geom state M)).map
      (fun fact => fact.key.history)).Nodup := by
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨children, ?_⟩
  have distinct : (mol.canonicalChildren node).Pairwise (fun l r => l.atom ≠ r.atom) := by
    simpa only [List.Nodup, List.pairwise_map] using
      child_atoms_nodup mol wellFormed single unique node
  exact distinct.imp_of_mem fun {l r} lm rm neq =>
    child_history_disjoint step mol depth geom state M node l r lm rm neq

/-- Facts emitted by an arbitrary prepared step are unique by full occurrence history, at every
depth, geometry, incoming state and inherited context. -/
theorem facts_histories_nodup (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) :
    ∀ geom state M node,
      ((factsOfStep step mol depth geom state M node).map
        (fun fact => fact.key.history)).Nodup := by
  induction depth with
  | zero => simp [factsOfStep]
  | succ depth ih =>
      intro geom state M node
      have forest := forest_histories_nodup step mol wellFormed single unique depth geom state M
        node (fun child _ => ih geom state M child)
      have absent : node.history ∉
          (((mol.canonicalChildren node).flatMap
            (factsOfStep step mol depth geom state M)).map
              (fun fact => fact.key.history)) := by
        intro member
        obtain ⟨fact, factMem, historyEq⟩ := List.mem_map.mp member
        obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp factMem
        have bound :=
          (history_suffix step mol depth geom state M child fact member).length_le
        rw [historyEq, mol.canonicalChildren_history node child edge, List.length_cons] at bound
        omega
      rw [factsOfStep_succ, List.map_append, List.map_map]
      cases value : descriptorOfStep step mol depth geom state M node with
      | none => simpa using forest
      | some descriptor =>
          simpa [factOf_key, canonicalOccurrenceKey] using List.nodup_cons.mpr ⟨absent, forest⟩

/-- The same uniqueness read on occurrence keys. -/
theorem facts_keys_nodup (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    ((factsOfStep step mol depth geom state M node).map (·.key)).Nodup := by
  apply List.Nodup.of_map CanonicalOccurrenceKey.history
  simpa only [List.map_map, Function.comp_def] using
    facts_histories_nodup step mol wellFormed single unique depth geom state M node

/-- Full-history uniqueness of every canonical child's facts, collected at any context. -/
theorem childrenUnder_histories_nodup (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (M : MarkContext) :
    ((childrenUnder mol (factsOfStep step mol depth) geom state node M).map
      (fun fact => fact.key.history)).Nodup := by
  cases depth with
  | zero => simp [childrenUnder_factsOfStep_zero]
  | succ depth =>
      simpa [childrenUnder] using
        forest_histories_nodup step mol wellFormed single unique (depth + 1) geom state M node
          (fun child _ =>
            facts_histories_nodup step mol wellFormed single unique (depth + 1)
              geom state M child)

/-- Key uniqueness of every canonical child's facts, collected at any context. -/
theorem childrenUnder_keys_nodup (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (M : MarkContext) :
    ((childrenUnder mol (factsOfStep step mol depth) geom state node M).map (·.key)).Nodup := by
  apply List.Nodup.of_map CanonicalOccurrenceKey.history
  simpa only [List.map_map, Function.comp_def] using
    childrenUnder_histories_nodup step mol wellFormed single unique depth geom state node M

/-- At any inherited context `L`, the collected canonical-child facts admit duplicate-free
insertion into the incoming empty state. This is the generic form of the comparison and
fallback append facts. -/
theorem extension_succeeds_at (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (node : Node) (L : MarkContext) :
    appendFacts? [] (childrenUnder mol (factsOfStep step mol depth) geom [] node L) =
      some (childrenUnder mol (factsOfStep step mol depth) geom [] node L) :=
  appendFacts_of_nodup [] _
    (childrenUnder_keys_nodup step mol wellFormed single unique depth geom [] node L)

/-- The comparison-context append succeeds at the incoming empty state. -/
theorem extension_succeeds (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (node : Node) (M : MarkContext) :
    appendFacts? [] (childrenUnder mol (factsOfStep step mol depth) geom [] node M) =
      some (childrenUnder mol (factsOfStep step mol depth) geom [] node M) :=
  extension_succeeds_at step mol wellFormed single unique depth geom node M

/-- The fallback-context append succeeds at the incoming empty state, for every reference. -/
theorem fallback_extension_succeeds (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (node : Node) (M : MarkContext) (s : Nat) :
    appendFacts? [] (childrenUnder mol (factsOfStep step mol depth) geom [] node (M ++ [s])) =
      some (childrenUnder mol (factsOfStep step mol depth) geom [] node (M ++ [s])) :=
  extension_succeeds_at step mol wellFormed single unique depth geom node (M ++ [s])

/-! ## The concrete prepared-context recursion -/

/-- Full-history uniqueness of the actual `preparedFacts`, at every depth, geometry, incoming
state and inherited context. -/
theorem preparedFacts_histories_nodup (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    ((preparedFacts mol ops depth geom state M node).map
      (fun fact => fact.key.history)).Nodup := by
  unfold preparedFacts
  exact facts_histories_nodup (rawStepPrepared? ops) mol wellFormed single unique depth
    geom state M node

/-- Key uniqueness of the actual `preparedFacts`, at every depth, geometry, incoming state and
inherited context. -/
theorem preparedFacts_keys_nodup (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    ((preparedFacts mol ops depth geom state M node).map (·.key)).Nodup := by
  unfold preparedFacts
  exact facts_keys_nodup (rawStepPrepared? ops) mol wellFormed single unique depth
    geom state M node

/-- Full-history uniqueness of all canonical children's actual prepared facts, collected at any
context. Every canonical child is visited; no tied-child restriction is used. -/
theorem preparedChildrenUnder_histories_nodup (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (M : MarkContext) :
    ((childrenUnder mol (preparedFacts mol ops depth) geom state node M).map
      (fun fact => fact.key.history)).Nodup := by
  unfold preparedFacts
  exact childrenUnder_histories_nodup (rawStepPrepared? ops) mol wellFormed single unique depth
    geom state node M

/-- Key uniqueness of all canonical children's actual prepared facts, collected at any
context. -/
theorem preparedChildrenUnder_keys_nodup (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (M : MarkContext) :
    ((childrenUnder mol (preparedFacts mol ops depth) geom state node M).map (·.key)).Nodup := by
  unfold preparedFacts
  exact childrenUnder_keys_nodup (rawStepPrepared? ops) mol wellFormed single unique depth
    geom state node M

/-- **Comparison append.** At the root's incoming empty state, the actual same-context child
state of every occurrence admits duplicate-free insertion. -/
theorem prepared_comparison_append_succeeds (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (node : Node) (M : MarkContext) :
    appendFacts? [] (childrenUnder mol (preparedFacts mol ops depth) geom [] node M) =
      some (childrenUnder mol (preparedFacts mol ops depth) geom [] node M) := by
  unfold preparedFacts
  exact extension_succeeds (rawStepPrepared? ops) mol wellFormed single unique depth geom node M

/-- **Fallback append.** At the same original incoming empty state, every extended fallback
context `M ++ [s]` also admits duplicate-free insertion. -/
theorem prepared_fallback_append_succeeds (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (node : Node) (M : MarkContext) (s : Nat) :
    appendFacts? [] (childrenUnder mol (preparedFacts mol ops depth) geom [] node (M ++ [s])) =
      some (childrenUnder mol (preparedFacts mol ops depth) geom [] node (M ++ [s])) := by
  unfold preparedFacts
  exact fallback_extension_succeeds (rawStepPrepared? ops) mol wellFormed single unique depth
    geom node M s

/-- The actual prepared comparison runs on the successfully appended same-context child state,
at the root's incoming `[]`. -/
theorem preparedStep_compares_on_generated_children (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (node : Node) (M : MarkContext) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) :
    rawStepPrepared? ops mol geom [] M node
        (childrenUnder mol (preparedFacts mol ops depth) geom [] node) =
      comparisonAt? ops mol geom [] M node
        (childrenUnder mol (preparedFacts mol ops depth) geom [] node) atoms
        (childrenUnder mol (preparedFacts mol ops depth) geom [] node M) :=
  preparedStep_compares_on_sameContext_children mol ops depth geom [] M node atoms _
    frame (prepared_comparison_append_succeeds mol ops wellFormed single unique depth geom node M)

/-- The actual prepared fallback reads the successfully appended extended-context child state,
starting from the root's incoming `[]`. -/
theorem preparedStep_fallback_uses_generated_children (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (node : Node) (M : MarkContext) (s : Nat) :
    evaluateFallback? mol ops geom [] node M
        (childrenUnder mol (preparedFacts mol ops depth) geom [] node) s =
      markedReadingJoint? mol ops geom
        (childrenUnder mol (preparedFacts mol ops depth) geom [] node (M ++ [s]))
        node (M ++ [s]) s :=
  preparedStep_fallback_uses_extendedChildren mol ops depth geom [] M node s _
    (prepared_fallback_append_succeeds mol ops wellFormed single unique depth geom node M s)

/-! ## Instantiation from certified authoritative input -/

open CertifiedLocalizedCIPInput
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)

include agreement admissible supported single in
/-- Under actual authoritative/admissible certified input, the comparison-context append for the
concrete prepared recursion succeeds without any extra uniqueness premise. -/
theorem authoritative_comparison_append_succeeds (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (node : Node) (M : MarkContext) :
    appendFacts? [] (childrenUnder mol (preparedFacts mol ops depth) geom [] node M) =
      some (childrenUnder mol (preparedFacts mol ops depth) geom [] node M) :=
  prepared_comparison_append_succeeds mol ops admissible.1.1
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 depth geom node M

include agreement admissible supported single in
/-- Under actual authoritative/admissible certified input, every fallback-context append for the
concrete prepared recursion succeeds without any extra uniqueness premise. -/
theorem authoritative_fallback_append_succeeds (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (node : Node) (M : MarkContext) (s : Nat) :
    appendFacts? [] (childrenUnder mol (preparedFacts mol ops depth) geom [] node (M ++ [s])) =
      some (childrenUnder mol (preparedFacts mol ops depth) geom [] node (M ++ [s])) :=
  prepared_fallback_append_succeeds mol ops admissible.1.1
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 depth geom node M s

end TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.history_suffix
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.facts_histories_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.facts_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.childrenUnder_histories_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.childrenUnder_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.extension_succeeds_at
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.extension_succeeds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.fallback_extension_succeeds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.preparedFacts_histories_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.preparedFacts_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.preparedChildrenUnder_histories_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.preparedChildrenUnder_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.prepared_comparison_append_succeeds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.prepared_fallback_append_succeeds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.preparedStep_compares_on_generated_children
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.preparedStep_fallback_uses_generated_children
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.authoritative_comparison_append_succeeds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts.authoritative_fallback_append_succeeds
