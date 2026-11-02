import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator
import TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Generated promotion facts have distinct occurrence keys

On a well-formed single-bond graph with unique bonds, recursive facts never repeat an
occurrence history. This holds with rings, arbitrary comparison operations, geometries,
input states and promotion contexts. The proof follows actual canonical children; revisiting
the same physical atom along different paths does not identify those occurrence histories.

Consequently appending the internally generated promotion facts to the public evaluator's
empty input state always succeeds. This removes the duplicate-key refusal, not the independent
ordering, geometry, consensus or chemical-correctness obligations.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness

open LocalizedMarkedOperationEvaluator
open LocalizedGenericMarkedRecalculation
  (Geometry factOf appendFacts? canonicalChildren_forcedLeaf)
open LocalizedMarkedReachedFrameNeighbors

theorem factOf_key (node : Node) (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    (factOf node descriptor).key = canonicalOccurrenceKey node := by
  cases descriptor with
  | chiral raw => rfl
  | pseudoasymmetric raw => cases raw <;> rfl

theorem child_atoms_nodup (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (node : Node) :
    ((mol.canonicalChildren node).map (·.atom)).Nodup := by
  cases leaf : node.forcedLeaf with
  | true => simp [canonicalChildren_forcedLeaf mol node leaf]
  | false =>
      rw [children_atoms mol wellFormed single node leaf]
      exact (mol.canonicalIncidentNeighbors_nodup node.atom unique).erase node.parent

/-- Every emitted fact retains the suffix of the actual occurrence at which recursion began. -/
theorem history_suffix (mol : RawMolecule) (ops : Operations) (depth : Nat) :
    ∀ geom state ctx node fact, fact ∈ facts mol ops depth geom state ctx node →
      node.history <:+ fact.key.history := by
  induction depth with
  | zero => simp [facts]
  | succ depth ih =>
      intro geom state ctx node fact member
      rw [facts_succ] at member
      rcases List.mem_append.mp member with own | descendant
      · obtain ⟨descriptor, _, rfl⟩ := List.mem_map.mp own
        simp [factOf_key, canonicalOccurrenceKey]
      · obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp descendant
        have suffix := ih geom state ctx child fact member
        have step : node.history <:+ child.history := by
          rw [mol.canonicalChildren_history node child edge]
          exact List.suffix_cons _ _
        exact step.trans suffix

private theorem child_history_disjoint (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (node left right : Node) (leftEdge : left ∈ mol.canonicalChildren node)
    (rightEdge : right ∈ mol.canonicalChildren node) (different : left.atom ≠ right.atom) :
    List.Disjoint
      ((facts mol ops depth geom state ctx left).map (fun fact => fact.key.history))
      ((facts mol ops depth geom state ctx right).map (fun fact => fact.key.history)) := by
  intro history leftMember rightMember
  obtain ⟨lf, lm, le⟩ := List.mem_map.mp leftMember
  obtain ⟨rf, rm, re⟩ := List.mem_map.mp rightMember
  have ls := history_suffix mol ops depth geom state ctx left lf lm
  have rs := history_suffix mol ops depth geom state ctx right rf rm
  rw [le] at ls
  rw [re] at rs
  have length : left.history.length = right.history.length := by
    rw [mol.canonicalChildren_history node left leftEdge,
      mol.canonicalChildren_history node right rightEdge]
    rfl
  have same := (List.suffix_of_suffix_length_le ls rs (Nat.le_of_eq length)).eq_of_length length
  rw [mol.canonicalChildren_history node left leftEdge,
    mol.canonicalChildren_history node right rightEdge] at same
  exact different (List.cons.inj same).1

private theorem forest_histories_nodup (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (children : ∀ child ∈ mol.canonicalChildren node,
      ((facts mol ops depth geom state ctx child).map (fun fact => fact.key.history)).Nodup) :
    (((mol.canonicalChildren node).flatMap (facts mol ops depth geom state ctx)).map
      (fun fact => fact.key.history)).Nodup := by
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨children, ?_⟩
  have distinct : (mol.canonicalChildren node).Pairwise (fun l r => l.atom ≠ r.atom) := by
    simpa only [List.Nodup, List.pairwise_map] using
      child_atoms_nodup mol wellFormed single unique node
  exact distinct.imp_of_mem fun {l r} lm rm neq =>
    child_history_disjoint mol ops depth geom state ctx node l r lm rm neq

/-- Generated facts are unique by full history, even before their provenance is inspected. -/
theorem facts_histories_nodup (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) :
    ∀ geom state ctx node,
      ((facts mol ops depth geom state ctx node).map (fun fact => fact.key.history)).Nodup := by
  induction depth with
  | zero => simp [facts]
  | succ depth ih =>
      intro geom state ctx node
      have forest := forest_histories_nodup mol ops wellFormed single unique depth geom state ctx
        node (fun child _ => ih geom state ctx child)
      have absent : node.history ∉
          (((mol.canonicalChildren node).flatMap (facts mol ops depth geom state ctx)).map
            (fun fact => fact.key.history)) := by
        intro member
        obtain ⟨fact, fm, historyEq⟩ := List.mem_map.mp member
        obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp fm
        have bound := (history_suffix mol ops depth geom state ctx child fact member).length_le
        rw [historyEq, mol.canonicalChildren_history node child edge, List.length_cons] at bound
        omega
      rw [facts_succ, List.map_append, List.map_map]
      cases value : descriptor? mol ops depth geom state ctx node with
      | none => simpa using forest
      | some descriptor =>
          simpa [factOf_key, canonicalOccurrenceKey] using List.nodup_cons.mpr ⟨absent, forest⟩

theorem facts_keys_nodup (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    ((facts mol ops depth geom state ctx node).map (·.key)).Nodup := by
  apply List.Nodup.of_map CanonicalOccurrenceKey.history
  simpa only [List.map_map, Function.comp_def] using
    facts_histories_nodup mol ops wellFormed single unique depth geom state ctx node

theorem underWith_keys_nodup (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (mark : Nat) :
    ((underWith mol ops geom state node (facts mol ops depth) mark).map (·.key)).Nodup := by
  have forest := forest_histories_nodup mol ops wellFormed single unique depth geom state
    (some mark) node (fun child _ =>
      facts_histories_nodup mol ops wellFormed single unique depth geom state (some mark) child)
  have selected : (tiedChildren mol ops state node).Sublist (mol.canonicalChildren node) := by
    unfold tiedChildren
    split
    · exact List.filter_sublist
    · exact List.nil_sublist _
  have subset := (selected.flatMap (facts mol ops depth geom state (some mark))).map
    (fun fact => fact.key.history)
  apply List.Nodup.of_map CanonicalOccurrenceKey.history
  simpa only [underWith, List.map_map, Function.comp_def] using forest.sublist subset

/-- The duplicate guard accepts any globally key-distinct concatenation. -/
theorem appendFacts_of_nodup (state added : OccurrenceAuxState)
    (distinct : ((state ++ added).map (·.key)).Nodup) :
    appendFacts? state added = some (state ++ added) := by
  induction added generalizing state with
  | nil => simp [appendFacts?]
  | cons fact rest ih =>
      have fresh : ¬ ∃ old ∈ state, old.key = fact.key := by
        intro ⟨old, member, equal⟩
        have disjoint := (List.nodup_append.mp (by
          simpa only [List.map_append, List.map_cons] using distinct)).2.2
        exact disjoint fact.key (List.mem_map.mpr ⟨old, member, equal⟩) fact.key (by simp) rfl
      have guard : (state.any fun old => old.key == fact.key) = false := by
        simp only [List.any_eq_false, beq_iff_eq]
        intro old member equal
        exact fresh ⟨old, member, equal⟩
      have remaining : (((state ++ [fact]) ++ rest).map (·.key)).Nodup := by
        simpa only [List.append_assoc, List.singleton_append] using distinct
      simp only [appendFacts?, DeclarativeCIP.ProductionOccurrenceRules456.appendInputFact?, guard,
        Bool.false_eq_true, ↓reduceIte]
      simpa only [List.append_assoc, List.singleton_append] using ih (state ++ [fact]) remaining

/-- Public recursion starts from the empty state. Every generated promotion extension succeeds,
including the independently recomputed mirror geometry. -/
theorem generated_extension_succeeds (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (node : Node) (mark : Nat) :
    appendFacts? [] (underWith mol ops geom [] node (facts mol ops depth) mark) =
      some (underWith mol ops geom [] node (facts mol ops depth) mark) := by
  exact appendFacts_of_nodup [] _ (underWith_keys_nodup mol ops wellFormed single unique
    depth geom [] node mark)

end TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness.history_suffix
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness.facts_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness.underWith_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness.appendFacts_of_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness.generated_extension_succeeds
