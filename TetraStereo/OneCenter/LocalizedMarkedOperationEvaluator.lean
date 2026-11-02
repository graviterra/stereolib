import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Recursive marked evaluation parameterized by its comparison operations

One recursion generates references, promotion contexts, temporary facts and mirror-derived case.
The ordinary partition and marked ranker are explicit operations. The bounded instance is proved
equal to the accepted original evaluator on all inputs, not just the cage. This permits an
uncapped instance without prescribing labels or duplicating a separate recursion for it.

Operation totality and chemical correctness are separate from the recursion. Arbitrary operations
may refuse or return malformed orders; this module makes no chemical claim about such instances.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator

open LocalizedGenericMarkedRecalculation hiding tiedChildren rawStep? underWith rawWith?
  descriptorWith? facts descriptor? assignCenter? assign facts_succ facts_stable facts_stable_add
  descriptorWith?_congr assignCenter?_stable

abbrev Node := RawMolecule.CanonicalBranchNode

structure Operations where
  ordinary : OccurrenceAuxState → Node → Option (List Nat × List (Option Ordering))
  marked : OccurrenceAuxState → Node → Nat → Option Rule6TrackedRanking

def boundedOperations (mol : RawMolecule) (fuel : Nat) : Operations where
  ordinary := LocalizedGenericMarkedRecalculation.ordinary? mol fuel
  marked := LocalizedGenericMarkedRecalculation.marked? mol fuel

def markedReading? (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (mark : Nat) : Option RS := do
  let atoms ← frameAtoms? mol node
  let ranking ← ops.marked state node mark
  let ranked ← rankedAtoms? atoms ranking
  readback? geom ranked

def tiedChildren (mol : RawMolecule) (ops : Operations) (state : OccurrenceAuxState)
    (node : Node) : List Node :=
  match frameAtoms? mol node, ops.ordinary state node with
  | some atoms, some (sorted, adjacent) =>
      let eligible := eligibleOf atoms sorted adjacent
      (mol.canonicalChildren node).filter fun child => eligible.contains child.atom
  | _, _ => []

def rawStep? (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) : Option RS := do
  let atoms ← frameAtoms? mol node
  let (sorted, adjacent) ← ops.ordinary state node
  if ¬ atoms.Nodup ∨ consistent adjacent = false then none
  else if strict adjacent then
    let ranked ← atomsAt? atoms sorted
    readback? geom ranked
  else
    let eligible := eligibleOf atoms sorted adjacent
    let evaluate := fun r => do
      let temp ← appendFacts? state (under r)
      markedReading? mol ops geom temp node r
    match ctx with
    | some r => if atoms.contains r then evaluate r else consensus (eligible.map evaluate)
    | none => consensus (eligible.map evaluate)

def underWith (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node)
    (sub : Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState)
    (mark : Nat) : OccurrenceAuxState :=
  (tiedChildren mol ops state node).flatMap (sub geom state (some mark))

def rawWith? (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (sub : Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState) : Option RS :=
  rawStep? mol ops geom state ctx node (underWith mol ops geom state node sub)

def descriptorWith? (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (sub : Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  caseFromMirror? (rawWith? mol ops geom state ctx node sub)
    (rawWith? mol ops (mirror geom) state ctx node sub)

def facts (mol : RawMolecule) (ops : Operations) :
    Nat → Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState
  | 0, _, _, _, _ => []
  | depth + 1, geom, state, ctx, node =>
      (descriptorWith? mol ops geom state ctx node (facts mol ops depth)).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (facts mol ops depth geom state ctx)

def descriptor? (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorWith? mol ops geom state ctx node (facts mol ops depth)

def assignCenter? (mol : RawMolecule) (ops : Operations) (geom : Geometry) (center : Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptor? mol ops (structuralDepth mol (canonicalCenterRoot center)) geom [] none
    (canonicalCenterRoot center)

def assign (mol : RawMolecule) (ops : Operations) (geom : Geometry) :
    List (Nat × LocalizedTetrahedralRSPseudoDescriptor) :=
  (List.range mol.atomCount).filterMap fun center =>
    (assignCenter? mol ops geom center).map fun d => (center, d)

theorem facts_succ (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    facts mol ops (depth + 1) geom state ctx node =
      (descriptor? mol ops depth geom state ctx node).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (facts mol ops depth geom state ctx) := rfl

theorem mem_tiedChildren_actual (mol : RawMolecule) (ops : Operations)
    (state : OccurrenceAuxState) (node child : Node)
    (member : child ∈ tiedChildren mol ops state node) : child ∈ mol.canonicalChildren node := by
  unfold tiedChildren at member
  split at member
  · exact (List.mem_filter.mp member).1
  · simp at member

theorem descriptorWith?_congr (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (sub₁ sub₂ : Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState)
    (agree : ∀ child ∈ mol.canonicalChildren node, ∀ g s x, sub₁ g s x child = sub₂ g s x child) :
    descriptorWith? mol ops geom state ctx node sub₁ =
      descriptorWith? mol ops geom state ctx node sub₂ := by
  have under : ∀ g, underWith mol ops g state node sub₁ = underWith mol ops g state node sub₂ := by
    intro g
    funext mark
    unfold underWith
    exact flatMap_congr_mem _ _ _ fun child member =>
      agree child (mem_tiedChildren_actual mol ops state node child member) g state (some mark)
  unfold descriptorWith? rawWith?
  rw [under geom, under (mirror geom)]

/-- Exact preservation of every generated fact for the accepted bounded operations. -/
theorem bounded_facts_eq_original (mol : RawMolecule) (fuel depth : Nat) :
    ∀ geom state ctx node, facts mol (boundedOperations mol fuel) depth geom state ctx node =
      LocalizedGenericMarkedRecalculation.facts mol fuel depth geom state ctx node := by
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro geom state ctx node
      have descriptor : descriptor? mol (boundedOperations mol fuel) depth geom state ctx node =
          LocalizedGenericMarkedRecalculation.descriptor? mol fuel depth geom state ctx node := by
        unfold descriptor?
        rw [descriptorWith?_congr mol (boundedOperations mol fuel) geom state ctx node _
          (LocalizedGenericMarkedRecalculation.facts mol fuel depth)
          (fun child _ g s x => ih g s x child)]
        rfl
      rw [facts_succ, LocalizedGenericMarkedRecalculation.facts_succ, descriptor]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child _ => ih geom state ctx child

theorem bounded_descriptor_eq_original (mol : RawMolecule) (fuel depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    descriptor? mol (boundedOperations mol fuel) depth geom state ctx node =
      LocalizedGenericMarkedRecalculation.descriptor? mol fuel depth geom state ctx node := by
  unfold descriptor?
  rw [descriptorWith?_congr mol (boundedOperations mol fuel) geom state ctx node _
    (LocalizedGenericMarkedRecalculation.facts mol fuel depth)
    (fun child _ g s x => bounded_facts_eq_original mol fuel depth g s x child)]
  rfl

theorem bounded_assign_eq_original (mol : RawMolecule) (geom : Geometry) :
    assign mol (boundedOperations mol (comparatorFuel mol)) geom =
      LocalizedGenericMarkedRecalculation.assign mol geom := by
  unfold assign LocalizedGenericMarkedRecalculation.assign
  apply List.filterMap_congr
  intro center _
  exact congrArg (Option.map (fun d => (center, d)))
    (bounded_descriptor_eq_original mol _ _ geom [] none (canonicalCenterRoot center))

theorem facts_forcedLeaf (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) (leaf : node.forcedLeaf = true) :
    facts mol ops depth geom state ctx node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
      simp [facts, descriptorWith?, rawWith?, rawStep?, frameAtoms?_forcedLeaf mol node leaf,
        canonicalChildren_forcedLeaf mol node leaf, caseFromMirror?]

/-- Sufficient structural depth loses no contributing occurrence, for either operation instance. -/
theorem facts_stable (mol : RawMolecule) (ops : Operations) (wellFormed : WellFormedBonds mol) :
    ∀ depth geom state ctx node, Sufficient mol depth node →
      facts mol ops depth geom state ctx node = facts mol ops (depth + 1) geom state ctx node := by
  intro depth
  induction depth with
  | zero =>
      intro geom state ctx node sufficient
      rcases sufficient with leaf | ⟨good, bound⟩
      · rw [facts_forcedLeaf mol ops 0 geom state ctx node leaf,
          facts_forcedLeaf mol ops 1 geom state ctx node leaf]
      · have := good.length_le
        omega
  | succ depth ih =>
      intro geom state ctx node sufficient
      rcases sufficient with leaf | ⟨good, bound⟩
      · rw [facts_forcedLeaf mol ops _ geom state ctx node leaf,
          facts_forcedLeaf mol ops _ geom state ctx node leaf]
      · have children : ∀ child ∈ mol.canonicalChildren node, ∀ g s x,
            facts mol ops depth g s x child = facts mol ops (depth + 1) g s x child :=
          fun child member g s x => ih g s x child (Sufficient.child wellFormed good bound member)
        rw [facts_succ, facts_succ]
        unfold descriptor?
        rw [descriptorWith?_congr mol ops geom state ctx node _ _ children,
          flatMap_congr_mem _ _ _ fun child member => children child member geom state ctx]

theorem facts_stable_add (mol : RawMolecule) (ops : Operations) (wellFormed : WellFormedBonds mol)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (sufficient : Sufficient mol depth node) (k : Nat) :
    facts mol ops (depth + k) geom state ctx node = facts mol ops depth geom state ctx node := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have deeper : Sufficient mol (depth + k) node := by
        rcases sufficient with leaf | ⟨good, bound⟩
        · exact Or.inl leaf
        · exact Or.inr ⟨good, by omega⟩
      rw [← ih, Nat.add_succ, ← facts_stable mol ops wellFormed (depth + k) geom state ctx node deeper]

theorem assignCenter?_stable (mol : RawMolecule) (ops : Operations)
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (center : Nat)
    (valid : center < mol.atomCount) (k : Nat) :
    descriptor? mol ops (structuralDepth mol (canonicalCenterRoot center) + k) geom [] none
        (canonicalCenterRoot center) = assignCenter? mol ops geom center := by
  unfold assignCenter? descriptor?
  apply descriptorWith?_congr
  intro child member g s x
  have good : GoodNode mol (canonicalCenterRoot center) := by
    refine ⟨List.nodup_singleton center, ?_⟩
    intro atom memberHistory
    simp only [canonicalCenterRoot, List.mem_singleton] at memberHistory
    rw [memberHistory]
    exact valid
  have bound : mol.atomCount + 1 ≤ structuralDepth mol (canonicalCenterRoot center) + 1 +
      (canonicalCenterRoot center).history.length := by
    have := good.length_le
    unfold structuralDepth
    omega
  exact facts_stable_add mol ops wellFormed _ g s x child
    (Sufficient.child wellFormed good bound member) k

end TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator.bounded_facts_eq_original
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator.bounded_descriptor_eq_original
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator.bounded_assign_eq_original
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator.facts_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator.assignCenter?_stable
