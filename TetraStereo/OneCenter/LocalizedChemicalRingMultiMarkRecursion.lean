import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000














































namespace TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion

open LocalizedGenericMarkedRecalculation hiding tiedChildren rawStep? underWith rawWith?
  descriptorWith? facts descriptor? assignCenter? assign facts_succ facts_stable facts_stable_add
  descriptorWith?_congr assignCenter?_stable sufficient_structuralDepth
open LocalizedMarkedOperationEvaluator (Operations tiedChildren mem_tiedChildren_actual)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- The inherited-mark context: the marks carried into an occurrence, oldest first. -/
abbrev MarkContext := List Nat

/-! ## The context discipline -/

/-- A local fallback at mark `s` keeps every inherited mark and adds `s`. -/
theorem mem_append_singleton_of_mem {M : MarkContext} {s x : Nat} (member : x ∈ M) :
    x ∈ M ++ [s] := by
  rw [List.mem_append]
  exact Or.inl member

/-- The fallback mark itself is present in the extended context. -/
theorem mem_append_singleton_self (M : MarkContext) (s : Nat) : s ∈ M ++ [s] := by
  rw [List.mem_append]
  exact Or.inr (by simp)

/-- Extending the context strictly increases its length; no fallback reuses the old context. -/
theorem length_append_singleton_gt (M : MarkContext) (s : Nat) :
    M.length < (M ++ [s]).length := by
  simp [List.length_append]

/-! ## Generic multi-mark recursion -/

/-- One-occurrence raw step of a multi-mark recursive evaluator. Compared with
`LocalizedChemicalRingSenseTransport.Step`, the inherited context is a list of marks rather than
an optional single mark. The continuation `under s` is expected to be the standard tied-child
state generated under `M ++ [s]`; `underMulti` below is that standard construction, so the step
never has to discard `M` to obtain child facts. -/
abbrev MultiStep := RawMolecule → Operations → Geometry → OccurrenceAuxState → MarkContext →
  Node → (Nat → OccurrenceAuxState) → Option RS

/-- Tied-child state for one local fallback mark. Every tied child is evaluated under the
extended context `M ++ [s]`; no fact generated under a different context contributes here. -/
def underMulti (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    Nat → OccurrenceAuxState :=
  fun s => (tiedChildren mol ops state node).flatMap fun child => sub geom state (M ++ [s]) child

@[simp] theorem underMulti_apply (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) (s : Nat) :
    underMulti mol ops geom state M node sub s =
      (tiedChildren mol ops state node).flatMap
        (fun child => sub geom state (M ++ [s]) child) := rfl

/-- Membership in the fallback state is exactly membership in a tied child's state at the
extended context `M ++ [s]`. -/
theorem mem_underMulti_iff (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) (s : Nat)
    (fact : OccurrenceAuxFact) :
    fact ∈ underMulti mol ops geom state M node sub s ↔
      ∃ child ∈ tiedChildren mol ops state node,
        fact ∈ sub geom state (M ++ [s]) child := by
  rw [underMulti_apply, List.mem_flatMap]

/-- One occurrence with an explicit child continuation, at context `M`. -/
def rawWithMulti? (step : MultiStep) (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) : Option RS :=
  step mol ops geom state M node (underMulti mol ops geom state M node sub)

/-- The mirror-cased descriptor of one occurrence with an explicit child continuation. -/
def descriptorWithMulti (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  caseFromMirror?
    (rawWithMulti? step mol ops geom state M node sub)
    (rawWithMulti? step mol ops (mirror geom) state M node sub)

theorem descriptorWithMulti_apply (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    descriptorWithMulti step mol ops geom state M node sub =
      caseFromMirror?
        (step mol ops geom state M node (underMulti mol ops geom state M node sub))
        (step mol ops (mirror geom) state M node
          (underMulti mol ops (mirror geom) state M node sub)) := rfl

/-- The terminating occurrence recursion at context `M`. At every framed occurrence the
mirror-cased descriptor fact is contributed; descents below framed occurrences continue, and
the child facts contributed to the parent remain at the same context `M`. The extended context
`M ++ [s]` is used only inside `descriptorWithMulti` for the fallback reading with mark `s`. -/
def factsMulti (step : MultiStep) (mol : RawMolecule) (ops : Operations) :
    Nat → Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState
  | 0, _, _, _, _ => []
  | depth + 1, geom, state, M, node =>
      (descriptorWithMulti step mol ops geom state M node (factsMulti step mol ops depth)).toList.map
          (factOf node) ++
        (mol.canonicalChildren node).flatMap (factsMulti step mol ops depth geom state M)

theorem factsMulti_succ (step : MultiStep) (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    factsMulti step mol ops (depth + 1) geom state M node =
      (descriptorWithMulti step mol ops geom state M node
        (factsMulti step mol ops depth)).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (factsMulti step mol ops depth geom state M) := rfl

/-- The descriptor of an occurrence whose descendants are generated at `depth`. -/
def descriptorMulti (step : MultiStep) (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorWithMulti step mol ops geom state M node (factsMulti step mol ops depth)

theorem descriptorMulti_eq (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    descriptorMulti step mol ops depth geom state M node =
      descriptorWithMulti step mol ops geom state M node (factsMulti step mol ops depth) := rfl

/-- The fallback continuation as a function is exactly the tied-child state at `M ++ [s]`. -/
theorem underMulti_factsMulti_fun (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    underMulti mol ops geom state M node (factsMulti step mol ops depth) =
      (fun s => (tiedChildren mol ops state node).flatMap
        (fun child => factsMulti step mol ops depth geom state (M ++ [s]) child)) := by
  funext s
  rw [underMulti_apply]

theorem descriptorMulti_uses_child_context (step : MultiStep) (mol : RawMolecule)
    (ops : Operations) (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (M : MarkContext) (node : Node) :
    descriptorMulti step mol ops depth geom state M node =
      caseFromMirror?
        (step mol ops geom state M node (fun s =>
          (tiedChildren mol ops state node).flatMap
            (fun child => factsMulti step mol ops depth geom state (M ++ [s]) child)))
        (step mol ops (mirror geom) state M node (fun s =>
          (tiedChildren mol ops state node).flatMap
            (fun child => factsMulti step mol ops depth (mirror geom) state (M ++ [s]) child))) := by
  rw [descriptorMulti_eq, descriptorWithMulti_apply,
    underMulti_factsMulti_fun step mol ops depth geom state M node,
    underMulti_factsMulti_fun step mol ops depth (mirror geom) state M node]

/-! ## The exact fallback state -/

/-- The state supplied to the fallback reading with mark `s` is exactly the tied children
generated at the extended context `M ++ [s]`. -/
theorem underMulti_factsMulti (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (s : Nat) :
    underMulti mol ops geom state M node (factsMulti step mol ops depth) s =
      (tiedChildren mol ops state node).flatMap
        (fun child => factsMulti step mol ops depth geom state (M ++ [s]) child) := rfl

/-- Every fact in the fallback state comes from a tied child evaluated at the extended context
`M ++ [s]`; no fact generated at the occurrence's own context `M` contributes to a fallback. -/
theorem mem_underMulti_factsMulti_iff (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (s : Nat) (fact : OccurrenceAuxFact) :
    fact ∈ underMulti mol ops geom state M node (factsMulti step mol ops depth) s ↔
      ∃ child ∈ tiedChildren mol ops state node,
        fact ∈ factsMulti step mol ops depth geom state (M ++ [s]) child :=
  mem_underMulti_iff mol ops geom state M node (factsMulti step mol ops depth) s fact

/-! ## Congruence and stability -/

/-- A step that refuses at an occurrence without a four-ligand frame. -/
def MultiStepNoFrame (step : MultiStep) : Prop :=
  ∀ (mol : RawMolecule) (ops : Operations) (geom : Geometry) (state : OccurrenceAuxState)
    (M : MarkContext) (node : Node) (under : Nat → OccurrenceAuxState),
    frameAtoms? mol node = none → step mol ops geom state M node under = none

/-- Descriptors depend on the child continuation only through the facts of canonical children,
at every context. -/
theorem descriptorWithMulti_congr (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub₁ sub₂ : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (agree : ∀ child ∈ mol.canonicalChildren node, ∀ g st M',
      sub₁ g st M' child = sub₂ g st M' child) :
    descriptorWithMulti step mol ops geom state M node sub₁ =
      descriptorWithMulti step mol ops geom state M node sub₂ := by
  have under : ∀ g, underMulti mol ops g state M node sub₁ =
      underMulti mol ops g state M node sub₂ := by
    intro g
    funext s
    rw [underMulti_apply, underMulti_apply]
    exact flatMap_congr_mem _ _ _ fun child member =>
      agree child (mem_tiedChildren_actual mol ops state node child member) g state (M ++ [s])
  unfold descriptorWithMulti rawWithMulti?
  rw [under geom, under (mirror geom)]

/-- Descriptors at two depths agree when the child facts agree at every context. -/
theorem descriptorMulti_congr (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (first second : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext)
    (node : Node)
    (agree : ∀ child ∈ mol.canonicalChildren node, ∀ g st M',
      factsMulti step mol ops first g st M' child = factsMulti step mol ops second g st M' child) :
    descriptorMulti step mol ops first geom state M node =
      descriptorMulti step mol ops second geom state M node := by
  unfold descriptorMulti
  exact descriptorWithMulti_congr step mol ops geom state M node
    (factsMulti step mol ops first) (factsMulti step mol ops second) agree

theorem descriptorWithMulti_none_of_frame (step : MultiStep) (mol : RawMolecule)
    (ops : Operations) (noFrame : MultiStepNoFrame step) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (frame : frameAtoms? mol node = none) :
    descriptorWithMulti step mol ops geom state M node sub = none := by
  unfold descriptorWithMulti rawWithMulti?
  rw [noFrame mol ops geom state M node _ frame,
    noFrame mol ops (mirror geom) state M node _ frame]
  rfl

/-- A forced leaf contributes no facts at any depth and any context. -/
theorem factsMulti_forcedLeaf (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (noFrame : MultiStepNoFrame step) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (leaf : node.forcedLeaf = true) :
    factsMulti step mol ops depth geom state M node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
      have frame : frameAtoms? mol node = none := frameAtoms?_forcedLeaf mol node leaf
      have descriptor : descriptorMulti step mol ops depth geom state M node = none := by
        rw [descriptorMulti_eq]
        exact descriptorWithMulti_none_of_frame step mol ops noFrame geom state M node _ frame
      simp only [descriptorMulti_eq] at descriptor
      rw [factsMulti_succ, descriptor, canonicalChildren_forcedLeaf mol node leaf]
      rfl

/-- **Structural stability.** Once the depth leaves no room for a longer duplicate-free
in-range history, increasing it never changes the contributed facts, at any context. This is the
multi-mark analogue of the accepted single-reference `facts_stable`; only `WellFormedBonds` and
the step's frame refusal are used. -/
theorem factsMulti_stable (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (wellFormed : WellFormedBonds mol) (noFrame : MultiStepNoFrame step) :
    ∀ (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node),
      Sufficient mol depth node →
      factsMulti step mol ops depth geom state M node =
        factsMulti step mol ops (depth + 1) geom state M node := by
  intro depth
  induction depth with
  | zero =>
      intro geom state M node sufficient
      rcases sufficient with leaf | ⟨good, bound⟩
      · rw [factsMulti_forcedLeaf step mol ops noFrame 0 geom state M node leaf,
          factsMulti_forcedLeaf step mol ops noFrame 1 geom state M node leaf]
      · have := good.length_le
        omega
  | succ depth ih =>
      intro geom state M node sufficient
      rcases sufficient with leaf | ⟨good, bound⟩
      · rw [factsMulti_forcedLeaf step mol ops noFrame _ geom state M node leaf,
          factsMulti_forcedLeaf step mol ops noFrame _ geom state M node leaf]
      · have children : ∀ child ∈ mol.canonicalChildren node, ∀ g st M',
            factsMulti step mol ops depth g st M' child =
              factsMulti step mol ops (depth + 1) g st M' child :=
          fun child member g st M' =>
            ih g st M' child (Sufficient.child wellFormed good bound member)
        have descriptor : descriptorMulti step mol ops depth geom state M node =
            descriptorMulti step mol ops (depth + 1) geom state M node := by
          apply descriptorMulti_congr
          intro child member g st M'
          exact children child member g st M'
        simp only [descriptorMulti_eq] at descriptor
        rw [factsMulti_succ, factsMulti_succ, descriptor,
          flatMap_congr_mem _ _ _ fun child member => children child member geom state M]

theorem factsMulti_stable_add (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (wellFormed : WellFormedBonds mol) (noFrame : MultiStepNoFrame step)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sufficient : Sufficient mol depth node) (k : Nat) :
    factsMulti step mol ops (depth + k) geom state M node =
      factsMulti step mol ops depth geom state M node := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have deeper : Sufficient mol (depth + k) node := by
        rcases sufficient with leaf | ⟨good, bound⟩
        · exact Or.inl leaf
        · exact Or.inr ⟨good, by omega⟩
      rw [← ih, Nat.add_succ, ← factsMulti_stable step mol ops wellFormed noFrame (depth + k)
        geom state M node deeper]

/-- A `GoodNode` is sufficient at its own structural depth. -/
theorem sufficient_structuralDepth (mol : RawMolecule) (node : Node) (good : GoodNode mol node) :
    Sufficient mol (structuralDepth mol node) node := by
  refine Or.inr ⟨good, ?_⟩
  unfold structuralDepth
  have := good.length_le
  omega

/-- **No new fuel at structural depth.** Every context `M` is stable beyond the structural
depth of the occurrence. -/
theorem factsMulti_structuralDepth_stable (step : MultiStep) (mol : RawMolecule)
    (ops : Operations) (wellFormed : WellFormedBonds mol) (noFrame : MultiStepNoFrame step)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (good : GoodNode mol node) (k : Nat) :
    factsMulti step mol ops (structuralDepth mol node + k) geom state M node =
      factsMulti step mol ops (structuralDepth mol node) geom state M node :=
  factsMulti_stable_add step mol ops wellFormed noFrame (structuralDepth mol node) geom state M node
    (sufficient_structuralDepth mol node good) k

/-- Descriptor stability at the structural depth, for an arbitrary reached occurrence and
arbitrary inherited context. -/
theorem descriptorMulti_structuralDepth_stable (step : MultiStep) (mol : RawMolecule)
    (ops : Operations) (wellFormed : WellFormedBonds mol) (noFrame : MultiStepNoFrame step)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (good : GoodNode mol node) (k : Nat) :
    descriptorMulti step mol ops (structuralDepth mol node + k) geom state M node =
      descriptorMulti step mol ops (structuralDepth mol node) geom state M node := by
  apply descriptorMulti_congr
  intro child member g st M'
  have bound : mol.atomCount + 1 ≤ structuralDepth mol node + 1 + node.history.length := by
    unfold structuralDepth
    have := good.length_le
    omega
  exact factsMulti_stable_add step mol ops wellFormed noFrame (structuralDepth mol node) g st M'
    child (Sufficient.child wellFormed good bound member) k

/-- The root call at an empty inherited context. The local fallback at the root is the first
extension `[] ++ [s]`. -/
def assignCenterWith? (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (geom : Geometry) (center : Nat) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorMulti step mol ops (structuralDepth mol (canonicalCenterRoot center)) geom [] []
    (canonicalCenterRoot center)

/-- Structural-depth stability of the root call for every center index. -/
theorem assignCenterWith?_stable (step : MultiStep) (mol : RawMolecule) (ops : Operations)
    (wellFormed : WellFormedBonds mol) (noFrame : MultiStepNoFrame step) (geom : Geometry)
    (center : Nat) (valid : center < mol.atomCount) (k : Nat) :
    descriptorMulti step mol ops (structuralDepth mol (canonicalCenterRoot center) + k) geom [] []
        (canonicalCenterRoot center) = assignCenterWith? step mol ops geom center := by
  unfold assignCenterWith?
  apply descriptorMulti_structuralDepth_stable step mol ops wellFormed noFrame geom [] []
    (canonicalCenterRoot center) ?_ k
  refine ⟨List.nodup_singleton center, ?_⟩
  intro atom memberHistory
  simp only [canonicalCenterRoot, List.mem_singleton] at memberHistory
  rw [memberHistory]
  exact valid

/-! ## Concrete operations with a joint marked comparator

The marked field below is the explicit implementation interface. `markedJoint state node L s`
must produce the marked ranking of the reference `s` while preserving **all** marks in `L` in one
jointly built layout. The recursion always calls it with `L = M ++ [s]` and with child facts
generated under the same `M ++ [s]`. Nothing here constructs such a comparator or claims that
per-mark sorted keys can be combined into one.
-/







structure MultiOperations where
  ordinary : OccurrenceAuxState → Node → Option (List Nat × List (Option Ordering))
  contextOrder : OccurrenceAuxState → Node → MarkContext →
    Option (List Nat × List (Option Ordering))
  markedJoint : OccurrenceAuxState → Node → MarkContext → Nat → Option Rule6TrackedRanking

/-- The single-mark view of a multi-operation, with the empty inherited context. This shows
that the existing `Operations` record fits the interface at `M = []`. The traversal used by
`factsMulti` is the ordinary one; the concrete step tests `contextOrder` separately. -/
def toOperations (ops : MultiOperations) : Operations where
  ordinary := ops.ordinary
  marked := fun state node mark => ops.markedJoint state node [] mark

@[simp] theorem toOperations_ordinary (ops : MultiOperations) :
    (toOperations ops).ordinary = ops.ordinary := rfl

/-- The joint marked reading at context `M`: the comparator is called with the full extended
list `M ++ [s]`, never with `s` alone. -/
def markedReadingJoint? (mol : RawMolecule) (ops : MultiOperations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (M : MarkContext) (s : Nat) : Option RS := do
  let atoms ← frameAtoms? mol node
  let ranking ← ops.markedJoint state node M s
  let ranked ← rankedAtoms? atoms ranking
  readback? geom ranked

/-- One fallback reference evaluation: append the child facts generated under `M ++ [s]` and
read the joint comparator at the same extended context. -/
def evaluateMulti? (mol : RawMolecule) (ops : MultiOperations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (M : MarkContext)
    (under : Nat → OccurrenceAuxState) (s : Nat) : Option RS := do
  let temp ← appendFacts? state (under s)
  markedReadingJoint? mol ops geom temp node (M ++ [s]) s

/-- The concrete context-aware step. It first tests the joint current-context order
`contextOrder state node M`: if that order is strict, the inherited marks already determine the
reading and the sorted slots are read back directly. Otherwise the eligible class of that same
context order is used, and every local reference `s` is evaluated at `M ++ [s]` with the joint
comparator. The step never substitutes the unmarked ordinary order for the context order. The
traversal `under` is the ordinary tied-child state; see `ContextTiesWithinOrdinary` for the
explicit coverage contract on that superset. -/
def rawStepMulti? (ops : MultiOperations) (mol : RawMolecule) (_molOps : Operations)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (under : Nat → OccurrenceAuxState) : Option RS := do
  let atoms ← frameAtoms? mol node
  let (sorted, adjacent) ← ops.contextOrder state node M
  if ¬ atoms.Nodup ∨ consistent adjacent = false then none
  else if strict adjacent then
    let ranked ← atomsAt? atoms sorted
    readback? geom ranked
  else
    consensus ((eligibleOf atoms sorted adjacent).map
      (evaluateMulti? mol ops geom state node M under))

theorem rawStepMulti?_noFrame (ops : MultiOperations) : MultiStepNoFrame (rawStepMulti? ops) := by
  intro mol molOps geom state M node under frame
  simp [rawStepMulti?, frame]








def ContextTiesWithinOrdinary (ops : MultiOperations) (mol : RawMolecule) : Prop :=
  ∀ (state : OccurrenceAuxState) (node : Node) (M : MarkContext)
    (atoms sorted : List Nat) (adjacent : List (Option Ordering)),
    frameAtoms? mol node = some atoms →
    ops.contextOrder state node M = some (sorted, adjacent) →
    ∃ ordinarySorted ordinaryAdjacent,
      ops.ordinary state node = some (ordinarySorted, ordinaryAdjacent) ∧
        ∀ child ∈ mol.canonicalChildren node,
          child.atom ∈ eligibleOf atoms sorted adjacent →
            child.atom ∈ eligibleOf atoms ordinarySorted ordinaryAdjacent

/-- Coverage of the ordinary traversal under the explicit `ContextTiesWithinOrdinary` contract. -/
theorem mem_tiedChildren_of_context_eligible (ops : MultiOperations) (mol : RawMolecule)
    (refines : ContextTiesWithinOrdinary ops mol) (state : OccurrenceAuxState) (node : Node)
    (M : MarkContext) (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (contextOrder : ops.contextOrder state node M = some (sorted, adjacent))
    (child : Node) (member : child ∈ mol.canonicalChildren node)
    (eligible : child.atom ∈ eligibleOf atoms sorted adjacent) :
    child ∈ tiedChildren mol (toOperations ops) state node := by
  obtain ⟨ordinarySorted, ordinaryAdjacent, ordinaryOrder, within⟩ :=
    refines state node M atoms sorted adjacent frame contextOrder
  unfold tiedChildren
  rw [frame, toOperations_ordinary, ordinaryOrder, List.mem_filter]
  exact ⟨member, List.contains_iff_mem.mpr (within child member eligible)⟩

/-- Generated facts of the concrete multi-mark evaluator. The `Operations` argument used for
the tied children is `toOperations ops`; the step itself carries the joint comparator. -/
def facts (mol : RawMolecule) (ops : MultiOperations) :
    Nat → Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState :=
  factsMulti (rawStepMulti? ops) mol (toOperations ops)

/-- Descriptor of an occurrence under the concrete multi-mark evaluator. -/
def descriptor? (mol : RawMolecule) (ops : MultiOperations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorMulti (rawStepMulti? ops) mol (toOperations ops) depth geom state M node

theorem facts_succ (mol : RawMolecule) (ops : MultiOperations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    facts mol ops (depth + 1) geom state M node =
      (descriptor? mol ops depth geom state M node).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (facts mol ops depth geom state M) := rfl

/-- Exact fallback state of the concrete evaluator: children at `M ++ [s]`. -/
theorem facts_under (mol : RawMolecule) (ops : MultiOperations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) (s : Nat) :
    underMulti mol (toOperations ops) geom state M node (facts mol ops depth) s =
      (tiedChildren mol (toOperations ops) state node).flatMap
        (fun child => facts mol ops depth geom state (M ++ [s]) child) := rfl

/-- Membership form of `facts_under`: each fallback fact comes from a tied child at the extended
context `M ++ [s]`. -/
theorem mem_facts_under_iff (mol : RawMolecule) (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) (s : Nat)
    (fact : OccurrenceAuxFact) :
    fact ∈ underMulti mol (toOperations ops) geom state M node (facts mol ops depth) s ↔
      ∃ child ∈ tiedChildren mol (toOperations ops) state node,
        fact ∈ facts mol ops depth geom state (M ++ [s]) child :=
  mem_underMulti_factsMulti_iff (rawStepMulti? ops) mol (toOperations ops) depth geom state M node
    s fact

/-- Descriptor of the concrete evaluator uses exactly the extended-context child states. -/
theorem descriptor?_uses_child_context (mol : RawMolecule) (ops : MultiOperations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    descriptor? mol ops depth geom state M node =
      caseFromMirror?
        (rawStepMulti? ops mol (toOperations ops) geom state M node (fun s =>
          (tiedChildren mol (toOperations ops) state node).flatMap
            (fun child => facts mol ops depth geom state (M ++ [s]) child)))
        (rawStepMulti? ops mol (toOperations ops) (mirror geom) state M node (fun s =>
          (tiedChildren mol (toOperations ops) state node).flatMap
            (fun child => facts mol ops depth (mirror geom) state (M ++ [s]) child))) := by
  unfold descriptor?
  exact descriptorMulti_uses_child_context (rawStepMulti? ops) mol (toOperations ops) depth geom
    state M node

/-- Structural stability of the concrete evaluator, at any context. -/
theorem facts_stable (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) :
    ∀ (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node),
      Sufficient mol depth node →
      facts mol ops depth geom state M node = facts mol ops (depth + 1) geom state M node :=
  factsMulti_stable (rawStepMulti? ops) mol (toOperations ops) wellFormed
    (rawStepMulti?_noFrame ops)

theorem facts_stable_add (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sufficient : Sufficient mol depth node) (k : Nat) :
    facts mol ops (depth + k) geom state M node = facts mol ops depth geom state M node :=
  factsMulti_stable_add (rawStepMulti? ops) mol (toOperations ops) wellFormed
    (rawStepMulti?_noFrame ops) depth geom state M node sufficient k

/-- Structural-depth stability of the concrete evaluator, any context, no new fuel. -/
theorem facts_structuralDepth_stable (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (state : OccurrenceAuxState)
    (M : MarkContext) (node : Node) (good : GoodNode mol node) (k : Nat) :
    facts mol ops (structuralDepth mol node + k) geom state M node =
      facts mol ops (structuralDepth mol node) geom state M node :=
  factsMulti_structuralDepth_stable (rawStepMulti? ops) mol (toOperations ops) wellFormed
    (rawStepMulti?_noFrame ops) geom state M node good k

/-- Descriptor stability at the structural depth of the concrete evaluator. -/
theorem descriptor_structuralDepth_stable (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (state : OccurrenceAuxState)
    (M : MarkContext) (node : Node) (good : GoodNode mol node) (k : Nat) :
    descriptor? mol ops (structuralDepth mol node + k) geom state M node =
      descriptor? mol ops (structuralDepth mol node) geom state M node :=
  descriptorMulti_structuralDepth_stable (rawStepMulti? ops) mol (toOperations ops) wellFormed
    (rawStepMulti?_noFrame ops) geom state M node good k

/-- The root call of the concrete multi-mark evaluator. The inherited context starts empty; the
root's local fallback reads each eligible mark at `[] ++ [s] = [s]`. -/
def assignCenter? (mol : RawMolecule) (ops : MultiOperations) (geom : Geometry) (center : Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  assignCenterWith? (rawStepMulti? ops) mol (toOperations ops) geom center

/-- Structural-depth stability of the concrete root call. -/
theorem assignCenter?_stable (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (center : Nat)
    (valid : center < mol.atomCount) (k : Nat) :
    descriptor? mol ops (structuralDepth mol (canonicalCenterRoot center) + k) geom [] []
        (canonicalCenterRoot center) = assignCenter? mol ops geom center :=
  assignCenterWith?_stable (rawStepMulti? ops) mol (toOperations ops) wellFormed
    (rawStepMulti?_noFrame ops) geom center valid k

end TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.mem_append_singleton_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.mem_append_singleton_self
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.length_append_singleton_gt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.underMulti
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.underMulti_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.mem_underMulti_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.rawWithMulti?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorWithMulti
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorWithMulti_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.factsMulti
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.factsMulti_succ
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorMulti
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorMulti_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorMulti_uses_child_context
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.underMulti_factsMulti_fun
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.underMulti_factsMulti
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.mem_underMulti_factsMulti_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.MultiStepNoFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorWithMulti_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorMulti_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorWithMulti_none_of_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.factsMulti_forcedLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.factsMulti_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.factsMulti_stable_add
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.sufficient_structuralDepth
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.factsMulti_structuralDepth_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptorMulti_structuralDepth_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.assignCenterWith?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.assignCenterWith?_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.toOperations
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.toOperations_ordinary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.markedReadingJoint?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.evaluateMulti?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.rawStepMulti?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.rawStepMulti?_noFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.ContextTiesWithinOrdinary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.mem_tiedChildren_of_context_eligible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.facts
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptor?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.facts_succ
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.facts_under
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.mem_facts_under_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptor?_uses_child_context
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.facts_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.facts_stable_add
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.facts_structuralDepth_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.descriptor_structuralDepth_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.assignCenter?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion.assignCenter?_stable
