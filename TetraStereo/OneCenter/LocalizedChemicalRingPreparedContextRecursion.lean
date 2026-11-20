import TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000




































namespace TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion

open TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
open TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion
  (MultiOperations markedReadingJoint?)

/-- Canonical branch node of the raw molecule. -/
abbrev Node := RawMolecule.CanonicalBranchNode

/-- The inherited-mark context: the marks carried into an occurrence, oldest first. -/
abbrev MarkContext := List Nat

/-- Child facts supplied to a step as a function of the context they were generated under.
There is no sentinel atom and no single-reference encoding. -/
abbrev ChildStates := MarkContext → OccurrenceAuxState

/-- One-occurrence step whose child facts are a context-indexed continuation. -/
abbrev PreparedStep := RawMolecule → Geometry → OccurrenceAuxState → MarkContext → Node →
  ChildStates → Option RS

/-- Facts of every canonical child generated at the requested context. -/
def childrenUnder (mol : RawMolecule)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (geom : Geometry) (state : OccurrenceAuxState) (node : Node) : ChildStates :=
  fun L => (mol.canonicalChildren node).flatMap fun child => sub geom state L child

/-- Membership in the prepared child state is exactly membership in the facts of some canonical
child generated at the same context. This is the full canonical-child coverage statement; no
ordinary tied-child restriction occurs. -/
theorem mem_childrenUnder_iff (mol : RawMolecule)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (geom : Geometry) (state : OccurrenceAuxState) (node : Node) (L : MarkContext)
    (fact : OccurrenceAuxFact) :
    fact ∈ childrenUnder mol sub geom state node L ↔
      ∃ child ∈ mol.canonicalChildren node, fact ∈ sub geom state L child := by
  unfold childrenUnder
  rw [List.mem_flatMap]

/-- A fact of a canonical child generated at context `L` appears in the prepared state at `L`. -/
theorem canonicalChild_facts_mem_sameContext (mol : RawMolecule)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (geom : Geometry) (state : OccurrenceAuxState) (node : Node) (L : MarkContext)
    (child : Node) (member : child ∈ mol.canonicalChildren node)
    (fact : OccurrenceAuxFact) (factMem : fact ∈ sub geom state L child) :
    fact ∈ childrenUnder mol sub geom state node L :=
  (mem_childrenUnder_iff mol sub geom state node L fact).mpr ⟨child, member, factMem⟩

/-- Prepared comparison input at the occurrence's own context. -/
def prepareComparison? (state : OccurrenceAuxState) (under : ChildStates)
    (M : MarkContext) : Option OccurrenceAuxState :=
  appendFacts? state (under M)

/-- One fallback reference evaluation. It appends the child facts generated at `M ++ [s]` to the
**original** incoming state and reads the joint comparator at that same extended context. The
`M`-prepared state does not occur in this definition. -/
def evaluateFallback? (mol : RawMolecule) (ops : MultiOperations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (M : MarkContext) (under : ChildStates)
    (s : Nat) : Option RS := do
  let temp ← appendFacts? state (under (M ++ [s]))
  markedReadingJoint? mol ops geom temp node (M ++ [s]) s

/-- The fallback evaluation uses the original incoming state and child facts at `M ++ [s]`. -/
theorem evaluateFallback?_uses_original (mol : RawMolecule) (ops : MultiOperations)
    (geom : Geometry) (state : OccurrenceAuxState) (node : Node) (M : MarkContext)
    (under : ChildStates) (s : Nat) (temp : OccurrenceAuxState)
    (append : appendFacts? state (under (M ++ [s])) = some temp) :
    evaluateFallback? mol ops geom state node M under s =
      markedReadingJoint? mol ops geom temp node (M ++ [s]) s := by
  simp [evaluateFallback?, append]

/-- The part of a step after the frame and the prepared comparison state are known. The
`prepared` argument is the appended same-context child state; the fallback branch still refers to
the original `state`, never to `prepared`. -/
def comparisonAt? (ops : MultiOperations) (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) (under : ChildStates)
    (atoms : List Nat) (prepared : OccurrenceAuxState) : Option RS :=
  match ops.contextOrder prepared node M with
  | none => none
  | some (sorted, adjacent) =>
      if ¬ atoms.Nodup ∨ consistent adjacent = false then none
      else if strict adjacent then
        (do
          let ranked ← atomsAt? atoms sorted
          readback? geom ranked)
      else
        consensus ((eligibleOf atoms sorted adjacent).map
          (evaluateFallback? mol ops geom state node M under))

/-- The concrete prepared step. The frame is tested first; only then are the same-context child
facts appended, and only then is the inherited context order compared on that prepared state. -/
def rawStepPrepared? (ops : MultiOperations) (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) (under : ChildStates) :
    Option RS := do
  let atoms ← frameAtoms? mol node
  let prepared ← prepareComparison? state under M
  comparisonAt? ops mol geom state M node under atoms prepared

/-- **Same-context comparison.** When the frame and the prepared append succeed, the inherited
context order is compared on `appendFacts? state (under M)` and not on the incoming state
alone. -/
theorem rawStepPrepared?_compares_at_prepared (ops : MultiOperations) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (under : ChildStates) (atoms : List Nat) (prepared : OccurrenceAuxState)
    (frame : frameAtoms? mol node = some atoms)
    (append : appendFacts? state (under M) = some prepared) :
    rawStepPrepared? ops mol geom state M node under =
      comparisonAt? ops mol geom state M node under atoms prepared := by
  simp [rawStepPrepared?, prepareComparison?, frame, append]

/-- If the same-context child facts cannot be appended (duplicate occurrence key), the step
refuses instead of comparing on the stale incoming state. -/
theorem rawStepPrepared?_none_of_appendFails (ops : MultiOperations) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (under : ChildStates) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (append : appendFacts? state (under M) = none) :
    rawStepPrepared? ops mol geom state M node under = none := by
  simp [rawStepPrepared?, prepareComparison?, frame, append]

/-- The inherited context order is compared on the prepared state at any accepted append. -/
theorem comparisonAt?_contextOrder (ops : MultiOperations) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (under : ChildStates) (atoms : List Nat) (prepared : OccurrenceAuxState)
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (order : ops.contextOrder prepared node M = some (sorted, adjacent)) :
    comparisonAt? ops mol geom state M node under atoms prepared =
      (if ¬ atoms.Nodup ∨ consistent adjacent = false then none
       else if strict adjacent then
         (do
           let ranked ← atomsAt? atoms sorted
           readback? geom ranked)
       else
         consensus ((eligibleOf atoms sorted adjacent).map
           (fun s => evaluateFallback? mol ops geom state node M under s))) := by
  simp [comparisonAt?, order]

/-- **Separate fallback state.** In the tied branch the step returns exactly the consensus of
fallback evaluations that each append child facts at `M ++ [s]` to the original incoming state. -/
theorem rawStepPrepared?_consensus_uses_original (ops : MultiOperations) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (under : ChildStates) (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (prepared : OccurrenceAuxState)
    (frame : frameAtoms? mol node = some atoms)
    (append : appendFacts? state (under M) = some prepared)
    (order : ops.contextOrder prepared node M = some (sorted, adjacent))
    (nodup : atoms.Nodup) (consistentAdj : consistent adjacent = true)
    (notStrict : strict adjacent = false) :
    rawStepPrepared? ops mol geom state M node under =
      consensus ((eligibleOf atoms sorted adjacent).map
        (fun s => evaluateFallback? mol ops geom state node M under s)) := by
  rw [rawStepPrepared?_compares_at_prepared ops mol geom state M node under atoms prepared
      frame append,
    comparisonAt?_contextOrder ops mol geom state M node under atoms prepared sorted adjacent
      order]
  simp [nodup, consistentAdj, notStrict]

/-- The strict branch reads back the sorted slots, and does not consult any fallback state. -/
theorem rawStepPrepared?_strict_uses_prepared (ops : MultiOperations) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (under : ChildStates) (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (prepared : OccurrenceAuxState)
    (frame : frameAtoms? mol node = some atoms)
    (append : appendFacts? state (under M) = some prepared)
    (order : ops.contextOrder prepared node M = some (sorted, adjacent))
    (nodup : atoms.Nodup) (consistentAdj : consistent adjacent = true)
    (strictAdj : strict adjacent = true) :
    rawStepPrepared? ops mol geom state M node under =
      (do
        let ranked ← atomsAt? atoms sorted
        readback? geom ranked) := by
  rw [rawStepPrepared?_compares_at_prepared ops mol geom state M node under atoms prepared
      frame append,
    comparisonAt?_contextOrder ops mol geom state M node under atoms prepared sorted adjacent
      order]
  simp [nodup, consistentAdj, strictAdj]

/-- A step that refuses at an occurrence without a four-ligand frame. -/
def PreparedStepNoFrame (step : PreparedStep) : Prop :=
  ∀ (mol : RawMolecule) (geom : Geometry) (state : OccurrenceAuxState)
    (M : MarkContext) (node : Node) (under : ChildStates),
    frameAtoms? mol node = none → step mol geom state M node under = none

/-- The concrete step refuses before touching the child continuation when no frame exists. -/
theorem rawStepPrepared?_noFrame (ops : MultiOperations) :
    PreparedStepNoFrame (rawStepPrepared? ops) := by
  intro mol geom state M node under frame
  simp [rawStepPrepared?, frame]

/-- With an explicit child continuation, one occurrence is evaluated at context `M`. -/
def rawWithPrepared? (step : PreparedStep) (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    Option RS :=
  step mol geom state M node (childrenUnder mol sub geom state node)

theorem rawWithPrepared?_apply (step : PreparedStep) (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    rawWithPrepared? step mol geom state M node sub =
      step mol geom state M node (childrenUnder mol sub geom state node) := rfl

/-- The mirror-cased descriptor. Each geometry receives its **own** child state generated under
that geometry and the same context `M`; the two are never conflated. -/
def descriptorWithPrepared (step : PreparedStep) (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  caseFromMirror?
    (step mol geom state M node (childrenUnder mol sub geom state node))
    (step mol (mirror geom) state M node (childrenUnder mol sub (mirror geom) state node))

/-- Definitional form of the descriptor: original and mirrored geometries each use their own
same-context child facts. -/
theorem descriptorWithPrepared_apply (step : PreparedStep) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    descriptorWithPrepared step mol geom state M node sub =
      caseFromMirror?
        (step mol geom state M node (childrenUnder mol sub geom state node))
        (step mol (mirror geom) state M node
          (childrenUnder mol sub (mirror geom) state node)) := rfl

/-- The same-generic descriptor through the explicit raw call. -/
theorem descriptorWithPrepared_eq (step : PreparedStep) (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    descriptorWithPrepared step mol geom state M node sub =
      caseFromMirror?
        (rawWithPrepared? step mol geom state M node sub)
        (rawWithPrepared? step mol (mirror geom) state M node sub) := rfl

/-- Descriptors depend on the child continuation only through the facts of canonical children,
at every context. The two continuations are compared on all canonical children and all contexts,
which covers the same-context comparison state and every possible `M ++ [s]` fallback state. -/
theorem descriptorWithPrepared_congr (step : PreparedStep) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub₁ sub₂ : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (agree : ∀ child ∈ mol.canonicalChildren node, ∀ g st M',
      sub₁ g st M' child = sub₂ g st M' child) :
    descriptorWithPrepared step mol geom state M node sub₁ =
      descriptorWithPrepared step mol geom state M node sub₂ := by
  have children : ∀ g, childrenUnder mol sub₁ g state node =
      childrenUnder mol sub₂ g state node := by
    intro g
    funext L
    unfold childrenUnder
    exact flatMap_congr_mem _ _ _ fun child member => agree child member g state L
  unfold descriptorWithPrepared
  rw [children geom, children (mirror geom)]

/-- A framed refusal descriptor is `none` at every context and for every child continuation; the
continuation is not evaluated. -/
theorem descriptorWithPrepared_none_of_frame (step : PreparedStep) (mol : RawMolecule)
    (noFrame : PreparedStepNoFrame step) (geom : Geometry) (state : OccurrenceAuxState)
    (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (frame : frameAtoms? mol node = none) :
    descriptorWithPrepared step mol geom state M node sub = none := by
  unfold descriptorWithPrepared
  rw [noFrame mol geom state M node _ frame,
    noFrame mol (mirror geom) state M node _ frame]
  rfl

/-- The terminating occurrence recursion at context `M`. Every canonical child is visited (not
only ordinary tied children). A child recursive call uses `depth`, so depth decreases
structurally; the descriptor at this occurrence uses the child facts at the same `depth`. -/
def factsOfStep (step : PreparedStep) (mol : RawMolecule) :
    Nat → Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState
  | 0, _, _, _, _ => []
  | depth + 1, geom, state, M, node =>
      (descriptorWithPrepared step mol geom state M node
        (factsOfStep step mol depth)).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (factsOfStep step mol depth geom state M)

/-- The descriptor of an occurrence whose descendants are generated at `depth`. -/
def descriptorOfStep (step : PreparedStep) (mol : RawMolecule) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorWithPrepared step mol geom state M node (factsOfStep step mol depth)

/-- One unfolding step of the facts recursion. The child calls use the same context `M` and the
strictly smaller `depth`; the occurrence's own descriptor also uses those same-`depth`, same-`M`
child facts. -/
theorem factsOfStep_succ (step : PreparedStep) (mol : RawMolecule) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    factsOfStep step mol (depth + 1) geom state M node =
      (descriptorOfStep step mol depth geom state M node).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (factsOfStep step mol depth geom state M) := rfl

/-- Facts at depth zero are empty at every context. -/
theorem factsOfStep_zero (step : PreparedStep) (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    factsOfStep step mol 0 geom state M node = [] := rfl

/-- At depth zero the same-context child state is empty. Such a comparison sees only the
incoming state. The sufficient-depth theorems below justify the root's structural-depth call;
this equation alone makes no adequacy claim for an arbitrarily small depth. -/
theorem childrenUnder_factsOfStep_zero (step : PreparedStep) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (node : Node) (M : MarkContext) :
    childrenUnder mol (factsOfStep step mol 0) geom state node M = [] := by
  unfold childrenUnder
  have h : (fun child : Node => factsOfStep step mol 0 geom state M child) = fun _ => [] := by
    funext child
    rfl
  rw [h]
  exact flatMap_nil_fun (mol.canonicalChildren node)

/-- A forced leaf contributes no facts at any depth and any context. The descriptor is refused
before the child continuation is inspected, and a forced leaf has no canonical children. -/
theorem factsOfStep_forcedLeaf (step : PreparedStep) (mol : RawMolecule)
    (noFrame : PreparedStepNoFrame step) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (leaf : node.forcedLeaf = true) :
    factsOfStep step mol depth geom state M node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
      have frame : frameAtoms? mol node = none := frameAtoms?_forcedLeaf mol node leaf
      have descriptor : descriptorOfStep step mol depth geom state M node = none := by
        unfold descriptorOfStep
        exact descriptorWithPrepared_none_of_frame step mol noFrame geom state M node _ frame
      rw [factsOfStep_succ, descriptor, canonicalChildren_forcedLeaf mol node leaf]
      rfl

/-- Descriptors at two depths agree when the child facts agree at every context. -/
theorem descriptorOfStep_congr (step : PreparedStep) (mol : RawMolecule) (first second : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (agree : ∀ child ∈ mol.canonicalChildren node, ∀ g st M',
      factsOfStep step mol first g st M' child =
        factsOfStep step mol second g st M' child) :
    descriptorOfStep step mol first geom state M node =
      descriptorOfStep step mol second geom state M node := by
  unfold descriptorOfStep
  exact descriptorWithPrepared_congr step mol geom state M node _ _ agree

/-- **Structural stability.** Once the depth leaves no room for a longer duplicate-free in-range
history, increasing it never changes the contributed facts, at any context and for any step that
refuses without a frame. Only `WellFormedBonds` and the no-frame refusal are used. -/
theorem factsOfStep_stable (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : WellFormedBonds mol) (noFrame : PreparedStepNoFrame step) :
    ∀ (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node),
      Sufficient mol depth node →
      factsOfStep step mol depth geom state M node =
        factsOfStep step mol (depth + 1) geom state M node := by
  intro depth
  induction depth with
  | zero =>
      intro geom state M node sufficient
      rcases sufficient with leaf | ⟨good, bound⟩
      · rw [factsOfStep_forcedLeaf step mol noFrame 0 geom state M node leaf,
          factsOfStep_forcedLeaf step mol noFrame 1 geom state M node leaf]
      · have := good.length_le
        omega
  | succ depth ih =>
      intro geom state M node sufficient
      rcases sufficient with leaf | ⟨good, bound⟩
      · rw [factsOfStep_forcedLeaf step mol noFrame _ geom state M node leaf,
          factsOfStep_forcedLeaf step mol noFrame _ geom state M node leaf]
      · have children : ∀ child ∈ mol.canonicalChildren node, ∀ g st M',
            factsOfStep step mol depth g st M' child =
              factsOfStep step mol (depth + 1) g st M' child :=
          fun child member g st M' =>
            ih g st M' child (Sufficient.child wellFormed good bound member)
        have descriptor : descriptorOfStep step mol depth geom state M node =
            descriptorOfStep step mol (depth + 1) geom state M node := by
          apply descriptorOfStep_congr
          intro child member g st M'
          exact children child member g st M'
        rw [factsOfStep_succ, factsOfStep_succ, descriptor,
          flatMap_congr_mem _ _ _ fun child member => children child member geom state M]

/-- Stability under adding fuel once the depth is sufficient. -/
theorem factsOfStep_stable_add (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : WellFormedBonds mol) (noFrame : PreparedStepNoFrame step)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sufficient : Sufficient mol depth node) (k : Nat) :
    factsOfStep step mol (depth + k) geom state M node =
      factsOfStep step mol depth geom state M node := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have deeper : Sufficient mol (depth + k) node := by
        rcases sufficient with leaf | ⟨good, bound⟩
        · exact Or.inl leaf
        · exact Or.inr ⟨good, by omega⟩
      rw [← ih, Nat.add_succ, ← factsOfStep_stable step mol wellFormed noFrame (depth + k)
        geom state M node deeper]

/-- A `GoodNode` is sufficient at its own structural depth. -/
theorem sufficient_structuralDepth (mol : RawMolecule) (node : Node) (good : GoodNode mol node) :
    Sufficient mol (structuralDepth mol node) node := by
  refine Or.inr ⟨good, ?_⟩
  unfold structuralDepth
  have := good.length_le
  omega

/-- **No new fuel at structural depth.** Every context `M` is stable beyond the structural depth
of the occurrence. -/
theorem factsOfStep_structuralDepth_stable (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : WellFormedBonds mol) (noFrame : PreparedStepNoFrame step)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (good : GoodNode mol node) (k : Nat) :
    factsOfStep step mol (structuralDepth mol node + k) geom state M node =
      factsOfStep step mol (structuralDepth mol node) geom state M node :=
  factsOfStep_stable_add step mol wellFormed noFrame (structuralDepth mol node) geom state M node
    (sufficient_structuralDepth mol node good) k

/-- Descriptor stability at the structural depth, for an arbitrary reached occurrence and
arbitrary inherited context. -/
theorem descriptorOfStep_structuralDepth_stable (step : PreparedStep) (mol : RawMolecule)
    (wellFormed : WellFormedBonds mol) (noFrame : PreparedStepNoFrame step)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (good : GoodNode mol node) (k : Nat) :
    descriptorOfStep step mol (structuralDepth mol node + k) geom state M node =
      descriptorOfStep step mol (structuralDepth mol node) geom state M node := by
  apply descriptorOfStep_congr
  intro child member g st M'
  have bound : mol.atomCount + 1 ≤ structuralDepth mol node + 1 + node.history.length := by
    unfold structuralDepth
    have := good.length_le
    omega
  exact factsOfStep_stable_add step mol wellFormed noFrame (structuralDepth mol node) g st M'
    child (Sufficient.child wellFormed good bound member) k

/-! ## The concrete prepared-context evaluator -/

/-- Facts generated by the concrete prepared-context evaluator. -/
def preparedFacts (mol : RawMolecule) (ops : MultiOperations) :
    Nat → Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState :=
  factsOfStep (rawStepPrepared? ops) mol

/-- Descriptor of an occurrence under the concrete prepared-context evaluator. -/
def preparedDescriptor? (mol : RawMolecule) (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorOfStep (rawStepPrepared? ops) mol depth geom state M node

/-- One unfolding step of the concrete facts recursion. -/
theorem preparedFacts_succ (mol : RawMolecule) (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    preparedFacts mol ops (depth + 1) geom state M node =
      (preparedDescriptor? mol ops depth geom state M node).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (preparedFacts mol ops depth geom state M) := rfl

/-- Same-context comparison for the concrete step: the appended child facts are exactly the
facts of all canonical children generated at `M`. -/
theorem preparedStep_compares_on_sameContext_children (mol : RawMolecule) (ops : MultiOperations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (atoms : List Nat) (prepared : OccurrenceAuxState)
    (frame : frameAtoms? mol node = some atoms)
    (append : appendFacts? state
      (childrenUnder mol (preparedFacts mol ops depth) geom state node M) = some prepared) :
    rawStepPrepared? ops mol geom state M node
        (childrenUnder mol (preparedFacts mol ops depth) geom state node) =
      comparisonAt? ops mol geom state M node
        (childrenUnder mol (preparedFacts mol ops depth) geom state node) atoms prepared :=
  rawStepPrepared?_compares_at_prepared ops mol geom state M node
    (childrenUnder mol (preparedFacts mol ops depth) geom state node) atoms prepared frame append

/-- Fallback comparison for the concrete step: the temporary state is `appendFacts?` of the
**original** incoming state and the child facts generated at `M ++ [s]`. -/
theorem preparedStep_fallback_uses_extendedChildren (mol : RawMolecule) (ops : MultiOperations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (s : Nat) (temp : OccurrenceAuxState)
    (append : appendFacts? state
      (childrenUnder mol (preparedFacts mol ops depth) geom state node (M ++ [s])) = some temp) :
    evaluateFallback? mol ops geom state node M
        (childrenUnder mol (preparedFacts mol ops depth) geom state node) s =
      markedReadingJoint? mol ops geom temp node (M ++ [s]) s :=
  evaluateFallback?_uses_original mol ops geom state node M
    (childrenUnder mol (preparedFacts mol ops depth) geom state node) s temp append

/-- **Every canonical child is covered at either context.** For a canonical child, the facts it
generates at `M` occur in the prepared comparison state at `M`, and the facts it generates at
`M ++ [s]` occur in the fallback state at `M ++ [s]`. -/
theorem canonicalChildren_covered (mol : RawMolecule) (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (child : Node) (member : child ∈ mol.canonicalChildren node) :
    (∀ fact ∈ preparedFacts mol ops depth geom state M child,
        fact ∈ childrenUnder mol (preparedFacts mol ops depth) geom state node M) ∧
    (∀ (s : Nat) (fact : OccurrenceAuxFact),
        fact ∈ preparedFacts mol ops depth geom state (M ++ [s]) child →
        fact ∈ childrenUnder mol (preparedFacts mol ops depth) geom state node (M ++ [s])) := by
  constructor
  · intro fact factMem
    exact canonicalChild_facts_mem_sameContext mol (preparedFacts mol ops depth) geom state node M
      child member fact factMem
  · intro s fact factMem
    exact canonicalChild_facts_mem_sameContext mol (preparedFacts mol ops depth) geom state node
      (M ++ [s]) child member fact factMem

/-- The facts recursion exports every canonical child's same-context facts to the parent. -/
theorem canonicalChild_facts_mem_parent (mol : RawMolecule) (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node child : Node)
    (member : child ∈ mol.canonicalChildren node) (fact : OccurrenceAuxFact)
    (factMem : fact ∈ preparedFacts mol ops depth geom state M child) :
    fact ∈ preparedFacts mol ops (depth + 1) geom state M node := by
  rw [preparedFacts_succ]
  exact List.mem_append.mpr
    (Or.inr (List.mem_flatMap.mpr ⟨child, member, factMem⟩))

/-- The same export at an extended context. -/
theorem canonicalChild_facts_mem_parent_extended (mol : RawMolecule) (ops : MultiOperations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext)
    (node child : Node) (member : child ∈ mol.canonicalChildren node) (s : Nat)
    (fact : OccurrenceAuxFact)
    (factMem : fact ∈ preparedFacts mol ops depth geom state (M ++ [s]) child) :
    fact ∈ preparedFacts mol ops (depth + 1) geom state (M ++ [s]) node :=
  canonicalChild_facts_mem_parent mol ops depth geom state (M ++ [s]) node child member fact factMem

/-- Concrete strict branch: only the prepared same-context state is compared. -/
theorem preparedStep_strict (mol : RawMolecule) (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (atoms sorted : List Nat) (adjacent : List (Option Ordering)) (prepared : OccurrenceAuxState)
    (frame : frameAtoms? mol node = some atoms)
    (append : appendFacts? state
      (childrenUnder mol (preparedFacts mol ops depth) geom state node M) = some prepared)
    (order : ops.contextOrder prepared node M = some (sorted, adjacent))
    (nodup : atoms.Nodup) (consistentAdj : consistent adjacent = true)
    (strictAdj : strict adjacent = true) :
    rawStepPrepared? ops mol geom state M node
        (childrenUnder mol (preparedFacts mol ops depth) geom state node) =
      (do
        let ranked ← atomsAt? atoms sorted
        readback? geom ranked) :=
  rawStepPrepared?_strict_uses_prepared ops mol geom state M node
    (childrenUnder mol (preparedFacts mol ops depth) geom state node) atoms sorted adjacent prepared
    frame append order nodup consistentAdj strictAdj

/-- Concrete consensus branch: each fallback starts from the original incoming state and its own
extended-context child facts. -/
theorem preparedStep_consensus (mol : RawMolecule) (ops : MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (atoms sorted : List Nat) (adjacent : List (Option Ordering)) (prepared : OccurrenceAuxState)
    (frame : frameAtoms? mol node = some atoms)
    (append : appendFacts? state
      (childrenUnder mol (preparedFacts mol ops depth) geom state node M) = some prepared)
    (order : ops.contextOrder prepared node M = some (sorted, adjacent))
    (nodup : atoms.Nodup) (consistentAdj : consistent adjacent = true)
    (notStrict : strict adjacent = false) :
    rawStepPrepared? ops mol geom state M node
        (childrenUnder mol (preparedFacts mol ops depth) geom state node) =
      consensus ((eligibleOf atoms sorted adjacent).map
        (fun s => evaluateFallback? mol ops geom state node M
          (childrenUnder mol (preparedFacts mol ops depth) geom state node) s)) :=
  rawStepPrepared?_consensus_uses_original ops mol geom state M node
    (childrenUnder mol (preparedFacts mol ops depth) geom state node) atoms sorted adjacent prepared
    frame append order nodup consistentAdj notStrict

/-- Structural stability of the concrete evaluator, at any context. -/
theorem preparedFacts_stable (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) :
    ∀ (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node),
      Sufficient mol depth node →
      preparedFacts mol ops depth geom state M node =
        preparedFacts mol ops (depth + 1) geom state M node :=
  factsOfStep_stable (rawStepPrepared? ops) mol wellFormed (rawStepPrepared?_noFrame ops)

theorem preparedFacts_stable_add (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sufficient : Sufficient mol depth node) (k : Nat) :
    preparedFacts mol ops (depth + k) geom state M node =
      preparedFacts mol ops depth geom state M node :=
  factsOfStep_stable_add (rawStepPrepared? ops) mol wellFormed (rawStepPrepared?_noFrame ops)
    depth geom state M node sufficient k

/-- Structural-depth stability of the concrete evaluator, any context, no new fuel. -/
theorem preparedFacts_structuralDepth_stable (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (state : OccurrenceAuxState)
    (M : MarkContext) (node : Node) (good : GoodNode mol node) (k : Nat) :
    preparedFacts mol ops (structuralDepth mol node + k) geom state M node =
      preparedFacts mol ops (structuralDepth mol node) geom state M node :=
  factsOfStep_structuralDepth_stable (rawStepPrepared? ops) mol wellFormed
    (rawStepPrepared?_noFrame ops) geom state M node good k

/-- Descriptor stability at the structural depth of the concrete evaluator. -/
theorem preparedDescriptor_structuralDepth_stable (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (state : OccurrenceAuxState)
    (M : MarkContext) (node : Node) (good : GoodNode mol node) (k : Nat) :
    preparedDescriptor? mol ops (structuralDepth mol node + k) geom state M node =
      preparedDescriptor? mol ops (structuralDepth mol node) geom state M node :=
  descriptorOfStep_structuralDepth_stable (rawStepPrepared? ops) mol wellFormed
    (rawStepPrepared?_noFrame ops) geom state M node good k

/-- The root call of the concrete prepared-context evaluator. The inherited context starts empty;
each root fallback reads `[] ++ [s] = [s]`. -/
def preparedAssignCenter? (mol : RawMolecule) (ops : MultiOperations) (geom : Geometry)
    (center : Nat) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorOfStep (rawStepPrepared? ops) mol
    (structuralDepth mol (canonicalCenterRoot center)) geom [] []
    (canonicalCenterRoot center)

/-- Structural-depth stability of the concrete root call. -/
theorem preparedAssignCenter?_stable (mol : RawMolecule) (ops : MultiOperations)
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (center : Nat)
    (valid : center < mol.atomCount) (k : Nat) :
    preparedDescriptor? mol ops (structuralDepth mol (canonicalCenterRoot center) + k) geom [] []
        (canonicalCenterRoot center) = preparedAssignCenter? mol ops geom center := by
  unfold preparedAssignCenter? preparedDescriptor?
  apply descriptorOfStep_structuralDepth_stable (rawStepPrepared? ops) mol wellFormed
    (rawStepPrepared?_noFrame ops) geom [] [] (canonicalCenterRoot center) ?_ k
  refine ⟨List.nodup_singleton center, ?_⟩
  intro atom memberHistory
  simp only [canonicalCenterRoot, List.mem_singleton] at memberHistory
  rw [memberHistory]
  exact valid

end TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.Node
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.MarkContext
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.ChildStates
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.PreparedStep
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.childrenUnder
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.mem_childrenUnder_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.canonicalChild_facts_mem_sameContext
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.prepareComparison?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.evaluateFallback?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.evaluateFallback?_uses_original
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.comparisonAt?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.rawStepPrepared?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.rawStepPrepared?_compares_at_prepared
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.rawStepPrepared?_none_of_appendFails
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.comparisonAt?_contextOrder
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.rawStepPrepared?_consensus_uses_original
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.rawStepPrepared?_strict_uses_prepared
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.PreparedStepNoFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.rawStepPrepared?_noFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.rawWithPrepared?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.rawWithPrepared?_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.descriptorWithPrepared
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.descriptorWithPrepared_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.descriptorWithPrepared_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.descriptorWithPrepared_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.descriptorWithPrepared_none_of_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.factsOfStep
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.descriptorOfStep
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.factsOfStep_succ
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.factsOfStep_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.childrenUnder_factsOfStep_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.factsOfStep_forcedLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.descriptorOfStep_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.factsOfStep_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.factsOfStep_stable_add
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.sufficient_structuralDepth
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.factsOfStep_structuralDepth_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.descriptorOfStep_structuralDepth_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedFacts
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedFacts_succ
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedStep_compares_on_sameContext_children
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedStep_fallback_uses_extendedChildren
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.canonicalChildren_covered
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.canonicalChild_facts_mem_parent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.canonicalChild_facts_mem_parent_extended
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedStep_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedStep_consensus
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedFacts_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedFacts_stable_add
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedFacts_structuralDepth_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor_structuralDepth_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedAssignCenter?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedAssignCenter?_stable
