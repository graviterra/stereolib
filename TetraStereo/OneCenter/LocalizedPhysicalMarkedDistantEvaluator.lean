import TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Structurally bounded recursion retaining distant references

This successor uses the existing occurrence children, temporary-fact construction, mirror case
classification and structural depth. Only the inherited-reference choice changes, through
`LocalizedPhysicalMarkedDistantReference.rawStep?`. The old evaluator remains available.

The fixed-depth equations and stabilization proofs derive termination/stability from the same
finite occurrence histories. Frame-local rankers preserve all prior generated facts and reports.
These are operational properties; chemical sufficiency of the broader policy is a separate goal.
-/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator

open LocalizedGenericMarkedRecalculation hiding tiedChildren rawStep? underWith rawWith?
  descriptorWith? facts descriptor? assignCenter? assign facts_succ facts_stable facts_stable_add
  descriptorWith?_congr assignCenter?_stable
open LocalizedMarkedOperationEvaluator (Operations tiedChildren underWith mem_tiedChildren_actual)
open LocalizedPhysicalMarkedDistantReference (rawStep? FrameLocalOperations rawStep_eq_of_frameLocal)

abbrev Node := RawMolecule.CanonicalBranchNode

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


/-- All generated facts are preserved for callback implementations that cannot read nonlocal marks. -/
theorem facts_eq_of_frameLocal (mol : RawMolecule) (ops : Operations)
    (localOps : FrameLocalOperations mol ops) :
    ∀ depth geom state ctx node, facts mol ops depth geom state ctx node =
      LocalizedMarkedOperationEvaluator.facts mol ops depth geom state ctx node := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro geom state ctx node
      have descriptor : descriptor? mol ops depth geom state ctx node =
          LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom state ctx node := by
        unfold descriptor?
        rw [descriptorWith?_congr mol ops geom state ctx node _
          (LocalizedMarkedOperationEvaluator.facts mol ops depth)
          (fun child _ g s x => ih g s x child)]
        unfold descriptorWith? rawWith? LocalizedMarkedOperationEvaluator.descriptor?
          LocalizedMarkedOperationEvaluator.descriptorWith?
          LocalizedMarkedOperationEvaluator.rawWith?
        rw [rawStep_eq_of_frameLocal mol ops localOps,
          rawStep_eq_of_frameLocal mol ops localOps]
      rw [facts_succ, LocalizedMarkedOperationEvaluator.facts_succ, descriptor]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child _ => ih geom state ctx child

theorem descriptor_eq_of_frameLocal (mol : RawMolecule) (ops : Operations)
    (localOps : FrameLocalOperations mol ops) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    descriptor? mol ops depth geom state ctx node =
      LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom state ctx node := by
  unfold descriptor?
  rw [descriptorWith?_congr mol ops geom state ctx node _
    (LocalizedMarkedOperationEvaluator.facts mol ops depth)
    (fun child _ g s x => facts_eq_of_frameLocal mol ops localOps depth g s x child)]
  unfold descriptorWith? rawWith? LocalizedMarkedOperationEvaluator.descriptor?
    LocalizedMarkedOperationEvaluator.descriptorWith? LocalizedMarkedOperationEvaluator.rawWith?
  rw [rawStep_eq_of_frameLocal mol ops localOps, rawStep_eq_of_frameLocal mol ops localOps]

theorem assign_eq_of_frameLocal (mol : RawMolecule) (ops : Operations)
    (localOps : FrameLocalOperations mol ops) (geom : Geometry) :
    assign mol ops geom = LocalizedMarkedOperationEvaluator.assign mol ops geom := by
  unfold assign LocalizedMarkedOperationEvaluator.assign
  apply List.filterMap_congr
  intro center _
  exact congrArg (Option.map (fun d => (center, d)))
    (descriptor_eq_of_frameLocal mol ops localOps _ geom [] none (canonicalCenterRoot center))

end TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator.descriptorWith?_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator.facts_forcedLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator.facts_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator.assignCenter?_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator.facts_eq_of_frameLocal
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator.descriptor_eq_of_frameLocal
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator.assign_eq_of_frameLocal
