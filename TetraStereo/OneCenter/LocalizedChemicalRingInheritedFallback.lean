import TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
An isolated experimental successor retries a refused inherited reading with the existing
no-context consensus, using the SAME continuation. Each local reference therefore still
receives its own generated child facts. Successful inherited steps are preserved for fixed
continuations; no preservation of whole recursive reports is asserted.

The existing evaluator and production defaults are unchanged. Chemical completeness remains
open, including whether the actual boundary and reference constraints exclude nontrivial
even stabilizers in the relevant reached contexts. No concrete A4 molecular obstruction is
established here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback

open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingOrientationInduction (StepNoFrame)
open LocalizedMarkedOperationEvaluator (Operations underWith mem_tiedChildren_actual)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? mirror caseFromMirror? factOf
  flatMap_congr_mem structuralDepth canonicalChildren_forcedLeaf
  frameAtoms?_forcedLeaf WellFormedBonds GoodNode Sufficient consensus)

abbrev Node := RawMolecule.CanonicalBranchNode

private def retry {α : Type} (first : Option α) (fallback : Unit → Option α) : Option α :=
  match first with
  | some value => some value
  | none => fallback ()

private theorem retry_map {α β : Type} (f : α → β) (first : Option α)
    (fallback : Unit → Option α) :
    retry (first.map f) (fun u => (fallback u).map f) = (retry first fallback).map f := by
  cases first <;> rfl

/-- Retry a refused inherited step with the existing local consensus. The no-context
case is executed only once, including when it refuses. -/
def rawStep? (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) : Option RS :=
  match ctx with
  | none => LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under
  | some mark => retry
      (LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state (some mark) node under)
      (fun _ => LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under)

private theorem rawStep_eq_retry (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) :
    rawStep? mol ops geom state ctx node under =
      retry (LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under)
        (fun _ => LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under) := by
  cases ctx with
  | some mark => rfl
  | none =>
      unfold rawStep?
      cases LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under <;> rfl

theorem rawStep_none (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (under : Nat → OccurrenceAuxState) :
    rawStep? mol ops geom state none node under =
      LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under := rfl

/-- Preservation holds at one step with exactly the same supplied child continuation. -/
theorem rawStep_preserves_some (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) (value : RS)
    (success : LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under =
      some value) : rawStep? mol ops geom state ctx node under = some value := by
  simp only [rawStep_eq_retry, success, retry]

theorem rawStep_eq_some_iff (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) (value : RS) :
    rawStep? mol ops geom state ctx node under = some value ↔
      LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under = some value ∨
      (LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under = none ∧
       LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under = some value) := by
  rw [rawStep_eq_retry]
  cases LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under <;>
    simp [retry]

/-- Exact condition for an added successful step; the failed inherited step is explicit. -/
theorem rawStep_added_some_iff (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) (value : RS) :
    (rawStep? mol ops geom state ctx node under = some value ∧
      LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under = none) ↔
      (LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under = none ∧
       LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under = some value) := by
  rw [rawStep_eq_some_iff]
  cases LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under <;> simp

/-- Retrying cannot rescue consensus when the refused reference is itself eligible. -/
theorem consensus_none_of_refused_eligible (eligible : List Nat) (reading : Nat → Option RS)
    (mark : Nat) (member : mark ∈ eligible) (refused : reading mark = none) :
    consensus (eligible.map reading) = none := by
  cases found : consensus (eligible.map reading) with
  | none => rfl
  | some value =>
      have all := (consensus_eq_some_iff _ value).mp found
      have impossible := all.2 (reading mark) (List.mem_map.mpr ⟨mark, member, rfl⟩)
      rw [refused] at impossible
      contradiction

theorem stepMap {mol : RawMolecule} {ops : Operations} {σ : Nat → Nat}
    (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol) (cov : Covariant mol ops σ) :
    StepMap rawStep? mol ops σ := by
  intro node reached geom ctx under under' hu
  have previous := distantStep_map sym wellFormed unique single cov
  rw [rawStep_eq_retry, rawStep_eq_retry, previous node reached geom ctx under under' hu]
  have fallback := previous node reached geom none under under' hu
  simp only [Option.map_none] at fallback
  rw [fallback]

theorem stepCongr (mol : RawMolecule) (ops : Operations) : StepCongr rawStep? mol ops := by
  intro first second node agree state ctx under
  have previous := distantStep_congr_geom (mol := mol) (ops := ops)
  rw [rawStep_eq_retry, rawStep_eq_retry,
    previous first second node agree state ctx under,
    previous first second node agree state none under]

private theorem retry_flip (s : ℝ) (first : Option RS) (fallback : Unit → Option RS) :
    retry (flipBy s first) (fun u => flipBy s (fallback u)) = flipBy s (retry first fallback) := by
  unfold flipBy
  split_ifs
  · rfl
  · exact retry_map RS.swap first fallback

theorem stepFlip (mol : RawMolecule) (ops : Operations) : StepFlip mol ops rawStep? := by
  intro s first second node atoms frame flip state ctx under
  have previous := distantStep_flip mol ops s first second node atoms frame flip
  rw [rawStep_eq_retry, rawStep_eq_retry, previous state ctx under, previous state none under]
  exact retry_flip s _ _

theorem stepNoFrame (mol : RawMolecule) (ops : Operations) : StepNoFrame mol ops rawStep? := by
  intro geom state ctx node under frame
  have previous := LocalizedChemicalRingOrientationInduction.distantStep_noFrame mol ops
  simp only [rawStep_eq_retry, previous geom state ctx node under frame,
    previous geom state none node under frame, retry]

/-- The existing finite occurrence recursion instantiated with the experimental step. -/
def facts (mol : RawMolecule) (ops : Operations) := factsWith rawStep? mol ops

def descriptor? (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorWith rawStep? mol ops depth geom state ctx node

def assignCenter? (mol : RawMolecule) (ops : Operations) (geom : Geometry) (center : Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptor? mol ops (structuralDepth mol (canonicalCenterRoot center)) geom [] none
    (canonicalCenterRoot center)

theorem facts_succ (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    facts mol ops (depth + 1) geom state ctx node =
      (descriptor? mol ops depth geom state ctx node).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (facts mol ops depth geom state ctx) := rfl

private theorem descriptor_congr (mol : RawMolecule) (ops : Operations) (first second : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (agree : ∀ child ∈ mol.canonicalChildren node, ∀ g s x,
      facts mol ops first g s x child = facts mol ops second g s x child) :
    descriptor? mol ops first geom state ctx node = descriptor? mol ops second geom state ctx node := by
  have under : ∀ g, underWith mol ops g state node (facts mol ops first) =
      underWith mol ops g state node (facts mol ops second) := by
    intro g
    funext mark
    unfold underWith
    exact flatMap_congr_mem _ _ _ fun child member =>
      agree child (mem_tiedChildren_actual mol ops state node child member) g state (some mark)
  change caseFromMirror? (rawStep? mol ops geom state ctx node
      (underWith mol ops geom state node (facts mol ops first)))
      (rawStep? mol ops (mirror geom) state ctx node
        (underWith mol ops (mirror geom) state node (facts mol ops first))) = _
  rw [under geom, under (mirror geom)]
  rfl

theorem facts_forcedLeaf (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) (leaf : node.forcedLeaf = true) :
    facts mol ops depth geom state ctx node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
      have absent := LocalizedChemicalRingOrientationInduction.descriptorWith_none_of_frame
        mol ops rawStep? (stepNoFrame mol ops) depth geom state ctx node
        (frameAtoms?_forcedLeaf mol node leaf)
      change descriptor? mol ops depth geom state ctx node = none at absent
      rw [facts_succ, absent, canonicalChildren_forcedLeaf mol node leaf]
      rfl

/-- Adequate structural depth stabilizes without any successful-output premise. -/
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
        rw [facts_succ, facts_succ, descriptor_congr mol ops depth (depth + 1) geom state ctx node children,
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
  unfold assignCenter?
  apply descriptor_congr
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

end TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.rawStep?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.rawStep_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.rawStep_preserves_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.rawStep_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.rawStep_added_some_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.consensus_none_of_refused_eligible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.stepMap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.stepCongr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.stepFlip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.stepNoFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.facts
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.descriptor?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.assignCenter?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.facts_succ
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.facts_forcedLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.facts_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.facts_stable_add
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback.assignCenter?_stable
