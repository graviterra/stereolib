import TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable
import TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingPartitionTable

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedGenericMarkedRecalculation (strict)

/-- Store the thunks in a concrete list. A partially applied recursive lookup function
would instead be specialized into rebuilding the thunk at each query. -/
private structure Table (α β : Type) where
  rows : List (α × Thunk β)
  miss : α → β

@[noinline] private def makeTable {α β : Type} (f : α → β) (keys : List α) : Table α β :=
  ⟨keys.map (fun k => (k, ⟨fun _ => f k⟩)), f⟩

private def lookup {α β : Type} [DecidableEq α] (tab : Table α β) (key : α) : β :=
  match tab.rows.lookup key with
  | some cell => cell.get
  | none => tab.miss key

private theorem lookup_make {α β : Type} [DecidableEq α] (f : α → β) (keys : List α) (key : α) :
    lookup (makeTable f keys) key = f key := by
  induction keys with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : key = a
    · subst key
      simp [lookup, makeTable, Thunk.get]
    · have unequal : (key == a) = false := by
        cases e : key == a with
        | false => rfl
        | true => exact False.elim (h (eq_of_beq e))
      simpa [lookup, makeTable, List.lookup, unequal] using ih

abbrev Partition := List Nat × List (Option Ordering) × Nat

variable (input : CertifiedLocalizedCIPInput)
  (reader : input.LocalizedRerootChildReader (retainedCarrierFuel input)) (mol : RawMolecule)

open LocalizedMarkedRetainedOrdinaryRanking (sortBy? adjacentBy)
open LocalizedMarkedRetainedOperations (positions?)
open LocalizedMarkedRetainedPromotedOperations (adjacentPromotionCount?)
open LocalizedMarkedRetainedStateReader (rawStateView)
open LocalizedGenericMarkedRecalculation (frameAtoms?)

/-- Share each of the four ordinary keys and each demanded joint key through sorting,
promotion counting, and adjacent comparisons, also for nonempty auxiliary states. -/
private def slotPartition (st : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (refs : List input.Atom) (W D : Nat) : Option Partition := do
  let target ← LocalizedMarkedCarrierLookup.lookup? input node
  let atoms ← frameAtoms? mol node
  let frame ← LocalizedChemicalRingCachedOperations.frame input reader target
  let view := rawStateView input st target
  let ordinary := makeTable (fun i => LocalizedChemicalRingCachedOperations.compound input reader target view
    (localizedOccurrenceRerootEvaluationFuel (retainedCarrierFuel input)) (frame.cursorAt i)) (List.finRange 4)
  let joint := makeTable (fun i => LocalizedChemicalRingJointCachedSparse.build? input reader target view
    refs W D (2 * (retainedCarrierFuel input + 1)) (frame.cursorAt i)) (List.finRange 4)
  let prior := fun a b => (do
    let l ← lookup ordinary a
    let r ← lookup ordinary b
    some (localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 l r))).map
        ConstitutionalDescriptorHierarchyComparison.ordering
  let before := fun a b => (prior a b).bind fun ord =>
    if ord = .eq then do
      let l ← lookup joint a
      let r ← lookup joint b
      some (LocalizedChemicalRingJointMarkerSparse.compareSparse input l r)
    else some ord
  let sorted ← sortBy? before (List.finRange 4)
  let count ← adjacentPromotionCount? prior before sorted
  let positions ← positions? input atoms frame sorted
  pure (positions,adjacentBy before sorted,count)

private theorem slotPartition_eq (st : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (refs : List input.Atom) (W D : Nat) :
    slotPartition input reader mol st node refs W D =
      LocalizedChemicalRingJointCachedExecutable.partition? input reader mol st node refs W D := by
  unfold slotPartition LocalizedChemicalRingJointCachedExecutable.partition?
  simp only [lookup_make]
  rfl

private def partition (st : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (ctx : List Nat) : Option Partition := do
  let refs ← LocalizedChemicalRingJointExecutable.references? input ctx
  slotPartition input reader mol st node refs
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))

private abbrev Cache := Table RawMolecule.CanonicalBranchNode (Table (List Nat) (Option Partition))

@[noinline] private def withCache (cache : Cache) : MultiOperations :=
  let run := fun (st : OccurrenceAuxState) node ctx =>
    if st = [] then lookup (lookup cache node) ctx else partition input reader mol st node ctx
  { ordinary := LocalizedChemicalRingCachedOperations.ordinary input reader mol
    contextOrder := fun st node ctx => (run st node ctx).map fun row => (row.1,row.2.1)
    markedJoint := fun st node ctx _ => (run st node ctx).map fun row =>
      { positions := row.1, unique := strict row.2.1, pseudoComparisons := row.2.2 } }

/-- Cache only the empty auxiliary state. Context and occurrence identity, including its full
path, are part of the key. The two consumers share the same full partition, including ties. -/
def operations (nodes : List RawMolecule.CanonicalBranchNode) (contexts : List (List Nat)) : MultiOperations :=
  withCache input reader mol (makeTable (fun node => makeTable (partition input reader mol [] node) contexts) nodes)

private theorem partition_empty (st : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (ctx : List Nat) :
    (if st = [] then partition input reader mol [] node ctx else partition input reader mol st node ctx) =
      partition input reader mol st node ctx := by
  split <;> simp_all

theorem operations_eq (nodes : List RawMolecule.CanonicalBranchNode) (contexts : List (List Nat)) :
    operations input reader mol nodes contexts = LocalizedChemicalRingJointCachedExecutable.operations input reader mol := by
  simp only [operations, withCache, lookup_make, partition_empty]
  unfold LocalizedChemicalRingJointCachedExecutable.operations
  congr 1
  · funext st node ctx
    unfold partition LocalizedChemicalRingJointCachedExecutable.contextOrder?
    simp only [slotPartition_eq]
    cases LocalizedChemicalRingJointExecutable.references? input ctx with
    | none => rfl
    | some refs =>
      dsimp only [Bind.bind, Option.bind]
      cases LocalizedChemicalRingJointCachedExecutable.partition? input reader mol st node refs
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) <;> rfl
  · funext st node ctx mark
    unfold partition LocalizedChemicalRingJointCachedExecutable.markedJoint?
    simp only [slotPartition_eq]
    cases LocalizedChemicalRingJointExecutable.references? input ctx with
    | none => rfl
    | some refs =>
      dsimp only [Bind.bind, Option.bind]
      cases LocalizedChemicalRingJointCachedExecutable.partition? input reader mol st node refs
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) <;> rfl

open LocalizedChemicalRingPreparedContextRecursion
open LocalizedGenericMarkedRecalculation (Geometry mirror caseFromMirror? factOf)

private structure Sides (α : Type) where
  front : α
  back : α

private def side {α : Type} (s : Sides α) (b : Bool) := if b then s.back else s.front

private def view (g : Geometry) (b : Bool) := if b then mirror g else g

private theorem other_view (g : Geometry) (b : Bool) : view g (!b) = mirror (view g b) := by
  cases b <;> simp [view, LocalizedChemicalRingOrientationInduction.mirror_mirror]

private abbrev Facts := Sides (Table MarkContext OccurrenceAuxState)

private def gathered (children : List Facts) (b : Bool) (ctx : MarkContext) : OccurrenceAuxState :=
  children.flatMap fun child => lookup (side child b) ctx

private def tabulate {α : Type} (contexts : List MarkContext) (f : Bool → MarkContext → α) :
    Sides (Table MarkContext α) := ⟨makeTable (f false) contexts, makeTable (f true) contexts⟩

private theorem tabulate_eq {α : Type} (cs : List MarkContext) (f : Bool → MarkContext → α)
    (b : Bool) (ctx : MarkContext) : lookup (side (tabulate cs f) b) ctx = f b ctx := by
  cases b <;> simp [tabulate,side,lookup_make]

private def rawSides (step : PreparedStep) (mol : RawMolecule) (g : Geometry)
    (st : OccurrenceAuxState) (cs : List MarkContext) (n : Node) (children : List Facts) :=
  tabulate cs fun b ctx => step mol (view g b) st ctx n (gathered children b)

private def observed (step : PreparedStep) (mol : RawMolecule) (g : Geometry)
    (st : OccurrenceAuxState) (cs : List MarkContext) (n : Node) (children : List Facts) :=
  let raw := rawSides step mol g st cs n children
  fun b ctx => caseFromMirror? (lookup (side raw b) ctx) (lookup (side raw (!b)) ctx)

private def facts (step : PreparedStep) (mol : RawMolecule) (g : Geometry)
    (st : OccurrenceAuxState) (cs : List MarkContext) : Nat → Node → Facts
  | 0, _ => tabulate cs fun _ _ => []
  | depth+1, n =>
    let children := (mol.canonicalChildren n).map (facts step mol g st cs depth)
    let readings := observed step mol g st cs n children
    tabulate cs fun b ctx => (readings b ctx).toList.map (factOf n) ++ gathered children b ctx

private theorem gather_eq (step : PreparedStep) (mol : RawMolecule) (g : Geometry)
    (st : OccurrenceAuxState) (cs : List MarkContext) (depth : Nat)
    (correct : ∀ n b ctx, lookup (side (facts step mol g st cs depth n) b) ctx =
      factsOfStep step mol depth (view g b) st ctx n) (n : Node) (b : Bool) :
    gathered ((mol.canonicalChildren n).map (facts step mol g st cs depth)) b =
      childrenUnder mol (factsOfStep step mol depth) (view g b) st n := by
  funext ctx
  simp [gathered, List.flatMap_map, correct, childrenUnder]

private theorem facts_correct (step : PreparedStep) (mol : RawMolecule) (g : Geometry)
    (st : OccurrenceAuxState) (cs : List MarkContext) (depth : Nat) :
    ∀ n b ctx, lookup (side (facts step mol g st cs depth n) b) ctx =
      factsOfStep step mol depth (view g b) st ctx n := by
  induction depth with
  | zero => intro n b ctx; simp [facts, tabulate_eq, factsOfStep]
  | succ depth ih =>
    intro n b ctx
    simp only [facts, tabulate_eq, observed, rawSides, factsOfStep_succ, descriptorOfStep,
      descriptorWithPrepared, gather_eq step mol g st cs depth ih, other_view]
    rfl

/-- Memoize actual descendant facts on each geometry and at every listed ordered context.
An unlisted context is still regenerated. The incoming state stays fixed throughout this tree. -/
def descriptor (step : PreparedStep) (mol : RawMolecule) (g : Geometry)
    (st : OccurrenceAuxState) (cs : List MarkContext) (depth : Nat) (ctx : MarkContext) (n : Node) :=
  let children := (mol.canonicalChildren n).map (facts step mol g st cs depth)
  observed step mol g st cs n children false ctx

theorem descriptor_eq (step : PreparedStep) (mol : RawMolecule) (g : Geometry)
    (st : OccurrenceAuxState) (cs : List MarkContext) (depth : Nat) (ctx : MarkContext) (n : Node) :
    descriptor step mol g st cs depth ctx n = descriptorOfStep step mol depth g st ctx n := by
  simp only [descriptor, observed, rawSides, tabulate_eq,
    gather_eq step mol g st cs depth (facts_correct step mol g st cs depth),
    descriptorOfStep, descriptorWithPrepared]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingPartitionTable

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPartitionTable.operations_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPartitionTable.descriptor_eq
