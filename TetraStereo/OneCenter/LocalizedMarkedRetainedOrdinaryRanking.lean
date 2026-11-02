import TetraStereo.OneCenter.LocalizedRetainedContextGeneratedDescriptor
import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Ordinary Rules-1–5 ranking of a raw auxiliary state at a retained carrier occurrence

The actual retained evaluator (`ruleMajorDescriptorExec?`, `compareRuleMajorOccurrenceExecAt?`)
is parameterized by a dependency view. This module runs it with the view of a raw auxiliary
state (`rawStateView`) at any real detected carrier occurrence of a simple-bonded certified
input, rings included, and connects the result to the independent retained specification of the
raw-state descriptor map.

* `RetainedExecutionFrame` compiles the four actual ligand arms at such an occurrence for any
  tetrahedral molecular reader: executable frame, stage families, successful compound builds and
  a common finite window. Its existence is derived; nothing about a successful comparison or
  sort is assumed.
* `executionData` turns it into the generic `ContextDescriptorExecutionData`, so the actual
  executable descriptor returns a letter exactly when the independent retained judgment on the
  actual stage graphs holds at the actual cursor coordinates.
* `ordinaryPartition?` is the executable tie-tolerant four-ligand partition for the marked
  interface: positions sorted by the actual through-Rule-5 callback, with adjacent decisions.
  For the raw-state view it succeeds and equals the stable insertion order of the independent
  retained complete ligand keys; adjacent decisions are `gt` or `eq`, and the partition is strict
  exactly when those keys are pairwise distinct.

This stays on the certified carrier. Mapping a raw marked node to its carrier occurrence and
aligning raw frame positions with the certified frame are separate obligations.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree Rule4aTableBridge
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedMolecularRule5

/-! ## A total-order sort with an optional comparator -/

section KeySort

variable {α : Type}

/-- Fail-closed insertion: `none` on a missing decision, otherwise the stable insertion used by
the raw cursor sorter. -/
def insertBy? (before : α → α → Option Ordering) (candidate : α) :
    List α → Option (List α)
  | [] => some [candidate]
  | head :: tail =>
      match before candidate head with
      | none => none
      | some Ordering.gt | some Ordering.eq => some (candidate :: head :: tail)
      | some Ordering.lt => (insertBy? before candidate tail).map fun sorted => head :: sorted

def sortBy? (before : α → α → Option Ordering) : List α → Option (List α)
  | [] => some []
  | candidate :: rest => do
      let sorted ← sortBy? before rest
      insertBy? before candidate sorted

/-- Decisions between consecutive entries. -/
def adjacentBy (before : α → α → Option Ordering) : List α → List (Option Ordering)
  | first :: second :: rest => before first second :: adjacentBy before (second :: rest)
  | _ => []

/- The key order is a linear order; the comparator is any lawful `Ordering`-valued comparison
on it (the retained keys use the `Lex` instance's `compare`, not the linear order's). -/
variable {K : Type} [LinearOrder K] (cmp : K → K → Ordering)
  (lt_iff : ∀ a b, cmp a b = Ordering.lt ↔ a < b)
  (eq_iff : ∀ a b, cmp a b = Ordering.eq ↔ a = b)
  (key : α → K)

/-- Descending stable order of a key. -/
abbrev keyOrder (entries : List α) : List α :=
  entries.insertionSort fun a b => key b ≤ key a

include lt_iff eq_iff in
theorem cmp_gt_iff (a b : K) : cmp a b = Ordering.gt ↔ b < a := by
  constructor
  · intro gt
    rcases lt_trichotomy a b with lt | eq | gt'
    · have observed := (lt_iff a b).mpr lt
      rw [gt] at observed
      cases observed
    · have observed := (eq_iff a b).mpr eq
      rw [gt] at observed
      cases observed
    · exact gt'
  · intro gt'
    cases observed : cmp a b with
    | lt => exact absurd ((lt_iff a b).mp observed) (lt_asymm gt')
    | eq => exact absurd ((eq_iff a b).mp observed) (ne_of_gt gt')
    | gt => rfl

include lt_iff in
theorem insertBy?_key (candidate : α) (entries : List α) :
    insertBy? (fun a b => some (cmp (key a) (key b))) candidate entries =
      some (entries.orderedInsert (fun a b => key b ≤ key a) candidate) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      by_cases order : key head ≤ key candidate
      · have notLt : cmp (key candidate) (key head) ≠ .lt := by
          intro contrary
          exact not_lt_of_ge order ((lt_iff _ _).mp contrary)
        rw [List.orderedInsert_cons_of_le (fun a b => key b ≤ key a) tail order]
        cases compared : cmp (key candidate) (key head) with
        | lt => exact absurd compared notLt
        | eq => simp [insertBy?, compared]
        | gt => simp [insertBy?, compared]
      · have lt : cmp (key candidate) (key head) = .lt :=
          (lt_iff _ _).mpr (lt_of_not_ge order)
        rw [List.orderedInsert_of_not_le (fun a b => key b ≤ key a) tail order]
        simp [insertBy?, lt, ih]

include lt_iff in
theorem sortBy?_key (entries : List α) :
    sortBy? (fun a b => some (cmp (key a) (key b))) entries = some (keyOrder key entries) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      simp only [sortBy?, ih, keyOrder, List.insertionSort_cons, Option.bind_eq_bind,
        Option.bind_some]
      exact insertBy?_key cmp lt_iff key head _

include lt_iff in
/-- A comparator that is everywhere the key comparison sorts successfully into the key order. -/
theorem sortBy?_eq_keyOrder (before : α → α → Option Ordering) (entries : List α)
    (corresponds : ∀ a b, before a b = some (cmp (key a) (key b))) :
    sortBy? before entries = some (keyOrder key entries) := by
  have beforeEq : before = fun a b => some (cmp (key a) (key b)) :=
    funext fun a => funext fun b => corresponds a b
  rw [beforeEq]
  exact sortBy?_key cmp lt_iff key entries

instance keyOrder_total : Std.Total fun a b : α => key b ≤ key a :=
  ⟨fun a b => le_total (key b) (key a)⟩

instance keyOrder_isTrans : IsTrans α fun a b => key b ≤ key a :=
  ⟨fun _ _ _ first second => le_trans second first⟩

instance keyOrder_lt_isTrans : IsTrans α fun a b => key b < key a :=
  ⟨fun _ _ _ first second => lt_trans second first⟩

theorem keyOrder_perm (entries : List α) : (keyOrder key entries).Perm entries :=
  List.perm_insertionSort _ entries

theorem keyOrder_pairwise (entries : List α) :
    (keyOrder key entries).Pairwise fun a b => key b ≤ key a :=
  List.pairwise_insertionSort _ entries

include lt_iff eq_iff in
/-- On a descending list every adjacent key decision is `gt` or `eq`. -/
theorem adjacentBy_key_consistent :
    ∀ entries : List α, entries.Pairwise (fun a b => key b ≤ key a) →
      ∀ decision ∈ adjacentBy (fun a b => some (cmp (key a) (key b))) entries,
        decision = some Ordering.gt ∨ decision = some Ordering.eq
  | [], _, _, member => by simp [adjacentBy] at member
  | [_], _, _, member => by simp [adjacentBy] at member
  | first :: second :: rest, sorted, decision, member => by
      simp only [adjacentBy, List.mem_cons] at member
      rcases member with head | tail
      · subst head
        have order : key second ≤ key first :=
          (List.pairwise_cons.mp sorted).1 second List.mem_cons_self
        rcases lt_or_eq_of_le order with lt | eq
        · exact Or.inl (congrArg some ((cmp_gt_iff cmp lt_iff eq_iff _ _).mpr lt))
        · exact Or.inr (congrArg some ((eq_iff _ _).mpr eq.symm))
      · exact adjacentBy_key_consistent (second :: rest) (List.pairwise_cons.mp sorted).2
          decision tail

include lt_iff eq_iff in
/-- Every adjacent decision is `gt` exactly when consecutive keys strictly decrease. -/
theorem adjacentBy_key_all_gt_iff :
    ∀ entries : List α,
      (∀ decision ∈ adjacentBy (fun a b => some (cmp (key a) (key b))) entries,
        decision = some Ordering.gt) ↔
      entries.IsChain fun a b => key b < key a
  | [] => by simp [adjacentBy]
  | [_] => by simp [adjacentBy]
  | first :: second :: rest => by
      rw [List.isChain_cons_cons]
      simp only [adjacentBy, List.mem_cons, forall_eq_or_imp]
      rw [adjacentBy_key_all_gt_iff (second :: rest)]
      constructor
      · rintro ⟨head, tail⟩
        exact ⟨(cmp_gt_iff cmp lt_iff eq_iff _ _).mp (Option.some.inj head), tail⟩
      · rintro ⟨head, tail⟩
        exact ⟨congrArg some ((cmp_gt_iff cmp lt_iff eq_iff _ _).mpr head), tail⟩

/-- A descending key order whose consecutive keys strictly decrease is a strictly descending
chain of pairwise distinct keys; conversely distinct keys force strict consecutive decrease. -/
theorem keyOrder_chain_iff_injective (entries : List α) (nodup : entries.Nodup) :
    (keyOrder key entries).IsChain (fun a b => key b < key a) ↔
      ∀ a ∈ entries, ∀ b ∈ entries, key a = key b → a = b := by
  have sorted := keyOrder_pairwise key entries
  have perm := keyOrder_perm key entries
  have orderNodup : (keyOrder key entries).Nodup := perm.nodup_iff.mpr nodup
  constructor
  · intro chain a ha b hb equal
    have strict : (keyOrder key entries).Pairwise fun a b => key b < key a :=
      List.isChain_iff_pairwise.mp chain
    by_contra different
    have ha' : a ∈ keyOrder key entries := perm.mem_iff.mpr ha
    have hb' : b ∈ keyOrder key entries := perm.mem_iff.mpr hb
    have either := (List.Pairwise.forall (fun _ _ h => h.symm)
      (strict.imp fun h => Or.inr h)) ha' hb' different
    rw [equal] at either
    exact either.elim (lt_irrefl _) (lt_irrefl _)
  · intro injective
    rw [List.isChain_iff_pairwise]
    refine (List.pairwise_and_iff.mpr ⟨sorted, ?_⟩).imp fun ⟨le, ne⟩ => lt_of_le_of_ne le ne
    have distinct : (keyOrder key entries).Pairwise (· ≠ ·) := orderNodup
    exact distinct.imp_of_mem fun {a b} ha hb different equal =>
      different (injective b (perm.mem_iff.mp hb) a (perm.mem_iff.mp ha) equal).symm

end KeySort

/-! ## Compiled retained execution at a real detected carrier occurrence -/

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput}

/-- Four actual ligand arms of one carrier occurrence under the molecular reader of a descriptor
map: executable frame, actual stage families, successful compound builds and a common window.
`unit` is only needed for the specification side, so it is not a field. -/
structure RetainedExecutionFrame
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)) where
  center : input.TetrahedralCenter
  centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center
  frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input)
  frameComputed : input.localizedNoDoubleFourLigandFrameExec? target = some frame
  childAt : ∀ index, frame.cursorAt index ∈ input.executableLocalizedRerootChildren
    ({ occurrence := target, previous? := none })
  stages : ∀ index, input.RuleMajorContextStages (retainedCarrierFuel input)
    (input.localizedDependencyLabel target (input.molecularView descriptorMap target))
    (frame.cursorAt index)
  compounds : Fin 4 → input.LocalizedRerootCompoundRule45Key
  compoundBuilt : ∀ index,
    input.buildActualRuleMajorCompoundRule45KeyExec? target (input.molecularView descriptorMap target)
      (2 * (retainedCarrierFuel input + 1)) (frame.cursorAt index) = some (compounds index)
  W : Nat
  D : Nat
  widthBound : ∀ index, (stages index).widthBound ≤ W
  depthBound : ∀ index, (stages index).depthBound ≤ D

/-- **Every real detected carrier occurrence of a simple-bonded input compiles**, for any
descriptor map. The frame, stage families and compound builds are derived from the finite
single-bond graph; acyclicity is not used and no comparison outcome is assumed. -/
theorem exists_retainedExecutionFrame
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1) :
    Nonempty (RetainedExecutionFrame descriptorMap target) := by
  have centerMember : unit.1.atom ∈ input.tetrahedralCenterSet := by
    change unit.1.atom ∈ input.moleculeGraph.tetrahedralCenterSet
    exact (input.moleculeGraph.mem_tetrahedralCenterSet unit.1.atom).2
      ((input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card unit.1.atom).2 unit.2)
  let center : input.TetrahedralCenter := ⟨unit.1.atom, centerMember⟩
  obtain ⟨current, currentObserved⟩ :=
    input.localizedRerootCursor_current_exists
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor (retainedCarrierFuel input))
  have currentHead : target.1.node.history.head? = some current := by
    have headEq := input.declarativeLocalizedOccurrence_node_history_head_eq_current
      ((input.mem_localizedOccurrences_iff (retainedCarrierFuel input) target.1).mp target.2)
    rw [currentObserved] at headEq
    exact headEq
  have rootLast : target.1.node.history.getLast? = some target.1.root :=
    input.frameCarrierOccurrence_history_getLast_eq_root target
  have unitAtomCurrent := input.molecularFrameUnit_atom_eq_current target.1 currentHead rootLast
  have unitAtomEq : unit.1.atom = current := by
    calc
      unit.1.atom = (input.molecularFrameUnit target.1).atom :=
        (congrArg OccurrenceUnit.atom targetUnit).symm
      _ = current := unitAtomCurrent
  have targetCurrent : target.1.node.current? = some center.1 := by
    rw [currentObserved]
    exact congrArg some unitAtomEq.symm
  have centerReal : input.RealTetrahedralCenterNode target.1.node center := ⟨real, targetCurrent⟩
  have centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).2 centerReal
  have enough : input.certified.input.molecule.atomCount ≤ retainedCarrierFuel input :=
    Nat.le_succ _
  obtain ⟨frame, _alpha, frameComputed, _ligandAt⟩ :=
    input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      singleBonded enough target center centerReal
  have noDoubleFrameComputed : input.localizedNoDoubleFourLigandFrameExec? target = some frame := by
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target]
    exact frameComputed
  let targetCursor : input.LocalizedRerootCursor (retainedCarrierFuel input) := ⟨target, none⟩
  have childAt (index : Fin 4) : frame.cursorAt index ∈
      input.executableLocalizedRerootChildren targetCursor := by
    rw [← input.localizedOccurrenceFourLigandFrame_cursors_eq_executable target frame frameComputed]
    exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  let read := input.localizedDependencyLabel target (input.molecularView descriptorMap target)
  let stages : ∀ index : Fin 4, input.RuleMajorContextStages (retainedCarrierFuel input) read
      (frame.cursorAt index) := fun index => Classical.choice
    (input.exists_ruleMajorContextStages_at_actualChild (retainedCarrierFuel input) read
      targetCursor (frame.cursorAt index) (childAt index))
  have compoundsBuiltExists (index : Fin 4) : ∃ compound,
      input.buildActualRuleMajorCompoundRule45KeyExec? target (input.molecularView descriptorMap target)
        (2 * (retainedCarrierFuel input + 1)) (frame.cursorAt index) = some compound := by
    obtain ⟨compound, built⟩ := input.exists_buildActualRuleMajorCompoundRule45Key_at_twice
      target (input.molecularView descriptorMap target) (frame.cursorAt index)
      (LocalizedOccurrenceFourLigandFrame.cursorAt_valid input target frame
        (input.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed) index)
    rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact ⟨compound, built⟩
  let compounds : Fin 4 → input.LocalizedRerootCompoundRule45Key :=
    fun index => Classical.choose (compoundsBuiltExists index)
  have execBuilt (index : Fin 4) :
      input.buildActualRuleMajorCompoundRule45KeyExec? target (input.molecularView descriptorMap target)
        (2 * (retainedCarrierFuel input + 1)) (frame.cursorAt index) = some (compounds index) :=
    Classical.choose_spec (compoundsBuiltExists index)
  let W := Finset.univ.sup fun index : Fin 4 => (stages index).widthBound
  let D := Finset.univ.sup fun index : Fin 4 => (stages index).depthBound
  have widthBound (index : Fin 4) : (stages index).widthBound ≤ W :=
    Finset.le_sup (f := fun i : Fin 4 => (stages i).widthBound) (Finset.mem_univ index)
  have depthBound (index : Fin 4) : (stages index).depthBound ≤ D :=
    Finset.le_sup (f := fun i : Fin 4 => (stages i).depthBound) (Finset.mem_univ index)
  exact ⟨{
    center := center
    centerComputed := centerComputed
    frame := frame
    frameComputed := noDoubleFrameComputed
    childAt := childAt
    stages := stages
    compounds := compounds
    compoundBuilt := execBuilt
    W := W
    D := D
    widthBound := widthBound
    depthBound := depthBound }⟩

namespace RetainedExecutionFrame

variable {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)}
  (frames : RetainedExecutionFrame descriptorMap target)

/-- Actual Rule-4a stage graph of each compiled ligand. -/
def actualArmGraphs : Fin 4 → RootedDigraph input.Atom :=
  fun slot => ruleMajorTreeGraph (frames.stages slot).a.tree

/-- Independent retained complete Rule-5 keys of the actual stage graphs at the compiled
window, for the unit of the target. -/
def retainedKeys (unit : DetectedOccurrence input.moleculeGraph) : Fin 4 → CompleteLigandRule5Key :=
  retainedContextualFrameKeysAt input.moleculeGraph descriptorMap unit frames.actualArmGraphs
    frames.W frames.D

/-- Actual cursor coordinates of the compiled frame. -/
def coordinates : Fin 4 → Option CartesianPoint3 :=
  fun slot => input.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot)

/-- The actual comparison callback at this frame is the compound comparison of the built keys. -/
theorem callbackEq :
    (fun left right => input.compareRuleMajorOccurrenceExecAt? target
      (input.molecularView descriptorMap target) frames.frame left right) =
      compoundActualCompareAt input frames.compounds := by
  funext left right
  rw [CertifiedLocalizedCIPInput.compareRuleMajorOccurrenceExecAt?,
    localizedOccurrenceRerootEvaluationFuel, frames.compoundBuilt left, frames.compoundBuilt right]
  rfl

variable (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (singleBonded : input.moleculeGraph.SimpleBonded)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

include tetrahedralMap singleBonded targetUnit

/-- Through-Rule-5 order of the compiled compounds is the retained key order. -/
theorem fullOrdering (left right : Fin 4) :
    (input.compareLocalizedRerootCompoundThroughRule5
      (frames.compounds left) (frames.compounds right)).ordering =
      compare (frames.retainedKeys unit left) (frames.retainedKeys unit right) := by
  have agreement := retainedMolecularCompound_throughRule5 descriptorMap tetrahedralMap singleBonded
    ⟨target, none⟩ unit targetUnit (frames.frame.cursorAt left) (frames.frame.cursorAt right)
    (frames.childAt left) (frames.childAt right) (frames.stages left) (frames.stages right)
    (frames.widthBound left) (frames.depthBound left) (frames.widthBound right)
    (frames.depthBound right) (frames.compoundBuilt left) (frames.compoundBuilt right)
  simpa [retainedKeys, actualArmGraphs, retainedContextualFrameKeysAt] using agreement.1

/-- Prior order of the compiled compounds is the retained prior-key order. -/
theorem priorComparison (left right : Fin 4) :
    input.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds left).prior (frames.compounds right).prior =
      compare (ofLex (frames.retainedKeys unit left)).1 (ofLex (frames.retainedKeys unit right)).1 := by
  have agreement := retainedMolecularCompound_prior_compare descriptorMap tetrahedralMap
    singleBonded ⟨target, none⟩ unit targetUnit (frames.frame.cursorAt left)
    (frames.frame.cursorAt right) (frames.childAt left) (frames.childAt right)
    (frames.stages left) (frames.stages right) (frames.widthBound left) (frames.depthBound left)
    (frames.widthBound right) (frames.depthBound right) (frames.compoundBuilt left)
    (frames.compoundBuilt right)
  simpa [retainedKeys, actualArmGraphs, retainedContextualFrameKeysAt,
    retainedCompleteLigandRule5KeyAt_prior] using agreement

omit tetrahedralMap singleBonded targetUnit in
/-- Every compiled compound has a legal reading shape. -/
theorem readingShape (index : Fin 4) : input.RuleMajorReadingShape (frames.compounds index) := by
  have uniformBuilt : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage
        (input.localizedDependencyLabel target (input.molecularView descriptorMap target))
        (2 * (retainedCarrierFuel input + 1)) position)
      (frames.frame.cursorAt index) = some (frames.compounds index) := by
    rw [← input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact frames.compoundBuilt index
  exact input.contextStages_compound_rule5ReadingShape (frames.stages index) uniformBuilt

/-- Execution algebra of the actual evaluator at the compiled frame. -/
def executionData :
    input.ContextDescriptorExecutionData target (input.molecularView descriptorMap target) where
  center := frames.center
  centerComputed := frames.centerComputed
  frame := frames.frame
  frameComputed := frames.frameComputed
  compounds := frames.compounds
  keys := frames.retainedKeys unit
  callbackEq := frames.callbackEq
  fullOrdering := frames.fullOrdering tetrahedralMap singleBonded unit targetUnit
  priorComparison := frames.priorComparison tetrahedralMap singleBonded unit targetUnit
  shaped := frames.readingShape

/-- **The actual executable descriptor with this reader returns a letter exactly when the
independent retained judgment holds** on the actual stage graphs at the actual coordinates. -/
theorem exec_some_iff_retainedJudgment (descriptor : LocalizedAuxiliaryLabel) :
    input.ruleMajorDescriptorExec? target (input.molecularView descriptorMap target) =
        some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.moleculeGraph descriptorMap unit
        frames.actualArmGraphs frames.W frames.D frames.coordinates descriptor :=
  (frames.executionData tetrahedralMap singleBonded unit targetUnit).exec_some_iff_completeRootJudgment
    descriptor

theorem exec_none_iff_no_retainedJudgment :
    input.ruleMajorDescriptorExec? target (input.molecularView descriptorMap target) = none ↔
      ¬ ∃ descriptor, RetainedContextualDescriptorJudgmentAt input.moleculeGraph descriptorMap unit
        frames.actualArmGraphs frames.W frames.D frames.coordinates descriptor :=
  (frames.executionData tetrahedralMap singleBonded unit targetUnit).exec_none_iff_no_completeRootJudgment

end RetainedExecutionFrame

end

/-! ## The raw-state instantiation and the executable tie-tolerant partition -/

section RawState

variable (input : CertifiedLocalizedCIPInput)

/-- The actual pairwise ordinary decision at a frame, read by the raw state. -/
def rawStateBefore (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (left right : Fin 4) : Option Ordering :=
  (input.compareRuleMajorOccurrenceExecAt? target (rawStateView input state target) frame
    left right).map ConstitutionalDescriptorHierarchyComparison.ordering

/-- Executable tie-tolerant ordinary partition of a carrier occurrence under a raw state: frame
positions in descending actual order together with the adjacent decisions. Unlike the strict
tracked order of the retained evaluator, ties are reported rather than refused. -/
def ordinaryPartition? (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)) :
    Option (List (Fin 4) × List (Option Ordering)) := do
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  let sorted ← sortBy? (rawStateBefore input state target frame) (List.finRange 4)
  some (sorted, adjacentBy (rawStateBefore input state target frame) sorted)

/-- Chosen compilation of a real detected carrier occurrence under a raw state. -/
noncomputable def rawStateFrames (singleBonded : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1) :
    RetainedExecutionFrame (rawStateDescriptorMap input state) target :=
  Classical.choice (exists_retainedExecutionFrame (rawStateDescriptorMap input state) singleBonded
    target real unit targetUnit)

variable (singleBonded : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

include singleBonded real unit targetUnit

/-- Independent retained complete keys of the four compiled arms of the raw-state compilation. -/
noncomputable def rawStateKeys : Fin 4 → CompleteLigandRule5Key :=
  (rawStateFrames input singleBonded state target real unit targetUnit).retainedKeys unit

/-- **The actual retained evaluator run on a raw state's view returns a letter exactly when the
independent retained judgment of the raw-state descriptor map holds.** Rings allowed. -/
theorem rawState_exec_some_iff_retainedJudgment (descriptor : LocalizedAuxiliaryLabel) :
    input.ruleMajorDescriptorExec? target (rawStateView input state target) = some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.moleculeGraph (rawStateDescriptorMap input state)
        unit (rawStateFrames input singleBonded state target real unit targetUnit).actualArmGraphs
        (rawStateFrames input singleBonded state target real unit targetUnit).W
        (rawStateFrames input singleBonded state target real unit targetUnit).D
        (rawStateFrames input singleBonded state target real unit targetUnit).coordinates
        descriptor := by
  rw [rawStateView_eq_molecularView]
  exact (rawStateFrames input singleBonded state target real unit targetUnit).exec_some_iff_retainedJudgment
    (rawStateDescriptorMap_tetrahedral input state) singleBonded unit targetUnit descriptor

theorem rawState_exec_none_iff_no_retainedJudgment :
    input.ruleMajorDescriptorExec? target (rawStateView input state target) = none ↔
      ¬ ∃ descriptor, RetainedContextualDescriptorJudgmentAt input.moleculeGraph
        (rawStateDescriptorMap input state) unit
        (rawStateFrames input singleBonded state target real unit targetUnit).actualArmGraphs
        (rawStateFrames input singleBonded state target real unit targetUnit).W
        (rawStateFrames input singleBonded state target real unit targetUnit).D
        (rawStateFrames input singleBonded state target real unit targetUnit).coordinates
        descriptor := by
  rw [rawStateView_eq_molecularView]
  exact (rawStateFrames input singleBonded state target real unit targetUnit).exec_none_iff_no_retainedJudgment
    (rawStateDescriptorMap_tetrahedral input state) singleBonded unit targetUnit

/-- The actual pairwise decision of the raw-state view is the retained key comparison. -/
theorem rawStateBefore_eq_keys (left right : Fin 4) :
    rawStateBefore input state target
        (rawStateFrames input singleBonded state target real unit targetUnit).frame left right =
      some (compare (rawStateKeys input singleBonded state target real unit targetUnit left)
        (rawStateKeys input singleBonded state target real unit targetUnit right)) := by
  unfold rawStateBefore rawStateKeys
  rw [rawStateView_eq_molecularView]
  have callback := congrFun (congrFun
    (rawStateFrames input singleBonded state target real unit targetUnit).callbackEq left) right
  rw [callback]
  simp only [compoundActualCompareAt, Option.map_some, localizedOccurrenceRule45ComparisonRecord]
  rw [(rawStateFrames input singleBonded state target real unit targetUnit).fullOrdering
    (rawStateDescriptorMap_tetrahedral input state) singleBonded unit targetUnit left right]

/-- **The executable partition succeeds and is the stable descending order of the independent
retained keys**, with the adjacent decisions being those key comparisons. -/
theorem ordinaryPartition?_eq :
    ordinaryPartition? input state target =
      some (keyOrder (rawStateKeys input singleBonded state target real unit targetUnit)
          (List.finRange 4),
        adjacentBy (fun left right => some
            (compare (rawStateKeys input singleBonded state target real unit targetUnit left)
              (rawStateKeys input singleBonded state target real unit targetUnit right)))
          (keyOrder (rawStateKeys input singleBonded state target real unit targetUnit)
            (List.finRange 4))) := by
  have beforeEq : rawStateBefore input state target
      (rawStateFrames input singleBonded state target real unit targetUnit).frame =
      fun left right => some
        (compare (rawStateKeys input singleBonded state target real unit targetUnit left)
          (rawStateKeys input singleBonded state target real unit targetUnit right)) :=
    funext fun left => funext fun right =>
      rawStateBefore_eq_keys input singleBonded state target real unit targetUnit left right
  unfold ordinaryPartition?
  rw [(rawStateFrames input singleBonded state target real unit targetUnit).frameComputed]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [beforeEq, sortBy?_key compare completeLigandRule5Key_compare_lt_iff
    (rawStateKeys input singleBonded state target real unit targetUnit)]
  rfl

/-- The partition positions are a permutation of the four frame slots. -/
theorem ordinaryPartition?_perm :
    ∃ sorted adjacent, ordinaryPartition? input state target = some (sorted, adjacent) ∧
      sorted.Perm (List.finRange 4) :=
  ⟨_, _, ordinaryPartition?_eq input singleBonded state target real unit targetUnit,
    keyOrder_perm _ _⟩

/-- Every adjacent decision of the partition is `gt` or `eq`: no inverted or missing decision. -/
theorem ordinaryPartition?_consistent :
    ∃ sorted adjacent, ordinaryPartition? input state target = some (sorted, adjacent) ∧
      ∀ decision ∈ adjacent,
        decision = some Ordering.gt ∨ decision = some Ordering.eq :=
  ⟨_, _, ordinaryPartition?_eq input singleBonded state target real unit targetUnit,
    adjacentBy_key_consistent compare completeLigandRule5Key_compare_lt_iff
      completeLigandRule5Key_compare_eq_iff
      (rawStateKeys input singleBonded state target real unit targetUnit) _
      (keyOrder_pairwise _ _)⟩

/-- **The partition is strict exactly when the retained keys of the four arms are pairwise
distinct.** Strictness is then the ordinary fast path; a tie is an actual retained-key tie. -/
theorem ordinaryPartition?_strict_iff :
    ∃ sorted adjacent, ordinaryPartition? input state target = some (sorted, adjacent) ∧
      ((∀ decision ∈ adjacent, decision = some Ordering.gt) ↔
        Function.Injective (rawStateKeys input singleBonded state target real unit targetUnit)) := by
  refine ⟨_, _, ordinaryPartition?_eq input singleBonded state target real unit targetUnit, ?_⟩
  rw [adjacentBy_key_all_gt_iff compare completeLigandRule5Key_compare_lt_iff
      completeLigandRule5Key_compare_eq_iff
      (rawStateKeys input singleBonded state target real unit targetUnit)
      (keyOrder (rawStateKeys input singleBonded state target real unit targetUnit)
        (List.finRange 4)),
    keyOrder_chain_iff_injective (rawStateKeys input singleBonded state target real unit targetUnit)
      (List.finRange 4) (List.nodup_finRange 4)]
  constructor
  · intro injective a b equal
    exact injective a (List.mem_finRange a) b (List.mem_finRange b) equal
  · intro injective a _ b _ equal
    exact injective equal

end RawState

end TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.cmp_gt_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.sortBy?_eq_keyOrder
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.adjacentBy_key_consistent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.adjacentBy_key_all_gt_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.keyOrder_chain_iff_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.exists_retainedExecutionFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.RetainedExecutionFrame.callbackEq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.RetainedExecutionFrame.fullOrdering
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.RetainedExecutionFrame.priorComparison
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.RetainedExecutionFrame.executionData
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.RetainedExecutionFrame.exec_some_iff_retainedJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.RetainedExecutionFrame.exec_none_iff_no_retainedJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawState_exec_some_iff_retainedJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawState_exec_none_iff_no_retainedJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateBefore_eq_keys
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.ordinaryPartition?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.ordinaryPartition?_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.ordinaryPartition?_consistent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.ordinaryPartition?_strict_iff
