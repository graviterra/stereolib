import TetraStereo.Engine.RingRetainedChemicalCoverage

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedChemicalPreorder
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRetainedConstitution (Incident)
open RingRetainedChemicalTrace

abbrev Site (i : Input) := i.certified.LocalizedCIPOccurrence (i.certified.certified.input.molecule.atomCount+1)
abbrev Direction (i : Input) (f : Site i) :=
  {a : Site i // i.certified.LocalizedCarrierTreeAdjacent a.val f.val}

/-- Each direction of the original molecular frame occurs with its identity
and its proof of adjacency, including the old parent at a nested site. -/
def directions (i : Input) (f : Site i) : List (Direction i f) :=
  (i.certified.localizedRerootNeighborFrames (fuel := i.certified.certified.input.molecule.atomCount+1)
    f.val).attach.map fun x =>
    let member := (i.certified.mem_localizedRerootNeighborFrames_iff f.val x.val).mp x.property
    ⟨⟨x.val,member.1⟩, member.2⟩

theorem present {i : Input} {f : Site i} (a : Direction i f) : a ∈ directions i f := by
  have mem := (i.certified.mem_localizedRerootNeighborFrames_iff f.val a.val.val).mpr
    ⟨a.val.property,a.property⟩
  exact List.mem_map.mpr ⟨⟨_,mem⟩,List.mem_attach ..,rfl⟩

private theorem covered {i : Input} {f : Site i} (a : Direction i f) :
    (key? i ⟨a.val,some f⟩).isSome = true := by
  exact Option.isSome_iff_exists.mpr
    (RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) _
      ((i.certified.mem_localizedRerootNeighborFrames_iff f.val a.val.val).mpr
        ⟨a.val.property,a.property⟩))

def keyFor {i : Input} {f : Site i} (a : Direction i f) : Key :=
  (key? i ⟨a.val,some f⟩).get (covered a)

theorem read_key {i : Input} {f : Site i} (a : Direction i f) :
    key? i ⟨a.val,some f⟩ = some (keyFor a) := (Option.some_get _).symm

abbrev Table (i : Input) (f : Site i) := List (Direction i f × Key)

/-- Materialize one constitutional key per directed arm, shared across all
opponents. Opponent identity and presentation order do not enter its key. -/
def table (i : Input) (f : Site i) : Table i f :=
  (directions i f).map fun a => (a,keyFor a)

private theorem lookup_map {α β : Type} [BEq α] [LawfulBEq α] (values : List α) (k : α → β) {x : α}
    (hem : x ∈ values) : ((values.map fun a => (a,k a)).lookup x) = some (k x) := by
  induction values with
  | nil => contradiction
  | cons v vs ih =>
    by_cases eq : x = v
    · subst v; simp
    · have tail := (List.mem_cons.mp hem).resolve_left eq
      have different : (x == v) = false := Bool.eq_false_iff.mpr (fun h => eq (eq_of_beq h))
      simp [List.lookup,different,ih tail]

theorem lookup_direction {i : Input} {f : Site i} (a : Direction i f) :
    (table i f).lookup a = some (keyFor a) := lookup_map _ _ (present a)

def compareIn? {i : Input} {f : Site i} (t : Table i f) (a b : Direction i f) : Option Ordering := do
  return compareKeys (← t.lookup a) (← t.lookup b)

def orderWord (k : Key) : List Word := [k.atomic.word,k.duplicate.word,k.mass.word]

theorem compare_word (a b : Key) : compareKeys a b = compare (orderWord a) (orderWord b) := by
  simp only [compareKeys,keyTrace,cipTraceOutcome,orderWord,List.compare_cons_cons]
  cases compare a.atomic.word b.atomic.word <;>
    cases compare a.duplicate.word b.duplicate.word <;>
    cases compare a.mass.word b.mass.word <;> rfl

/-- All pairwise source outcomes, including every constitutional tie, can be
read back from this one finite table. A diagonal query also has value equality. -/
theorem table_order {i : Input} {f : Site i} (a b : Direction i f) :
    compareIn? (table i f) a b = some (compare (orderWord (keyFor a)) (orderWord (keyFor b))) := by
  simp [compareIn?,lookup_direction,compare_word]

theorem table_source {i : Input} {f : Site i} (a b : Direction i f)
    (inc : Incident i.certified f a.val b.val) :
    (compareAt? i f a.val b.val).map cipTraceOutcome = compareIn? (table i f) a b := by
  simp [compareAt?,inc,trace?,read_key a,read_key b,compareIn?,lookup_direction,compareKeys]

/-- The two orders cannot form a cycle. Ties are equality of the exact three
constitutional words and strict comparisons use the first unequal rule. -/
theorem table_tie {i : Input} {f : Site i} (a b : Direction i f) :
    compareIn? (table i f) a b = some .eq ↔ orderWord (keyFor a) = orderWord (keyFor b) := by
  simp [table_order]

theorem table_reverse {i : Input} {f : Site i} (a b : Direction i f) :
    compareIn? (table i f) a b = (compareIn? (table i f) b a).map Ordering.swap := by
  rw [table_order,table_order,Option.map_some]
  exact congrArg some (Std.OrientedCmp.eq_swap (cmp := compare))

/-- Nonstrict priority on one common molecular frame is a total preorder. -/
def AtLeast {i : Input} {f : Site i} (a b : Direction i f) : Prop :=
  (compareIn? (table i f) a b).any Ordering.isGE = true

theorem total_preorder {i : Input} {f : Site i} :
    (∀ a : Direction i f, AtLeast a a) ∧
    (∀ a b c : Direction i f, AtLeast a b → AtLeast b c → AtLeast a c) ∧
    (∀ a b : Direction i f, AtLeast a b ∨ AtLeast b a) := by
  simp only [AtLeast,table_order,Option.any_some]
  refine ⟨fun a => ?_,fun a b c ab bc => Std.TransCmp.isGE_trans ab bc,fun a b => ?_⟩
  · simp
  · rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := orderWord (keyFor a)) (b := orderWord (keyFor b))]
    cases compare (orderWord (keyFor b)) (orderWord (keyFor a)) <;> decide

/-- The representative is the least slot with this full molecular priority
word. It names a tie class and makes no ordering choice between its ligands. -/
def representative {i : Input} {f : Site i} (arms : Fin 4 → Direction i f) (a : Fin 4) : Fin 4 :=
  let word := fun s => orderWord (keyFor (arms s))
  (Finset.univ.filter (fun b => word a = word b)).min' ⟨a,by simp⟩

theorem class_iff {i : Input} {f : Site i} (arms : Fin 4 → Direction i f) (a b : Fin 4) :
    representative arms a = representative arms b ↔ compareIn? (table i f) (arms a) (arms b) = some .eq := by
  rw [table_tie]
  have same (x : Fin 4) : orderWord (keyFor (arms x)) =
      orderWord (keyFor (arms (representative arms x))) := by
    let group := Finset.univ.filter fun k => orderWord (keyFor (arms x)) = orderWord (keyFor (arms k))
    have h : representative arms x ∈ group := Finset.min'_mem _ _
    exact (Finset.mem_filter.mp h).2
  constructor
  · intro rr
    have h := same a
    rw [rr] at h
    exact h.trans (same b).symm
  · intro eqn
    unfold representative
    simp only [eqn]

/-- The sizes count the actual four slots in each distinct priority class.
Ascending order here only presents the multiplicities. -/
def blockSizes (classes : Fin 4 → Fin 4) : List Nat :=
  let labels := (List.finRange 4).map classes
  let sizes := (List.finRange 4).map fun a => (labels.filter (· == a)).length
  ([1,2,3,4] : List Nat).flatMap fun n => sizes.filter (· == n)

private theorem four_blocks (classes : Fin 4 → Fin 4) :
    blockSizes classes ∈ ([[1,1,1,1],[1,1,2],[2,2],[1,3],[4]] : List (List Nat)) := by
  have closed : ∀ a b c d : Fin 4, blockSizes ![a,b,c,d] ∈
      ([[1,1,1,1],[1,1,2],[2,2],[1,3],[4]] : List (List Nat)) := by decide +kernel
  have eta : classes = ![classes 0,classes 1,classes 2,classes 3] := by
    funext k; fin_cases k <;> rfl
  exact eta.symm ▸ closed (classes 0) (classes 1) (classes 2) (classes 3)

/-- These are the five exhaustive multiplicity shapes after the complete
constitutional comparison on the original retained frame. -/
theorem five_shapes {i : Input} {f : Site i} (arms : Fin 4 → Direction i f) :
    blockSizes (representative arms) ∈ ([[1,1,1,1],[1,1,2],[2,2],[1,3],[4]] : List (List Nat)) :=
  four_blocks _

end TetraStereo.Engine.RingRetainedChemicalPreorder

assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.present
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.lookup_direction
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.table_source
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.table_tie
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.table_reverse
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.total_preorder
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.class_iff
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.five_shapes
