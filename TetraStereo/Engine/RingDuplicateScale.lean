import TetraStereo.Engine.RingMassDifference

/-! Strictly increasing duplicate relabellings commute with key assembly. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingDuplicateScale
open OneCenter RingRetainedChemicalTrace
open private shallow deep byDescending makeColumn mergeLayers rulePrefix from
  TetraStereo.Engine.RingRetainedChemicalTrace

/-- Apply a rank relabelling only to the duplicate coordinate. -/
def observation (f : Nat → Nat) (o : Observation) : Observation :=
  ⟨o.atomic, f o.duplicate, o.mass⟩

def scalar (f : Nat → Nat) : Stage → Nat → Nat
  | .duplicate => f
  | _ => id

def column (f : Nat → Nat) (s : Stage) (c : Column) : Column :=
  ⟨c.word.map (List.map (scalar f s)), c.levels.map (List.map (List.map (scalar f s)))⟩

def key (f : Nat → Nat) (k : Key) : Key :=
  ⟨observation f k.root,column f .atomic k.atomic,
    column f .duplicate k.duplicate,column f .mass k.mass⟩

private theorem scalar_compare {f : Nat → Nat} (hf : StrictMono f) (s : Stage) (a b : Nat) :
    compare (scalar f s a) (scalar f s b) = compare a b := by
  cases s <;> try rfl
  change compare (f a) (f b) = compare a b
  cases h : compare a b with
  | lt => exact compare_lt_iff_lt.mpr (hf (compare_lt_iff_lt.mp h))
  | eq => exact Std.compare_eq_eq_iff_eq.mpr (congrArg f (Std.compare_eq_eq_iff_eq.mp h))
  | gt => exact compare_gt_iff_gt.mpr (hf (compare_gt_iff_gt.mp h))

/-- Lift exact three-way comparison preservation through arbitrary list boundaries. -/
theorem list_compare {α β : Type} [Ord α] [Ord β] (f : α → β)
    (h : ∀ a b, compare (f a) (f b) = compare a b) (xs ys : List α) :
    compare (xs.map f) (ys.map f) = compare xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih => cases ys with
    | nil => rfl
    | cons y ys => simp only [List.map_cons,List.compare_cons_cons,h,ih]

private theorem root_stage (f : Nat → Nat) (s : Stage) (k : Key) :
    (key f k).root.atStage s = scalar f s (k.root.atStage s) := by cases s <;> rfl

private theorem column_stage (f : Nat → Nat) (s : Stage) (k : Key) :
    (key f k).column s = column f s (k.column s) := by cases s <;> rfl

private theorem priorities {α : Type} [Ord α] (v w : Stage → Key → α)
    (h : ∀ s a b, compare (w s a) (w s b) = compare (v s a) (v s b))
    (ss : List Stage) (a b : Key) :
    compare (ss.map (w · a)) (ss.map (w · b)) =
      compare (ss.map (v · a)) (ss.map (v · b)) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons,List.compare_cons_cons,h,ih]

private theorem shallow_compare {f} (hf : StrictMono f) (s : Stage) (a b : Key) :
    compare (shallow s (key f a)) (shallow s (key f b)) = compare (shallow s a) (shallow s b) := by
  unfold shallow
  apply priorities (fun t k => k.root.atStage t) (fun t k => (key f k).root.atStage t)
  intro t a b
  simp only [root_stage]
  exact scalar_compare hf t _ _

private theorem deep_compare {f} (hf : StrictMono f) (s : Stage) (a b : Key) :
    compare (deep s (key f a)) (deep s (key f b)) = compare (deep s a) (deep s b) := by
  unfold deep
  apply priorities (fun t k => (k.column t).word) (fun t k => ((key f k).column t).word)
  intro t a b
  simp only [column_stage,column]
  exact list_compare _ (list_compare _ (scalar_compare hf t)) _ _

private theorem sorted_map {α : Type} [LinearOrder α] [Ord α] (lt : ∀ x y : α, compare x y = .lt ↔ x < y)
    (f : Nat → Nat) (v : Key → α) (w : Key → α)
    (h : ∀ a b, compare (w (key f a)) (w (key f b)) = compare (v a) (v b))
    (cs : List Key) :
    byDescending w (cs.map (key f)) = (byDescending v cs).map (key f) := by
  symm
  apply List.map_mergeSort
  intro a _ b _
  change decide (v b ≤ v a) = decide (w (key f b) ≤ w (key f a))
  congr 1
  rw [← not_lt, ← not_lt]
  rw [← lt, ← lt,h]

private theorem natlist_lt (x y : List Nat) : compare x y = .lt ↔ x < y :=
  DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => Std.compare_eq_eq_iff_eq) x y

private theorem wordlist_lt (x y : List Word) : compare x y = .lt ↔ x < y :=
  DeclarativeCIP.compareLex_eq_lt_iff_of compare
    (DeclarativeCIP.compareLex_eq_lt_iff_of compare natlist_lt
      (fun _ _ => Std.compare_eq_eq_iff_eq))
    (fun _ _ => Std.compare_eq_eq_iff_eq) x y

private theorem merge_map {α β : Type} (g : α → β) (xs ys : List (List α)) :
    (mergeLayers xs ys).map (List.map g) =
      mergeLayers (xs.map (List.map g)) (ys.map (List.map g)) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys with
    | nil => rfl
    | cons y ys => simp only [mergeLayers,List.map_cons,List.map_append,ih]

/-- Both shallow and deep sorting are recomputed with the relabelled keys. -/
theorem assemble_natural {f : Nat → Nat} (hf : StrictMono f)
    (o : Observation) (cs : List Key) :
    assemble (observation f o) (cs.map (key f)) = key f (assemble o cs) := by
  have col (s : Stage) : makeColumn (observation f o) (cs.map (key f)) s =
      column f s (makeColumn o cs s) := by
    have sh := sorted_map natlist_lt f (shallow s) (shallow s) (shallow_compare hf s) cs
    have de := sorted_map wordlist_lt f (deep s) (deep s) (deep_compare hf s) cs
    have forest (ks : List Key) :
        (ks.map (key f)).foldr (fun k acc => mergeLayers (k.column s).levels acc) [] =
          (ks.foldr (fun k acc => mergeLayers (k.column s).levels acc) []).map
            (List.map (List.map (scalar f s))) := by
      induction ks with
      | nil => rfl
      | cons k ks ih =>
        simp only [List.map_cons,List.foldr_cons,column_stage,column,ih]
        exact (merge_map (List.map (scalar f s)) _ _).symm
    simp only [makeColumn,sh,de,List.map_map,forest,column]
    cases s <;> simp [key,observation,Observation.atStage,scalar,List.map_flatten,List.map_map]
  change Key.mk _ _ _ _ = Key.mk _ _ _ _
  exact congrArg₂ (fun a p => Key.mk (observation f o) a p.1 p.2)
    (col .atomic) (congrArg₂ Prod.mk (col .duplicate) (col .mass))

/-- Relabelling preserves all three outcomes, including constitutional ties. -/
theorem compare_keys {f : Nat → Nat} (hf : StrictMono f) (a b : Key) :
    compareKeys (key f a) (key f b) = compareKeys a b := by
  have dup := list_compare _ (list_compare _ (scalar_compare hf .duplicate))
    a.duplicate.word b.duplicate.word
  simpa [compareKeys,keyTrace,key,column,scalar] using
    congrArg (fun r => cipTraceOutcome
      [CIPRuleDecision.mk .atomicNumber (compare a.atomic.word b.atomic.word),
       CIPRuleDecision.mk .duplicateAtom r,
       CIPRuleDecision.mk .isotopeMass (compare a.mass.word b.mass.word)]) dup


/-- Independent increasing normalizations can identify two pairs of keys.
The original comparisons then agree, including the equality outcome. -/
theorem compare_normalized {f g : Nat → Nat} (hf : StrictMono f) (hg : StrictMono g)
    (a b x y : Key) (ha : key f a = key g x) (hb : key f b = key g y) :
    compareKeys a b = compareKeys x y := by
  rw [← compare_keys hf a b,ha,hb,compare_keys hg]

/-- Generic recursive fold, with an observation at each node and explicit children. -/
def build {α : Type} (read : α → Option Observation) (children : α → List α) :
    Nat → α → Option Key
  | 0,_ => none
  | n+1,q => do
    let o ← read q
    let ks ← (children q).mapM (build read children n)
    return assemble o ks

/-- Naturality holds at every fuel depth, retaining failed reads as well. -/
theorem build_natural {α : Type} {f : Nat → Nat} (hf : StrictMono f)
    (read : α → Option Observation) (children : α → List α) (n : Nat) (q : α) :
    build (fun a => (read a).map (observation f)) children n q =
      (build read children n q).map (key f) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have ihfun := funext ih
    simp only [build]
    rw [ihfun]
    cases hr : read q with
    | none => rfl
    | some o =>
      have maps (xs : List α) :
          xs.mapM (fun a => (build read children n a).map (key f)) =
            (xs.mapM (build read children n)).map (List.map (key f)) := by
        induction xs with
        | nil => rfl
        | cons a xs ih =>
          simp only [List.mapM_cons,ih]
          cases build read children n a <;> cases xs.mapM (build read children n) <;> rfl
      rw [maps]
      cases hs : (children q).mapM (build read children n) <;>
        simp [assemble_natural hf]

end TetraStereo.Engine.RingDuplicateScale

assert_kernel_only TetraStereo.Engine.RingDuplicateScale.assemble_natural
assert_kernel_only TetraStereo.Engine.RingDuplicateScale.compare_keys
assert_kernel_only TetraStereo.Engine.RingDuplicateScale.compare_normalized
assert_kernel_only TetraStereo.Engine.RingDuplicateScale.build_natural
