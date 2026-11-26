import TetraStereo.Engine.RingFullPathRule5

/-! Run summaries retain only the emitted Boolean word. Rank and sphere boundaries
are deliberately absent. Counts store the number of *additional* equal hands, so
every run is nonempty. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStereoRuns

structure BoolRun where
  hand : Bool
  extra : Nat
  deriving DecidableEq, Repr

def expand : List BoolRun → List Bool
  | [] => []
  | r :: rs => List.replicate (r.extra + 1) r.hand ++ expand rs

def prepend (h : Bool) : List BoolRun → List BoolRun
  | [] => [⟨h,0⟩]
  | r :: rs => if h = r.hand then ⟨h,r.extra+1⟩ :: rs else ⟨h,0⟩ :: r :: rs

def encode : List Bool → List BoolRun
  | [] => []
  | h :: hs => prepend h (encode hs)

/-- Adjacent runs always have different hands. -/
def Normalized : List BoolRun → Prop
  | [] => True
  | [_] => True
  | a :: b :: rs => a.hand ≠ b.hand ∧ Normalized (b :: rs)

private theorem prepend_normalized (h : Bool) (rs : List BoolRun)
    (ok : Normalized rs) : Normalized (prepend h rs) := by
  cases rs with
  | nil => trivial
  | cons a rs =>
    by_cases same : h = a.hand
    · cases rs <;> simp_all [prepend,Normalized]
    · cases rs <;> simp_all [prepend,Normalized]

theorem encode_normalized (w : List Bool) : Normalized (encode w) := by
  induction w with
  | nil => trivial
  | cons h hs ih => exact prepend_normalized h _ ih

@[simp] theorem expand_prepend (h : Bool) (rs : List BoolRun) :
    expand (prepend h rs) = h :: expand rs := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    simp only [prepend]
    split
    · next eq => simp [expand,eq,List.replicate_succ]
    · simp [expand]

@[simp] theorem expand_encode (w : List Bool) : expand (encode w) = w := by
  induction w with
  | nil => rfl
  | cons h hs ih => simp [encode,ih]

theorem encode_injective : Function.Injective encode := by
  intro x y h
  simpa using congrArg expand h

@[simp] theorem encode_eq_iff (x y : List Bool) : encode x = encode y ↔ x = y :=
  encode_injective.eq_iff

/-- Canonicalization merges equal hands across all input block boundaries. -/
def normalize (rs : List BoolRun) : List BoolRun := encode (expand rs)

@[simp] theorem expand_normalize (rs : List BoolRun) : expand (normalize rs) = expand rs :=
  expand_encode _

@[simp] theorem normalize_eq_iff (x y : List BoolRun) :
    normalize x = normalize y ↔ expand x = expand y := encode_eq_iff _ _

/-- Merge a whole nonempty block into an already normalized suffix. -/
def merge (a : BoolRun) : List BoolRun → List BoolRun
  | [] => [a]
  | b :: bs => if a.hand = b.hand then ⟨a.hand,a.extra+b.extra+1⟩ :: bs else a :: b :: bs

private theorem encode_block (h : Bool) (n : Nat) (w : List Bool) :
    encode (List.replicate (n+1) h ++ w) = merge ⟨h,n⟩ (encode w) := by
  induction n with
  | zero => cases hw : encode w <;> simp [List.replicate_succ,encode,hw,merge,prepend]
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append,encode,ih]
    cases hw : encode w with
    | nil => simp [merge,prepend]
    | cons b bs =>
      simp only [merge]
      split
      · next same => simp [prepend,same,Nat.add_assoc]; omega
      · next different => simp [prepend]

/-- Canonicalize compressed blocks without materializing their hands. -/
def normalizeRuns : List BoolRun → List BoolRun
  | [] => []
  | a :: as => merge a (normalizeRuns as)

@[csimp] theorem normalize_fast : normalize = normalizeRuns := by
  funext rs
  induction rs with
  | nil => rfl
  | cons a as ih =>
    change encode (List.replicate (a.extra+1) a.hand ++ expand as) = merge a (normalizeRuns as)
    rw [encode_block]
    change merge a (normalize as) = _
    rw [ih]

@[simp] theorem normalizeRuns_exact (rs : List BoolRun) :
    normalizeRuns rs = encode (expand rs) := (congrFun normalize_fast rs).symm

@[simp] theorem normalizeRuns_eq_iff (x y : List BoolRun) :
    normalizeRuns x = normalizeRuns y ↔ expand x = expand y := by
  simp only [normalizeRuns_exact,encode_eq_iff]

theorem normalizeRuns_normalized (rs : List BoolRun) : Normalized (normalizeRuns rs) := by
  rw [normalizeRuns_exact]; exact encode_normalized _

@[simp] theorem expand_append (x y : List BoolRun) : expand (x ++ y) = expand x ++ expand y := by
  induction x with
  | nil => rfl
  | cons a as ih => simp [expand,ih,List.append_assoc]

/-- Append summaries and merge the equal boundary hands, irrespective of the
rank or sphere that emitted them. -/
def appendRuns (x y : List BoolRun) := normalizeRuns (x ++ y)

@[simp] theorem expand_appendRuns (x y : List BoolRun) :
    expand (appendRuns x y) = expand x ++ expand y := by
  simp [appendRuns]

private theorem cancel (h : Bool) (n : Nat) (x y : List Bool) :
    compare (List.replicate n h ++ x) (List.replicate n h ++ y) = compare x y := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,List.compare_cons_cons] using ih

/-- Fuel decreases once per exhausted run, never once per emitted hand.
`runCompare` supplies enough fuel for all runs. No expansion is executed. -/
private def compareAux : Nat → List BoolRun → List BoolRun → Ordering
  | 0, _, _ => .eq
  | _+1, [], [] => .eq
  | _+1, [], _::_ => .lt
  | _+1, _::_, [] => .gt
  | fuel+1, a::as, b::bs =>
    if a.hand ≠ b.hand then compare a.hand b.hand
    else if a.extra = b.extra then compareAux fuel as bs
    else if a.extra < b.extra then
      compareAux fuel as (⟨b.hand,b.extra-a.extra-1⟩::bs)
    else compareAux fuel (⟨a.hand,a.extra-b.extra-1⟩::as) bs

def runCompare (x y : List BoolRun) : Ordering := compareAux (x.length+y.length) x y

private theorem compareAux_exact (fuel : Nat) (x y : List BoolRun) :
    x.length + y.length ≤ fuel →
    compareAux fuel x y = compare (expand x) (expand y) := by
  induction fuel generalizing x y with
  | zero =>
    intro bound
    have hx : x = [] := by cases x <;> simp_all
    have hy : y = [] := by cases y <;> simp_all
    subst x; subst y; rfl
  | succ fuel ih =>
    intro bound
    cases x with
    | nil => cases y <;> simp [compareAux,expand,List.replicate_succ]
    | cons a as =>
      cases y with
      | nil => simp [compareAux,expand,List.replicate_succ]
      | cons b bs =>
        simp only [compareAux]
        split
        · next different =>
            cases ah : a.hand <;> cases bh : b.hand <;>
              simp_all [expand,List.replicate_succ,List.compare_cons_cons]
            all_goals rfl
        · next same =>
            have hands : a.hand = b.hand := by simpa using same
            split
            · next counts =>
                rw [ih _ _ (by simp_all only [List.length_cons]; omega)]
                simpa only [expand,hands,counts] using (cancel b.hand (b.extra+1) (expand as) (expand bs)).symm
            · next counts =>
                split
                · next less =>
                    rw [ih _ _ (by simp_all only [List.length_cons]; omega)]
                    have splitCount : b.extra+1 = (a.extra+1) + ((b.extra-a.extra-1)+1) := by omega
                    have rep : List.replicate (b.extra+1) b.hand =
                        List.replicate (a.extra+1) b.hand ++ List.replicate ((b.extra-a.extra-1)+1) b.hand := by
                      rw [splitCount]; exact List.replicate_add _ _ _
                    change compare (expand as) (List.replicate _ b.hand ++ expand bs) =
                      compare (List.replicate (a.extra+1) a.hand ++ expand as) (List.replicate (b.extra+1) b.hand ++ expand bs)
                    rw [rep,List.append_assoc,← hands,cancel]
                · next less =>
                    rw [ih _ _ (by simp_all only [List.length_cons]; omega)]
                    have splitCount : a.extra+1 = (b.extra+1) + ((a.extra-b.extra-1)+1) := by omega
                    have rep : List.replicate (a.extra+1) a.hand =
                        List.replicate (b.extra+1) a.hand ++ List.replicate ((a.extra-b.extra-1)+1) a.hand := by
                      rw [splitCount]; exact List.replicate_add _ _ _
                    change compare (List.replicate _ a.hand ++ expand as) (expand bs) =
                      compare (List.replicate (a.extra+1) a.hand ++ expand as) (List.replicate (b.extra+1) b.hand ++ expand bs)
                    rw [rep,List.append_assoc,hands,cancel]

theorem runCompare_exact (x y : List BoolRun) :
    runCompare x y = compare (expand x) (expand y) := compareAux_exact _ _ _ (Nat.le_refl _)

@[simp] theorem compare_encoded (x y : List Bool) :
    runCompare (encode x) (encode y) = compare x y := by
  simp [runCompare_exact]

end TetraStereo.Engine.RingStereoRuns

assert_kernel_only TetraStereo.Engine.RingStereoRuns.encode_eq_iff
assert_kernel_only TetraStereo.Engine.RingStereoRuns.compare_encoded

assert_kernel_only TetraStereo.Engine.RingStereoRuns.normalize_fast
assert_kernel_only TetraStereo.Engine.RingStereoRuns.encode_normalized
assert_kernel_only TetraStereo.Engine.RingStereoRuns.runCompare_exact

/-- A proper prefix with trillion-hand runs is decided by two run steps. -/
example : TetraStereo.Engine.RingStereoRuns.runCompare [⟨true,1000000000000⟩] [⟨true,1000000000001⟩] = .lt := by decide

/-- Equal hands merge even when supplied as separate source blocks. -/
example : TetraStereo.Engine.RingStereoRuns.normalizeRuns [⟨true,0⟩,⟨true,4⟩,⟨false,0⟩] =
    [⟨true,5⟩,⟨false,0⟩] := by decide
