import TetraStereo.Engine.RingConstitutionalTreeInvariant
import TetraStereo.Engine.RingAllLigandTwoShell

/-! Reconstruct the public constitutional comparison from unordered, rooted
ligand trees. Each parent retains its own children with their multiplicities. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingLigandTreeComparison
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingRetainedChemicalTrace
open RingRetainedChemicalPreorder (Site Direction keyFor read_key orderWord)
open RingConstitutionalTreeInvariant (Shape view)

open private through_direction from TetraStereo.Engine.RingAllLigandTwoShell
open private mapM_perm from TetraStereo.Engine.RingActivePairs
attribute [local instance] lexOrd

private abbrev Valid := {k : Key // WellFormed k}

private def pack (o : Observation) (ks : List Valid) : Valid :=
  ⟨assemble o (ks.map Subtype.val),assemble_framed o _ (by
    intro k hk
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hk
    exact c.property)⟩

private theorem pack_perm (o : Observation) {xs ys : List Valid} (p : xs.Perm ys) :
    pack o xs = pack o ys := by
  apply Subtype.ext
  apply assemble_perm o (p.map Subtype.val)
  intro k hk
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hk
  exact c.property

/-- Quotient elimination uses an arbitrary actual ordering of the children.
Permutation invariance discharges the choice and preserves any failed read. -/
private def collect {α : Type} (o : Observation) (read : α → Option Valid)
    (children : Multiset α) : Option Valid :=
  Quotient.liftOn children (fun xs => (xs.mapM read).map (pack o)) (by
    intro xs ys p
    change xs.Perm ys at p
    cases hx : xs.mapM read with
    | some ks =>
      obtain ⟨us,hu,perm⟩ := mapM_perm p.symm hx
      simp [hx,hu,pack_perm o perm]
    | none =>
      cases hy : ys.mapM read with
      | none => simp [hx,hy]
      | some us =>
        obtain ⟨ks,hk,_⟩ := mapM_perm p hy
        simp [hx] at hk)

private def checked : (n : Nat) → Shape n → Option Valid
  | 0,_ => none
  | n+1,t => t.1.bind fun obs => collect obs (checked n) t.2

/-- An executable fold reconstructs the three rule-major columns solely from
a finite unordered tree. Each parent retains its own bag of children. -/
def reconstruct (n : Nat) (t : Shape n) : Option Key :=
  (checked n t).map Subtype.val

private theorem map_reads {α : Type} {f : α → Option Key} {g : α → Option Valid}
    (xs : List α) {ks : List Key}
    (agree : ∀ x k, f x = some k → ∃ v, g x = some v ∧ v.val = k)
    (hit : xs.mapM f = some ks) : ∃ vs, xs.mapM g = some vs ∧ vs.map Subtype.val = ks := by
  induction xs generalizing ks with
  | nil => exact ⟨[],rfl,Option.some.inj hit⟩
  | cons x xs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨k,hk,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨ks,hks,out⟩ := Option.bind_eq_some_iff.mp more
    cases Option.some.inj out
    obtain ⟨v,hv,rfl⟩ := agree x k hk
    obtain ⟨vs,hs,rfl⟩ := ih hks
    exact ⟨v::vs,by simp [hv,hs],rfl⟩

/-- One fold proof works for either molecular mass convention. The reader supplies
only a primitive observation at each node and the unsorted list of its children. -/
private theorem checked_build (i : Input) (obs : Arm i → Option Observation)
    (source : (n : Nat) → Arm i → Shape n) (eval : Nat → Arm i → Option Key)
    (empty : ∀ q, eval 0 q = none)
    (expand : ∀ n q, source (n+1) q =
      (obs q,↑((i.certified.executableLocalizedRerootChildren q).map (source n))))
    (step : ∀ n q, eval (n+1) q = (do
      let o ← obs q
      let ks ← (i.certified.executableLocalizedRerootChildren q).mapM (eval n)
      return assemble o ks)) :
    ∀ n (q : Arm i) {k : Key}, eval n q = some k →
      ∃ v, checked n (source n q) = some v ∧ v.val = k := by
  intro n
  induction n with
  | zero => intro q k hit; simp [empty] at hit
  | succ n ih =>
    intro q k hit
    rw [step] at hit
    obtain ⟨o,ho,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨ks,hks,out⟩ := Option.bind_eq_some_iff.mp more
    cases Option.some.inj out
    let cs := i.certified.executableLocalizedRerootChildren q
    obtain ⟨vs,hu,eqn⟩ := map_reads (g := fun c => checked n (source n c)) cs
      (fun c _ h => ih c h) hks
    refine ⟨pack o vs,?_,congrArg (assemble o) eqn⟩
    rw [expand]
    change (obs q >>= fun o =>
      ((cs.map (source n)).mapM (checked n)).map (pack o)) = _
    simpa [ho,List.mapM_map,Function.comp_def] using congrArg (Option.map (pack o)) hu

/-- The operational depth bounds the entire retained ligand, including inward directions. -/
def depth (i : Input) := 2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1

abbrev tree {i : Input} {f : Site i} (a : Direction i f) :=
  view i (depth i) (⟨a.val,some f⟩ : Arm i)

section LegacyMass
open private build from TetraStereo.Engine.RingRetainedChemicalTrace
theorem reconstruct_direction {i : Input} {f : Site i} (a : Direction i f) :
    reconstruct (depth i) (tree a) = some (keyFor a) := by
  obtain ⟨v,hv,hk⟩ := checked_build i (fun q => observation? i q
    (i.certified.executableLocalizedRerootChildren q).isEmpty) (view i)
    (build i i.certified.executableLocalizedRerootChildren) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (depth i) _ (read_key a)
  simpa [reconstruct,tree,hv] using hk
end LegacyMass

/-- Characterize every public constitutional tie, including ties between distinct
directions. No public key or priority information enters the unordered tree. -/
theorem tie_iff {i : Input} {f : Site i} (a b : Direction i f) :
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) a b = some .eq ↔
      tree a = tree b := by
  rw [RingRetainedChemicalPreorder.table_order,Option.some.injEq,Std.compare_eq_eq_iff_eq]
  constructor
  · intro tied
    have same := RingPairGateCount.key_eq (key_source (read_key a)).formed
      (key_source (read_key b)).formed tied
    exact RingConstitutionalTreeInvariant.view_eq (read_key a) (same ▸ read_key b) _
  · intro h
    have equal := congrArg (reconstruct (depth i)) h
    rw [reconstruct_direction,reconstruct_direction] at equal
    exact congrArg orderWord (Option.some.inj equal)

/-- The complete three-way public ordering factors through two independently
constructed trees. The reconstruction recovers each full constitutional key. -/
theorem compare_from_trees {i : Input} {f : Site i} (a b : Direction i f) :
    (do let x ← reconstruct (depth i) (tree a)
        let y ← reconstruct (depth i) (tree b)
        pure (compareKeys x y)) =
      RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) a b := by
  simp [reconstruct_direction,RingRetainedChemicalPreorder.table_order,RingRetainedChemicalPreorder.compare_word]

section ZeroMass
open RingConstitutionalTreeInvariant (viewZero)
open private build from TetraStereo.Engine.RingZeroDuplicateMass

abbrev zeroTree {i : Input} {f : Site i} (a : Direction i f) :=
  viewZero i (depth i) (⟨a.val,some f⟩ : Arm i)

/-- Rebuild every branch using the zero mass observed directly at its closure nodes. -/
theorem reconstruct_zero {i : Input} {f : Site i} (a : Direction i f) :
    reconstruct (depth i) (zeroTree a) = some (RingZeroDuplicateMass.rebuiltFor a) := by
  have read : RingZeroDuplicateMass.rebuiltKey? i (⟨a.val,some f⟩ : Arm i) =
    some (RingZeroDuplicateMass.rebuiltFor a) := (Option.some_get _).symm
  obtain ⟨v,hv,hk⟩ := checked_build i (fun q => RingZeroDuplicateMass.read? i q
    (i.certified.executableLocalizedRerootChildren q).isEmpty) (viewZero i)
    (fun n q => build i i.certified.executableLocalizedRerootChildren n q)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (depth i) _ read
  simpa [reconstruct,zeroTree,hv] using hk

theorem zero_tie_iff {i : Input} {f : Site i} (a b : Direction i f) :
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) a b = some .eq ↔
      zeroTree a = zeroTree b :=
  (tie_iff a b).trans ((RingConstitutionalTreeInvariant.viewZero_eq_iff (read_key a) (read_key b) _).symm)

/-- Both child orderings are rebuilt from the zero-mass trees. Less, equal
and greater are all exactly the public constitutional result. -/
theorem zero_compare_from_trees {i : Input} {f : Site i} (a b : Direction i f) :
    (do let x ← reconstruct (depth i) (zeroTree a)
        let y ← reconstruct (depth i) (zeroTree b)
        pure (compareKeys x y)) =
      RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) a b := by
  rw [reconstruct_zero,reconstruct_zero,RingRetainedChemicalPreorder.table_order]
  change some (compareKeys _ _) = some _
  rw [RingRetainedChemicalPreorder.compare_word]
  exact congrArg some (RingZeroDuplicateMass.prefixes_agree a b).2

end ZeroMass

private def shapeDecidable : (n : Nat) → DecidableEq (Shape n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => by
    letI := shapeDecidable n
    exact inferInstanceAs (DecidableEq (Option Observation × Multiset (Shape n)))

/-- Compare a pair of materialized unordered trees without computing priority keys. -/
def sameTree (n : Nat) (a b : Shape n) : Bool := @decide _ (shapeDecidable n a b)

/-- Test the constitutional tie without computing or sorting any public priority keys. -/
def tied {i : Input} {f : Site i} (a b : Direction i f) : Bool :=
  sameTree _ (zeroTree a) (zeroTree b)

theorem tied_exact {i : Input} {f : Site i} (a b : Direction i f) :
    tied a b = true ↔
      RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) a b = some .eq := by
  rw [zero_tie_iff]
  letI := shapeDecidable (depth i)
  exact decide_eq_true_iff

private def stereoSuffix : List (List Word) → List (List Word)
  | first :: tail => first.drop 3 :: tail
  | [] => []

private theorem split_stages (a b c d e f : Word) (u v : List Word) (x y : List (List Word)) :
    compare ((a::b::c::u)::x) ((d::e::f::v)::y) =
      (compare [a,b,c] [d,e,f]).then (compare (u::x) (v::y)) := by
  simp only [List.compare_cons_cons]
  cases compare a d <;> cases compare b e <;> cases compare c f <;> rfl

/-- On every completed original or reflected trial, all stereo fields and the
promotion mark are consulted only if the two entire constitutional trees match. -/
theorem marked_compare {i : Input} {f : Site i} (a b : Direction i f)
    {r : RingNestedActivePair.Reader i} {rev} {x y : RingFullPathEligibility.Key}
    (rx : RingFullPathEligibility.Reads i r rev ⟨a.val,some f⟩ x)
    (ry : RingFullPathEligibility.Reads i r rev ⟨b.val,some f⟩ y) (ma mb : Word) :
    compare (RingFullPathTrialReadings.trialKey x ma) (RingFullPathTrialReadings.trialKey y mb) =
      (if tied a b then
        compare (stereoSuffix (RingFullPathTrialReadings.trialKey x ma))
          (stereoSuffix (RingFullPathTrialReadings.trialKey y mb))
       else compareKeys (keyFor a) (keyFor b)) := by
  obtain ⟨u,hx⟩ := through_direction a rx
  obtain ⟨v,hy⟩ := through_direction b ry
  have split :
      compare (RingFullPathTrialReadings.trialKey x ma) (RingFullPathTrialReadings.trialKey y mb) =
        (compareKeys (keyFor a) (keyFor b)).then
          (compare (stereoSuffix (RingFullPathTrialReadings.trialKey x ma))
            (stereoSuffix (RingFullPathTrialReadings.trialKey y mb))) := by
    simp only [RingRetainedChemicalPreorder.compare_word,RingFullPathTrialReadings.trialKey,
      hx,hy,orderWord,List.cons_append,List.nil_append,stereoSuffix]
    exact split_stages ..
  rw [split]
  have gate : tied a b = true ↔ compareKeys (keyFor a) (keyFor b) = .eq := by
    rw [tied_exact,RingRetainedChemicalPreorder.table_order,Option.some.injEq,
      RingRetainedChemicalPreorder.compare_word]
  cases h : compareKeys (keyFor a) (keyFor b) <;> simp_all

end TetraStereo.Engine.RingLigandTreeComparison
assert_kernel_only TetraStereo.Engine.RingLigandTreeComparison.reconstruct_direction
assert_kernel_only TetraStereo.Engine.RingLigandTreeComparison.tie_iff
assert_kernel_only TetraStereo.Engine.RingLigandTreeComparison.compare_from_trees
assert_kernel_only TetraStereo.Engine.RingLigandTreeComparison.tied_exact
assert_kernel_only TetraStereo.Engine.RingLigandTreeComparison.marked_compare
assert_kernel_only TetraStereo.Engine.RingLigandTreeComparison.zero_compare_from_trees
assert_kernel_only TetraStereo.Engine.RingLigandTreeComparison.zero_tie_iff
