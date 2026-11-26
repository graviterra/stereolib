import TetraStereo.Engine.RingZeroDuplicateMass

set_option autoImplicit false

namespace TetraStereo.Engine.RingConstitutionalTreeInvariant
open OneCenter RingRetainedChemicalTrace
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)

/-- Finite unordered trees labelled by the primitive constitutional observation. -/
def Shape : Nat → Type
  | 0 => Unit
  | n+1 => Option Observation × Multiset (Shape n)

/-- Read the executable children directly, retaining every repeated branch. -/
def view (i : Input) : (n : Nat) → Arm i → Shape n
  | 0, _ => ()
  | n+1, q =>
    (observation? i q (i.certified.executableLocalizedRerootChildren q).isEmpty,
      ↑((i.certified.executableLocalizedRerootChildren q).map (view i n)))

private def emptyShape : (n : Nat) → Shape n
  | 0 => ()
  | _+1 => (none,0)

private noncomputable def representative (n : Nat) (k : Key) : Shape n := by
  classical
  exact if h : ∃ s : Shape n, ∃ (i : Input) (q : Arm i), key? i q = some k ∧ view i n q = s
  then Classical.choose h else emptyShape n

private theorem representative_eq (n : Nat)
    (tie : ∀ {i j : Input} {a : Arm i} {b : Arm j} {k : Key},
      key? i a = some k → key? j b = some k → view i n a = view j n b)
    {i : Input} {q : Arm i} {k : Key} (read : key? i q = some k) :
    view i n q = representative n k := by
  classical
  have h : ∃ s : Shape n, ∃ (i : Input) (q : Arm i), key? i q = some k ∧ view i n q = s :=
    ⟨view i n q,i,q,read,rfl⟩
  obtain ⟨j,b,hb,eqn⟩ := Classical.choose_spec h
  simpa only [representative,dif_pos h] using (tie read hb).trans eqn

/-- A successful key exposes the actual primitive observation and valid child lookups. -/
theorem source {i : Input} {q : Arm i} {k : Key} (read : key? i q = some k) :
    observation? i q (i.certified.executableLocalizedRerootChildren q).isEmpty = some k.root ∧
    ∀ c ∈ i.certified.executableLocalizedRerootChildren q, ∃ v, key? i c = some v := by
  cases key_source read with
  | @node _ cs o ks frame obs lookup hit branches =>
    have actual := Option.some.inj
      (((i.certified.localizedRerootChildren?_eq_some_iff q cs).mpr frame).symm.trans
        (i.certified.localizedRerootChildren?_eq_some_executable q))
    constructor
    · simpa only [actual] using obs
    · intro c hc
      exact RingRetainedChemicalCoverage.key_total i
        (RingRetainedChemicalCoverage.admitted_atoms i) c
        (i.certified.localizedRerootChild_valid q c cs frame (by simpa only [actual] using hc))

private theorem mapped (n : Nat)
    (tie : ∀ {i j : Input} {a : Arm i} {b : Arm j} {k : Key},
      key? i a = some k → key? j b = some k → view i n a = view j n b)
    {i : Input} {q : Arm i} {k : Key} (read : key? i q = some k) :
    (i.certified.executableLocalizedRerootChildren q).map (view i n) =
      (RingChildKeyRecovery.childKeys i q).map (representative n) := by
  have valid := (source read).2
  change (i.certified.executableLocalizedRerootChildren q).map (view i n) =
    ((i.certified.executableLocalizedRerootChildren q).filterMap (key? i)).map (representative n)
  generalize hxs : i.certified.executableLocalizedRerootChildren q = xs
  have all : ∀ c ∈ xs, ∃ v, key? i c = some v := hxs ▸ valid
  clear valid hxs
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨v,hv⟩ := all c List.mem_cons_self
    simp only [List.map_cons,List.filterMap_cons,hv]
    exact congrArg₂ List.cons (representative_eq n tie hv)
      (ih (fun c hc => all c (List.mem_cons_of_mem _ hc)))

/-- Complete constitutional equality preserves the unordered observation tree at every depth,
including child multiplicities, across different inputs and retained occurrences. -/
theorem view_eq {i j : Input} {a : Arm i} {b : Arm j} {k : Key}
    (ka : key? i a = some k) (kb : key? j b = some k) (n : Nat) :
    view i n a = view j n b := by
  induction n generalizing i j a b k with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · exact (source ka).1.trans (source kb).1.symm
    · change (↑((i.certified.executableLocalizedRerootChildren a).map (view i n)) :
        Multiset (Shape n)) = ↑((j.certified.executableLocalizedRerootChildren b).map (view j n))
      rw [mapped n ih ka,mapped n ih kb]
      exact Quot.sound ((RingChildKeyRecovery.children_tie ka kb).1.map _)


open private zero read_zero from TetraStereo.Engine.RingZeroDuplicateMass

/-- Read zero duplicate mass directly at every occurrence of the actual tree. -/
def viewZero (i : Input) : (n : Nat) → Arm i → Shape n
  | 0, _ => ()
  | n+1, q =>
    (RingZeroDuplicateMass.read? i q (i.certified.executableLocalizedRerootChildren q).isEmpty,
      ↑((i.certified.executableLocalizedRerootChildren q).map (viewZero i n)))

/-- Change only observation labels, preserving all branch multiplicities. -/
def mapShape (f : Observation → Observation) : (n : Nat) → Shape n → Shape n
  | 0, _ => ()
  | n+1, t => (t.1.map f, t.2.map (mapShape f n))

private def restore (o : Observation) : Observation :=
  ⟨o.atomic,o.duplicate,if o.duplicate = 0 then o.mass else
    (CIPRule2MassData.rule2MassPico? o.atomic none).getD 0⟩

private theorem restore_zero {i : Input} {q : Arm i} {t o}
    (read : observation? i q t = some o) : restore (zero o) = o := by
  rcases RingMassDifference.observation_kind read with ⟨_,h⟩ | ⟨h,m⟩
  · cases o; simp_all [restore,zero]
  · cases o; simp_all [restore,zero,Nat.ne_of_gt h]

private theorem map_views (n : Nat) :
    ∀ {i : Input} {q : Arm i} {k : Key}, key? i q = some k →
      mapShape zero n (view i n q) = viewZero i n q ∧
      mapShape restore n (viewZero i n q) = view i n q := by
  induction n with
  | zero => intro i q k read; exact ⟨rfl,rfl⟩
  | succ n ih =>
    intro i q k read
    have observed := (source read).1
    have rz := read_zero observed
    have inverse := restore_zero observed
    have children (c : Arm i) (hc : c ∈ i.certified.executableLocalizedRerootChildren q) :
        mapShape zero n (view i n c) = viewZero i n c ∧
        mapShape restore n (viewZero i n c) = view i n c := by
      obtain ⟨v,hv⟩ := (source read).2 c hc
      exact ih hv
    constructor
    · apply Prod.ext
      · change (observation? i q _).map zero = RingZeroDuplicateMass.read? i q _
        rw [observed,rz]; rfl
      · simp only [mapShape,view,viewZero,Multiset.map_coe,List.map_map]
        apply congrArg (fun xs : List (Shape n) => (↑xs : Multiset (Shape n)))
        exact List.map_congr_left fun c hc => (children c hc).1
    · apply Prod.ext
      · change (RingZeroDuplicateMass.read? i q _).map restore = observation? i q _
        rw [observed,rz]; simp only [Option.map_some,inverse]
      · simp only [mapShape,view,viewZero,Multiset.map_coe,List.map_map]
        apply congrArg (fun xs : List (Shape n) => (↑xs : Multiset (Shape n)))
        exact List.map_congr_left fun c hc => (children c hc).2

/-- Zeroing closure masses loses no finite tree equality on successful molecular reads.
The inverse restores each duplicate mass solely from its atomic number. -/
theorem viewZero_eq_iff {i j : Input} {a : Arm i} {b : Arm j} {x y : Key}
    (ha : key? i a = some x) (hb : key? j b = some y) (n : Nat) :
    viewZero i n a = viewZero j n b ↔ view i n a = view j n b := by
  constructor
  · intro h
    have eqn := congrArg (mapShape restore n) h
    simpa only [(map_views n ha).2,(map_views n hb).2] using eqn
  · intro h
    have eqn := congrArg (mapShape zero n) h
    simpa only [(map_views n ha).1,(map_views n hb).1] using eqn

end TetraStereo.Engine.RingConstitutionalTreeInvariant

assert_kernel_only TetraStereo.Engine.RingConstitutionalTreeInvariant.view_eq

assert_kernel_only TetraStereo.Engine.RingConstitutionalTreeInvariant.viewZero_eq_iff
