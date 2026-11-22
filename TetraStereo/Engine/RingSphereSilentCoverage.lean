import TetraStereo.Engine.RingSphereCoverage

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereCoverage
open OneCenter CertifiedLocalizedCIPInput RingSphereReadings RingNestedActivePair
open RingActivePairs (Site)
open LocalizedChemicalRing (Input)

/-- A known absence at every materialized occurrence, including every leaf. -/
def Silent (p : Profile) := ∀ v ∈ p.flatten, v.publication = none

private theorem same_values {α : Type} {rows : List (List α)} {x : List α} (w : Word rows x) :
    rows.flatten.Perm x := by
  obtain ⟨_,p,rfl⟩ := w
  induction p with
  | nil => exact .nil
  | cons head _ ih => exact head.append ih

private theorem silent_ord (a b : List Nat) (ha : ∀ n ∈ a, n = 0) (hb : ∀ n ∈ b, n = 0) :
    lowerScore a b = 0 := by
  induction a generalizing b with
  | nil => rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [List.forall_mem_cons] at ha hb
      simpa only [lowerScore,ha.1,hb.1,if_true] using ih ys ha.2 hb.2

private theorem projected_zero (rev : Bool) {p : Profile} (sil : Silent p)
    (f : Option LocalizedAuxiliaryLabel → Nat) (z : f none = 0) {w}
    (hw : Word (p.map (List.map fun v => f (v.label rev))) w) : ∀ n ∈ w, n = 0 := by
  intro n hn
  have occurs := (same_values hw).mem_iff.mpr hn
  rw [← List.map_flatten] at occurs
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp occurs
  simpa only [Visit.label,sil v hv,Option.map_none] using z

private theorem silent_upper {p : Profile} (sil : Silent p) (rev : Bool) {w}
    (hw : Word (upperRows p rev) w) : w.filterMap id = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro label hl
  have occurs := (same_values hw).mem_iff.mpr hl
  rw [upper_flatten] at occurs
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp occurs
  have present : v ∈ p.flatten := by
    cases p with
    | nil => contradiction
    | cons top tail =>
      rcases List.mem_append.mp hv with here | below
      · exact List.mem_append_left _ here
      · obtain ⟨layer,member,inside⟩ := List.mem_flatMap.mp below
        exact List.mem_append_right _ (List.mem_flatten_of_mem member (List.mem_filter.mp inside).1)
  simp [Visit.label,sil v present,upper]

private theorem no_reference (rows : List (List (Option RS))) (silent : rows.flatten.filterMap id = []) :
    oneReference rows = true := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.flatten_cons,List.filterMap_append,List.append_eq_nil_iff] at silent
    simp [oneReference,silent.1,ih silent.2]

/-- Any two fully silent profiles have an exact zero at every stage on every
ordering and on either geometry. The number of interchangeable siblings is unrestricted. -/
theorem silent_decision {a b : Profile} (left : Silent a) (right : Silent b) (rev : Bool) :
    Agrees a b rev 0 := by
  have ords (f : Option LocalizedAuxiliaryLabel → Nat) (z : f none = 0) :
      Common ord (a.map (List.map fun v => f (v.label rev))) (b.map (List.map fun v => f (v.label rev))) 0 :=
    fun x y hx hy => congrArg some (silent_ord x y (projected_zero rev left f z hx) (projected_zero rev right f z hy))
  have localTie : Common RingSeededPairs.localSign? (upperRows a rev) (upperRows b rev) 0 := by
    intro x y hx hy
    simp only [RingSeededPairs.localSign?,← List.head?_filterMap,silent_upper left rev hx,silent_upper right rev hy]
    rfl
  have fixed (s : RS) : Common (RingSeededPairs.listSign? s) (upperRows a rev) (upperRows b rev) 0 := by
    intro x y hx hy
    simp [RingSeededPairs.listSign?,silent_upper left rev hx,silent_upper right rev hy,RingSeededPairs.compareBits]
  exact ⟨ords unit rfl,no_reference _ (silent_upper left rev (canonical _)),
    no_reference _ (silent_upper right rev (canonical _)),.fixed localTie (ords lower rfl) (fixed .R) (fixed .S)⟩

theorem silent_molecular {i : Input} {f a b : Site i} {read t l r}
    (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (left : RingSpherePopulation.profile? i read ⟨a,some f⟩ = some l)
    (right : RingSpherePopulation.profile? i read ⟨b,some f⟩ = some r)
    (full : l.map List.length = r.map List.length)
    (queue : (upperRows l false).map List.length = (upperRows r false).map List.length)
    (ls : Silent l) (rs : Silent r) : RingSpherePriority.score? i f a b read = some (0,0) :=
  (molecular_iff prior tie left right).mpr ⟨full,queue,silent_decision ls rs false,silent_decision ls rs true⟩

private theorem original_value {α β : Type} {xs : List α} {ys : List β} {f : α → Option β}
    (hit : xs.mapM f = some ys) {y} (mem : y ∈ ys) : ∃ x ∈ xs, f x = some y := by
  have rel := TerminalTie.mapM_forall₂ _ _ _ hit
  clear hit
  induction rel with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨x,hx,read⟩ := ih tail
      exact ⟨x,List.mem_cons_of_mem _ hx,read⟩

/-- Known absence on every reachable occurrence constructs a full, silent
profile directly from the molecular reader, at any depth of a ring. -/
theorem silent_profile {i : Input} {q : RingActivePairs.Arm i} {read : Reader i}
    (valid : i.certified.LocalizedRerootCursorValid q)
    (silent : ∀ t, RingRetainedChemicalTrace.Reaches i q t → read t.occurrence = some none) :
    ∃ p, RingSpherePopulation.profile? i read q = some p ∧ Silent p := by
  obtain ⟨p,hp⟩ := RingSpherePopulation.profile?_of_ready valid
    (fun t ht => ⟨none,silent t ht,rfl,fun _ => rfl⟩)
  refine ⟨p,hp,?_⟩
  intro v hv
  obtain ⟨row,hr,hv⟩ := List.mem_flatten.mp hv
  obtain ⟨rs,hr,hm⟩ := original_value (f := List.mapM (RingSpherePopulation.observe i read)) hp hr
  obtain ⟨t,ht,seen⟩ := original_value hm hv
  obtain ⟨d,hd,idx⟩ := List.getElem_of_mem hr
  have same := RingSpherePopulation.layer_at (RingSpherePopulation.full_complete (qs := [q]) (by simpa using valid)) d
  have occurs := same.mem_iff.mp (by simpa only [List.getElem?_eq_getElem hd,Option.getD_some,idx] using ht)
  obtain ⟨u,hu,path⟩ := (RingSpherePopulation.mem_distance d [q] t).mp occurs
  obtain rfl := List.mem_singleton.mp hu
  have blank := silent t path.reaches
  obtain ⟨z,_,result⟩ := Option.bind_eq_some_iff.mp seen
  unfold RingNestedActivePair.visit at result
  rw [blank] at result
  dsimp only [Option.bind_eq_bind,Option.bind_some] at result
  split at result <;> try contradiction
  obtain rfl := Option.some.inj result
  rfl

end TetraStereo.Engine.RingSphereCoverage

assert_kernel_only TetraStereo.Engine.RingSphereCoverage.silent_decision
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.silent_molecular
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.silent_profile
