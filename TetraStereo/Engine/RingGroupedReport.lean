import TetraStereo.Engine.RingGroupedGeometry
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedReport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Labels)
open RingActiveDistanceSchedule (View)
open RingGroupedPublication (Molecular)

abbrev Report := List (Nat × Option Labels)

def origin (i : Input) (a : i.certified.Atom) : Site i :=
  i.certified.localizedAtomRootOccurrenceExecutable _ a

theorem origin_address (i : Input) (a : i.certified.Atom) :
    (origin i a).val.root = a ∧ (origin i a).val.address = [] ∧ (origin i a).val.node.current? = some a :=
  ⟨rfl,rfl,rfl⟩

theorem origin_unique {i : Input} (q : Site i) (empty : q.val.address = []) :
    q = origin i q.val.root := by
  apply Subtype.ext
  exact i.certified.declarativeLocalizedOccurrence_functional_at_root_address
    ((i.certified.mem_localizedOccurrences_iff _ _).mp q.property)
    ((i.certified.mem_localizedOccurrences_iff _ _).mp (origin i q.val.root).property) rfl empty

def centres (i : Input) : List i.certified.Atom := i.certified.canonicalTetrahedralCenters.map Subtype.val

def carbons (i : Input) : List i.certified.Atom :=
  (RingCarbonReport.carbons i.molecule).attach.map fun a => ⟨a.val,by
    have h := ((RingCarbonReport.mem_carbons).mp a.property).1
    rw [← i.molecule.toSemanticMolecule?_atomCount i.certified.certified.input.molecule i.agreement.1] at h
    exact h⟩

theorem carbon_inventory (i : Input) : (carbons i).map Fin.val = RingCarbonReport.carbons i.molecule := by
  simp [carbons,List.map_map,Function.comp_def]

private def row? {i : Input} (s : View i) (a : i.certified.Atom) : Option (Nat × Option Labels) :=
  (s (origin i a)).map fun v => (a.val,v)

/-- Materialize one distance-ordered table and read each requested atom at
its own empty-address root. Missing cells fail the report. -/
def forAtoms? (i : Input) (atoms : List i.certified.Atom) : Option Report :=
  let s := RingGroupedPublication.state i
  atoms.mapM (row? s)

private def selected (i : Input) (atoms : List i.certified.Atom) : RingActiveDistanceSchedule.Rule i :=
  fun f read => if f.val.root ∈ atoms then RingGroupedPublication.publish? i f read else none

/-- Work for a report can be limited to the carriers of the requested
original atoms. Every dependency of a selected site has the same root. -/
private theorem selected_state (i : Input) (atoms : List i.certified.Atom) :
    ∀ q : Site i, q.val.root ∈ atoms →
    RingActiveDistanceSchedule.evaluate (selected i atoms) q = RingGroupedPublication.state i q := by
  let s := RingActiveDistanceSchedule.evaluate (selected i atoms)
  suffices ∀ n (t : Site i), RingActiveDistanceSchedule.height i - RingActiveDistanceSchedule.distance t = n →
      t.val.root ∈ atoms → s t = RingGroupedPublication.state i t from fun q on => this _ q rfl on
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t depth on
    have eqn : RingActiveDistanceSchedule.frozen s t = RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) t := by
      funext u
      unfold RingActiveDistanceSchedule.frozen
      split_ifs with off vis
      · rfl
      · have root := of_not_not off
        have deeper := vis.1
        have upper := RingActiveDistanceSchedule.distance_bound u
        exact ih _ (by omega) u rfl (root ▸ on)
      · rfl
    change RingActiveDistanceSchedule.evaluate (selected i atoms) t = _
    rw [RingActiveDistanceSchedule.evaluate_eq,RingGroupedPublication.state_eq]
    simpa only [selected,on,if_true] using congrArg (RingGroupedPublication.publish? i t) eqn

private def selectedReport (i : Input) (atoms : List i.certified.Atom) : Option Report :=
  let rows := RingActiveDistanceSchedule.table (selected i atoms) (RingActiveDistanceSchedule.height i + 1)
  atoms.mapM (row? (RingActiveDistanceSchedule.snapshot rows))

@[csimp] theorem selected_report : @forAtoms? = @selectedReport := by
  funext i atoms
  dsimp only [forAtoms?,selectedReport]
  rw [RingActiveDistanceSchedule.snapshot_table]
  have agree {α β : Type} (xs : List α) (f g : α → Option β) (same : ∀ x ∈ xs, f x = g x) :
      xs.mapM f = xs.mapM g := by
    induction xs with
    | nil => rfl
    | cons x xs ih => rw [List.mapM_cons,List.mapM_cons,same x List.mem_cons_self,ih (fun k hk => same k (List.mem_cons_of_mem _ hk))]
  apply agree
  intro a ha
  unfold row?
  exact congrArg (fun v => v.map fun l => (a.val,l)) (selected_state i atoms (origin i a) ha).symm

def report? (i : Input) := forAtoms? i (centres i)
def carbonReport? (i : Input) := forAtoms? i (carbons i)

/-- An inventory in molecular order with one independently derived pair
of labels or certified refusal at each addressed original atom. -/
def Correct (i : Input) (atoms : List i.certified.Atom) (r : Report) : Prop :=
  List.Forall₂ (fun a (row : Nat × Option Labels) => row.1 = a.val ∧ Molecular i (origin i a) row.2) atoms r

theorem correct_iff (i : Input) (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (r : Report) : forAtoms? i atoms = some r ↔ Correct i atoms r := by
  have physical := RingGroupedGeometry.physical coordinates
  have one (a : i.certified.Atom) (p : Nat × Option Labels) :
      row? (RingGroupedPublication.state i) a = some p ↔ p.1 = a.val ∧ Molecular i (origin i a) p.2 := by
    rcases p with ⟨n,v⟩
    rw [← RingGroupedPublication.molecular_iff physical]
    simp only [row?,Option.map_eq_some_iff,Prod.mk.injEq]
    constructor
    · rintro ⟨_,h,rfl,rfl⟩; exact ⟨rfl,h⟩
    · rintro ⟨rfl,h⟩; exact ⟨_,h,rfl,rfl⟩
  induction atoms generalizing r with
  | nil => cases r <;> simp [forAtoms?,Correct]
  | cons a as ih =>
    cases r with
    | nil =>
      unfold forAtoms? Correct
      rw [List.mapM_cons]
      cases row? (RingGroupedPublication.state i) a <;> cases as.mapM (row? (RingGroupedPublication.state i)) <;> simp
    | cons p ps =>
      change (a::as).mapM _ = some _ ↔ List.Forall₂ _ _ _
      rw [List.mapM_cons,List.forall₂_cons]
      change _ ↔ _ ∧ Correct i as ps
      apply Iff.trans ?_ (and_congr (one a p) (ih ps))
      unfold forAtoms?
      cases row? (RingGroupedPublication.state i) a <;> cases as.mapM (row? (RingGroupedPublication.state i)) <;> simp

theorem total (i : Input) (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : ∃ r, forAtoms? i atoms = some r ∧ Correct i atoms r := by
  have p := RingGroupedGeometry.physical coordinates
  obtain ⟨r,h⟩ := RingRetainedUnitPass.collect (row? (RingGroupedPublication.state i)) atoms (fun a _ => by
    obtain ⟨v,h⟩ := Option.isSome_iff_exists.mp (RingGroupedPublication.complete p (origin i a))
    exact ⟨(a.val,v),by simp [row?,h]⟩)
  exact ⟨r,h,(correct_iff i coordinates atoms r).mp h⟩

theorem correct_unique {i : Input} (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {atoms r s} (l : Correct i atoms r) (t : Correct i atoms s) : r = s :=
  Option.some.inj (((correct_iff i coordinates atoms r).mpr l).symm.trans ((correct_iff i coordinates atoms s).mpr t))

theorem molecular_report (i : Input) (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    ∃ r, report? i = some r ∧ Correct i (centres i) r := total i coordinates _

theorem carbon_report (i : Input) (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    ∃ r, carbonReport? i = some r ∧ Correct i (carbons i) r := total i coordinates _

end TetraStereo.Engine.RingGroupedReport

assert_kernel_only TetraStereo.Engine.RingGroupedReport.correct_iff
assert_kernel_only TetraStereo.Engine.RingGroupedReport.correct_unique
assert_kernel_only TetraStereo.Engine.RingGroupedReport.molecular_report
assert_kernel_only TetraStereo.Engine.RingGroupedReport.carbon_report

namespace TetraStereo.Engine.RingGroupedReport.Source
open OneCenter
open RingActivePairReport (Slot Matrix four? four_at matrix?)
open RingNestedActivePair (Reader Frame Labels)
open RingGroupedCentre (Arms cursor arms?)
open RingRetainedStereoDecision (Reads ArmProfile)
open RingGroupedPublication (Local Molecular)
open RingActiveDistanceSchedule (View Visible frozen)

private theorem four_of {α : Type} {g : Slot → Option α} {p : Slot → α}
    (atSlot : ∀ k, g k = some (p k)) : four? g = some p := by
  obtain ⟨w,hw⟩ := Option.isSome_iff_exists.mp (RingActivePairReport.four_full g (fun k => by rw [atSlot]; rfl))
  have eqn : w = p := funext fun k => Option.some.inj ((four_at hw k).symm.trans (atSlot k))
  exact eqn ▸ hw

private theorem frame_eq {i f} (fr : Frame i f) : RingNestedActivePair.frame? i f = some fr := by
  rcases fr with ⟨c,h,four,ids,read,physical⟩
  simp [RingNestedActivePair.frame?,Option.attach_eq_some _ ⟨c,h⟩,four,Option.attach_eq_some _ ⟨ids,read⟩,physical]

private theorem arms_eq {i f fr read} (a : @Arms i f fr read) : arms? fr read = some a := by
  rcases a with ⟨p,h,s⟩
  simp [arms?,Option.attach_eq_some _ ⟨p,four_of h⟩]

private theorem matrix_zero {reader m} (hm : matrix? reader = some m) : ∀ k, m.get k k = (0,0) := by
  unfold matrix? at hm
  obtain ⟨⟨g,h⟩,_,out⟩ := Option.bind_eq_some_iff.mp hm
  obtain rfl := Option.some.inj out
  intro k
  have atK := four_at (four_at h k) k
  exact (by simpa using atK.symm : g k k = (0,0))

private theorem matrix_eq {reader} (m : Matrix reader) (diag : ∀ k, m.get k k = (0,0)) :
    matrix? reader = some m := by
  rcases m with ⟨get,found⟩
  let e := fun (a b : Slot) => if a = b then some (0,0) else reader a b
  have all (a b : Slot) : e a b = some (get a b) := by
    by_cases eq : a = b
    · subst b; exact (if_pos rfl).trans (congrArg some (diag a)).symm
    · exact (if_neg eq).trans (found a b eq)
  have hit := four_of (fun a => four_of (all a))
  simp [matrix?,e,Option.attach_eq_some _ ⟨get,hit⟩]

private def fromReadings {i f read} (fr : Frame i f) (p : Slot → ArmProfile)
    (h : ∀ k, Reads i read false (cursor fr k) (p k)) : Arms fr read :=
  ⟨p,fun k => (RingGroupedStereo.arm_iff_reads _ (RingGroupedCentre.valid fr k) _).mpr (h k),h⟩

/-- Local witnesses use the four original directions, independently supplied rule
derivations, the twelve off-diagonal comparisons, and every eligible trial. -/
inductive SourceLocal (i : LocalizedChemicalRing.Input) (f : RingActivePairs.Site i) (read : Reader i) :
    Option Labels → Prop where
  | absent (missing : i.certified.localizedOccurrenceDescriptorCenter? f = none) : SourceLocal i f read none
  | centre (fr : Frame i f) (p : Slot → ArmProfile) (laws : ∀ k, Reads i read false (cursor fr k) (p k))
      (m : Matrix (fromReadings fr p laws).edge) (diag : ∀ k, m.get k k = (0,0))
      (d : RingGroupedTrials.Decision (fromReadings fr p laws) m) : SourceLocal i f read d.letters

theorem source_local_iff {i f read v} : SourceLocal i f read v ↔ Nonempty (Local i f read v) := by
  constructor
  · intro localRule
    cases localRule with
    | absent missing => exact ⟨.absent missing⟩
    | centre fr p h m diag d => exact ⟨.centre fr _ m d (frame_eq fr) (arms_eq _) (matrix_eq m diag)⟩
  · rintro ⟨localRule⟩
    cases localRule with
    | absent missing => exact .absent missing
    | centre fr a m d _ _ hm =>
      cases a with
      | mk p h s => exact .centre fr p s m (matrix_zero hm) d

/-- Visible deeper occurrences supply their own readings in the same frozen-reference
procedure. A local witness can reconstruct every intermediate frame, profile and matrix. -/
inductive SourceTree (i : LocalizedChemicalRing.Input) : RingActivePairs.Site i → Option Labels → Prop where
  | step {q v} (before : View i) (localRule : SourceLocal i q (frozen before q) v)
      (covered : ∀ t, Visible q t → (before t).isSome = true)
      (deeper : ∀ t, Visible q t → ∀ w, before t = some w → SourceTree i t w) : SourceTree i q v

theorem source_tree_iff {i q v} : SourceTree i q v ↔ Molecular i q v := by
  constructor
  · intro t
    induction t with
    | step before loc covered _ ih => exact .step before (source_local_iff.mp loc) covered ih
  · intro t
    induction t with
    | step before loc covered _ ih => exact .step before (source_local_iff.mpr loc) covered ih

/-- Exact report membership from the recursive witnesses. The comparison rules,
promotion threshold and frozen publication policy are those of the grouped evaluator. -/
theorem report_iff {i : LocalizedChemicalRing.Input} (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (r : RingGroupedReport.Report) :
    RingGroupedReport.forAtoms? i atoms = some r ↔
      List.Forall₂ (fun a row => row.1 = a.val ∧ SourceTree i (RingGroupedReport.origin i a) row.2) atoms r := by
  rw [RingGroupedReport.correct_iff i coord]
  constructor
  · intro h
    apply h.imp
    intro a row pair
    exact ⟨pair.1,source_tree_iff.mpr pair.2⟩
  · intro h
    apply h.imp
    intro a row pair
    exact ⟨pair.1,source_tree_iff.mp pair.2⟩

end TetraStereo.Engine.RingGroupedReport.Source

assert_kernel_only TetraStereo.Engine.RingGroupedReport.Source.report_iff
