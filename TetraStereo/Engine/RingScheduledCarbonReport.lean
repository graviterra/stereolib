import TetraStereo.Engine.RingActiveCarbonReport
import TetraStereo.Engine.RingMolecularSchedule

set_option autoImplicit false

namespace TetraStereo.Engine.RingScheduledCarbonReport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)

def AtRoot {i : Input} (atom : Nat) (q : Site i) : Prop :=
  q.val.root.val = atom ∧ q.val.address = [] ∧ q.val.node.current? = some q.val.root

instance {i atom q} : Decidable (@AtRoot i atom q) := by unfold AtRoot; infer_instance

/-- An original root, recognized as this exact tetrahedral center, with a resolved
two-geometry assignment or a proved absence at the recognized center. -/
structure Scheduled (i : Input) (atom : Nat) where
  site : Site i
  origin : AtRoot atom site
  center : i.certified.TetrahedralCenter
  recognized : i.certified.localizedOccurrenceDescriptorCenter? site = some center
  same : center.val = site.val.root
  letters : Option RingNestedActivePair.Labels
  published : RingMolecularSchedule.atRoot i site.val.root site = some letters

theorem Scheduled.derived {i atom} (s : Scheduled i atom) :
    RingMolecularSchedule.Derivation i s.site s.letters :=
  RingMolecularSchedule.derivation s.site rfl s.published

theorem Scheduled.mirror {i atom} (s : Scheduled i atom) :
    s.letters.all RingNestedActivePair.consistent = true := by
  cases h : s.letters with
  | none => rfl
  | some v => exact RingMolecularSchedule.mirror_label rfl (s.published.trans (congrArg some h))

theorem Scheduled.refusal {i atom} (s : Scheduled i atom) (noneAt : s.letters = none) :
    Nonempty (RingNestedActivePair.Refusal i s.site
      (RingNestedActivePair.masked s.site (RingMolecularSchedule.atRoot i s.site.val.root))) := by
  have no := (RingMolecularSchedule.structural_absence_iff (q := s.site) rfl).mp
    (s.published.trans (congrArg some noneAt))
  rcases no with absent | ⟨_,hit⟩
  · exact (absent s.center ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp s.recognized)).elim
  · obtain ⟨w,_⟩ := hit
    exact ⟨w⟩

private def at? (i : Input) (atom : Nat) (q : Site i) : Option (Scheduled i atom) := do
  if h : AtRoot atom q then
    let ⟨c,hc⟩ ← (i.certified.localizedOccurrenceDescriptorCenter? q).attach
    if eqv : c.val = q.val.root then
      let ⟨v,hv⟩ ← (RingMolecularSchedule.atRoot i q.val.root q).attach
      return ⟨q,h,c,hc,eqv,v,hv⟩
  none

def scheduled? (i : Input) (atom : Nat) : Option (Scheduled i atom) :=
  (RingActiveDistanceSchedule.sites i).findSome? (at? i atom)

theorem scheduled_iff (i : Input) (atom : Nat) :
    (scheduled? i atom).isSome = true ↔ Nonempty (Scheduled i atom) := by
  constructor
  · intro h
    exact ⟨(scheduled? i atom).get h⟩
  · rintro ⟨s⟩
    apply List.findSome?_isSome_iff.mpr
    refine ⟨s.site,List.mem_attach ..,?_⟩
    have center := Option.attach_eq_some _ ⟨s.center,s.recognized⟩
    have found := Option.attach_eq_some _ ⟨s.letters,s.published⟩
    simp [at?,s.origin,center,s.same,found]

private def resolved? (i : Input) (atom : Nat) : Option (Scheduled i atom) := do
  guard ((i.molecule.atoms[atom]?).any fun a => a.element == .C)
  scheduled? i atom

inductive Row (i : Input) (d atom : Nat) where
  | previous (r : RingActiveCarbonReport.Row i d atom) (found : RingActiveCarbonReport.carbon? i d atom = some r)
  | scheduled (s : Scheduled i atom)

def Row.label {i d atom} : Row i d atom → Option LocalizedAuxiliaryLabel
  | .previous r _ => r.label
  | .scheduled s => s.letters.map Prod.fst

/-- Prefer a resolved original-root publication, including a molecular refusal. Earlier
report methods cover additional marked classes when this schedule has an open cell. -/
def carbon? (i : Input) (d atom : Nat) : Option (Row i d atom) :=
  match resolved? i atom with
  | some s => some (.scheduled s)
  | none => (RingActiveCarbonReport.carbon? i d atom).attach.map (fun r => .previous r.val r.property)

theorem scheduled_priority {i d atom} {s : Scheduled i atom}
    (carbon : (i.molecule.atoms[atom]?).any (fun a => a.element == .C) = true)
    (found : scheduled? i atom = some s) : carbon? i d atom = some (.scheduled s) := by
  simp [carbon?,resolved?,carbon,found]

theorem preserves {i d atom r} (found : RingActiveCarbonReport.carbon? i d atom = some r)
    (agree : ∀ s, scheduled? i atom = some s → s.letters.map Prod.fst = r.label) :
    (carbon? i d atom).map Row.label = some r.label := by
  cases h : resolved? i atom with
  | none => simp [carbon?,h,Option.attach_eq_some _ ⟨r,found⟩,Row.label]
  | some s =>
    have issued : scheduled? i atom = some s := by
      cases c : (i.molecule.atoms[atom]?).any (fun a => a.element == .C) with
      | false => simp [resolved?,c] at h
      | true => simpa [resolved?,c] using h
    simp [carbon?,h,Row.label,agree s issued]

theorem carbon_isSome_iff (i : Input) (d atom : Nat) (member : atom ∈ RingCarbonReport.carbons i.molecule) :
    (carbon? i d atom).isSome = true ↔ (RingActiveCarbonReport.carbon? i d atom).isSome = true ∨
      Nonempty (Scheduled i atom) := by
  rw [← scheduled_iff]
  have raw := (RingCarbonReport.mem_carbons.mp member).2
  cases h : scheduled? i atom <;> simp [carbon?,resolved?,raw,h]

abbrev Report (i : Input) (d : Nat) := List ((atom : Nat) × Row i d atom)

def report? (i : Input) (d : Nat) : Option (Report i d) :=
  (RingCarbonReport.carbons i.molecule).mapM fun atom => (carbon? i d atom).map (Sigma.mk atom)

def labels {i d} (r : Report i d) := r.map fun row => (row.1,row.2.label)

theorem report_projection (i : Input) (depth : Nat) :
    (report? i depth).map labels = (RingCarbonReport.carbons i.molecule).mapM
      (fun root => (carbon? i depth root).map (fun row => (root,row.label))) := by
  unfold report?
  generalize RingCarbonReport.carbons i.molecule = roots
  induction roots with
  | nil => rfl
  | cons a as ih =>
    rw [List.mapM_cons,List.mapM_cons]
    cases head : carbon? i depth a <;>
      cases tail : as.mapM (m := Option) (fun root => (carbon? i depth root).map (Sigma.mk root)) <;>
      simp [tail,labels] at ih ⊢ <;> simp [← ih]

/-- When overlapping original-root and earlier verdicts agree, a previously complete
report has the same ordered projection, including every refusal. -/
theorem preserves_report {i d old} (found : RingActiveCarbonReport.report? i d = some old)
    (agree : ∀ atom r s, RingActiveCarbonReport.carbon? i d atom = some r → scheduled? i atom = some s →
      s.letters.map Prod.fst = r.label) :
    (report? i d).map labels = some (RingActiveCarbonReport.labels old) := by
  have step (j : Nat) {x : Nat × Option LocalizedAuxiliaryLabel}
      (hit : (RingActiveCarbonReport.carbon? i d j).map (fun row => (j,row.label)) = some x) :
      (carbon? i d j).map (fun row => (j,row.label)) = some x := by
    obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp hit
    obtain ⟨a,ha,eqn⟩ := Option.map_eq_some_iff.mp (preserves hv (fun s hs => agree j v s hv hs))
    simp [ha,eqn]
  have go (js : List Nat) (xs : List (Nat × Option LocalizedAuxiliaryLabel))
      (hit : js.mapM (fun j => (RingActiveCarbonReport.carbon? i d j).map (fun row => (j,row.label))) = some xs) :
      js.mapM (fun j => (carbon? i d j).map (fun row => (j,row.label))) = some xs := by
    induction js generalizing xs with
    | nil => exact hit
    | cons j js ih =>
      rw [List.mapM_cons] at hit ⊢
      obtain ⟨x,hx,rest⟩ := Option.bind_eq_some_iff.mp hit
      obtain ⟨tail,ht,ret⟩ := Option.bind_eq_some_iff.mp rest
      obtain rfl := Option.some.inj ret
      simp [step j hx,ih _ ht]
  rw [report_projection]
  exact go _ _ (by rw [← RingActiveCarbonReport.report_projection,found]; rfl)

theorem report_isSome_iff (i : Input) (d : Nat) :
    (report? i d).isSome = true ↔ ∀ root ∈ RingCarbonReport.carbons i.molecule,
      (RingActiveCarbonReport.carbon? i d root).isSome = true ∨ Nonempty (Scheduled i root) := by
  have total {α β : Type} (f : α → Option β) (xs : List α) :
      (xs.mapM f).isSome = true ↔ ∀ x ∈ xs, (f x).isSome = true := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.mapM_cons,List.forall_mem_cons]
      cases h : f x <;> cases t : xs.mapM f <;> simp_all
  unfold report?
  rw [total]
  apply forall_congr'
  intro root
  apply forall_congr'
  intro mem
  simpa using carbon_isSome_iff i d root mem

theorem inventory {i d r} (found : report? i d = some r) :
    r.map Sigma.fst = RingCarbonReport.carbons i.molecule := by
  have go (xs : List Nat) (rows : Report i d)
      (compiled : xs.mapM (m := Option) (fun j => (carbon? i d j).map (Sigma.mk j)) = some rows) :
      rows.map Sigma.fst = xs := by
    induction xs generalizing rows with
    | nil => simpa using compiled.symm
    | cons j js ih =>
      rw [List.mapM_cons] at compiled
      cases head : carbon? i d j <;>
        cases rest : js.mapM (m := Option) (fun k => (carbon? i d k).map (Sigma.mk k)) <;>
        simp [head,rest] at compiled
      subst rows
      simp [ih _ rest]
  exact go _ _ found

/-- Every projected row has its earlier report evidence or a finite derivation at the
original root. A derived assignment records both geometries and a derived refusal records
its molecular reason. -/
theorem evidence {i d} (r : Report i d) {atom letter} (listed : (atom,letter) ∈ labels r) :
    (∃ prev : RingActiveCarbonReport.Row i d atom, RingActiveCarbonReport.carbon? i d atom = some prev ∧
        letter = prev.label) ∨
    (∃ s : Scheduled i atom, letter = s.letters.map Prod.fst ∧ RingMolecularSchedule.Derivation i s.site s.letters ∧
        s.letters.all RingNestedActivePair.consistent = true) := by
  obtain ⟨⟨j,row⟩,_,eqn⟩ := List.mem_map.mp listed
  obtain rfl : j = atom := congrArg Prod.fst eqn
  have lab := congrArg Prod.snd eqn
  cases row with
  | previous v found => exact Or.inl ⟨v,found,lab.symm⟩
  | scheduled s => exact Or.inr ⟨s,lab.symm,s.derived,s.mirror⟩

theorem refusal_evidence {i d} (r : Report i d) {atom} (listed : (atom,none) ∈ labels r) :
    (∃ p : RingActiveCarbonReport.Row i d atom, RingActiveCarbonReport.carbon? i d atom = some p ∧ p.label = none) ∨
    (∃ s : Scheduled i atom, s.letters = none ∧ Nonempty (RingNestedActivePair.Refusal i s.site
      (RingNestedActivePair.masked s.site (RingMolecularSchedule.atRoot i s.site.val.root)))) := by
  rcases evidence r listed with ⟨p,found,absent⟩ | ⟨s,no,_⟩
  · exact Or.inl ⟨p,found,absent.symm⟩
  · have h : s.letters = none := Option.map_eq_none_iff.mp no.symm
    exact Or.inr ⟨s,h,s.refusal h⟩

end TetraStereo.Engine.RingScheduledCarbonReport

assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.Scheduled.derived
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.Scheduled.mirror
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.scheduled_iff
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.preserves
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.carbon_isSome_iff
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.report_isSome_iff
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.report_projection
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.inventory
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.evidence
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.refusal_evidence
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.Scheduled.refusal

assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.preserves_report

assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.scheduled_priority
