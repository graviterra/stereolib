import TetraStereo.Engine.RingOrientation

set_option autoImplicit false

namespace TetraStereo.Engine.RingGeometryCriterion
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Rule Cell View frozen)
open RingNestedActivePair (Frame Reader Labels)
open RingActivePairReport (Slot Matrix)
open RingGroupedCentre (Arms)
open RingChemicalPriority.ReferenceFrame (survivingHand)
attribute [local instance] lexOrd

/-- An unordered pair contributes when its priority reverses on reflection. -/
def reversals {i f fr read} (a : @Arms i f fr read) :=
  LocalizedChemicalRing.ConstitutionalPartition.pairs.countP fun p =>
    (compare (a.key false p.1) (a.key false p.2) == .gt) !=
    (compare (a.key true p.1) (a.key true p.2) == .gt)

theorem reversals_eq {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) :
    reversals a = RingActivePairReport.doubled m := by
  rw [← RingGroupedOrders.doubled_crossings a]
  apply (List.Perm.refl _).countP_congr
  intro p hp
  have ne := ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp hp)
  obtain ⟨z,allowed,got,order⟩ := a.represented p.1 p.2
  have value := Option.some.inj ((m.found _ _ ne).symm.trans got)
  change (_ != _) = (decide (0 < (m.get p.1 p.2).1) != decide (0 < (m.get p.1 p.2).2))
  rw [value,← order false,← order true]
  simp only [RingActivePairs.molecularValues,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with h | h | h | h | h <;> rw [h] <;> decide

/-- One signed volume, the marked and unmarked ligand words, and reflection
of the ordinary comparisons suffice to compute both physical letters. -/
structure Signature where
  balance : Int
  reversingPairs : Nat
  deriving DecidableEq, Repr

def Signature.letters (s : Signature) : Option Labels := (survivingHand s.balance).map fun hand =>
  let reflected := if s.reversingPairs % 2 = 0 then hand.swap else hand
  (RingNestedActivePair.label hand reflected,RingNestedActivePair.label reflected hand)

def signature? (i : Input) (q : Site i) (read : Reader i) : Option Signature := do
  let fr ← RingNestedActivePair.frame? i q
  let a ← RingGroupedCentre.arms? fr read
  return ⟨RingOrientation.baseline fr * RingOrientation.index a,reversals a⟩

def rule (i : Input) : Rule i := fun q read =>
  if i.certified.localizedOccurrenceDescriptorCenter? q = none then some none
  else (signature? i q read).map Signature.letters

/-- Recursing on the geometric criterion supplies its own frozen publications
at every depth, including auxiliaries required inside Rule 6 trials. -/
def state (i : Input) : View i :=
  RingActiveDistanceSchedule.snapshot (RingActiveDistanceSchedule.table (rule i) (RingActiveDistanceSchedule.height i + 1))

theorem state_eq {i : Input} (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    state i = RingGroupedPublication.state i := by
  rw [state,RingActiveDistanceSchedule.snapshot_table]
  symm
  apply RingActiveDistanceSchedule.unique
  intro q
  let read := frozen (RingGroupedPublication.state i) q
  have phys := RingGroupedGeometry.physical coordinates
  have ready := RingGroupedPublication.ready phys q
  obtain ⟨v,issued⟩ := Option.isSome_iff_exists.mp (RingGroupedPublication.complete phys q)
  obtain ⟨loc⟩ := RingGroupedPublication.issued ((RingGroupedPublication.state_eq i q).symm.trans issued)
  rw [issued]
  cases loc with
  | absent no => simp [rule,no]
  | centre fr a m d hf ha hm =>
    have no : i.certified.localizedOccurrenceDescriptorCenter? q ≠ none := by rw [fr.recognized]; simp
    simp only [rule,if_neg no,signature?,hf,Option.bind_eq_bind,Option.bind_some,ha,Option.pure_def,
      Option.map_some,Signature.letters,RingGroupedTrials.Decision.letters,
      RingOrientation.balance_from_geometry d ready,reversals_eq a m]

/-- A single original root contains every dependency of any trial below it. -/
def rootTable (i : Input) (root : i.certified.Atom) : RingActiveDistanceSchedule.Table i :=
  let selected : Rule i := fun q read => if q.val.root = root then rule i q read else none
  RingActiveDistanceSchedule.table selected (RingActiveDistanceSchedule.height i + 1)

def rootState (i : Input) (root : i.certified.Atom) : View i :=
  RingActiveDistanceSchedule.snapshot (rootTable i root)

theorem rootState_exact {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (q : Site i) :
    rootState i root q = if q.val.root = root then RingGroupedPublication.state i q else none := by
  let full := RingActiveDistanceSchedule.evaluate (rule i)
  let slice : View i := fun t => if t.val.root = root then full t else none
  let selected : Rule i := fun t read => if t.val.root = root then rule i t read else none
  have eqn := RingActiveDistanceSchedule.unique selected slice (by
    intro t
    by_cases on : t.val.root = root
    · have same : frozen slice t = frozen full t := by
        funext u
        by_cases h : u.val.root = t.val.root
        · simp only [frozen,if_neg (not_not_intro h),slice,if_pos (h.trans on)]
        · simp only [frozen,if_pos h]
      simp only [selected,slice,if_pos on]
      exact (RingActiveDistanceSchedule.evaluate_eq _ _).trans (congrArg (rule i t) same.symm)
    · simp [slice,selected,on])
  have whole : full = RingGroupedPublication.state i :=
    (RingActiveDistanceSchedule.snapshot_table ..).symm.trans (state_eq coords)
  change RingActiveDistanceSchedule.snapshot (RingActiveDistanceSchedule.table selected _) q = _
  rw [RingActiveDistanceSchedule.snapshot_table]
  change RingActiveDistanceSchedule.evaluate selected q = _
  rw [← eqn]
  simp only [slice,whole]

theorem rootReader_exact {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) :
    frozen (rootState i q.val.root) q = frozen (RingGroupedPublication.state i) q := by
  funext u
  by_cases on : u.val.root = q.val.root
  · simp only [frozen,if_neg (not_not_intro on),rootState_exact coords,if_pos on]
  · simp only [frozen,if_pos on]

theorem Signature.refusal_iff (s : Signature) : s.letters = none ↔ s.balance = 0 := by
  simp only [Signature.letters,Option.map_eq_none_iff,survivingHand]
  split <;> simp_all <;> omega

theorem Signature.descriptor_iff (s : Signature) : s.letters.isSome = true ↔ s.balance ≠ 0 :=
  Option.ne_none_iff_isSome.symm.trans (not_congr s.refusal_iff)

/-- For a recognized occurrence the signed geometric balance is always
defined. Zero is exactly a published refusal, positive and negative balances
give the two possible physical hands. -/
theorem at_centre {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) {c} (recognized : i.certified.localizedOccurrenceDescriptorCenter? q = some c) :
    ∃ s, signature? i q (frozen (state i) q) = some s ∧
      RingGroupedPublication.state i q = some s.letters ∧
      (RingGroupedPublication.state i q = some none ↔ s.balance = 0) := by
  have read := RingGroupedPublication.ready (RingGroupedGeometry.physical coords) q
  obtain ⟨fr,hf,_⟩ := RingGroupedGeometry.physical coords q c recognized
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (RingGroupedCentre.arms_ready fr read)
  rw [state_eq coords]
  let s : Signature := ⟨RingOrientation.baseline fr * RingOrientation.index a,reversals a⟩
  have sig : signature? i q (frozen (RingGroupedPublication.state i) q) = some s := by simp [signature?,hf,ha,s]
  have issued : RingGroupedPublication.state i q = some s.letters := by
    have eqn := RingActiveDistanceSchedule.evaluate_eq (rule i) q
    have same : RingActiveDistanceSchedule.evaluate (rule i) = RingGroupedPublication.state i :=
      (RingActiveDistanceSchedule.snapshot_table ..).symm.trans (state_eq coords)
    rw [same] at eqn
    simpa [rule,recognized,sig] using eqn
  exact ⟨s,sig,issued,by rw [issued,Option.some.injEq,Signature.refusal_iff]⟩

end TetraStereo.Engine.RingGeometryCriterion
assert_kernel_only TetraStereo.Engine.RingGeometryCriterion.state_eq
assert_kernel_only TetraStereo.Engine.RingGeometryCriterion.at_centre
