import TetraStereo.Engine.RingLigandExchange
import TetraStereo.Engine.RingStoreDecision





set_option autoImplicit false
namespace TetraStereo.Engine.RingExchangeStore
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Rule View height frozen)
open RingNestedActivePair (Frame frame?)
open RingPyramidalPublication (publish focusP)
open RingGlobalComparison (Called prior)
open RingStoreDecision (candidateRows firstDifference?)
open RingLigandExchange (PerNomination)

abbrev Selector (i : Input) := Site i → View i → Bool

/-- Only calls on the reachable public reader need a certificate. -/
def Certified {i : Input} (select : Selector i) : Prop :=
  ∀ f, let read := frozen (RingChemicalGraphProof.state i) f
       select f read = true → focusP i f = none ∧ ∃ fr : Frame i f, PerNomination fr read

/-- A covering family of exchanges on the public frozen reader certifies the selector. -/
theorem certified_of_covered {i : Input} {select : Selector i}
    (evidence : ∀ f, let read := frozen (RingChemicalGraphProof.state i) f
        select f read = true → focusP i f = none ∧ ∃ fr : Frame i f, RingLigandExchange.Covered fr read) :
    Certified select := by
  intro f read hit
  obtain ⟨tetra, fr, cover⟩ := evidence f hit
  exact ⟨tetra, fr, RingLigandExchange.perNomination_of_covered cover⟩

def rule {i : Input} (select : Selector i) : Rule i := fun f read =>
  if select f read then some none else publish i f read

/-- The selected sites are completed refusals when reached on the public reader. -/
def Refuses {i : Input} (select : Selector i) : Prop :=
  ∀ f, let read := frozen (RingChemicalGraphProof.state i) f
       select f read = true → publish i f read = some none

theorem Certified.refuses {i : Input} {select : Selector i}
    (cert : Certified select) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    Refuses select := by
  intro f read hit
  obtain ⟨tetra,fr,ex⟩ := cert f hit
  exact RingLigandExchange.publish_refusal fr geom tetra (RingChemicalGraphProof.ready geom f) ex

private theorem called_exact {i : Input} {select : Selector i} (sound : Refuses select)
    {r : i.certified.Atom} {n : Nat} {f : Site i} (call : Called i r n f) :
    rule select f (prior i r n) = publish i f (prior i r n) := by
  rw [RingGlobalComparison.prior_exact call]
  unfold rule
  split
  · exact (sound f ‹_›).symm
  · rfl

theorem stores_of_refuses {i : Input} {select : Selector i} (sound : Refuses select)
    (r : i.certified.Atom) :
    ∀ k ≤ height i + 1, candidateRows (rule select) r k = RingSphereStore.rows i r k := by
  apply (RingStoreDecision.trajectory_iff _ _ _).mp
  cases hit : firstDifference? (rule select) r (height i + 1) with
  | none => rfl
  | some pair =>
    obtain ⟨n,f⟩ := pair
    obtain ⟨lt,mem,_,diff⟩ := RingStoreDecision.firstDifference_some _ _ hit
    exact (diff (called_exact sound (Or.inl ⟨lt,mem⟩))).elim

/-- Every addressed row agrees throughout the independently executed trajectory. -/
theorem stores {i : Input} {select : Selector i}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (cert : Certified select)
    (r : i.certified.Atom) :
    ∀ k ≤ height i + 1, candidateRows (rule select) r k = RingSphereStore.rows i r k :=
  stores_of_refuses (cert.refuses geom) r

def root {i : Input} (select : Selector i) (r : i.certified.Atom) :=
  rule select (RingGroupedReport.origin i r) (RingSphereQueue.reader r
    (RingSphereQueue.viewOf (candidateRows (rule select) r (height i + 1))))

theorem root_of_refuses {i : Input} {select : Selector i}
    (sound : Refuses select)
    (r : i.certified.Atom) : root select r = RingChemicalGraphProof.root i r := by
  unfold root
  rw [stores_of_refuses sound r _ le_rfl]
  change rule select _ (prior i r (height i + 1)) = _
  rw [called_exact sound (Or.inr ⟨rfl,rfl⟩)]
  unfold prior RingSphereStore.rows
  rw [RingSphereQueue.stored_eq]
  rfl

theorem root_exact {i : Input} {select : Selector i}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (cert : Certified select)
    (r : i.certified.Atom) : root select r = RingChemicalGraphProof.root i r :=
  root_of_refuses (cert.refuses geom) r

/-- A discovery procedure may omit any site. Each proposed renaming is checked
against the retained branches and the current reader for its nomination. -/
abbrev Proposals (i : Input) := (f : Site i) → Frame i f → View i →
  Option (RingActivePairReport.Slot → RingBranchMatching.Proposal)

def checked {i : Input} (propose : Proposals i) : Selector i := fun f read =>
  focusP i f == none && (match frame? i f with
    | none => false
    | some fr => match propose f fr read with
      | none => false
      | some p => RingLigandExchange.check fr read p)

theorem checked_certified {i : Input} (propose : Proposals i) : Certified (checked propose) := by
  intro f read hit
  unfold checked at hit
  obtain ⟨tetra,found⟩ := Bool.and_eq_true_iff.mp hit
  refine ⟨eq_of_beq tetra,?_⟩
  cases frame : frame? i f with
  | none => simp [frame] at found
  | some fr =>
    cases proposal : propose f fr read with
    | none => simp [frame,proposal] at found
    | some p =>
      exact ⟨fr,RingLigandExchange.check_sound fr read p (by simpa [frame,proposal] using found)⟩

def report (propose : (i : Input) → Proposals i) (i : Input) (atoms : List i.certified.Atom) :
    Option RingGroupedReport.Report :=
  atoms.mapM fun r => (root (checked (propose i)) r).map fun labels => (r.val,labels)



theorem raw_exact (propose : (i : Input) → Proposals i) :
    RingRawComparisonLift.fromRaw (report propose) = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms geom
  unfold report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r _
  rw [root_exact geom (checked_certified _) r]
  rfl

end TetraStereo.Engine.RingExchangeStore

assert_kernel_only TetraStereo.Engine.RingExchangeStore.stores
assert_kernel_only TetraStereo.Engine.RingExchangeStore.root_exact
assert_kernel_only TetraStereo.Engine.RingExchangeStore.checked_certified
assert_kernel_only TetraStereo.Engine.RingExchangeStore.raw_exact
