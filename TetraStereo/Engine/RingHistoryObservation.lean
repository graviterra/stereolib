import TetraStereo.Engine.RingDuplicateScale
import TetraStereo.Engine.RingActivePairs
import TetraStereo.OneCenter.LocalizedRetainedArmExpansion
import TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback

set_option autoImplicit false

namespace TetraStereo.Engine.RingHistoryObservation
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRetainedConstitution (Cursor)
open RingRetainedChemicalTrace (Observation Key duplicateValue)
open RingActivePairs (Arm)
open private CertifiedLocalizedCIPInput.exists_carrier_ring_step
  CertifiedLocalizedCIPInput.duplicateRootDistance_eq_idxOf from
  TetraStereo.OneCenter.LocalizedRetainedArmExpansion

/-- Observe the physical atom and its parent history. Repetition alone selects
ordinary element mass and the original root-first index for a closure. Neither
provenance nor a stored duplicate index is read. -/
def observeHistory? (i : Input) (history : List i.certified.Atom)
    (terminal : Bool) : Option Observation := do
  let a ← history.head?
  let recd ← i.molecule.atoms[a.val]?
  let z := recd.element.atomicNumber
  guard (z > 0)
  if history.tail.contains a then
    let origin := history.tail.reverse.idxOf a
    guard (terminal && origin ≤ i.molecule.atomCount)
    let mass ← CIPRule2MassData.rule2MassPico? z none
    return ⟨z,duplicateValue i.molecule.atomCount (some origin),mass⟩
  else
    let mass ← CIPRule2MassData.rule2MassPico? z recd.isotope?
    return ⟨z,duplicateValue i.molecule.atomCount none,mass⟩

def observeNode? (i : Input) (node : OfficialCIPNode i.certified.Atom)
    (terminal : Bool) : Option Observation := observeHistory? i node.history terminal

/-- Changing any stored provenance, including its distance, has no effect. -/
theorem provenance_irrel (i : Input) (node : OfficialCIPNode i.certified.Atom)
    (p : OfficialCIPNodeProvenance) (terminal : Bool) :
    observeNode? i {node with provenance := p} terminal = observeNode? i node terminal := rfl

def observation? (i : Input) {d : Nat} (q : Cursor i.certified d) (terminal : Bool) :
    Option Observation := observeNode? i q.occurrence.val.node terminal

/-- The equality includes missing source-table records and either terminal flag,
and does not require validity of the cursor's reroot predecessor. -/
theorem observation_exact (i : Input) {d : Nat} (q : Cursor i.certified d) (terminal : Bool) :
    observation? i q terminal = RingRetainedChemicalTrace.observation? i q terminal := by
  rcases i.certified.carrierOccurrence_provenance_simple_or_ring i.single q.occurrence with real | ⟨distance,ring⟩
  · obtain ⟨nodup,head⟩ := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
      i.certified q.occurrence real
    cases hist : q.occurrence.val.node.history with
    | nil =>
        have current : q.occurrence.val.node.current? = none := by simpa [hist] using head
        simp [observation?,observeNode?,observeHistory?,RingRetainedChemicalTrace.observation?,current,hist]
    | cons a tail =>
        have current : q.occurrence.val.node.current? = some a := by simpa [hist] using head
        have absent : a ∉ tail := (List.nodup_cons.mp (hist ▸ nodup)).1
        simp [observation?,observeNode?,observeHistory?,RingRetainedChemicalTrace.observation?,current,hist,absent,real]
  · obtain ⟨parent,address,current,next,path,nodeEq,_,_,_,seen⟩ :=
      CertifiedLocalizedCIPInput.exists_carrier_ring_step i.certified i.single q.occurrence ring
    have idx := CertifiedLocalizedCIPInput.duplicateRootDistance_eq_idxOf i.certified parent next (List.mem_reverse.mpr seen)
    simp only [observation?,observeNode?,observeHistory?,RingRetainedChemicalTrace.observation?,nodeEq]
    simp [OfficialCIPNode.extend,seen,OfficialCIPNode.childProvenance,idx]

/-- On the admitted carrier, parent-history repetition characterizes ring
closures in both directions. The procedure itself never reads this tag. -/
theorem repeated_iff_ring (i : Input) {d : Nat} (q : Cursor i.certified d) :
    (∃ a, q.occurrence.val.node.history.head? = some a ∧
      a ∈ q.occurrence.val.node.history.tail) ↔
    ∃ origin, q.occurrence.val.node.provenance = .ringDuplicate origin := by
  rcases i.certified.carrierOccurrence_provenance_simple_or_ring i.single q.occurrence with real | ⟨distance,ring⟩
  · have nodup := (LocalizedActualBoundaryObservationReadback.occurrence_history_facts
      i.certified q.occurrence real).1
    cases hist : q.occurrence.val.node.history with
    | nil => simp [real]
    | cons a tail =>
        have absent : a ∉ tail := (List.nodup_cons.mp (hist ▸ nodup)).1
        simp [real,absent]
  · obtain ⟨parent,address,current,next,path,nodeEq,_,_,_,seen⟩ :=
      CertifiedLocalizedCIPInput.exists_carrier_ring_step i.certified i.single q.occurrence ring
    constructor
    · intro _; exact ⟨distance,ring⟩
    · intro _; exact ⟨next,by simp [nodeEq,OfficialCIPNode.extend],by simpa [nodeEq,OfficialCIPNode.extend] using seen⟩

/-- The reconstructed index is exactly the stored origin on every admitted
closure; the equality is a theorem, never an input to reconstruction. -/
theorem origin_exact (i : Input) {d : Nat} (q : Cursor i.certified d) (origin : Nat)
    (ring : q.occurrence.val.node.provenance = .ringDuplicate origin) :
    ∃ a, q.occurrence.val.node.history.head? = some a ∧
      q.occurrence.val.node.history.tail.reverse.idxOf a = origin := by
  obtain ⟨parent,address,current,next,path,nodeEq,_,_,_,seen⟩ :=
    CertifiedLocalizedCIPInput.exists_carrier_ring_step i.certified i.single q.occurrence ring
  have idx := CertifiedLocalizedCIPInput.duplicateRootDistance_eq_idxOf i.certified parent next (List.mem_reverse.mpr seen)
  have eqn : parent.history.reverse.idxOf next = origin := by
    simpa [nodeEq,OfficialCIPNode.extend,OfficialCIPNode.childProvenance,seen,idx] using ring
  exact ⟨next,by simp [nodeEq,OfficialCIPNode.extend],by simpa [nodeEq,OfficialCIPNode.extend] using eqn⟩

/-- Rebuild every layer and sort from the independent observation. -/
def keyAt? (i : Input) {d : Nat} (fuel : Nat) (q : Cursor i.certified d) : Option Key :=
  RingDuplicateScale.build
    (fun c => observation? i c (i.certified.executableLocalizedRerootChildren c).isEmpty)
    i.certified.executableLocalizedRerootChildren fuel q

open private build from TetraStereo.Engine.RingRetainedChemicalTrace

/-- Exact equality at every fuel, including early failure. -/
theorem build_exact (i : Input) {d : Nat} (fuel : Nat) (q : Cursor i.certified d) :
    keyAt? i fuel q =
      build i i.certified.executableLocalizedRerootChildren fuel q := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih =>
      simp only [keyAt?,RingDuplicateScale.build,build]
      have same : RingDuplicateScale.build
          (fun c : Cursor i.certified d => observation? i c
            (i.certified.executableLocalizedRerootChildren c).isEmpty)
          i.certified.executableLocalizedRerootChildren fuel =
          build i i.certified.executableLocalizedRerootChildren fuel := funext ih
      rw [same,observation_exact]

def key? (i : Input) (q : Arm i) : Option Key := keyAt? i (2*(i.certified.certified.input.molecule.atomCount + 1 + 1)+1) q

/-- All arms, including arbitrary original-parent directions and failed reads. -/
theorem keys_exact (i : Input) : key? i = RingRetainedChemicalTrace.key? i := by
  funext q
  exact build_exact i _ q

end TetraStereo.Engine.RingHistoryObservation

assert_kernel_only TetraStereo.Engine.RingHistoryObservation.provenance_irrel
assert_kernel_only TetraStereo.Engine.RingHistoryObservation.observation_exact
assert_kernel_only TetraStereo.Engine.RingHistoryObservation.build_exact
assert_kernel_only TetraStereo.Engine.RingHistoryObservation.keys_exact

assert_kernel_only TetraStereo.Engine.RingHistoryObservation.repeated_iff_ring
assert_kernel_only TetraStereo.Engine.RingHistoryObservation.origin_exact
