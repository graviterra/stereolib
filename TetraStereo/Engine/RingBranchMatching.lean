import TetraStereo.Engine.RingGeometryExchange

set_option autoImplicit false

namespace TetraStereo.Engine.RingBranchMatching
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
open RingNestedActivePair (Frame Reader)
open RingGeometryExchange (Carrier Exchange)
open RingRetainedChemicalTrace (observation?)
open RingGroupedMark (bit)

/-- The finite row list is a proposed correspondence of directed occurrences.
The checker verifies both complete child lists, all primitive observations,
the frozen reader and the selected atom at every listed occurrence. -/
abbrev Rows (i : Input) := List (Arm i × Arm i)

private def edges {i : Input} (q : Arm i) := i.certified.executableLocalizedRerootChildren q

private def checkWith {i f} (fr : Frame i f) (read : Reader i) (s j k : Slot) (rows : Rows i)
    (children : Arm i → List (Arm i)) (correct : ∀ q, children q = edges q) : Option (Exchange fr read s j k) := do
  let domain := rows.map Prod.fst
  let image (q : Arm i) := ((rows.find? (fun r => r.1 == q)).map Prod.snd).getD (cursor fr k)
  let a := RingGroupedTrials.atom fr s
  if start : cursor fr j ∈ domain ∧ image (cursor fr j) = cursor fr k then
    if ok : ∀ q ∈ domain, (∀ t ∈ children q, t ∈ domain) ∧
        ((children q).map image).Perm (children (image q)) ∧
        observation? i q (children q).isEmpty = observation? i (image q) (children (image q)).isEmpty ∧
        read q.occurrence = read (image q).occurrence ∧ bit a q = bit a (image q) then
      let c : Carrier i i := {
        image := image
        domain := (· ∈ domain)
        below := fun q h => by simpa only [correct] using (ok q h).1
        children := fun q h => by simpa only [correct] using (ok q h).2.1
        observation := fun q h => by simpa only [correct] using (ok q h).2.2.1 }
      return ⟨c,start.1,start.2,fun q h => (ok q h).2.2.2.1,fun q h => (ok q h).2.2.2.2⟩
    else none
  else none

/-- The cache is certified on all cursors, so incomplete or reordered proposed
rows cannot cause the search to issue invalid molecular evidence. -/
def check? {i f} (fr : Frame i f) (read : Reader i) (s j k : Slot) (rows : Rows i) : Option (Exchange fr read s j k) :=
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount+1)) f.val.root
  checkWith fr read s j k rows (fun q => (cache.reader.readChildren q).getD []) (fun q => by dsimp only; rw [cache.reader.readChildren_eq]; rfl)

private def sameHistory {i : Input} (rename : Nat → Nat) (q t : Arm i) : Bool :=
  q.occurrence.val.node.provenance == t.occurrence.val.node.provenance &&
    q.occurrence.val.node.history.map (fun v => rename v.val) == t.occurrence.val.node.history.map Fin.val

private def collect {i : Input} (rename : Nat → Nat) (children : Arm i → List (Arm i)) :
    Nat → Arm i → Arm i → Option (Rows i)
  | 0,_,_ => none
  | n+1,q,t => do
    guard (sameHistory rename q t)
    let target := children t
    let sub ← (children q).mapM fun child => do
      let other ← target.find? (sameHistory rename child)
      collect rename children n child other
    return (q,t) :: sub.flatten

/-- A candidate permutation of atom identifiers proposes a branch matching.
The independent checker supplies the proof used by the refusal theorem. -/
def find? {i f} (fr : Frame i f) (read : Reader i) (s j k : Slot) (rename : Nat → Nat) :
    Option (Exchange fr read s j k) := do
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount+1)) f.val.root
  let children (q : Arm i) := (cache.reader.readChildren q).getD []
  let start := cursor fr j
  let rows ← collect rename children (i.certified.localizedRerootCursorBudget start+1) start (cursor fr k)
  checkWith fr read s j k rows children (fun q => by dsimp only [children]; rw [cache.reader.readChildren_eq]; rfl)

structure Proposal where
  left : Slot
  right : Slot
  rename : Nat → Nat

structure Refusal {i f fr read} (a : @RingGroupedCentre.Arms i f fr read) : Prop where
  promoted : 3 ≤ (RingGroupedOrders.marks a).length
  exchanges : ∀ s ∈ RingGroupedOrders.marks a, ∃ j k, j ≠ k ∧ Nonempty (Exchange fr read s j k)

def certify? {i f fr read} (a : @RingGroupedCentre.Arms i f fr read) (propose : Slot → Proposal) :
    Option (PLift (Refusal a)) := do
  if promoted : 3 ≤ (RingGroupedOrders.marks a).length then
    if checked : ∀ s ∈ RingGroupedOrders.marks a, (propose s).left ≠ (propose s).right ∧
        (find? fr read s (propose s).left (propose s).right (propose s).rename).isSome = true then
      return ⟨⟨promoted,fun s hs => ⟨_,_,(checked s hs).1,⟨Option.get _ (checked s hs).2⟩⟩⟩⟩
    else none
  else none

theorem Refusal.forces {i f fr read a m} (r : Refusal a) (d : @RingGroupedTrials.Decision i f fr read a m)
    (ready : RingGroupedStereo.Ready f read) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    d.letters = none := RingGeometryExchange.refuse_of_exchanges d ready coords r.promoted r.exchanges

end TetraStereo.Engine.RingBranchMatching
assert_kernel_only TetraStereo.Engine.RingBranchMatching.find?
assert_kernel_only TetraStereo.Engine.RingBranchMatching.certify?
assert_kernel_only TetraStereo.Engine.RingBranchMatching.Refusal.forces
