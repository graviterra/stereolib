import TetraStereo.Engine.RingOrdinaryLigandInventory
import TetraStereo.Engine.RingResidualPairDecision

/-! Recover a scheduled comparison from signed molecular path inventories and the
nominated mark. Equality of these observations is necessary and sufficient,
including for a pair that admits no branch exchange. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingTrialInventoryOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
open RingFullPathTrialReadings (trialKey bitWord markWords?)
open RingResidualPairDecision (Table TableExact)
open RingOrdinaryLigandInventory (Observation observe? assemble)
open RingRetainedChemicalTrace (Word)
open private keys_exact from TetraStereo.Engine.RingFullPathPublication
attribute [local instance] lexOrd

/-- The first component preserves group priorities and counts signed paths in each sphere.
The second component records occurrences of the nominated atom. -/
def observation? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (rev : Bool) (m : Option Slot) (s : Slot) : Option (Observation × Word) := do
  let ordinary ← observe? i r rev (cursor fr s)
  let marks ← markWords? fr r m
  return (ordinary,marks s)

def priority (obs : Observation × Word) := trialKey (assemble obs.1) obs.2

private theorem bit_injective {x y : List Bool} : bitWord x = bitWord y ↔ x = y := by
  constructor
  · intro h
    have inv (bs : List Bool) : (bitWord bs).map (fun w => decide (w = [1])) = bs := by
      induction bs with
      | nil => rfl
      | cons b bs ih => cases b <;> simp_all [bitWord]
    exact (inv x).symm.trans ((congrArg (List.map fun w => decide (w = [1])) h).trans (inv y))
  · rintro rfl; rfl

private theorem key_eq {x y : RingFullPathEligibility.Key} {a b : Word} :
    trialKey x a = trialKey y b ↔ x = y ∧ a = b := by
  cases x; cases y; simp [trialKey,bit_injective,and_assoc]

/-- Both observations exist on every ready frame. Their priorities recover the
direction. Equality of the observations themselves characterizes every surviving tie. -/
theorem pair {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {m : Option Slot} {tab : Table}
    (reported : TableExact fr r rev m tab) (a b : Slot) :
    ∃ x y, observation? fr r rev m a = some x ∧ observation? fr r rev m b = some y ∧
      compare (priority x) (priority y) = tab[a.val][b.val].order ∧
      (tab[a.val][b.val] = .tie ↔ x = y) := by
  obtain ⟨ks,_,only⟩ := keys_exact fr ready rev
  have source := (only ks).mpr rfl
  obtain ⟨ws,hw,wm⟩ := RingFullPathTrialReadings.mark_exact fr ready rev m
  have atSlot (s : Slot) : ∃ x, observe? i r rev (cursor fr s) = some x ∧ assemble x = ks s := by
    obtain ⟨k,hk,sk⟩ := RingFullPathEligibility.key_exact ready rev _ (RingGroupedCentre.valid fr s)
      (fr.direction s).property.1
    rw [← RingOrdinaryLigandInventory.key_exact] at hk
    obtain ⟨x,hx,eq⟩ := Option.map_eq_some_iff.mp hk
    exact ⟨x,hx,eq.trans ((sk _).mp (source s)).symm⟩
  obtain ⟨x,hx,kx⟩ := atSlot a
  obtain ⟨y,hy,ky⟩ := atSlot b
  have order := (reported ks ws source ((wm ws).mpr rfl) a b).2
  have obs := RingOrdinaryLigandInventory.tie_iff ready rev (cursor fr a) (cursor fr b)
    (RingGroupedCentre.valid fr a) (RingGroupedCentre.valid fr b) (fr.direction a).property.1
    (fr.direction b).property.1
  simp only [← RingOrdinaryLigandInventory.key_exact,RingOrdinaryLigandInventory.key?,hx,hy,
    Option.map_some,Option.some.injEq,kx,ky] at obs
  refine ⟨(x,ws a),(y,ws b),by simp [observation?,hx,hw],by simp [observation?,hy,hw],?_,?_⟩
  · simpa [priority,kx,ky] using order
  · have verdict : tab[a.val][b.val] = .tie ↔ tab[a.val][b.val].order = .eq := by
      cases tab[a.val][b.val] <;> simp [RingResidualPairDecision.Verdict.order]
    rw [verdict,← order,Std.compare_eq_eq_iff_eq,key_eq,obs]
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩

/-- At a reached public tetrahedral occurrence no keys, correspondence or
nomination schedule need be supplied. Both molecular observations are extracted
on the actual preceding sphere store. -/
theorem public_pair {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom} {batch : Nat}
    (called : RingGlobalComparison.Called i root batch f) :
    let r := RingGlobalComparison.prior i root batch
    ∃ out, RingResidualPairDecision.atSite? i root batch f = some out ∧
      ∀ t ∈ out, ∀ (rev : Bool) (a b : Slot),
        ∃ x y, observation? fr r rev t.nomination a = some x ∧ observation? fr r rev t.nomination b = some y ∧
          compare (priority x) (priority y) = (t.table rev)[a.val][b.val].order ∧
          ((t.table rev)[a.val][b.val] = .tie ↔ x = y) := by
  dsimp only
  obtain ⟨out,found,spec⟩ := RingResidualPairDecision.public_exact fr geom called
  refine ⟨out,found,?_⟩
  intro t member rev a b
  have ready : RingGroupedStereo.Ready f (RingGlobalComparison.prior i root batch) := by
    rw [RingGlobalComparison.prior_exact called]
    exact RingChemicalGraphProof.ready geom f
  apply pair fr ready _ a b
  cases rev
  · exact (spec.pairs t member).1
  · exact (spec.pairs t member).2

end TetraStereo.Engine.RingTrialInventoryOrder
assert_kernel_only TetraStereo.Engine.RingTrialInventoryOrder.pair
assert_kernel_only TetraStereo.Engine.RingTrialInventoryOrder.public_pair
