import TetraStereo.Engine.RingMolecularSilentTie
import TetraStereo.Engine.RingSingleTieCompletion

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereSingleTieRefusal
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame masked)
open RingActivePairReport (Slot Matrix)
open RingRetainedChemicalPreorder (orderWord keyFor)
open RingRetainedChemicalTrace (compareAt?)
open RingSingleTieCompletion (unitScore)
open RingSphereCoverage (NoVisibleCenter)

def key {i f} (fr : Frame i f) (s : Slot) := orderWord (keyFor (fr.direction s))
def state {i : Input} (f : Site i) := RingSpherePublication.atRoot i f.val.root

/-- The original carrier determines which of the four slots share a full
constitutional key. Only the directions actually in that pair require silence. -/
def OnePair {i f} (fr : Frame i f) (a b : Slot) :=
  ∀ x y : Slot, x ≠ y → (compare (key fr x) (key fr y) = .eq ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a))

theorem values {i f} (fr : Frame i f) {a b : Slot} (one : OnePair fr a b)
    (left : NoVisibleCenter i f ⟨(fr.direction a).val,some f⟩)
    (right : NoVisibleCenter i f ⟨(fr.direction b).val,some f⟩) (x y : Slot) (ne : x ≠ y) :
    let s := unitScore (compare (key fr x) (key fr y))
    RingSpherePublication.edges fr (masked f (state f)) x y = some (s,s) := by
  have cmp := (RingRetainedChemicalPreorder.table_source (fr.direction x) (fr.direction y) (fr.incident ne)).trans
    (RingRetainedChemicalPreorder.table_order ..)
  obtain ⟨t,prior,order⟩ := Option.map_eq_some_iff.mp cmp
  change cipTraceOutcome t = compare (key fr x) (key fr y) at order
  dsimp only
  cases result : compare (key fr x) (key fr y) with
  | eq =>
    have tied := order.trans result
    rcases (one x y ne).mp result with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact RingSphereCoverage.structural_edge prior tied left right
    · exact RingSphereCoverage.structural_edge prior tied right left
  | lt | gt =>
    apply RingSpherePriority.preserves
    apply RingProximalUnit.preserves
    have strict := order.trans result
    change compareAt? i f (fr.arm x).occurrence (fr.arm y).occurrence = some t at prior
    simp only [RingNestedActivePair.edge?,Option.attach_eq_some _ ⟨_,prior⟩,Option.bind_eq_bind,Option.bind_some]
    split <;> rename_i h <;> first | rfl | exact nomatch strict.symm.trans h

/-- The molecular graph assumptions construct all twelve signed comparisons,
their coherent matrix, and a refusal certificate excluding any marked trial. -/
theorem complete {i f} (fr : Frame i f) {a b : Slot} (ab : a < b) (one : OnePair fr a b)
    (left : NoVisibleCenter i f ⟨(fr.direction a).val,some f⟩)
    (right : NoVisibleCenter i f ⟨(fr.direction b).val,some f⟩) :
    let r := RingSpherePublication.edges fr (masked f (state f))
    ∃ m : Matrix r, RingActivePairReport.matrix? r = some m ∧ RingOrdinaryPairRefusal.Valid m a b ∧
      ∃ c : RingOrdinaryPairRefusal.Certificate m, RingOrdinaryPairRefusal.find? m = some c :=
  RingSingleTieCompletion.complete (key fr) _ ab one (values fr one left right)

/-- A previously unresolved site in the distance schedule becomes a
certified absence under the graph-defined single-pair condition. -/
theorem publishes {i : Input} {f : Site i} {fr : Frame i f} {a b : Slot}
    (frame : RingNestedActivePair.frame? i f = some fr) (ab : a < b) (one : OnePair fr a b)
    (left : NoVisibleCenter i f ⟨(fr.direction a).val,some f⟩)
    (right : NoVisibleCenter i f ⟨(fr.direction b).val,some f⟩)
    (previous : RingClosedGroupTie.publish? i f (RingActiveDistanceSchedule.frozen (state f) f) = none) :
    state f f = some none := by
  obtain ⟨m,hm,_,c,hc⟩ := complete fr ab one left right
  have masks : masked f (RingActiveDistanceSchedule.frozen (state f) f) = masked f (state f) := by
    apply RingNestedActivePair.masked_congr
    intro t vis
    simp [RingActiveDistanceSchedule.frozen,RingActiveDistanceSchedule.distance,vis.1,vis.2.1,vis.2.2]
  change RingSpherePublication.atRoot i f.val.root f = some none
  rw [RingSpherePublication.atRoot_eq rfl]
  have lifted : ∃ n : Matrix (RingSpherePublication.edges fr (masked f (RingActiveDistanceSchedule.frozen (state f) f))),
      RingActivePairReport.matrix? _ = some n ∧ ∃ d : RingOrdinaryPairRefusal.Certificate n,
        RingOrdinaryPairRefusal.find? n = some d := by
    rw [masks]
    exact ⟨m,hm,c,hc⟩
  obtain ⟨n,hn,d,hd⟩ := lifted
  exact RingSpherePublication.publish_of_ordinary previous frame hn hd

/-- Every such frame has a determined scheduled cell, including when an
earlier publisher has already decided it using this same frozen state. -/
theorem covered {i : Input} {f : Site i} {fr : Frame i f} {a b : Slot}
    (frame : RingNestedActivePair.frame? i f = some fr) (ab : a < b) (one : OnePair fr a b)
    (left : NoVisibleCenter i f ⟨(fr.direction a).val,some f⟩)
    (right : NoVisibleCenter i f ⟨(fr.direction b).val,some f⟩) : (state f f).isSome = true := by
  cases old : RingClosedGroupTie.publish? i f (RingActiveDistanceSchedule.frozen (state f) f) with
  | none => rw [publishes frame ab one left right old]; rfl
  | some v =>
    have found := RingSpherePublication.preserves old
    change (RingSpherePublication.atRoot i f.val.root f).isSome = true
    exact Option.isSome_iff_exists.mpr ⟨v,(RingSpherePublication.atRoot_eq rfl).trans found⟩

end TetraStereo.Engine.RingSphereSingleTieRefusal

assert_kernel_only TetraStereo.Engine.RingSphereSingleTieRefusal.values
assert_kernel_only TetraStereo.Engine.RingSphereSingleTieRefusal.complete
assert_kernel_only TetraStereo.Engine.RingSphereSingleTieRefusal.publishes
assert_kernel_only TetraStereo.Engine.RingSphereSingleTieRefusal.covered
