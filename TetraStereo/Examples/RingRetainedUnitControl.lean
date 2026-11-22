import TetraStereo.Examples.RingTiedSiblingPublication
import TetraStereo.Engine.RingSpherePriority

set_option autoImplicit false

namespace TetraStereo.Examples.RingRetainedUnitControl
open OneCenter Engine
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader Labels)

private def chiral (s : RS) : Labels := (.chiral s,.chiral s.swap)

private def marked {i : LocalizedChemicalRing.Input} (labels : List (List Nat × Labels)) : Reader i :=
  fun q => some (labels.lookup (q.val.node.history.map Fin.val))

private def expect (i : LocalizedChemicalRing.Input) (f a b : Site i) (r : Reader i)
    (rule : Option RingRetainedStereoDecision.Rule) (k m : Int) : IO Unit := do
  let got := RingGroupedStereo.comparison? i f a b r
  let wanted := some (RingRetainedStereoDecision.Result.mk rule k,RingRetainedStereoDecision.Result.mk rule m)
  unless got == wanted do throw (IO.userError s!"expected {repr wanted}, obtained {repr got}")

/-- Controlled frozen publications on the 31-atom ring fixture. The only
uppercase units in the two arms are on opposite sides of the Br/Cl branch
comparison. All other occurrences have a known absence in this reader. -/
private def view {i : LocalizedChemicalRing.Input} (q : Site i) : Option (Option Labels) :=
  if [[4,3,0,1],[12,5,0,1]].contains (q.val.node.history.map Fin.val) then
    some (some (.chiral .R,.chiral .S)) else some none

private def check (i : LocalizedChemicalRing.Input) (root : i.certified.Atom) (equalChildren : Bool) : IO Unit := do
  let sites := (RingActiveDistanceSchedule.sites i).filter fun q =>
    q.val.root == root && q.val.node.provenance == .realAtom
  let get (path : List Nat) : IO (Site i) := do
    let some q := sites.find? (fun q => q.val.node.history.map Fin.val == path)
      | throw (IO.userError s!"missing occurrence {path}")
    return q
  let f ← get [0,1]
  let a ← get [3,0,1]
  let b ← get [5,0,1]
  if equalChildren then
    let reader (both : Bool) := marked (i := i) [
      ([4,3,0,1],chiral .R),([7,3,0,1],chiral (if both then .S else .R)),
      ([6,5,0,1],chiral .S),([12,5,0,1],chiral .R)]
    expect i f a b (reader false) (some .likePair) 1 1
    expect i f a b (reader true) none 0 0
    return
  let read : Reader i := view
  let arm (q : Site i) : Arm i := ⟨q,some f⟩
  let firstRows (q : Site i) := (RingRetainedUnitPass.atArm i read (arm q)).map fun k => k.word.take 3
  unless firstRows a == some [[0],[2,0,0],[0,2,0]] && firstRows b == some [[0],[2,0,0],[2,0,0]] do
    throw (IO.userError "unexpected shallow or deep unit rows")
  unless (RingProximalUnit.edge? i f a b read).isNone && (RingSpherePriority.score? i f a b read).isNone do
    throw (IO.userError "the control no longer isolates the grouped comparison")
  unless RingSpherePriority.edge? i f a b read == some (-1,-1) &&
      RingSpherePriority.edge? i f b a read == some (1,1) do
    throw (IO.userError "incorrect signed Rule 4a score in the two directions")

  expect i f a b read (some .unit) (-1) (-1)
  expect i f a b (marked [([3,0,1],chiral .R),([5,0,1],chiral .R),
    ([7,3,0,1],chiral .R),([12,5,0,1],chiral .S)]) (some .likePair) 1 1
  expect i f a b (marked [([3,0,1],(.pseudoasymmetric .r,.pseudoasymmetric .r)),
    ([5,0,1],(.pseudoasymmetric .s,.pseudoasymmetric .s))]) (some .lower) 1 1
  expect i f a b (marked [([3,0,1],chiral .R),([5,0,1],chiral .S)]) (some .fixedPair) 2 (-2)
  expect i f a b (marked []) none 0 0

/-- Replacing both additional terminal fluorines with hydrogen makes the two
Br/Cl/H siblings within each arm constitutionally equal. Mixed hands in that
class require both references on the same ligand. -/
def verify : IO Unit := do
  check (RingTiedSiblingPublication.input false) (RingTiedSiblingPublication.original false) false
  let m := RingTiedSiblingPublication.molecule
  let matched := {m with atoms := (m.atoms.set 27 (.aliphatic .H)).set 30 (.aliphatic .H)}
  let some i := LocalizedChemicalRing.admitRawSpatial? matched (RingTiedSiblingPublication.spatial false)
    | throw (IO.userError "matched Br/Cl/H sibling control failed admission")
  let some root := (List.finRange i.certified.certified.input.molecule.atomCount).find? (fun a => a.val == 1)
    | throw (IO.userError "missing original root")
  check i root true

end TetraStereo.Examples.RingRetainedUnitControl
