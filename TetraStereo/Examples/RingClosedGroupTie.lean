import TetraStereo.Engine.RingClosedGroupTie
import TetraStereo.Examples.RingClosedPairGroup

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace TetraStereo.Examples.RingClosedGroupTie
open OneCenter Engine CertifiedLocalizedCIPInput
open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission
open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- The same 31-atom molecular graph as the strict Rule 4c control, with
two neighbor coordinates exchanged. C3 now has the same lowercase hand as C5,
while their two pairs of earlier-equivalent chiral children remain mixed. -/
abbrev molecule := RingClosedPairGroup.molecule

private def params : List Nat :=
  [0,1,2,3,4,5,6,8,7,9,10,11,12,13,15,14,16,17,18,19,20,21,23,22,24,26,25,27,30,28,29]
private def moment (t : ℚ) : CartesianPoint3 := ⟨t,t*t,t*t*t⟩
def spatial : SpatialConfiguration := ⟨params.map fun n => moment n⟩

def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

theorem admitted : LocalizedChemicalRing.admitRawSpatial? molecule spatial = some input :=
  (Option.some_get _).symm

private def param (a : input.certified.Atom) : Nat := params[a.val]?.getD 0

private theorem point (a : input.certified.Atom) :
    input.certified.spatialPointAt? a = some (moment (param a)) := by
  revert a
  decide +kernel

private theorem param_injective : Function.Injective param := by unfold Function.Injective; decide +kernel

private theorem volume (a b c d : ℚ) :
    CartesianPoint3.orientedVolume (moment a) (moment b) (moment c) (moment d) =
      (d-a)*(a-b)*(a-c)*(b-c)*(b-d)*(c-d) := by
  unfold moment CartesianPoint3.orientedVolume
  ring

theorem calibrated : LocalizedChemicalRing.coordinatesAdmitted input = true := by
  apply decide_eq_true
  intro center
  let lig := (actualCanonicalMolecule input.certified).ligandAtomAt center
  let x (k : Fin 4) : ℚ := param (lig k)
  have distinct (a b : Fin 4) (ne : a ≠ b) : x a ≠ x b := by
    intro eqn
    apply ne
    apply (actualCanonicalMolecule input.certified).ligandAtomAt_injective center
    apply param_injective
    change ((param (lig a) : Nat) : ℚ) = ((param (lig b) : Nat) : ℚ) at eqn
    exact_mod_cast eqn
  apply (centerAdmitted_iff _ _).mpr
  refine ⟨CartesianPoint3.orientedVolume (moment (x 0)) (moment (x 1)) (moment (x 2)) (moment (x 3)),?_,?_⟩
  · simp [coordinateVolume?,point,x,lig]
  · rw [volume]
    repeat' apply mul_ne_zero
    all_goals exact sub_ne_zero.mpr (distinct _ _ (by decide))


def original : input.certified.Atom := ⟨1,by decide +kernel⟩

private def expectedRequest : String := String.intercalate "\n" (["centres-1.0"] ++
  molecule.atoms.map (fun a => s!"a {a.element.atomicNumber} 0 0") ++
  molecule.bonds.map (fun b => s!"b {b.source} {b.target}") ++
  ["f 0 R 1 2 3 5","f 1 R 0 2 17 21","f 3 S 0 4 7 8","f 4 R 3 9 10 11",
   "f 5 R 0 6 12 13","f 6 S 5 14 15 16","f 7 S 3 25 26 27","f 12 R 5 28 29 30",
   "f 17 R 1 18 19 20","f 21 S 1 22 23 24"]) ++ "\n"

def referenceMatrix (direct : Bool) : List Int :=
  let ctxt : Int := if direct then 1 else -1
  [0,-1,ctxt,ctxt, 1,0,1,1, -ctxt,-1,0,0, -ctxt,-1,0,0]

/-- All sixteen entries of both matrices are compared to the pinned source at
both original addresses. The roots' lower-case publications and all four
children's hands come from the molecule's earlier distance-scheduled state. -/
def validate : IO Unit := do
  let i := input
  let request ← IO.ofExcept (CentresRing.request i)
  unless request == expectedRequest do throw (IO.userError s!"different molecular source input: {request}")
  let sites := (RingActiveDistanceSchedule.sites i).filter (fun q => q.val.root == original)
  let get (path : List Nat) : IO (RingActivePairs.Site i) := do
    let some q := sites.find? (fun q => q.val.node.provenance == .realAtom && q.val.node.history.map Fin.val == path) |
      throw (IO.userError s!"original occurrence missing at {path}")
    return q
  let view := RingActiveDistanceSchedule.snapshot (Engine.RingClosedGroupTie.publicationTable i original)
  for path in [[0,1],[0,2,1]] do
    let f ← get path
    let l ← get (3::path)
    let r ← get (5::path)
    let read := RingNestedActivePair.masked f view
    unless read l == some (some (Engine.RingClosedPairGroup.lower .s)) &&
        read r == some (some (Engine.RingClosedPairGroup.lower .s)) do
      throw (IO.userError s!"missing earlier s/s at {path}: {repr (read l,read r)}")
    for (ids,hand) in [([4,3],RS.R),([7,3],.S),([6,5],.S),([12,5],.R)] do
      let q ← get (ids ++ path)
      unless read q == some (some (Engine.RingClosedPairGroup.chiral hand)) do
        throw (IO.userError s!"missing earlier chiral publication at {ids ++ path}: {repr (read q)}")
    unless (Engine.RingClosedGroupTie.edge? i f l r read).isSome &&
        (Engine.RingClosedGroupTie.edge? i f r l read).isSome do
      throw (IO.userError s!"missing closed group tie at {path}")
    let some refusal := Engine.RingClosedGroupTie.refusal? i f read |
      throw (IO.userError s!"missing ordinary one-pair refusal at {path}")
    let fr := refusal.frame
    let m := refusal.matrix
    let tiedAtoms := fr.atoms [refusal.ordinary.a,refusal.ordinary.b]
    unless decide (tiedAtoms.Perm [3,5]) do
      throw (IO.userError s!"refusal uses different tied atoms at {path}: {tiedAtoms}")
    let some slots := ([1,2,3,5] : List Nat).mapM (fun atom =>
      (List.finRange 4).find? fun k => fr.atoms [k] == [atom]) |
      throw (IO.userError s!"unexpected incident ligands at {path}")
    let rows := slots.flatMap fun u => slots.map fun v => m.get u v
    let expected := referenceMatrix (path == [0,1])
    unless rows.map Prod.fst == expected && rows.map Prod.snd == expected do
      throw (IO.userError s!"molecular scores differ at {path}: {repr rows}")
    unless view f == some none do
      throw (IO.userError s!"original path did not publish its proved refusal at {path}: {repr (view f)}")
    IO.println s!"{path}: both roots s, mixed groups tie through both Rule 5 seeds, 32 signed entries, certified absence"
  unless view (← get [1]) == some (some RingNestedPublication.lowerR) do
    throw (IO.userError "missing scheduled original root 1 lowercase r")
  IO.println "both C0 refusals were available to original root C1, which publishes r/r"

end TetraStereo.Examples.RingClosedGroupTie
assert_kernel_only TetraStereo.Examples.RingClosedGroupTie.admitted
assert_kernel_only TetraStereo.Examples.RingClosedGroupTie.calibrated
