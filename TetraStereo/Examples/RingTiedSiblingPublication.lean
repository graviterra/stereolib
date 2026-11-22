import TetraStereo.Examples.RingNestedPublication
import TetraStereo.Engine.RingRetainedSiblingOrder

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace TetraStereo.Examples.RingTiedSiblingPublication

open OneCenter Engine CertifiedLocalizedCIPInput
open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

/-- The two arms at C0 each contain competing carbon siblings. Their first
sphere is identical, and their second spheres are Br/Cl/F versus Br/Cl/H.
All four sibling sites have independently oriented tetrahedral geometries. -/
def molecule : RawMolecule :=
  {RingNestedPublication.molecule with
    atoms := ((RingNestedPublication.molecule.atoms.set 7 (.aliphatic .C)).set 12 (.aliphatic .C)) ++
      ([.Br,.Cl,.F,.Br,.Cl,.F] : List Element).map AtomSpec.aliphatic
    bonds := RingNestedPublication.molecule.bonds ++
      ([(7,25),(7,26),(7,27),(12,28),(12,29),(12,30)] : List (Nat × Nat)).map
        (fun (a,b) => ⟨a,b,.single⟩)}

/-- The control exchanges two coordinates at each of C6 and C12, leaving
both parent centers and their constitutional priorities fixed. -/
private def parameters (control : Bool) : List Nat :=
  [0,1,2,3,4,5,6,8,7,9,10,11,12,13] ++ (if control then [14,15] else [15,14]) ++
  [16,17,18,19,20,21,23,22,24,25,26,27,28] ++ (if control then [29,30] else [30,29])
private def moment (t : ℚ) : CartesianPoint3 := ⟨t,t*t,t*t*t⟩
def spatial (control : Bool) : SpatialConfiguration := ⟨(parameters control).map fun n => moment n⟩
def input (control : Bool) := (LocalizedChemicalRing.admitRawSpatial? molecule (spatial control)).get
  (by cases control <;> decide +kernel)

theorem admitted (control : Bool) :
    LocalizedChemicalRing.admitRawSpatial? molecule (spatial control) = some (input control) :=
  (Option.some_get _).symm

private def parameter (control : Bool) (a : (input control).certified.Atom) :=
  (parameters control)[a.val]?.getD 0
private theorem point (control : Bool) (a : (input control).certified.Atom) :
    (input control).certified.spatialPointAt? a = some (moment (parameter control a)) := by
  cases control <;> revert a <;> decide +kernel
private theorem parameters_injective (control : Bool) : Function.Injective (parameter control) := by
  cases control <;> unfold Function.Injective <;> decide +kernel
private theorem volume (a b c d : ℚ) :
    CartesianPoint3.orientedVolume (moment a) (moment b) (moment c) (moment d) =
      (d-a)*(a-b)*(a-c)*(b-c)*(b-d)*(c-d) := by
  unfold moment CartesianPoint3.orientedVolume
  ring

theorem calibrated (control : Bool) : LocalizedChemicalRing.coordinatesAdmitted (input control) = true := by
  apply decide_eq_true
  intro center
  let lig := (actualCanonicalMolecule (input control).certified).ligandAtomAt center
  let x (k : Fin 4) : ℚ := parameter control (lig k)
  have distinct (a b : Fin 4) (ne : a ≠ b) : x a ≠ x b := by
    intro eqn
    apply ne
    apply (actualCanonicalMolecule (input control).certified).ligandAtomAt_injective center
    apply parameters_injective control
    change ((parameter control (lig a) : Nat) : ℚ) = ((parameter control (lig b) : Nat) : ℚ) at eqn
    exact_mod_cast eqn
  apply (centerAdmitted_iff _ _).mpr
  refine ⟨CartesianPoint3.orientedVolume (moment (x 0)) (moment (x 1)) (moment (x 2)) (moment (x 3)),?_,?_⟩
  · simp [coordinateVolume?,point,x,lig]
  · rw [volume]
    repeat' apply mul_ne_zero
    all_goals exact sub_ne_zero.mpr (distinct _ _ (by decide))

def original (control : Bool) : (input control).certified.Atom :=
  ⟨1,by cases control <;> decide +kernel⟩

private def expectedRequest (control : Bool) : String := String.intercalate "\n" (["centres-1.0"] ++
  molecule.atoms.map (fun a => s!"a {a.element.atomicNumber} 0 0") ++
  molecule.bonds.map (fun b => s!"b {b.source} {b.target}") ++
  ["f 0 R 1 2 3 5","f 1 R 0 2 17 21","f 3 S 0 4 7 8","f 4 R 3 9 10 11",
   "f 5 R 0 6 12 13",if control then "f 6 R 5 14 15 16" else "f 6 S 5 14 15 16","f 7 R 3 25 26 27",if control then "f 12 R 5 28 29 30" else "f 12 S 5 28 29 30",
   "f 17 R 1 18 19 20","f 21 S 1 22 23 24"]) ++ "\n"

/-- In the order-sensitive control, exchanging the order of the two
same-element children in *both* arms changes the first unlike comparison.
The per-ligand reference in each arm is its leading publication. -/
theorem order_changes_hand :
    RingSeededPairs.localSign? [some .R,some .S,some .R] [some .S,some .S,some .R] = some (-1) ∧
    RingSeededPairs.localSign? [some .R,some .R,some .S] [some .S,some .R,some .S] = some 1 := by
  decide +kernel

private def referenceMatrix (control direct rev : Bool) : List Int :=
  if control then
    let sign : Int := if direct then 1 else -1
    [0,-1,sign,sign, 1,0,1,1, -sign,-1,0,-1, -sign,-1,1,0]
  else RingNestedPublication.pinnedMatrix direct rev

/-- The reference matrices are the pinned release's comparison of every pair at C0,
intercepted when the source evaluates that original occurrence on each geometry. -/
private def validateGeometry (control : Bool) : IO Unit := do
  let i := input control
  let root := original control
  let req ← IO.ofExcept (CentresRing.request i)
  unless req == expectedRequest control do throw (IO.userError s!"tied-sibling source input differs: {req}")
  let sites := (RingActiveDistanceSchedule.sites i).filter fun q => q.val.root == root
  let get (path : List Nat) : IO (RingActivePairs.Site i) := do
    let some q := sites.find? (fun q => q.val.node.provenance == .realAtom && q.val.node.history.map Fin.val == path) |
      throw (IO.userError s!"original occurrence missing for {path}")
    return q
  let view := RingActiveDistanceSchedule.snapshot (RingMolecularSchedule.publicationTable i root)
  for path in [[0,1],[0,2,1]] do
    let focus ← get path
    for (id,order) in [(3,[7,4,8]),(5,[12,6,13])] do
      let q ← get (id :: path)
      let arm : RingActivePairs.Arm i := ⟨q,some focus⟩
      unless (RingActivePairs.children? i arm).isNone do
        throw (IO.userError s!"expected equal atomic numbers at {id :: path}")
      let some ranked := RingRetainedSiblingOrder.children? i arm |
        throw (IO.userError s!"missing constitutional sibling proof at {id :: path}")
      unless ranked.val.mapM (fun c => c.occurrence.val.node.current?.map Fin.val) == some order do
        throw (IO.userError s!"incorrect constitutional order at {id :: path}")
    for (site,hand) in [([3],RS.R),([4,3],.R),([7,3],.S),([5],.S),([6,5],if control then .R else .S),([12,5],if control then .S else .R)] do
      let q ← get (site ++ path)
      unless view q == some (some (.chiral hand,.chiral hand.swap)) do
        throw (IO.userError s!"incorrect earlier publication at {site ++ path}: {repr (view q)}")
    let read := RingNestedActivePair.masked focus view
    let some a := RingNestedActivePair.assign? i focus read |
      throw (IO.userError s!"missing nested assignment at {path}")
    let some slots := ([1,2,3,5] : List Nat).mapM (fun atom =>
      (List.finRange 4).find? fun k => a.frame.atoms [k] == [atom]) |
      throw (IO.userError s!"different physical frame at {path}")
    let rows := slots.flatMap fun k => slots.map fun j => a.matrix.get k j
    let direct := path == [0,1]
    unless rows.map Prod.fst == referenceMatrix control direct false &&
        rows.map Prod.snd == referenceMatrix control direct true do
      throw (IO.userError s!"tied-sibling comparison mismatch at {path}: {repr rows}")
    let expected : RingNestedActivePair.Labels :=
      if control then (.chiral .R,.chiral .S) else RingNestedPublication.lowerS
    unless a.labels == expected && view focus == some (some a.labels) do
      throw (IO.userError s!"wrong nested publication at {path}: {repr a.labels}")
    IO.println s!"control={control}, {path}: two sibling orders, six prior hands, 32 signed comparisons, {repr a.labels}"
  unless view (← get [1]) == some (some RingNestedPublication.lowerR) do
    throw (IO.userError "unexpected original-root assignment")
  IO.println "original carbon 1 publishes (r,r)"

def validate : IO Unit := do
  validateGeometry false
  validateGeometry true

end TetraStereo.Examples.RingTiedSiblingPublication

assert_kernel_only TetraStereo.Examples.RingTiedSiblingPublication.admitted
assert_kernel_only TetraStereo.Examples.RingTiedSiblingPublication.calibrated
assert_kernel_only TetraStereo.Examples.RingTiedSiblingPublication.order_changes_hand
