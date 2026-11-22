import TetraStereo.Engine.CentresRing
import TetraStereo.Engine.RingActivePairReport
import TetraStereo.Engine.RingStrictConstitution

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace TetraStereo.Examples.RingPairedAuxiliary

open OneCenter Engine LocalizedGenericMarkedRecalculation
open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

/-- The root belongs to an O–C–S triangle and carries two constitutionally
identical, two-center arms. Every H and halogen is bonded explicitly. -/
def molecule : RawMolecule where
  atoms := ([.C,.O,.S,.C,.C,.C,.C,.F,.H,.Br,.Cl,.H,.F,.H,.Br,.Cl,.H] : List Element).map AtomSpec.aliphatic
  bonds := ([(0,1),(1,2),(2,0),(0,3),(3,4),(0,5),(5,6),(3,7),(3,8),(4,9),(4,10),(4,11),
    (5,12),(5,13),(6,14),(6,15),(6,16)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

private def moment (t : ℚ) : CartesianPoint3 := ⟨t,t*t,t*t*t⟩

/-- The control exchanges only the coordinates of Br 9 and Cl 10. -/
def spatial (control : Bool) : SpatialConfiguration :=
  ⟨(([0,1,2,3,4,5,6,8,7] : List Nat) ++ (if control then [10,9] else [9,10]) ++
    [11,12,13,15,14,16]).map (fun t => moment t)⟩

def input (control : Bool) := (LocalizedChemicalRing.admitRawSpatial? molecule (spatial control)).get
  (by cases control <;> decide +kernel)

theorem admitted (control : Bool) :
    LocalizedChemicalRing.admitRawSpatial? molecule (spatial control) = some (input control) :=
  (Option.some_get _).symm

def geometry (control : Bool) : Geometry := fun i => (spatial control).positions[i]?

private def parameter (control : Bool) (n : Nat) : Nat :=
  (([0,1,2,3,4,5,6,8,7] : List Nat) ++ (if control then [10,9] else [9,10]) ++
    [11,12,13,15,14,16])[n]?.getD 0

private theorem point (control : Bool) (a : (input control).certified.Atom) :
    (input control).certified.spatialPointAt? a = some (moment (parameter control a.val)) := by
  cases control <;> revert a <;> decide +kernel

private theorem parameter_injective (control : Bool) :
    Function.Injective (fun a : (input control).certified.Atom => parameter control a.val) := by
  cases control <;> unfold Function.Injective <;> decide +kernel

private theorem volume (a b c d : ℚ) :
    CartesianPoint3.orientedVolume (moment a) (moment b) (moment c) (moment d) =
      (d-a)*(a-b)*(a-c)*(b-c)*(b-d)*(c-d) := by
  unfold moment CartesianPoint3.orientedVolume
  ring

theorem calibrated (control : Bool) : LocalizedChemicalRing.coordinatesAdmitted (input control) = true := by
  apply decide_eq_true
  intro center
  let i := input control
  let lig := (actualCanonicalMolecule i.certified).ligandAtomAt center
  let x (k : Fin 4) : ℚ := parameter control (lig k).val
  have distinct (a b : Fin 4) (ne : a ≠ b) : x a ≠ x b := by
    intro eqn
    apply ne
    apply (actualCanonicalMolecule i.certified).ligandAtomAt_injective center
    apply parameter_injective control
    change ((parameter control (lig a).val : Nat) : ℚ) = ((parameter control (lig b).val : Nat) : ℚ) at eqn
    exact_mod_cast eqn
  apply (centerAdmitted_iff _ _).mpr
  refine ⟨CartesianPoint3.orientedVolume (moment (x 0)) (moment (x 1)) (moment (x 2)) (moment (x 3)),?_,?_⟩
  · simp [coordinateVolume?,point,x,lig,i]
  · rw [volume]
    repeat' apply mul_ne_zero
    all_goals exact sub_ne_zero.mpr (distinct _ _ (by decide))

/-- Pinned release matrix in atom order 1,2,3,5. The argument is the
signed value for 3 against 5. All values include their casing magnitude. -/
def matrix (score : Int) : List Int :=
  [0,-1,1,1, 1,0,1,1, -1,-1,0,score, -1,-1,-score,0]

/-- Root readback on the source orders. Equal mirror hands give the lowercase
letter in the paired case. Switching the first beta center switches both
spheres to a strict Rule 4b comparison and gives opposite mirror hands. -/
theorem root_hands :
    readback? (geometry false) [2,1,3,5] = some .S ∧
    readback? (mirror (geometry false)) [2,1,5,3] = some .S ∧
    readback? (geometry true) [2,1,5,3] = some .R ∧
    readback? (mirror (geometry true)) [2,1,5,3] = some .S := by decide +kernel

def table (control : Bool) : Option (List Int × List Int × List Int) := do
  let i := input control
  let c ← i.certified.canonicalTetrahedralCenters.find? fun c => c.val.val == 0
  let slots ← ([1,2,3,5] : List Nat).mapM fun atom => (List.finRange 4).find? fun k =>
    (i.certified.canonicalLigandAtom c k).val == atom
  let rows ← slots.mapM (fun a => slots.mapM (fun b => do
    let prev ← i.certified.compareRuleMajorConstitutionAt? c a b
    let (actual,reflected) ← RingActivePairs.rootScore? i c a b
    let z : Int := match prev.outcome with | .lt => -1 | .eq => 0 | .gt => 1
    return (z,actual,reflected)))
  return (rows.flatten.map Prod.fst,rows.flatten.map (·.2.1),rows.flatten.map (·.2.2))

/-- Descriptor orders of the four non-root centers use only strict
constitutional priorities and independently calibrated coordinates. -/
def armHands (control : Bool) : Option (List RS) := do
  let i := input control
  [3,4,5,6].mapM fun atom => do
    let c ← i.certified.canonicalTetrahedralCenters.find? fun c => c.val.val == atom
    RingStrictConstitution.assign? i c

/-- Exact request bytes replayed by the content-authenticated Centres 1.0 runner. -/
def expectedRequest (control : Bool) : String :=
  String.intercalate "\n" (["centres-1.0"] ++
    ([6,8,16,6,6,6,6,9,1,35,17,1,9,1,35,17,1] : List Nat).map (fun z => s!"a {z} 0 0") ++
    molecule.bonds.map (fun b => s!"b {b.source} {b.target}") ++
    ["f 0 R 1 2 3 5","f 3 S 0 4 7 8",if control then "f 4 S 3 9 10 11" else "f 4 R 3 9 10 11",
      "f 5 R 0 6 12 13","f 6 S 5 14 15 16"]) ++ "\n"

def validate : IO Unit := do
  for control in [false,true] do
    let expected := if control then (-1 : Int) else 2
    let reflected := if control then (-1 : Int) else -2
    let some rows := table control | throw (IO.userError s!"missing root molecular comparison, control={control}")
    unless rows == (matrix 0,matrix expected,matrix reflected) do
      throw (IO.userError s!"unexpected root matrix, control={control}: {repr rows}")
    let hands := (if control then [.R,.S,.S,.S] else [.R,.R,.S,.S] : List RS)
    unless armHands control == some hands do
      throw (IO.userError s!"unexpected arm descriptors, control={control}: {repr (armHands control)}")
    let i := input control
    let derived := i.certified.canonicalTetrahedralCenters.map fun c =>
      (c.val.val,CentresRing.labelCode (RingActivePairReport.label? i c))
    let labels := if control then ["R","R","S","S","S"] else ["s","R","R","S","S"]
    unless derived == ([0,3,4,5,6].zip labels) do
      throw (IO.userError s!"public root or arm label differs, control={control}: {repr derived}")
    let req ← IO.ofExcept (CentresRing.request (input control) [0,3,4,5,6])
    unless req == expectedRequest control do
      throw (IO.userError s!"unexpected source request: {req}")
    IO.println s!"control={control}, labels={repr derived}, 16 constitutional and both 16 full scores agree"

#eval validate

end TetraStereo.Examples.RingPairedAuxiliary

assert_kernel_only TetraStereo.Examples.RingPairedAuxiliary.admitted
assert_kernel_only TetraStereo.Examples.RingPairedAuxiliary.calibrated
assert_kernel_only TetraStereo.Examples.RingPairedAuxiliary.root_hands
