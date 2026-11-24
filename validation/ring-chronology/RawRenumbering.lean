import TetraStereo.Engine.RingRawRenumbering
import TetraStereo.Engine.RingRebuiltStereo
import TetraStereo.Engine.RingGeometryCertificates
import TetraStereo.Examples.CentresRingSpiroCasing

open TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Examples
open RingRawRenumbering (find?)

private def admit (m : RawMolecule) (g : SpatialConfiguration) : IO LocalizedChemicalRing.Input := do
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "failed structural admission")
  return i

private def three (edges : List (Nat × Nat)) : RawMolecule where
  atoms := List.replicate 3 (.aliphatic .C)
  bonds := edges.map fun (a,b) => ⟨a,b,.single⟩

/-- Hanson et al., validation structure VS291, from compounds_3d.sdf at
CIPValidationSuite/ValidationSuite revision 6b9f9db46dadc6749da8234b05164e1e0fb413b9.
SDF coordinates have four decimal places. The source labels atom 2 as R under Rule 6. -/
private def vs291 : RawMolecule where
  atoms := ([.C, .C, .C, .O, .C, .O, .C, .C, .C, .H, .H,
    .H, .H, .H, .H, .H, .H, .H, .H, .H, .H] : List Element).map AtomSpec.aliphatic
  bonds := ([(1, 0), (0, 2), (1, 3), (1, 5), (1, 6), (2, 4), (3, 4),
    (5, 7), (6, 8), (7, 8), (0, 9), (0, 10), (2, 11), (2, 12),
    (4, 13), (4, 14), (6, 15), (6, 16), (7, 17), (7, 18), (8, 19),
    (8, 20)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

private def vs291Coordinates : SpatialConfiguration :=
  ⟨([(-26926, 7164, -4874), (-17296, 16144, 3001), (-39625, 8708, 3020),
    (-25354, 25327, 10475), (-38919, 23340, 6472), (-9445, 7860, 11564),
    (-7512, 24309, -5299), (4015, 7384, 6587), (4773, 15794, -5951),
    (-23755, -3332, -5511), (-28544, 10867, -15034), (-39174, 2661, 12140),
    (-48690, 6025, -2532), (-45766, 26372, 14415), (-40811, 29571, -2351),
    (-5128, 33667, -141), (-11355, 27088, -15142), (6783, -2998, 4574),
    (10654, 11200, 14373), (13968, 21768, -6360), (4556, 9465, -14891)] : List (Int × Int × Int)).map
    (fun (x,y,z) => ⟨(x : ℚ) / 10000,(y : ℚ) / 10000,(z : ℚ) / 10000⟩)⟩

private def publishedPromotion : IO Unit := do
  let i ← admit vs291 vs291Coordinates
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "VS291 coordinate admission")
  let some a := (List.finRange i.certified.certified.input.molecule.atomCount)[1]?
    | throw (IO.userError "VS291 missing atom 2")
  let rows := RingGroupedReport.forAtoms? i [a]
  unless rows == some [(1,some (.chiral RS.R,.chiral RS.S))] do
    throw (IO.userError s!"VS291 source expects 2R, observed {repr rows}")
  let some ctx := RingGeometryCertificates.prepare? i (RingGroupedReport.origin i a)
    | throw (IO.userError "VS291 incomplete geometric frame")
  let marks := RingGroupedOrders.marks ctx.arms
  let balance := RingOrientation.baseline ctx.fr * RingOrientation.index ctx.arms
  unless marks.length == 4 && balance == 4 do
    throw (IO.userError s!"VS291 promotion count {marks.length}, signed balance {balance}")
  let q := RingGroupedReport.origin i a
  let some rebuilt := RingRebuiltStereo.signature? i q ctx.read
    | throw (IO.userError "VS291 rebuilt signature missing")
  unless rebuilt.balance == 4 && rebuilt.letters == some (.chiral .R,.chiral .S) do
    throw (IO.userError s!"unexpected rebuilt VS291 balance {rebuilt.balance}")
  unless RingRebuiltStereo.report? i [a] == rows do throw (IO.userError "VS291 rebuilt recursive report differs")
  IO.println "All four VS291 promotions yield R. The rebuilt balance is +4 and its recursive report gives R/S at SDF atom 2."

def main (args : List String) : IO Unit := do
  if args == ["--promotion"] then return ← publishedPromotion
  unless args.isEmpty do throw (IO.userError "expected --promotion or no arguments")
  let i ← admit CentresRingSpiroCasing.molecule CentresRingSpiroCasing.spatial
  let j ← admit CentresRingSpiroCasing.renumbered CentresRingSpiroCasing.moved
  let some r := find? i j | throw (IO.userError "fluorospiro renumbering missing")
  let atoms := List.finRange i.certified.certified.input.molecule.atomCount
  unless atoms.all (fun a => (r.atoms a).val == CentresRingSpiroCasing.rename a.val) do
    throw (IO.userError "incorrect recovered fluorospiro atom numbers")
  unless LocalizedChemicalRing.coordinatesAdmitted i && LocalizedChemicalRing.coordinatesAdmitted j do
    throw (IO.userError "fluorospiro coordinates failed admission")
  let some focus := atoms.head? | throw (IO.userError "missing spiro atom")
  let expected := some (.chiral RS.S,.chiral RS.R)
  unless RingGroupedReport.forAtoms? i [focus] == some [(0,expected)] &&
      RingGroupedReport.forAtoms? j [r.atoms focus] == some [(3,expected)] do
    throw (IO.userError "descriptor changed at the recovered spiro atom")
  let samePlace : SpatialConfiguration := ⟨List.replicate 3 ⟨0,0,0⟩⟩
  let path ← admit (three [(0,1),(1,2)]) samePlace
  let swapped ← admit (three [(2,0),(1,0)]) samePlace
  let cycle ← admit (three [(0,1),(1,2),(2,0)]) samePlace
  let some ambiguous := find? path swapped | throw (IO.userError "coincident-coordinate search failed")
  let some middle := (List.finRange path.certified.certified.input.molecule.atomCount)[1]?
    | throw (IO.userError "missing middle atom")
  unless (ambiguous.atoms middle).val == 0 do throw (IO.userError "incorrect middle atom")
  unless (find? path cycle).isNone do throw (IO.userError "different bond topology accepted")
  IO.println "Recovered fluorospiro 0 → 3 with S/R, matched coincident coordinates by bond topology, and rejected the extra ring bond."
  publishedPromotion
