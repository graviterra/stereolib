import TetraStereo.Examples.LocalizedChemicalRingSpiroProjection
import TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime

open TetraStereo.OneCenter TetraStereo.Engine.LocalizedChemicalRing
open LocalizedGenericMarkedRecalculation (frameAtoms? readback?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open TetraStereo.Examples

private def exportFrames (name smiles : String) (spatial : SpatialConfiguration) : IO Unit := do
  let .ok (some input) := admitSmilesSpatial? smiles spatial | throw (IO.userError "admission")
  unless coordinatesAdmitted input do throw (IO.userError "coordinates")
  IO.println s!"graph {name}"
  for a in input.molecule.atoms do
    unless a.isotope?.isNone && a.charge == 0 do throw (IO.userError "unsupported atom")
    IO.println s!"atom {a.element.atomicNumber}"
  for b in input.molecule.bonds do
    unless input.molecule.bondOrder b.source b.target == 1 do throw (IO.userError "unsupported bond")
    IO.println s!"bond {b.source} {b.target}"
  for c in input.certified.canonicalTetrahedralCenters do
    let some ids := frameAtoms? input.molecule (canonicalCenterRoot c.1.val)
      | throw (IO.userError "missing frame")
    let some hand := readback? (inputGeometry input.certified) ids | throw (IO.userError "flat frame")
    let parity := match hand with | .R => "R" | .S => "S"
    IO.println s!"frame {c.1.val} {parity} {String.intercalate " " (ids.map toString)}"

def main : IO Unit := do
  exportFrames "spiro" LocalizedChemicalRingSpiroProjection.smiles LocalizedChemicalRingSpiroProjection.spatial
  exportFrames "propellane" LocalizedChemicalRingPropellaneLifetime.smiles LocalizedChemicalRingPropellaneLifetime.spatial
