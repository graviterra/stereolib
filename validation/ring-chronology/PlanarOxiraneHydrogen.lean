import TetraStereo.Engine.RingHydrogenReport
import TetraStereo.Engine.RingPlanarHydrogenChoices

/-! A synthetic partial-coordinate control for monodeutero-oxirane. Atom 0
is CHD, 1 is O, and 2 is CH₂. The three written neighbours of atom 0 and
the central atom lie in one plane. Geometry admission uses the four ligand
coordinates. The two explicit completions are controls for that predicate. -/
open TetraStereo.OneCenter TetraStereo.Engine

namespace PlanarOxiraneHydrogen

private def planar : SpatialConfiguration :=
  ⟨[⟨0,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩,⟨-2,-3,0⟩,⟨0,2,1⟩,⟨0,2,-1⟩]⟩

private def oxirane (mass : Nat) : RawMolecule :=
  { atoms := [.aliphatic .C,.aliphatic .O,.aliphatic .C,
      {AtomSpec.aliphatic .H with isotope? := some mass, explicitHydrogens? := some 0},
      .aliphatic .H,.aliphatic .H]
    bonds := [(0,1),(1,2),(2,0),(0,3),(2,4),(2,5)].map fun (a,b) => ⟨a,b,.single⟩ }

private def admitted (m : RawMolecule) (g : SpatialConfiguration) :=
  (LocalizedChemicalRing.admitRawSpatial? m g).map LocalizedChemicalRing.coordinatesAdmitted

def check : IO Unit := do
  for mass in [1,2] do
    let m := oxirane mass
    let some (out,pos) := RingHydrogenCompletion.prepare? m planar
      | throw (IO.userError "hydrogen preparation failed")
    unless admitted m planar == some true && RingHydrogenCompletion.plan m == [(0,1)] do
      throw (IO.userError "source admission or missing-H plan changed")
    let ordinary := mass == 1
    let expectedH : CartesianPoint3 := ⟨1,2,if ordinary then 6 else 0⟩
    unless pos.positions.getLast? == some expectedH && admitted out pos == some ordinary do
      throw (IO.userError "generated H position or completed coordinate admission changed")
    for ids in [[1],[0],[2],[]] do
      let expected : Option RingGroupedReport.Report :=
        if ordinary then some (ids.map fun id => (id,none)) else none
      unless RingHydrogenReport.fromRaw? m planar ids == expected do
        throw (IO.userError s!"unexpected omitted-H report for isotope {mass} and IDs {ids}")
    for z in [(1 : Int),-1] do
      let written : SpatialConfiguration := ⟨planar.positions ++ [⟨0,0,z⟩]⟩
      let actual := if z = 1 then RS.R else RS.S
      let expected : RingGroupedReport.Report :=
        [(0,if ordinary then none else some (.chiral actual,.chiral actual.swap)),(1,none),(2,none)]
      unless admitted out written == some true &&
          RingHydrogenReport.fromRaw? out written [0,1,2] == some expected &&
          RingHydrogenReport.fromRaw? out written [1] == some [(1,none)] &&
          RingHydrogenReport.fromRaw? out written [] == some [] do
        throw (IO.userError s!"unexpected explicit-H report for isotope {mass} and z={z}")
  IO.println "Planar CHD oxirane: omitted-H admission loss, opposite explicit carbon hands, invariant oxygen and empty requests verified."

end PlanarOxiraneHydrogen

def main : IO Unit := PlanarOxiraneHydrogen.check
