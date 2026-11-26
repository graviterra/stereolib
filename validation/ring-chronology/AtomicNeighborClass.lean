import TetraStereo.Engine.RingAtomicNeighborOrder

/-! A realized ring control for the independent first-shell atomic-number class.
Omitted P-H has two physical choices; the absolute C0 request remains determined. -/
set_option autoImplicit false
namespace AtomicNeighborClass
open TetraStereo.OneCenter TetraStereo.Engine
open RingAtomicNeighborOrder

private def molecule : RawMolecule := {
  atoms := ([.C,.O,.S,.P,.Br,.F] : List Element).map AtomSpec.aliphatic
  bonds := ([(0,1),(0,2),(1,2),(0,3),(0,4),(3,5)] : List (Nat × Nat)).map
    fun ab => ⟨ab.1,ab.2,.single⟩ }

private def coordinates : SpatialConfiguration := ⟨[
  ⟨0,0,0⟩,⟨2,2,2⟩,⟨-2,-2,2⟩,⟨2,-2,-2⟩,⟨-2,2,-2⟩,⟨4,1,-2⟩]⟩

private def reading (x : SpatialConfiguration) (ids : List Nat) : Option RS :=
  LocalizedGenericMarkedRecalculation.readback? (RingWrittenPHReadings.geometry x) ids

private def labels (h : RS) : RingNestedActivePair.Labels := (.chiral h,.chiral h.swap)

def audit : IO Unit := do
  let mut original : Option RS := none
  for reflected in [false,true] do
    let x : SpatialConfiguration := if reflected then
      ⟨coordinates.positions.map fun p => {p with x := -p.x}⟩ else coordinates
    let some source := LocalizedChemicalRing.admitRawSpatial? molecule x
      | throw (IO.userError "atomic-neighbor source structural admission failed")
    unless LocalizedChemicalRing.coordinatesAdmitted source do
      throw (IO.userError "atomic-neighbor source coordinate admission failed")
    let some (out,pos) := RingHydrogenCompletion.prepare? molecule x
      | throw (IO.userError "atomic-neighbor preparation failed")
    unless out.atomCount == 7 && RingHydrogenCompletion.addedParents molecule == [3] do
      throw (IO.userError "expected exactly one implicit P hydrogen")
    unless classify? out 0 == some (.ranked [4,2,3,1]) &&
        classify? out 3 == some (.ranked [5,0,6,3]) do
      throw (IO.userError "independent Z classifier did not recover complete C/P physical orders")
    let some carbon := reading x [4,2,3,1]
      | throw (IO.userError "independent C0 determinant is zero")
    if reflected then
      unless original == some carbon.swap do throw (IO.userError "C0 determinant did not reverse")
    else original := some carbon
    let stableIds := [0,1,2,4,5,0]
    let stable : RingGroupedReport.Report := stableIds.map fun n => (n,if n == 0 then some (labels carbon) else none)
    unless RingHydrogenReport.fromRaw? molecule x stableIds == some stable do
      throw (IO.userError "omitted P-H contaminated an independently determined C0 request")
    unless (RingHydrogenReport.fromRaw? molecule x [3]).isNone &&
        (RingHydrogenReport.fromRaw? molecule x [0,3,0]).isNone &&
        (RingHydrogenReport.fromRaw? molecule x [6]).isNone do
      throw (IO.userError "P-H ambiguity or original-ID rejection was lost")
    let variants := RingPyramidalChoices.variants molecule x out pos
    unless variants.length == 2 do throw (IO.userError "expected two independent P-H placements")
    let mut hands : List RS := []
    for written in variants do
      let some i := LocalizedChemicalRing.admitRawSpatial? out written
        | throw (IO.userError "explicit P-H structural admission failed")
      unless LocalizedChemicalRing.coordinatesAdmitted i do
        throw (IO.userError "explicit P-H coordinate admission failed")
      let some phosphorus := reading written [5,0,6,3]
        | throw (IO.userError "explicit P-H determinant is zero")
      hands := hands ++ [phosphorus]
      let ids := List.range 7 ++ [0,3,0,6,3]
      let expected : RingGroupedReport.Report := ids.map fun n =>
        (n,if n == 0 then some (labels carbon) else if n == 3 then some (labels phosphorus) else none)
      unless directReport? out written ids == some expected do
        throw (IO.userError "independent direct report disagreed with physical determinant expectations")
      unless RingHydrogenReport.fromRaw? out written ids == some expected do
        throw (IO.userError "explicit P-H native report disagreed with independent atomic-neighbor report")
      IO.println s!"Atomic-neighbor mirror {reflected}: C0 {repr carbon}, explicit P3 {repr phosphorus}; independent/native full rows and repetitions agree."
    unless hands.contains .R && hands.contains .S do
      throw (IO.userError "P-H placement population did not realize both hands")
    IO.println s!"Atomic-neighbor mirror {reflected}: omitted H keeps C0 absolute, rejects P3/mixed requests and generated source ID6."

end AtomicNeighborClass

def main : IO Unit := AtomicNeighborClass.audit
