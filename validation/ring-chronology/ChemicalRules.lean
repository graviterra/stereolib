import TetraStereo.Examples.BlueBookCyclobutanediol
import TetraStereo.Examples.BlueBookRingAssemblyProof
import TetraStereo.Examples.BlueBookHexachlorocyclohexaneProof
import TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries
import TetraStereo.Engine.PublicAPI

open TetraStereo.OneCenter TetraStereo.Engine.RingChemicalPriority TetraStereo.Examples
open CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Recursive

private def allFrames (m : RawMolecule) (g : Geometry) : Bool :=
  (List.range m.atomCount).all fun i => (g i).isSome &&
    ((m.atoms[i]?).any (fun a => a.element == .C) == false || (readback? g (m.writtenNeighbors i)).isSome)

/-- Try each source stage in order, without consulting the family formula. -/
private def fullRingReading (g : Geometry) (i : Fin 6) : Option Reading := Id.run do
  for stage in [Stage.fourB,Stage.five] do
    let hint (p : List Nat) := (BlueBookHexachlorocyclohexane.hints p).map
      (fun f => {f with stage := stage})
    if let some r := certifyHalogenated BlueBookHexachlorocyclohexane.molecule g hint
        BlueBookHexachlorocyclohexane.radius 2 [i.val] then return some r.val
  return none

def main : IO Unit := do
  unless allFrames BlueBookCyclobutanediol.molecule BlueBookCyclobutanediol.geometry &&
      allFrames BlueBookRingAssembly.molecule BlueBookRingAssembly.geometry &&
      allFrames BlueBookHexachlorocyclohexane.molecule BlueBookHexachlorocyclohexane.geometry do
    throw (IO.userError "missing coordinates or degenerate carbon")
  let m := BlueBookRingAssembly.molecule
  let g := BlueBookRingAssembly.geometry
  let hint := BlueBookRingAssembly.hints
  let radius := BlueBookRingAssembly.radius
  for (atom,expected) in BlueBookRingAssembly.rootReadings do
    let some c := certify m g hint radius 5 [atom] | throw (IO.userError s!"unresolved C-{atom}")
    let some r := certify m (mirror g) hint radius 5 [atom] | throw (IO.userError s!"mirror C-{atom}")
    unless c.val == expected && r.val == expected.reverse do
      throw (IO.userError s!"wrong reading at C-{atom}")
    IO.println s!"C-{atom}: {repr c.val.label}, reflected {repr r.val.label}"
  let wrong (mutate : Recursive.Frame → Recursive.Frame) (path : List Nat) :=
    if path == [8] then (hint path).map mutate else hint path
  for invalid in [wrong (fun f => {f with rename := id}),wrong (fun f => {f with stage := .five})] do
    unless (certify m g invalid radius 5 [8]).isNone do throw (IO.userError "invalid step accepted")
  unless (certify m g hint radius 2 [8]).isNone do throw (IO.userError "missing recursive evidence accepted")
  for i in List.range 6 do
    let h : RS := if i < 4 then .R else .S
    let g := BlueBookHexachlorocyclohexane.geometry
    unless BlueBookHexachlorocyclohexane.atRoot g i == some ⟨h,h.swap⟩ &&
        BlueBookHexachlorocyclohexane.atRoot (mirror g) i == some ⟨h.swap,h⟩ do
      throw (IO.userError s!"hexachlorocyclohexane C-{i+1} disagrees with its published assignment")
  let leftFacts : Facts := [([8,7,4],⟨.R,.R⟩),([8,7,4,3,2,1],⟨.S,.R⟩),
    ([8,7,4,5,6,1],⟨.R,.S⟩)]
  let isotope := {m with atoms := m.atoms.modify 3 (fun a => {a with isotope? := some 13})}
  let some arm := occurrence? isotope [8,7] | throw (IO.userError "missing isotopically labelled arm")
  unless (molecularReferences? isotope arm leftFacts false).isNone do
    throw (IO.userError "equidistant carbon occurrences with distinct isotope environments voted together")
  unless PairSpheres.seniorLeft? [[true,false]] [[false,false]] == some true &&
      (PairSpheres.seniorLeft? [[true,false]] [[false,true]]).isNone do
    throw (IO.userError "within-sphere permutation bounds failed")
  for mask in List.finRange 64 do
    let g := BlueBookHexachlorocyclohexaneSeries.faces mask
    for i in List.finRange 6 do
      let some a := TetraStereo.Engine.classifyHexachlorocyclohexaneCenter? g i
        | throw (IO.userError s!"family refusal at mask {mask}, C-{i.val+1}")
      let chemical := HexachlorocyclohexaneFamily.reading a.profile a.center
      unless fullRingReading g i == some chemical && fullRingReading (mirror g) i == some chemical.reverse do
        throw (IO.userError s!"independent recursive ranking disagrees at mask {mask}, C-{i.val+1}")
  let missing : Geometry := fun j => if j = 6 then none else BlueBookHexachlorocyclohexane.geometry j
  unless (TetraStereo.Engine.classifyHexachlorocyclohexaneCenter? missing 1).isNone do
    throw (IO.userError "missing chlorine coordinate admitted")
  IO.println "All 384 numbered ring assignments and 384 mirror readings matched independent graph traversal."
  IO.println "Three geometries checked. Eleven roots and their mirrors matched. Invalid frames, inadequate fuel and an unresolved sphere received no certificate."
