import TetraStereo.Engine.RingConfiguredPriorities
import TetraStereo.Examples.LocalizedChemicalRingSpiroProjection
import TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime

open TetraStereo TetraStereo.OneCenter TetraStereo.Engine
open TetraStereo.Examples
open LocalizedGenericMarkedRecalculation (readback?)
open CentresRing (labelCode)

private def getInput (s : String) (g : SpatialConfiguration) : IO LocalizedChemicalRing.Input := do
  let .ok (some input) := LocalizedChemicalRing.admitSmilesSpatial? s g
    | throw (IO.userError s!"failed to admit {s}")
  return input

private def check (name : String) (input : LocalizedChemicalRing.Input)
    (expected : List (Nat × String)) : IO (CentresRing.Result input) := do
  let r ← IO.ofExcept (← CentresRing.analyze input)
  let assigned := r.report.filterMap fun (a,d) => d.map fun _ => (a,labelCode d)
  unless assigned == expected do throw (IO.userError s!"{name}: {repr assigned}, expected {repr expected}")
  IO.println s!"{name}: {r.report.length} candidates; assigned {repr assigned}; {((r.traces.map (·.updates.length)).sum)} auxiliary assignments"
  return r

/-- Distinct moment-curve points give nonzero volume for every four distinct atoms.
To match a source annotation, reflect one ligand through another ligand point.
Choose a ligand outside every other annotated frame, preferring an attached hydrogen. -/
private def spatialFor (smiles : String) : IO SpatialConfiguration := do
  let norm ← IO.ofExcept (parseAndNormalizeOpenSMILESCertified smiles [])
  let m := norm.result.parsed.withExplicitHydrogens
  let mut points : List CartesianPoint3 := (List.range m.atoms.length).map fun i =>
    let t := (i : ℚ)
    ⟨t,t*t,t*t*t⟩
  let annotated := m.atoms.zipIdx.filterMap (fun (a,i) => a.tetrahedral?.map fun _ => i)
  for (a,i) in m.atoms.zipIdx do
    if let some parity := a.tetrahedral? then
      let order := m.writtenNeighbors i
      let wanted := RawMolecule.descriptorOfParity parity true
      if readback? (fun j => points[j]?) order != some wanted then
        let privateLigand := fun j => annotated.all fun k => i == k || !(m.writtenNeighbors k).contains j
        let some h := order.find? (fun j => privateLigand j && (m.atoms[j]?.map AtomSpec.element) == some .H)
            <|> order.find? privateLigand
          | throw (IO.userError "no independently movable source ligand")
        let some other := order.find? (· != h) | throw (IO.userError "missing other ligand")
        let some p := points[h]? | throw (IO.userError "missing movable ligand position")
        let some q := points[other]? | throw (IO.userError "missing ligand position")
        points := points.set h ⟨2*q.x-p.x,2*q.y-p.y,2*q.z-p.z⟩
      unless readback? (fun j => points[j]?) order == some wanted do throw (IO.userError "source parity")
  for i in annotated do
    let some (some parity) := (m.atoms[i]?).map AtomSpec.tetrahedral? | throw (IO.userError "source atom")
    unless readback? (fun j => points[j]?) (m.writtenNeighbors i) == some (RawMolecule.descriptorOfParity parity true) do
      throw (IO.userError "constructed coordinates differ from source stereochemistry")
  return ⟨points⟩

private def rejected (name : String) (input : LocalizedChemicalRing.Input) (rows : List CentresRing.CenterTrace) : IO Unit := do
  if (CentresRing.verify input rows).isOk then throw (IO.userError s!"accepted damaged trace: {name}")

private def selectedLines : List Nat := [46,49,50,87,89,90,94,95,96,97,100,101,102,115,117,119]

private def suite (file : String) (molecular chemical : Bool := false)
    (selected : List Nat := selectedLines) (mirror configured : Bool := false) : IO Unit := do
  let lines := (← IO.FS.readFile file).splitOn "\n"
  let mut errors : List String := []
  for line in selected do
    try
      let some row := lines[line-1]? | throw (IO.userError "unexpected end of source")
      let smiles :: expected :: _ := (row.splitToList Char.isWhitespace).filter (!·.isEmpty)
        | throw (IO.userError "expected source columns")
      let spatial ← spatialFor smiles
      let input ← getInput smiles (if mirror then ⟨spatial.positions.map CartesianPoint3.reflectX⟩ else spatial)
      let centers := input.molecule.atoms.zipIdx.filterMap (fun (a,i) => a.tetrahedral?.map fun _ => i)
      let result ← if chemical then do
        unless RingChemicalPriority.saturatedWithHalogens input.molecule do
          throw (IO.userError "outside the neutral saturated C/H/O/halogen proof domain")
        let packet ← IO.ofExcept (← CentresRing.Molecular.observe input centers)
        let updates := (packet.receipt.traces.map (·.updates.length)).sum
        if configured then
          let evidence ← IO.ofExcept (CentresRing.ConfiguredPriority.checkSource input packet centers 3)
          IO.println s!"configured line {line}: {packet.observed.length} comparisons, {updates} auxiliary publications"
          pure evidence.source.molecular.replay
        else
          let evidence ← IO.ofExcept (CentresRing.ComparisonAgreement.diagnoseSource input packet 3 centers)
          unless (CentresRing.ComparisonAgreement.requireAgreement evidence.centers).isSome do
            throw (IO.userError "the source and molecular root readings disagree")
          IO.println s!"chemical line {line}: {packet.observed.length} comparisons, {updates} auxiliary publications"
          pure evidence.source.molecular.replay
      else if molecular then do
        let e ← IO.ofExcept (← CentresRing.Molecular.analyze input centers)
        let aux := (e.molecular.replay.traces.map fun t => t.updates.length).sum
        IO.println s!"molecular line {line}: {e.observed.length} comparisons, {aux} auxiliary publications"
        pure e.molecular.replay
      else IO.ofExcept (← CentresRing.analyze input centers)
      let letters := result.report.filterMap fun (_,d) => d.map fun _ => labelCode d
      let wanted := (expected.splitOn ",").map fun code =>
        if mirror then match code with | "R" => "S" | "S" => "R" | c => c else code
      unless letters == wanted do throw (IO.userError s!"expected {repr wanted}, got {repr letters}")
      IO.println s!"validate.smi line {line} {repr letters}"
    catch e =>
      IO.println s!"validate.smi line {line} FAILED {e}"
      errors := s!"{line}: {e}" :: errors
  unless errors.isEmpty do throw (IO.userError (String.intercalate "\n" errors.reverse))

private structure RegressionReceipt where
  smiles : String
  expected : String
  packet : CentresRing.Molecular.SourceReceipt
  deriving Lean.FromJson, Lean.ToJson

/-- Verbatim inputs from validate.smi at Centres release aaed608e. -/
private def configuredCases : List (Nat × String × String × Nat × Nat) :=
  [(46,"C1CCC2(C1)CC[C@]1(CCC3(CCCC3)C1)C2","S",16,0),
   (100,"[H][C@]12C3CCC4CCCC(CCC1CCC3)[C@]24[H]","s,s",76,18),
   (101,"[H][C@]12C3CCC4CCCC(CCC1CCC3)[C@@]24[H]","r,r",75,18)]

private def coordinateComparisons {m g cs} {ts : List CentresRing.CenterTrace} :
    CentresRing.ComparisonAgreement.Each (CentresRing.ConfiguredPriority.CheckedCenter m g cs) ts →
      Option (List (Bool × String))
  | .nil => some []
  | .cons audit tail => do
    let outcome ← audit.compareCoordinates? 3
    let value := match outcome with
      | .agrees c _ => (true,labelCode (c.verdict.bind RingChemicalPriority.Recursive.Reading.label))
      | .differs c _ => (false,labelCode (c.verdict.bind RingChemicalPriority.Recursive.Reading.label))
    return value :: (← coordinateComparisons tail)

private def regressionReceipt (dir : System.FilePath) (source : Option (List String)) : IO Unit := do
  for (n,pinnedSmiles,expected,calls,updates) in configuredCases do
    let file := dir / s!"{n}.json"
    let receipt : RegressionReceipt ← match source with
      | none => do
        IO.ofExcept ((Lean.Json.parse (← IO.FS.readFile file)).bind (Lean.fromJson? (α := RegressionReceipt)))
      | some lines => do
        let some row := lines[n-1]? | throw (IO.userError s!"missing validation line {n}")
        let smiles :: letters :: _ := (row.splitToList Char.isWhitespace).filter (!·.isEmpty)
          | throw (IO.userError s!"missing source columns at {n}")
        unless smiles == pinnedSmiles && letters == expected do throw (IO.userError s!"source row {n} differs")
        let input ← getInput smiles (← spatialFor smiles)
        let centers := input.molecule.atoms.zipIdx.filterMap fun (a,i) => a.tetrahedral?.map fun _ => i
        let packet ← IO.ofExcept (← CentresRing.Molecular.observe input centers)
        pure (RegressionReceipt.mk smiles letters packet)
    unless receipt.smiles == pinnedSmiles && receipt.expected == expected do throw (IO.userError s!"receipt row {n} differs")
    let input ← getInput pinnedSmiles (← spatialFor pinnedSmiles)
    let centers := input.molecule.atoms.zipIdx.filterMap fun (a,i) => a.tetrahedral?.map fun _ => i
    let packet := receipt.packet
    let verified ← IO.ofExcept (CentresRing.ConfiguredPriority.checkSource input packet centers 3)
    let letters := (verified.source.molecular.replay.report.map fun (_,d) => labelCode d)
    unless letters == expected.splitOn "," && packet.observed.length == calls &&
        (packet.receipt.traces.map (·.updates.length)).sum == updates do
      throw (IO.userError s!"line {n}: unexpected configured report {repr letters}")
    if n == 46 then
      let d ← IO.ofExcept (CentresRing.ComparisonAgreement.diagnoseSource input packet 3 centers)
      unless (CentresRing.ComparisonAgreement.requireAgreement d.centers).isSome do
        throw (IO.userError "case 46 full-coordinate derivation")
    else
      let physical := coordinateComparisons verified.checked
      let wanted := if n == 100 then ["R","S"] else ["R","R"]
      unless physical == some (wanted.map fun code => (false,code)) do
        throw (IO.userError s!"case {n}: full geometry {repr physical}")
    if source.isSome then
      IO.FS.createDirAll dir
      IO.FS.writeFile file (Lean.toJson receipt).compress
    IO.println s!"line {n}: {repr letters}, {calls} independently checked calls, {updates} publications"

def main (args : List String) : IO Unit := do
  if let ["--save-configured-receipts",file,dir] := args then
    return ← regressionReceipt dir (some ((← IO.FS.readFile file).splitOn "\n"))
  if let ["--verify-configured-receipts",dir] := args then return ← regressionReceipt dir none
  if let "--configured" :: file :: requested := args then
    let some lines := requested.mapM String.toNat? | throw (IO.userError "expected numbered validation lines")
    return ← suite file false true (if lines.isEmpty then selectedLines else lines) false true
  if let "--chemical-mirror" :: file :: requested := args then
    let some lines := requested.mapM String.toNat? | throw (IO.userError "expected numbered validation lines")
    return ← suite file false true (if lines.isEmpty then selectedLines else lines) true
  if let "--chemical" :: file :: requested := args then
    let some lines := requested.mapM String.toNat? | throw (IO.userError "expected numbered validation lines")
    return ← suite file false true (if lines.isEmpty then selectedLines else lines)
  if let ["--molecular",file] := args then return ← suite file true
  if let [file] := args then suite file
  let spiro ← getInput LocalizedChemicalRingSpiroProjection.smiles LocalizedChemicalRingSpiroProjection.spatial
  let r ← check "Blue Book spiro" spiro [(0,"R")]
  let annotated ← IO.ofExcept (← CentresRing.analyze spiro [0])
  unless annotated.report == [(0,some (.chiral .R))] && annotated.traces.all (·.updates.isEmpty) do
    throw (IO.userError "source-annotated inventory")
  let reversed ← IO.ofExcept (← CentresRing.analyze spiro [2,0])
  unless reversed.report == [(2,none),(0,some (.chiral .R))] do throw (IO.userError "inventory order")
  for invalid in [[0,0],[1]] do
    if (← CentresRing.analyze spiro invalid).isOk then throw (IO.userError "invalid requested centers")
  let root :: rest := r.traces | throw (IO.userError "missing spiro trace")
  let first :: [full] := root.passes | throw (IO.userError "missing full spiro pass")
  let base :: [trial] := full.trials | throw (IO.userError "missing spiro two-class promotion")
  let c :: cs := base.comparisons | throw (IO.userError "missing comparisons")
  let changeFull := fun f => { root with passes := [first,f] } :: rest
  rejected "missing center" spiro rest
  rejected "public letter" spiro ({root with label := "s"} :: rest)
  rejected "missing occurrence" spiro ({root with discovered := root.discovered.drop 1} :: rest)
  rejected "missing auxiliary" spiro ({root with updates := root.updates.drop 1} :: rest)
  rejected "wrong schedule" spiro ({root with updates := root.updates.reverse} :: rest)
  rejected "wrong auxiliary" spiro ({root with updates := root.updates.map (fun u => {u with label := "invalid"})} :: rest)
  rejected "wrong root comparator operands" spiro (changeFull {full with trials :=
    [{base with comparisons := {c with left := 999} :: cs}, trial]})
  rejected "wrong selected atom" spiro (changeFull {full with trials := [base,{trial with mark := none}]})
  rejected "wrong reference exit" spiro (changeFull {full with after := some 999})
  let reflected := LocalizedChemicalRingSpiroProjection.spatial.positions.map CartesianPoint3.reflectX
  let _ ← check "spiro mirror" (← getInput LocalizedChemicalRingSpiroProjection.smiles ⟨reflected⟩) [(0,"S")]
  let _ ← check "propellane" (← getInput LocalizedChemicalRingPropellaneLifetime.smiles
    LocalizedChemicalRingPropellaneLifetime.spatial) []
  for (smiles,letter) in [("C[C@H]1CC[C@@H](C)CC1","s"),("C[C@H]1CC[C@H](C)CC1","r")] do
    let _ ← check "Centres 1.0 para-dimethylcyclohexane" (← getInput smiles (← spatialFor smiles))
      [(1,letter),(4,letter)]
  let methane ← getInput "C" (← spatialFor "C")
  let methaneResult ← check "four-way methane" methane []
  unless methaneResult.traces.any (fun t => t.passes.any (fun p => p.trials.length == 3)) do
    throw (IO.userError "four-way branch missing")
  let _ ← check "no centers" (← getInput "O" (← spatialFor "O")) []
  let large := String.intercalate "." (List.replicate 64 "[H][H]" ++ ["FC(Cl)(Br)I"])
  let control ← getInput "FC(Cl)(Br)I" (← spatialFor "FC(Cl)(Br)I")
  let halo ← IO.ofExcept (← CentresRing.analyze control)
  let [(_,some d)] := halo.report | throw (IO.userError "halomethane must resolve")
  let _ ← check "atom identity above 127" (← getInput large (← spatialFor large)) [(129,labelCode (some d))]
  let isotope := "FC([2H])([H])I"
  let isoInput ← getInput isotope (← spatialFor isotope)
  let iso ← IO.ofExcept (← CentresRing.analyze isoInput)
  let [(_,some (.chiral _))] := iso.report | throw (IO.userError "isotopic ligands must resolve")
  let _ ← check "isotope removed" (← getInput "FC([H])([H])I" (← spatialFor "FC([H])([H])I")) []
  IO.println "Isotope distinction and nine damaged-transcript rejections passed."
