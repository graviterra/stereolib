import TetraStereo.Engine.RingRootIndexedEarly
import TetraStereo.Engine.RingSparseFoldedReport

/-! Replay the Hanson VS242 C36 query using the published neutral 3D molfile.
Run from the repository root with the bounded Lean controls in BUILDING.md.
Pass --vs262 for C27 of Figure 8 or --vs265 for C122 of the third-sphere example.
Pass --vs265-cycle and the generated molfile path for the cyclic control.
Pass --paired-cyclopropyl for the checked-in 25-atom cyclic ligand control. Prefix the
arguments with --folded or --sparse-folded to execute those implementations.
Pass --paired-family with the SDF exported by check_paired_cyclopropyl_donors.py
to test all 64 ordered hand triples and their mirror outputs. The --paired-store
mode reads the sparse folded store on each model and its explicit reflection.
Use --paired-report for every atom on every model and its explicit reflection.
The default corpus and its hash are shared with check_figure14_regeneration.py.

In both geometries the best Rule 4b words at N17 and N39 are 11001010.
The Rule 5 fixed-R words are 10101001 and 10100110, respectively.
Here 1 denotes a like pair. The fifth comparison favors N17. The separate
check_vs242_cross_band.py replay checks the reference words with Jmol. -/

open TetraStereo.OneCenter TetraStereo.Engine

namespace VS242PublicReport

private def field (line : String) (start width : Nat) : String :=
  (String.ofList ((line.toList.drop start).take width)).trimAscii.toString

private def coordinate (text : String) : Except String ℚ := do
  let n ← (← Lean.Json.parse text).getNum?
  return (n.mantissa : ℚ) / 10 ^ n.exponent

private def atom (line : String) : Except String (AtomSpec × CartesianPoint3) := do
  unless field line 34 2 == "0" && field line 36 3 == "0" do
    throw "expected a neutral atom with natural isotopic composition"
  let element ← match field line 31 3 with
    | "Br" => pure Element.Br
    | "F" => pure Element.F
    | "C" => pure Element.C
    | "Cl" => pure Element.Cl
    | "H" => pure Element.H
    | "N" => pure Element.N
    | "O" => pure Element.O
    | symbol => throw s!"unexpected element {symbol}"
  return (AtomSpec.aliphatic element,
    ⟨← coordinate (field line 0 10), ← coordinate (field line 10 10), ← coordinate (field line 20 10)⟩)

private def bond (atomCount : Nat) (line : String) : Except String RawBond := do
  let some a := (field line 0 3).toNat? | throw "invalid first bond endpoint"
  let some b := (field line 3 3).toNat? | throw "invalid second bond endpoint"
  unless field line 6 3 == "1" && 0 < a && a ≤ atomCount && 0 < b && b ≤ atomCount do
    throw "expected a single bond with valid endpoints"
  return ⟨a-1,b-1,.single⟩

structure Example where
  name : String
  atoms : Nat
  bonds : Nat
  root : Nat
  original : RS
  fixtureHash : Option String := none

def vs242 : Example := ⟨"VS242",106,105,35,.R,none⟩
def vs262 : Example := ⟨"VS262",94,93,26,.R,none⟩

def vs265 : Example := ⟨"VS265",137,136,121,.S,none⟩
def vs265Cycle : Example := ⟨"VS265-synthetic-cyclopentane",135,135,121,.S,
  some "910d295cc60ce37de4b967e621719d27f04e345ba13538c38cd86e75a49c19ce"⟩

def cyclopropyl : Example := ⟨"paired cyclopropyl donors",25,26,0,.R,
  some "630c05ba50ea667ef31886264ad55c4ef30876f1cbcccde6e34a0c8f68aa9356"⟩

private def parse (e : Example) (corpus : String) : Except String (RawMolecule × SpatialConfiguration) := do
  let [record] := (corpus.splitOn "$$$$\n").filter (·.startsWith (e.name ++ "\n")) |
    throw s!"expected exactly one {e.name} record"
  let lines := record.splitOn "\n"
  let some counts := lines[3]? | throw "missing V2000 counts"
  unless field counts 0 3 == toString e.atoms && field counts 3 3 == toString e.bonds &&
      counts.endsWith "V2000" && lines[4+e.atoms+e.bonds]? == some "M  END" do
    throw s!"unexpected {e.name} counts or property block"
  let atoms ← ((lines.drop 4).take e.atoms).mapM atom
  let bonds ← ((lines.drop (4+e.atoms)).take e.bonds).mapM (bond e.atoms)
  return (⟨atoms.map Prod.fst,bonds,[],[]⟩, ⟨atoms.map Prod.snd⟩)

private def checkedFile (file expectedHash : String) : IO String := do
  let digest ← IO.Process.output {cmd := "sha256sum", args := #["--",file]}
  unless digest.exitCode == 0 && digest.stdout.startsWith (expectedHash ++ " ") do
    throw (IO.userError s!"unexpected SHA-256 for {file}")
  IO.FS.readFile file

def load (file : String) (e : Example := vs242) : IO (RawMolecule × SpatialConfiguration) := do
  let hash := e.fixtureHash.getD "28a000b36506dabe5a45f6d7672451c61c6e34f3e0f027f2599000d850273325"
  IO.ofExcept (parse e (← checkedFile file hash))

abbrev Evaluator := RawMolecule → SpatialConfiguration → List Nat → Option RingGroupedReport.Report

/-- The entry donor fixes the best seed. The two relative hands then rank the
arms. Complementary triples require the fixed-R comparison and lowercase casing. -/
private def expectedRoot (a b : Bool × Bool × Bool) : Option RingNestedActivePair.Labels :=
  let relative (h : Bool × Bool × Bool) := [h.1 == h.2.1,h.1 == h.2.2]
  match compare (relative a) (relative b) with
  | .gt => some (.chiral .R,.chiral .S)
  | .lt => some (.chiral .S,.chiral .R)
  | .eq =>
    if a.1 == b.1 then none
    else
      let hand := if a.1 then PseudoRS.r else PseudoRS.s
      some (.pseudoasymmetric hand,.pseudoasymmetric hand)

/-- One-based physical histories in the same order as the Jmol occurrence replay.
The second visit to the ring exit exchanges its real predecessor and closure
copy. The second visit to the distal CH(Cl)Br retains its original hand. -/
private def donorPaths (arm : Nat) (h : Bool × Bool × Bool) : List (List Nat × Bool) :=
  [([1,arm],h.1), ([1,arm,arm+1],h.2.1), ([1,arm,arm+1,arm+7],h.2.2),
   ([1,arm,arm+2,arm+1],!h.2.1), ([1,arm,arm+2,arm+1,arm+7],h.2.2)]

/-- Read a single stored table at all ten real occurrences. The raw lift supplies
the public admission and coordinate preparation. The view is the public lookup
at this cut by RingSparseFoldedReport.sparse_exact. Index the observations by
request position since a physical atom can occur at two different addresses. -/
private def occurrenceRows (paths : List (List Nat)) : RingRawComparisonLift.TypedEvaluation :=
  fun i atoms => do
    let [root] := atoms | none
    let rows := RingSparseFoldedReport.sparse i root 0
    let view := RingSphereQueue.viewOf rows
    -- Every requested history must be present exactly once below. Requiring
    -- ten assigned rows also rules out any additional assigned occurrences.
    guard (rows.countP (fun row => (row.2.bind id).isSome) == paths.length)
    paths.zipIdx.mapM fun (path,idx) => do
      let [row] := rows.filter (fun row =>
        row.1.val.root == root && row.1.val.node.provenance == .realAtom &&
        row.1.val.node.history.reverse.map (fun a => a.val+1) == path) | none
      let labels ← view row.1
      return (idx,labels)

private def checkStore (name : String) (m : RawMolecule) (g : SpatialConfiguration)
    (donors : List (List Nat × Bool)) : IO Unit := do
  let paths := donors.map Prod.fst
  let expected : RingGroupedReport.Report := donors.zipIdx.map fun ((_,right),idx) =>
    let h : RS := if right then .R else .S
    (idx, some (.chiral h,.chiral h.swap))
  let actual := RingRawComparisonLift.fromRaw (occurrenceRows paths) m g [0]
  unless actual == some expected do
    throw (IO.userError s!"{name}: paths {paths}, store {repr actual}, expected {repr expected}")

private def checkAllAtoms (evaluate : Evaluator) (name : String) (m : RawMolecule) (g : SpatialConfiguration)
    (a b : Bool × Bool × Bool) : IO Unit := do
  let expectedHand (right : Bool) : Option RingNestedActivePair.Labels :=
    let h := if right then RS.R else RS.S
    some (.chiral h,.chiral h.swap)
  let rows : RingGroupedReport.Report := (List.range 25).map fun id =>
    let pair := match id with
      | 0 => expectedRoot a b
      | 3 => expectedHand a.1 | 4 => expectedHand a.2.1 | 10 => expectedHand a.2.2
      | 14 => expectedHand b.1 | 15 => expectedHand b.2.1 | 21 => expectedHand b.2.2
      | _ => none
    (id,pair)
  let mirror : SpatialConfiguration := ⟨g.positions.map fun p => ⟨-p.x,p.y,p.z⟩⟩
  let reflected := rows.map fun (n,pair) => (n,pair.map Prod.swap)
  for (placement,expected) in [(g,rows),(mirror,reflected)] do
    let actual := evaluate m placement (List.range 25)
    unless actual == some expected do
      throw (IO.userError s!"{name}: all-atom report {repr actual}, expected {repr expected}")

def checkFamily (evaluate : Evaluator) (path : String) (store := false) (allAtoms := false) : IO Unit := do
  let sdf ← checkedFile path "cf6af652cba05cef4ee12f5eb66e0718e837625eda460829e9781ae83d75d7fb"
  let triples := [false,true].flatMap fun a =>
    [false,true].flatMap fun b => [false,true].map fun c => (a,b,c)
  let name (h : Bool × Bool × Bool) := String.ofList ([h.1,h.2.1,h.2.2].map fun b => if b then 'R' else 'S')
  for a in triples do
    for b in triples do
      let caseName := name a ++ "-" ++ name b
      let (m,g) ← IO.ofExcept (parse {cyclopropyl with name := caseName} sdf)
      if allAtoms then checkAllAtoms evaluate caseName m g a b
      else if store then
        let donors := donorPaths 4 a ++ donorPaths 15 b
        checkStore caseName m g donors
        let mirror : SpatialConfiguration := ⟨g.positions.map fun p => ⟨-p.x,p.y,p.z⟩⟩
        checkStore (caseName ++ " reflected") m mirror (donors.map fun (p,h) => (p,!h))
      else
        let actual := evaluate m g [0]
        let expected := some [(0,expectedRoot a b)]
        unless actual == expected do
          throw (IO.userError s!"{caseName} C1 gave {repr actual}, expected {repr expected}")
    IO.println s!"All eight right ligands agree for {name a}"
    (← IO.getStdout).flush
  if allAtoms then
    IO.println "128 whole reports: all 3200 atom rows, including refusals"
  else if store then
    IO.println "128 root stores: 1280 path lookups, 2560 descriptor readings"
  else
    IO.println "64 cyclic ligand pairs verified on input and reflected coordinates"

end VS242PublicReport

def main (args : List String) : IO Unit := do
  let (evaluate, settings) : VS242PublicReport.Evaluator × List String := match args with
    | "--folded" :: rest => (RingFoldedLigandReport.fromRaw?,rest)
    | "--sparse-folded" :: rest => (RingSparseFoldedReport.fromRaw?,rest)
    | _ => (RingRootIndexedEarly.sparseFromRaw?,args)
  if let ["--paired-store",path] := settings then
    if args.head? == some "--folded" then
      throw (IO.userError "--paired-store reads the sparse folded store; use --paired-store or --sparse-folded --paired-store")
    return ← VS242PublicReport.checkFamily evaluate path true
  if let ["--paired-report",path] := settings then
    return ← VS242PublicReport.checkFamily evaluate path false true
  if let ["--paired-family",path] := settings then
    return ← VS242PublicReport.checkFamily evaluate path
  let (e, paths) := match settings with
    | "--paired-cyclopropyl" :: rest => (VS242PublicReport.cyclopropyl,rest)
    | "--vs265-cycle" :: rest => (VS242PublicReport.vs265Cycle,rest)
    | "--vs265" :: rest => (VS242PublicReport.vs265,rest)
    | "--vs262" :: rest => (VS242PublicReport.vs262,rest)
    | _ => (VS242PublicReport.vs242,settings)
  let file ← match paths with
    | [] =>
      if e.name == VS242PublicReport.cyclopropyl.name then
        pure "validation/ring-chronology/PairedCyclopropylDonors.mol"
      else if e.fixtureHash.isSome then
        throw (IO.userError "supply the pinned synthetic molfile path")
      else pure ".cache/compounds_3d.sdf"
    | [path] => pure path
    | _ => throw (IO.userError "expected a pinned structure, or --paired-family, --paired-report or --paired-store followed by the pinned family SDF")
  let (m,g) ← VS242PublicReport.load file e
  -- All three routes have a kernel-checked equality to RingHydrogenReport.fromRaw?.
  let report := evaluate m g [e.root]
  unless report == some [(e.root,some (.chiral e.original,.chiral e.original.swap))] do
    throw (IO.userError s!"unexpected {e.name} C{e.root+1} public report {repr report}")
  let letter (h : RS) := if h == .R then "R" else "S"
  IO.println s!"{e.name} C{e.root+1} receives {letter e.original} on the input coordinates and {letter e.original.swap} on the mirror"
