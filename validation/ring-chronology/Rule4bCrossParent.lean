import TetraStereo.Engine.RingRebuiltStereo
import TetraStereo.Engine.PublicAPI
import TetraStereo.Engine.RingFullPathEligibility

open TetraStereo.OneCenter TetraStereo.Engine

-- Exact neutral atom and single-bond decoding for the cross-parent fixture.
private def fields (line : String) := (line.splitOn " ").filter (· != "")

private def coord (text : String) : Except String ℚ := do
  let n ← (← Lean.Json.parse text).getNum?
  return (n.mantissa : ℚ) / 10 ^ n.exponent

private def atom (line : String) : Except String (AtomSpec × CartesianPoint3) := do
  let x :: y :: z :: symbol :: "0" :: "0" :: _ := fields line | throw "expected a neutral unlabeled atom"
  let e ← match symbol with
    | "Cl" => pure Element.Cl
    | "F" => pure Element.F
    | "S" => pure Element.S
    | "C" => pure Element.C
    | "N" => pure Element.N
    | "O" => pure Element.O
    | "H" => pure Element.H
    | _ => throw "unexpected element"
  return (AtomSpec.aliphatic e, ⟨← coord x, ← coord y, ← coord z⟩)

private def bond (line : String) : Except String RawBond := do
  let a :: b :: "1" :: _ := fields line | throw "expected single bond"
  let some i := a.toNat? | throw "invalid bond endpoint"
  let some j := b.toNat? | throw "invalid bond endpoint"
  unless 0 < i && i ≤ 41 && 0 < j && j ≤ 41 do throw "out-of-range bond endpoint"
  return ⟨i-1,j-1,.single⟩

private def parse (text : String) : Except String (RawMolecule × List CartesianPoint3) := do
  let lines := text.splitOn "\n"
  unless (fields lines[3]!).take 2 == ["41","41"] && lines[86]! == "M  END" do
    throw "unexpected model size"
  let atoms ← ((lines.drop 4).take 41).mapM atom
  let bonds ← ((lines.drop 45).take 41).mapM bond
  return (⟨atoms.map Prod.fst, bonds, [], []⟩, atoms.map Prod.snd)


open RingActivePairs (Site Arm)
open RingActiveDistanceSchedule (Cell View frozen)
open LocalizedChemicalRing (Input)

private structure Entry (i : Input) where
  site : Site i
  cell : Cell
  exactCell : cell = RingGroupedPublication.state i site

private def cached (i : Input) : List (Entry i) → View i
  | [], q => if i.certified.localizedOccurrenceDescriptorCenter? q = none then some none
             else RingGroupedPublication.state i q
  | e :: es, q => if e.site = q then e.cell else cached i es q

private theorem cached_exact (i : Input) (entries : List (Entry i)) :
    cached i entries = RingGroupedPublication.state i := by
  funext q
  induction entries with
  | nil =>
    simp only [cached]
    split
    next no => exact ((RingGroupedPublication.state_eq i q).trans (RingSphereQueue.grouped_skips i q _ no)).symm
    next => rfl
  | cons e es ih =>
    simp only [cached]
    split
    next equal => exact e.exactCell.trans (congrArg _ equal)
    next => exact ih

private def entry (i : Input) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) :
    Option (Entry i) :=
  match hit : RingSphereQueue.early? i q with
  | none => none
  | some sig => some ⟨q, some sig.letters, (RingSphereQueue.early_exact geom hit).symm⟩

def main (args : List String) : IO Unit := do
  let (m,g) ← IO.ofExcept (parse (include_str "Rule4bCrossParent.mol"))
  let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨g⟩ | throw (IO.userError "structure")
  if geom : LocalizedChemicalRing.coordinatesAdmitted i = true then
    let sites := (RingActiveDistanceSchedule.sites i).filter fun q => q.val.root.val == 0
    let get (path : List Nat) : IO (Site i) := do
      let some q := sites.find? (fun q => q.val.node.history.map Fin.val == path && q.val.node.provenance == .realAtom)
        | throw (IO.userError s!"path {path}")
      return q
    let f ← get [0]
    let a ← get [1,0]
    let b ← get [2,0]
    let root := f.val.root
    if args == ["--full-path-report"] then
      let result := ringMolecularReportFromRaw? m ⟨g⟩ [root.val]
      unless result == some [(0,none)] do throw (IO.userError s!"cross-parent full-path report {repr result}")
      IO.println "Full-path report from its own recursive auxiliary store: root 0 unassigned."
      return
    let inventory := sites.filter fun q => decide (RingSphereQueue.candidate root q)
    unless inventory.length == 8 do throw (IO.userError s!"unexpected inventory {inventory.length}")
    let some entries := inventory.mapM (entry i geom) | throw (IO.userError "unresolved auxiliary")
    let read := frozen (cached i entries) f
    have exactReader : read = frozen (RingGroupedPublication.state i) f := by
      unfold read
      rw [cached_exact]
    for j in List.range 8 do
      let q ← get [7+j,3+j/2,1+j/4,0]
      let s : RS := if [0,1,4,6].contains j then .R else .S
      unless read q == some (some (.chiral s,.chiral s.swap)) do throw (IO.userError s!"wrong hand at {j}")
    IO.println "All eight reachable publications agree with the independently specified leaf hands."
    (← IO.getStdout).flush
    unless RingRetainedUnitPass.compareUnit? i f a b read == some 0 do
      throw (IO.userError "the molecular Rule 4b entry condition failed")
    for q in [a,b] do
      let arm : Arm i := ⟨q,some f⟩
      let some profile := RingGroupedStereo.arm? i read arm | throw (IO.userError "missing molecular hits")
      let x :: xs := profile.hits | throw (IO.userError "missing chiral occurrences")
      unless xs.length == 3 && xs.all (fun y => y.path == x.path) do
        throw (IO.userError "the four chiral units are not one through-4a path rank")
      unless RingOccurrenceStereo.seeds? i read false arm == some [.R,.S] do
        throw (IO.userError "unexpected references")
      let word := if q == a then [1,1,0,0] else [1,0,1,0]
      for s in [RS.R,RS.S] do
        unless (RingOccurrenceStereo.pairs? i read false false s arm).map (List.map Bool.toNat) == some word do
          throw (IO.userError "unexpected grouped reading")
      IO.println s!"Grouped words with either reference: {word}"
      for rev in [false,true] do
        for seed in [RS.R,RS.S] do
          unless RingFullPathPairs.pairs? i read rev seed arm == some [true,true,false,false] do
            throw (IO.userError "unexpected full-path reading")
      IO.println "Full-path words are 1100 with either reference on both geometries."
      (← IO.getStdout).flush
    for rev in [false,true] do
      unless RingFullPathPairs.decision? i read rev ⟨a,some f⟩ ⟨b,some f⟩ == some 0 do
        throw (IO.userError "full-path Rule 4b failed to tie")
      unless RingFullPathPairs.hanson? i read rev ⟨a,some f⟩ ⟨b,some f⟩ == some 0 do
        throw (IO.userError "best-of-both Rule 4b failed to tie")
    let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "missing tetrahedral frame")
    for rev in [false,true] do
      let some keys := RingActivePairReport.four? (fun s =>
        RingFullPathEligibility.key? i read rev (RingGroupedCentre.cursor fr s))
        | throw (IO.userError "missing ordinary ligand ranking")
      let ties := (RingFullPathEligibility.tiedSlots keys).map fun s => (fr.direction s).val
      unless ties.length == 2 && ties.contains a && ties.contains b &&
          (RingFullPathEligibility.candidates keys).isEmpty do
        throw (IO.userError "unexpected promotion gate after Rule 5")
      unless RingFullPathRule5.score? i read rev ⟨a,some f⟩ ⟨b,some f⟩ == some 0 do
        throw (IO.userError "fixed-reference Rule 5 failed to tie")
      IO.println s!"Geometry mirror={rev}: only the N ligands tie after Rule 5. No promotion candidate."
      (← IO.getStdout).flush
    unless RingZeroDuplicateMass.compareAt? i f a b == some .eq do throw (IO.userError "constitutional comparison")
    let result : RingRetainedStereoDecision.Result := ⟨some .likePair,1⟩
    unless RingOccurrenceStereo.comparison? i f a b read == some (result,result) do
      throw (IO.userError "expected the grouped Rule 4b decision on both geometries")
    have rootLaw : RingGroupedPublication.publish? i f read = RingGroupedPublication.state i f := by
      rw [exactReader, ← RingGroupedPublication.state_eq]
    let wanted : RingActiveDistanceSchedule.Cell := some (some (.chiral .R,.chiral .S))
    if h : RingGroupedPublication.publish? i f read = wanted then
      let _verified : RingGroupedPublication.state i f = wanted := rootLaw.symm.trans h
      IO.println "Reachable grouped result: actual R, mirror S, Rule 4b scores (+1,+1)"
    else throw (IO.userError "unexpected grouped result at the root")
  else throw (IO.userError "coordinate admission")
