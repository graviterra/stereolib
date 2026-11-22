import TetraStereo.Examples.RingDimethylThiiraneBoundary
import TetraStereo.Engine.CentresRing
import TetraStereo.Engine.CentresRingMolecularMass
import TetraStereo.Engine.RingScheduledCarbonReport
import TetraStereo.Engine.RingRetainedChemicalTrace
import TetraStereo.Engine.RingRetainedSilentPair

set_option autoImplicit false

namespace TetraStereo.Examples.RingRetainedMethylRefusal
open Engine OneCenter LocalizedGenericMarkedRecalculation
open RingDimethylThiiraneBoundary (molecule spatial geometry)

/-- Putting the earlier methyl first would produce opposite uppercase letters
on the two original digraphs, on exactly the same molecular coordinates. -/
theorem depth_order_readbacks :
    readback? geometry [2,1,3,4] = some .S ∧ readback? geometry [2,1,4,3] = some .R ∧
    readback? (mirror geometry) [2,1,3,4] = some .R ∧ readback? (mirror geometry) [2,1,4,3] = some .S := by
  decide +kernel

private def molecularRequest (m : RawMolecule) (reflected : Bool) : String :=
  let frames := if reflected then
    ["f 0 S 1 2 3 4","f 1 R 0 2 5 6","f 3 R 0 7 8 9","f 4 S 0 10 11 12"]
    else ["f 0 R 1 2 3 4","f 1 S 0 2 5 6","f 3 S 0 7 8 9","f 4 R 0 10 11 12"]
  String.intercalate "\n" (["centres-1.0"] ++
    m.atoms.map (fun a => s!"a {a.element.atomicNumber} {a.isotope?.getD 0} {a.charge}") ++
    m.bonds.map (fun b => s!"b {b.source} {b.target}") ++ frames) ++ "\n"

private def checkRoot (i : LocalizedChemicalRing.Input) (start other : Nat) : IO Unit := do
  let root : i.certified.Atom ← if h : start < i.certified.certified.input.molecule.atomCount then
    pure ⟨start,h⟩ else throw (IO.userError s!"missing methyl {start}")
  let sites := (RingActiveDistanceSchedule.sites i).filter fun s => s.val.root == root
  let get (path : List Nat) : IO (RingActivePairs.Site i) := do
    let some s := sites.find? (fun s => s.val.node.provenance == .realAtom &&
        s.val.node.history.map Fin.val == path) | throw (IO.userError s!"missing real occurrence {path}")
    return s
  let focus ← get [0,start]
  let inward ← get [start]
  let outward ← get [other,0,start]
  let some legacy := RingRetainedConstitution.compareAt? i.certified focus inward outward |
    throw (IO.userError "missing retained comparator baseline")
  unless legacy.map (·.outcome) == [.eq,.gt,.eq] do
    throw (IO.userError s!"expected separation on original depth only, got {repr legacy}")
  let some corrected := RingRetainedChemicalTrace.compareAt? i focus inward outward |
    throw (IO.userError "missing molecular methyl comparison")
  unless corrected.map (·.outcome) == [.eq,.eq,.eq] do
    throw (IO.userError s!"expected equality through Rule 2, got {repr corrected}")
  let rank (a : Nat) := if a == 2 then 2 else if a == 1 then 1 else 0
  let direction (a : Nat) := if a == start then pure inward else get [a,0,start]
  for a in [2,1,start,other] do
    for b in [2,1,start,other] do
      if a != b then
        let l ← direction a
        let r ← direction b
        let some trace := RingRetainedChemicalTrace.compareAt? i focus l r |
          throw (IO.userError s!"missing comparison {a}/{b}")
        unless cipTraceOutcome trace == compare (rank a) (rank b) do
          throw (IO.userError s!"incorrect order for {a}/{b}")
  unless (RingRetainedAuxiliary.publication? i focus).isNone do
    throw (IO.userError "direct constitutional ranker claimed a value despite methyl equality")
  let some refusal := RingRetainedSilentPair.find? i focus |
    throw (IO.userError "missing structural methyl-pair refusal")
  unless refusal.focus == 0 && ([refusal.exchange.left,refusal.exchange.right].mergeSort (· ≤ ·)) == [3,4] do
    throw (IO.userError "refusal certificate names a different pair")
  let view := RingActiveDistanceSchedule.snapshot (RingMolecularSchedule.publicationTable i root)
  unless view focus == some none do
    throw (IO.userError s!"expected a proved absence at {[0,start]}, got {repr (view focus)}")
  IO.println s!"root C{start}, auxiliary C0: S2 > C1 > C{start} = C{other}; both methyls real, refusal published"

/-- P-92.3 gives ordinary H and an explicit ¹H the same datum. Centres 1.0
uses a natural-abundance value for ordinary H. For ²H the comparison is strict
in the same direction under both conventions. -/
theorem hydrogen_spelling :
    CIPRule2MassData.rule2MassPico? 1 none = CIPRule2MassData.rule2MassPico? 1 (some 1) ∧
    CentresRing.Molecular.massMicro 1 1 < CentresRing.Molecular.massMicro 1 0 ∧
    (CIPRule2MassData.rule2MassPico? 1 none).getD 0 < (CIPRule2MassData.rule2MassPico? 1 (some 2)).getD 0 ∧
    CentresRing.Molecular.massMicro 1 0 < CentresRing.Molecular.massMicro 1 2 :=
  ⟨CIPRule2MassData.ordinary_hydrogen_eq_protium,by decide,CIPRule2MassData.ordinary_hydrogen_lt_deuterium,by decide⟩

private def checkIsotope (mass : Nat) (reflected : Bool) (g : SpatialConfiguration) : IO Unit := do
  let m := {molecule with atoms := molecule.atoms.set 6 {element := .H,isotope? := some mass}}
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "isotope intake failed")
  let req ← IO.ofExcept (CentresRing.request i)
  unless req == molecularRequest m reflected do throw (IO.userError "isotope control request differs")
  let root : i.certified.Atom ← if h : 1 < i.certified.certified.input.molecule.atomCount then
    pure ⟨1,h⟩ else throw (IO.userError "isotope control missing C1")
  let sites := (RingActiveDistanceSchedule.sites i).filter fun q => q.val.root == root
  let get (path : List Nat) : IO (RingActivePairs.Site i) := do
    let some q := sites.find? (fun q => q.val.node.provenance == .realAtom && q.val.node.history.map Fin.val == path) |
      throw (IO.userError s!"missing isotope control occurrence {path}")
    return q
  let focus ← get [1]
  let left ← get [5,1]
  let right ← get [6,1]
  let some trace := RingRetainedChemicalTrace.compareAt? i focus left right |
    throw (IO.userError "missing isotope comparison")
  let massOrder : Ordering := if mass == 1 then .eq else .lt
  unless trace.map (·.outcome) == [.eq,.eq,massOrder] do throw (IO.userError s!"incorrect isotope trace {repr trace}")
  let table := RingActiveDistanceSchedule.snapshot (RingMolecularSchedule.publicationTable i root)
  if mass == 1 then
    unless (RingRetainedAuxiliary.publication? i focus).isNone && table focus == some none do
      throw (IO.userError s!"expected a scheduled refusal for H and ¹H, got {repr (table focus)}")
    let some report := RingScheduledCarbonReport.report? i 1 |
      throw (IO.userError "no public whole-carbon report on the ¹H control")
    unless RingScheduledCarbonReport.labels report == [(0,none),(1,none),(3,none),(4,none)] do
      throw (IO.userError s!"incorrect public report on the ¹H control: {repr (RingScheduledCarbonReport.labels report)}")
  else
    let hand : RS := if reflected then .R else .S
    unless (RingRetainedAuxiliary.publication? i focus) == some (some hand) &&
        table focus == some (some (.chiral hand,.chiral hand.swap)) do
      throw (IO.userError s!"incorrect absolute letter on the ²H control: {repr (table focus)}")
  IO.println s!"C1, H6 mass {mass}, reflected {reflected}: {repr (table focus)}"

def validate : IO Unit := do
  for reflected in [false,true] do
    let g := if reflected then ⟨spatial.positions.map CartesianPoint3.reflectX⟩ else spatial
    let some i := LocalizedChemicalRing.admitRawSpatial? molecule g |
      throw (IO.userError "coordinate intake failed")
    let req ← IO.ofExcept (CentresRing.request i)
    unless req == molecularRequest molecule reflected do
      throw (IO.userError s!"pinned dimethylthiirane request differs: {req}")
    checkRoot i 3 4
    checkRoot i 4 3
    checkIsotope 1 reflected g
    checkIsotope 2 reflected g

end TetraStereo.Examples.RingRetainedMethylRefusal

assert_kernel_only TetraStereo.Examples.RingRetainedMethylRefusal.depth_order_readbacks
assert_kernel_only TetraStereo.Examples.RingRetainedMethylRefusal.hydrogen_spelling
