import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.BlueBookCarbonReports
import TetraStereo.Examples.BlueBookRingAssembly
import TetraStereo.Examples.Rule6CageAuxiliaries
import TetraStereo.Examples.RingSignedTwoPairSpiro
import TetraStereo.Examples.CentresRingSpiroCasing

namespace TetraStereo.Examples.ReferenceDerivations
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority Recursive

private def requireReport (m : RawMolecule) (g : Geometry) (depth fuel : Nat)
    (expected : List (Nat × Option LocalizedAuxiliaryLabel)) : IO Unit := do
  let some report := deriveRingReferenceCarbons? m g depth fuel |
    throw (IO.userError s!"unresolved carbon in {m.atomCount}-atom report, expected {repr expected}")
  unless report.labels == expected do
    throw (IO.userError s!"expected {repr expected}, derived {repr report.labels}")

private def assembly (a b : RS) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  (List.range 17).map fun k => (k+1,match k+1 with
    | 1 | 13 => some (.chiral a)
    | 4 => some (.pseudoasymmetric .r)
    | 8 => some (.chiral b)
    | 10 => some (.pseudoasymmetric .s)
    | _ => none)

private def requireAnswer (m : RawMolecule) (g : Geometry) (depth fuel : Nat)
    (p : List Nat) (i j : Nat) (want : CentresRing.ComparisonAgreement.Answer) : IO Unit := do
  let got := do
    let cert ← deriveRingReferenceOccurrence? m g depth fuel p
    let frame ← cert.frame? depth
    let row ← frame.rows.find? (fun r => r.i == i && r.j == j)
    CentresRing.ComparisonAgreement.answer? row.basis none
  unless got == some want do
    throw (IO.userError s!"priority at {repr p}, {i} versus {j}: expected {repr want}, derived {repr got}")

def check : IO Unit := do
  for rev in [false,true] do
    let geom (g : Geometry) := if rev then mirror g else g
    requireAnswer BlueBookRule4aSource.molecule (geom BlueBookRule4aSource.geometry) 1 3
      [4] 3 5 ⟨some .stereoClass,1⟩
    let m := BlueBookRingAssembly.molecule
    let g := geom BlueBookRingAssembly.geometry
    requireAnswer m g 3 5 [1] 2 6 ⟨some .likePair,1⟩
    requireAnswer m g 3 5 [8] 7 9 ⟨some .lower,1⟩
    requireAnswer m g 3 5 [4] 3 5 ⟨some .handedPair,if rev then 2 else -2⟩
  requireReport Rule6CageAuxiliaries.spiroPentane (fun _ => none) 1 1
    ((List.range 5).map (·,none))
  requireReport BlueBookRule4aSource.molecule BlueBookRule4aSource.geometry 1 3
    BlueBookCarbonReports.alcoholExpected
  requireReport BlueBookCyclobutanediol.molecule BlueBookCyclobutanediol.invertedThird 2 2
    (BlueBookCarbonReports.diolExpected .s)
  for rev in [false,true] do
    let geom (g : Geometry) := if rev then mirror g else g
    let a : RS := if rev then .R else .S
    let b := a.swap
    requireReport CentresRing.SpiroSource.molecule (geom BlueBookCarbonReports.spiroGeometry) 1 1
      (BlueBookCarbonReports.spiroExpected b)
    requireReport BlueBookCyclobutanediol.molecule (geom BlueBookCyclobutanediol.geometry) 2 2
      (BlueBookCarbonReports.diolExpected .r)
    requireReport BlueBookRingAssembly.molecule (geom BlueBookRingAssembly.geometry) 3 5 (assembly a b)
    let signedLabels := [some (.chiral a),some (.chiral a),some (.chiral b),some (.chiral a),
      some (.chiral b),none,none,none,none]
    requireReport RingSignedTwoPairSpiro.molecule (geom RingSignedTwoPairSpiro.geometry) 2 3
      (signedLabels.zipIdx.map fun (v,i) => (i,v))
    let some sc := deriveRingReferenceOccurrence? RingSignedTwoPairSpiro.molecule
        (geom RingSignedTwoPairSpiro.geometry) 2 3 [0] | throw (IO.userError "signed spiro")
    let absent := InventoryPriority.omissions sc.published
    unless absent.length == 8 && RingSignedTwoPairSpiro.omissions.all absent.contains do
      throw (IO.userError s!"different auxiliary omission paths {repr absent}")
    let fluoro := [some (.chiral a),some (.chiral b),some (.chiral a),some (.chiral b),some (.chiral a)]
    requireReport CentresRingSpiroCasing.molecule (geom (fun i => CentresRingSpiroCasing.spatial.positions[i]?)) 2 2
      (fluoro.zipIdx.map fun (v,i) => (i,v))
    requireReport CentresRingSpiroCasing.renumbered (geom (fun i => CentresRingSpiroCasing.moved.positions[i]?)) 2 2
      ((List.range 5).map fun i => (i,(fluoro[CentresRingSpiroCasing.rename i]?).join))
    let some c := deriveRingReferenceOccurrence? Rule6CageAuxiliaries.twins
      (geom Rule6CageAuxiliaries.twinGeometry) 2 3 [0] | throw (IO.userError "two-cage parent")
    unless c.verdict.bind Reading.label == some (.pseudoasymmetric .r) && c.published.length == 32 &&
        c.published.lookup [0,3] == some (some ⟨a,b⟩) && c.published.lookup [0,22] == some (some ⟨b,a⟩) do
      throw (IO.userError "two-cage verdict or bridgehead publications")
    let some bridge := deriveRingReferenceOccurrence? Rule6CageAuxiliaries.twins
      (geom Rule6CageAuxiliaries.twinGeometry) 2 2 [0,3] | throw (IO.userError "missing bridgehead")
    let some comparison := bridge.compare? 5 6 4 | throw (IO.userError "missing signed comparison")
    unless comparison.verdict.ordering == .lt && comparison.verdict.route? == some [6,9,12,4] do
      throw (IO.userError "incorrect molecular route in the recursively published table")
    IO.println s!"Verified complete ring reports and both bridgehead publications (reflection {rev})."
  unless (deriveRingReferenceOccurrence? Rule6CageAuxiliaries.twins
      Rule6CageAuxiliaries.twinGeometry 2 0 [0]).isNone do
    throw (IO.userError "zero fuel assigned a verdict")

end TetraStereo.Examples.ReferenceDerivations

def main := TetraStereo.Examples.ReferenceDerivations.check
