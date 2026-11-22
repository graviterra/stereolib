import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.RingNestedReport
import TetraStereo.Examples.RingDiscoveredFrames
import TetraStereo.Examples.BlueBookCarbonReports
import TetraStereo.Examples.BlueBookCarbonReportStability
import TetraStereo.Examples.BlueBookRingAssembly
import TetraStereo.Examples.Rule6CageAuxiliaries
import TetraStereo.Examples.RingTwoPairFluorospiro
import TetraStereo.Examples.RingSignedTwoPairSpiro

set_option autoImplicit false

namespace TetraStereo.Examples.DiscoveredReports
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority Recursive

private def requireLabels (m : RawMolecule) (g : Geometry) (fuel depth : Nat)
    (expected : List (Nat × Option LocalizedAuxiliaryLabel)) : IO Unit := do
  let some report := classifyDiscoveredRingCarbons? m g fuel depth |
    throw (IO.userError "unresolved carbon in the whole report")
  unless report.labels == expected do
    throw (IO.userError s!"unexpected carbon report {repr report.labels}")

def assemblyLabels (reflected : Bool) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  (List.range 17).map fun k =>
    let i := k+1
    (i, match i with
      | 1 | 13 => some (.chiral (if reflected then .R else .S))
      | 4 => some (.pseudoasymmetric .r)
      | 8 => some (.chiral (if reflected then .S else .R))
      | 10 => some (.pseudoasymmetric .s)
      | _ => none)

private structure ExpectedDecision where
  path : List Nat
  stage : Stage
  left : Facts
  right : Facts
  actual : List Nat
  reflected : List Nat
  reading : Reading

private def decidingStage {m p d f ls rs x y} :
    @DiscoveredPriority.Basis m p d f ls rs x y → Option Stage
  | .classes _ => none
  | .stereo s .. => some s

private def signedEntries (facts : Facts) (rev : Bool) : InventoryPriority.Entries :=
  facts.map fun (p,r) => (p,some (if rev then r.reverse else r))

/-- Check the first discovered rule, each complete addressed auxiliary
inventory and both orders against the expected geometry readings. Either
enumeration of the two compared arms is permissible. -/
private def requireDecision (m : RawMolecule) (g : Geometry) (fuel depth : Nat)
    (rev : Bool) (want : ExpectedDecision) : IO Unit := do
  let some cert := inspectRingOccurrence? m g want.path fuel (fun _ => none) (fun _ => depth) |
    throw (IO.userError s!"no occurrence result at {repr want.path}")
  let .discovered found := cert.val |
    throw (IO.userError s!"no discovered priority proof at {repr want.path}")
  let stage := decidingStage found.step.basis
  unless stage == some want.stage do
    throw (IO.userError s!"unexpected stage {repr stage} at {repr want.path}")
  let left := signedEntries want.left rev
  let right := signedEntries want.right rev
  let same := (found.left.Perm left ∧ found.right.Perm right) ∨
    (found.left.Perm right ∧ found.right.Perm left)
  unless decide same do
    throw (IO.userError s!"unexpected signed ligand paths at {repr want.path}: {repr (found.left,found.right)}")
  let actual := if rev then want.reflected else want.actual
  let reflected := if rev then want.actual else want.reflected
  unless found.step.actual.ligands == actual && found.step.reflected.ligands == reflected &&
      found.reading == (if rev then want.reading.reverse else want.reading) do
    throw (IO.userError s!"unexpected ligand order or reading at {repr want.path} (mirror {rev})")

/-- The full addressed auxiliaries in the P-93.6 proof, in the original
numbering. Paths to the same physical atom through different ring routes
remain separate. -/
private def assemblyDecisions : List ExpectedDecision :=
  [⟨[8],.fourC,
    [([8,7,4],⟨.R,.R⟩),([8,7,4,3,2,1],⟨.S,.R⟩),([8,7,4,5,6,1],⟨.R,.S⟩)],
    [([8,9,10],⟨.S,.S⟩),([8,9,10,11,12,13],⟨.S,.R⟩),([8,9,10,15,14,13],⟨.R,.S⟩)],
    [0,7,9,31],[0,7,9,31],⟨.R,.S⟩⟩,
   ⟨[1],.fourB,
    [([1,2,3,4],⟨.S,.R⟩),([1,2,3,4,7,8],⟨.S,.R⟩),([1,2,3,4,7,8,9,10],⟨.S,.S⟩),
     ([1,2,3,4,7,8,9,10,11,12,13],⟨.S,.R⟩),([1,2,3,4,7,8,9,10,15,14,13],⟨.R,.S⟩)],
    [([1,6,5,4],⟨.R,.S⟩),([1,6,5,4,7,8],⟨.S,.R⟩),([1,6,5,4,7,8,9,10],⟨.S,.S⟩),
     ([1,6,5,4,7,8,9,10,11,12,13],⟨.S,.R⟩),([1,6,5,4,7,8,9,10,15,14,13],⟨.R,.S⟩)],
    [2,6,17,19],[2,6,17,19],⟨.S,.R⟩⟩,
   ⟨[13],.fourB,
    [([13,12,11,10],⟨.R,.S⟩),([13,12,11,10,9,8],⟨.R,.S⟩),([13,12,11,10,9,8,7,4],⟨.R,.R⟩),
     ([13,12,11,10,9,8,7,4,3,2,1],⟨.S,.R⟩),([13,12,11,10,9,8,7,4,5,6,1],⟨.R,.S⟩)],
    [([13,14,15,10],⟨.S,.R⟩),([13,14,15,10,9,8],⟨.R,.S⟩),([13,14,15,10,9,8,7,4],⟨.R,.R⟩),
     ([13,14,15,10,9,8,7,4,3,2,1],⟨.S,.R⟩),([13,14,15,10,9,8,7,4,5,6,1],⟨.R,.S⟩)],
    [12,14,16,39],[12,14,16,39],⟨.S,.R⟩⟩,
   ⟨[4],.five,[([4,3,2,1],⟨.S,.R⟩)],[([4,5,6,1],⟨.R,.S⟩)],
    [7,5,3,24],[7,3,5,24],⟨.R,.R⟩⟩,
   ⟨[10],.five,[([10,11,12,13],⟨.S,.R⟩)],[([10,15,14,13],⟨.R,.S⟩)],
    [9,15,11,34],[9,11,15,34],⟨.S,.S⟩⟩]

/-- Reverse the eleven atom indices in the constructed bottom-pair fixture.
The original bond-list order and all coordinates are transported. -/
private def reverseId (i : Nat) := 10-i

private def renumbered : RawMolecule where
  atoms := RingDiscoveredFrames.molecule.atoms.reverse
  bonds := RingDiscoveredFrames.molecule.bonds.map fun b =>
    {b with source := reverseId b.source, target := reverseId b.target}

private def renumberedGeometry : Geometry := fun i =>
  if i < 11 then RingDiscoveredFrames.geometry (reverseId i) else none

private def bottom : ExpectedDecision :=
  ⟨[0],.five,[([0,3],⟨.R,.S⟩)],[([0,4],⟨.S,.R⟩)],[1,2,3,4],[1,2,4,3],⟨.S,.S⟩⟩

private def renumberDecision (w : ExpectedDecision) : ExpectedDecision :=
  let paths (fs : Facts) := fs.map fun (p,r) => (p.map reverseId,r)
  {w with path := w.path.map reverseId, left := paths w.left, right := paths w.right,
          actual := w.actual.map reverseId, reflected := w.reflected.map reverseId}

private def checkCachedOccurrences : IO Unit := do
  let m := BlueBookCyclobutanediol.molecule
  let g := BlueBookCyclobutanediol.geometry
  let paths := [[0],[0,1,2],[0,3,2],[0],[999]]
  let some batch := inspectRingOccurrences? m g paths 2 (fun _ => none) (fun _ => 2) |
    throw (IO.userError "diol batch failed admission")
  unless (batch.val.map Sigma.fst).length == 4 do
    throw (IO.userError "repeated root did not produce exactly one cached row")
  for (p,want) in ([([0],some ⟨.R,.R⟩),([0,1,2],some ⟨.R,.S⟩),
      ([0,3,2],some ⟨.S,.R⟩),([999],none)] : List (List Nat × Option Reading)) do
    let actual := OccurrenceTable.read p batch.val
    unless actual.bind (·.reading) == want && actual.isSome == want.isSome do
      throw (IO.userError s!"incorrect cached result at {repr p}")
  requireLabels Rule6CageAuxiliaries.spiroPentane (fun _ => none) 1 0
    [(0,none),(1,none),(2,none),(3,none),(4,none)]

def check : IO Unit := do
  checkCachedOccurrences
  for rev in [false,true] do
    let g := if rev then mirror RingSignedTwoPairSpiro.geometry else RingSignedTwoPairSpiro.geometry
    let hand := if rev then RS.R else RS.S
    let expected : List (Nat × Option LocalizedAuxiliaryLabel) := [hand,hand,hand.swap,hand,hand.swap].zipIdx.map (fun (h,i) => (i,some (.chiral h)))
    requireLabels RingSignedTwoPairSpiro.molecule g (RingSignedTwoPairSpiro.molecule.atomCount+2) 2
      (expected ++ [(5,none),(6,none),(7,none),(8,none)])
    unless RingSignedTwoPairSpiro.inspect g == some (⟨hand,hand.swap⟩,RingSignedTwoPairSpiro.omissions) do
      throw (IO.userError "incorrect signed spiro center or omitted occurrence paths")
  IO.println "Verified all nine carbons and eight certified auxiliary absences in the substituted spiro molecule on both geometries."
  let fluorospiro := CentresRingSpiroCasing.molecule
  let renamed := CentresRingSpiroCasing.renumbered
  for rev in [false,true] do
    let g := if rev then mirror RingTwoPairFluorospiro.geometry else RingTwoPairFluorospiro.geometry
    let g' := if rev then mirror RingTwoPairFluorospiro.movedGeometry else RingTwoPairFluorospiro.movedGeometry
    let labels (hands : List RS) : List (Nat × Option LocalizedAuxiliaryLabel) := hands.zipIdx.map fun (hand,i) =>
      (i,some (.chiral (if rev then hand.swap else hand)))
    requireLabels fluorospiro g (fluorospiro.atomCount+2) 2 (labels [.S,.R,.S,.R,.S])
    requireLabels renamed g' (renamed.atomCount+2) 2 (labels [.R,.R,.S,.S,.S])
  IO.println "Verified all five fluorospiro carbons at the molecular fuel bound under both numberings and their reflections."
  requireLabels BlueBookRule4aSource.molecule BlueBookRule4aSource.geometry 3 1
    BlueBookCarbonReports.alcoholExpected
  requireLabels BlueBookCyclobutanediol.molecule BlueBookCyclobutanediol.geometry 2 2
    (BlueBookCarbonReports.diolExpected .r)
  requireLabels CentresRing.SpiroSource.molecule BlueBookCarbonReports.spiroGeometry 1 1
    (BlueBookCarbonReports.spiroExpected .R)
  for rev in [false,true] do
    let g := if rev then mirror RingNestedAbsence.geometry else RingNestedAbsence.geometry
    requireLabels (RingNestedAbsence.molecule 12) g 2 1 RingNestedReport.allAbsent
    requireLabels (RingNestedAbsence.molecule 13) g 2 1 (RingNestedReport.labelled (if rev then .R else .S))
  IO.println "Verified complete carbon reports for the diol, the Rule 4a alcohol, the spiro example and both isotope variants."
  for rev in [false,true] do
    let g := if rev then mirror BlueBookRingAssembly.geometry else BlueBookRingAssembly.geometry
    requireLabels BlueBookRingAssembly.molecule g 5 3 (assemblyLabels rev)
    for target in assemblyDecisions do
      requireDecision BlueBookRingAssembly.molecule g 5 3 rev target
    requireDecision RingDiscoveredFrames.molecule
      (if rev then mirror RingDiscoveredFrames.geometry else RingDiscoveredFrames.geometry) 2 1 rev bottom
    requireDecision renumbered (if rev then mirror renumberedGeometry else renumberedGeometry)
      2 1 rev (renumberDecision bottom)
  IO.println "Verified all seventeen fresh carbon roots of the P-93.6 two-ring alcohol, five deciding stages with their full paths, and the renumbered bottom pair on both geometries."

end TetraStereo.Examples.DiscoveredReports

def main := TetraStereo.Examples.DiscoveredReports.check

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredPriority.Step.chemical_letter
assert_kernel_only TetraStereo.Engine.RingCarbonReport.Report.absence_of_label
assert_kernel_only TetraStereo.Engine.RingCarbonReport.Report.positive_of_label
assert_kernel_only TetraStereo.Examples.RingDiscoveredFrames.bottom_pair
assert_kernel_only TetraStereo.Examples.RingNestedReport.one_isotope_report
assert_kernel_only TetraStereo.Examples.BlueBookCarbonReports.published_spiro
assert_kernel_only TetraStereo.Engine.inspectRingOccurrences?_lookup
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule.permute_layer
assert_kernel_only TetraStereo.Examples.Rule6CageAuxiliaries.spiroPentane_carbon_report
assert_kernel_only TetraStereo.Engine.classifyRingCarbonsAtBound?_stable
assert_kernel_only TetraStereo.Examples.BlueBookCarbonReportStability.diol_reports
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Step.uppercase
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.presentations
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.all_marks_follow_scaffold
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.renumbered_report
assert_kernel_only TetraStereo.Engine.signedRingPair_omission_evidence
assert_kernel_only TetraStereo.Examples.RingSignedTwoPairSpiro.original_report
assert_kernel_only TetraStereo.Examples.RingSignedTwoPairSpiro.mirror_report
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Trial.same_reading_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.cancellation_iff_equal_counts
