import TetraStereo.Engine.RingOccurrenceTable
import TetraStereo.Examples.BlueBookCarbonReports

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option Elab.async false

namespace TetraStereo.Examples.BlueBookCarbonReportStability
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority
open BlueBookCyclobutanediol (molecule geometry invertedThird)
open BlueBookCarbonReports (diolExpected)

/-- The four distinct occurrence addresses compare the two routes between
the methines in the P-92.6 ring. Each route stops at a duplicate before
it can reach another auxiliary candidate. -/
theorem diol_frontier :
    let roots := [[0],[2]]
    let next := OccurrenceTable.frontierAt molecule 1 roots
    next.length = 4 ∧ [0,1,2] ∈ next ∧ [0,3,2] ∈ next ∧
      [2,1,0] ∈ next ∧ [2,3,0] ∈ next ∧
      OccurrenceTable.frontierAt molecule 2 roots = [] := by
  decide +kernel

/-- At both methines the complete dependent result stabilizes by fuel two
for any coordinates, choice of frames and constitutional search radius. -/
theorem diol_methines (g : Geometry) (hint : List Nat → Option Recursive.Frame)
    (radius : List Nat → Nat) (extra i : Nat) (methine : i = 0 ∨ i = 2) :
    RingAuxiliaryInventory.classify? molecule g hint radius 2 [i] =
      RingAuxiliaryInventory.classify? molecule g hint radius (2+extra) [i] := by
  apply OccurrenceTable.stable_of_empty_frontier molecule g hint radius 2 extra [[0],[2]]
  · exact diol_frontier.2.2.2.2.2
  · rcases methine with rfl | rfl <;> decide

private def expected (h : PseudoRS) (i : Nat) : Option LocalizedAuxiliaryLabel :=
  if i = 0 ∨ i = 2 then some (.pseudoasymmetric h) else none

private def atFuel (g : Geometry) (fuel i : Nat) :=
  (RingCarbonReport.atCarbon? molecule g fuel (fun _ => none) (fun _ => 2) i).map
    RingCarbonReport.Verdict.label

private theorem domain : saturatedWithHalogens molecule = true := by decide +kernel

private theorem methineRow (g : Geometry) (extra i : Nat) (methine : i = 0 ∨ i = 2) :
    atFuel g 2 i = atFuel g (2+extra) i := by
  have carbon : (molecule.atoms[i]?).any (fun a => a.element == .C) = true := by
    rcases methine with rfl | rfl <;> decide +kernel
  have noH : (RingCarbonReport.hydrogens? molecule i).isNone = true := by
    rcases methine with rfl | rfl <;> decide +kernel
  unfold atFuel
  simp only [RingCarbonReport.atCarbon?_label_of_no_hydrogens domain carbon noH,
    diol_methines g (fun _ => none) (fun _ => 2) extra i methine]

private theorem report_from_methines (g : Geometry) (h : PseudoRS) (extra : Nat)
    (first : atFuel g 2 0 = some (some (.pseudoasymmetric h)))
    (third : atFuel g 2 2 = some (some (.pseudoasymmetric h))) :
    (classifyDiscoveredRingCarbons? molecule g (2+extra) 2).map (·.labels) =
      some (diolExpected h) := by
  have ids : RingCarbonReport.carbons molecule = [0,1,2,3] := by decide +kernel
  have hydrogen (i : Nat) (methylene : i = 1 ∨ i = 3) : atFuel g (2+extra) i = some none := by
    apply RingCarbonReport.atCarbon?_label_of_hydrogens domain
    · rcases methylene with rfl | rfl <;> decide +kernel
    · rcases methylene with rfl | rfl <;> decide +kernel
  have rows (i : Nat) (present : i ∈ RingCarbonReport.carbons molecule) :
      atFuel g (2+extra) i = some (expected h i) := by
    rw [ids] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl | rfl
    · exact (methineRow g extra 0 (Or.inl rfl)).symm.trans first
    · exact hydrogen 1 (Or.inl rfl)
    · exact (methineRow g extra 2 (Or.inr rfl)).symm.trans third
    · exact hydrogen 3 (Or.inr rfl)
  exact (classifyRingCarbons?_labels_of_rows (expected h) domain rows).trans (by rw [ids]; rfl)

/-- Both published methines remain lowercase r after reflection. Inverting
one methine gives the independently checked stereoisomer with two lowercase s
descriptors. The complete reports include the two nonstereogenic CH₂ sites. -/
theorem diol_reports (extra : Nat) :
    (classifyDiscoveredRingCarbons? molecule geometry (2+extra) 2).map (·.labels) =
        some (diolExpected .r) ∧
    (classifyDiscoveredRingCarbons? molecule (mirror geometry) (2+extra) 2).map (·.labels) =
        some (diolExpected .r) ∧
    (classifyDiscoveredRingCarbons? molecule invertedThird (2+extra) 2).map (·.labels) =
        some (diolExpected .s) := by
  exact ⟨report_from_methines geometry .r extra (by decide +kernel) (by decide +kernel),
    report_from_methines (mirror geometry) .r extra (by decide +kernel) (by decide +kernel),
    report_from_methines invertedThird .s extra (by decide +kernel) (by decide +kernel)⟩

end TetraStereo.Examples.BlueBookCarbonReportStability

assert_kernel_only TetraStereo.Examples.BlueBookCarbonReportStability.diol_frontier
assert_kernel_only TetraStereo.Examples.BlueBookCarbonReportStability.diol_methines
assert_kernel_only TetraStereo.Examples.BlueBookCarbonReportStability.diol_reports
