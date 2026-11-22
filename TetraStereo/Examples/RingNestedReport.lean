import TetraStereo.Examples.RingNestedAbsence
import TetraStereo.Engine.RingCarbonReport

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false

namespace TetraStereo.Examples.RingNestedReport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine RingChemicalPriority Recursive RingNestedAbsence

/-- The central CHF carbon and the four carbons in each cyclobutyl ring,
in molecular index order. -/
def allAbsent : List (Nat × Option LocalizedAuxiliaryLabel) :=
  [0,3,4,5,6,14,15,16,17].map fun i => (i,none)

/-- A single isotope at C4 creates two stereogenic centers. The labelled
C4 remains CH₂ and the other ring attachment carbon C14 remains
nonstereogenic under its own fresh-root comparison. -/
def labelled (hand : RS) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  [(0,some (.chiral hand)),(3,some (.chiral hand)),(4,none),(5,none),(6,none),
   (14,none),(15,none),(16,none),(17,none)]

def report (m : RawMolecule) (g : Geometry) :=
  Engine.classifyRingCarbons? m g 2 (fun _ => none) (fun _ => 1)

def labels (m : RawMolecule) (g : Geometry) := (report m g).map (·.labels)

private def carbonIds : List Nat := [0,3,4,5,6,14,15,16,17]

private def methylenes : List Nat := [4,5,6,15,16,17]

private def row (m : RawMolecule) (g : Geometry) (i : Nat) :=
  (RingCarbonReport.atCarbon? m g 2 (fun _ => none) (fun _ => 1) i).map
    RingCarbonReport.Verdict.label

private def expected (hand : Option RS) (i : Nat) : Option LocalizedAuxiliaryLabel :=
  if i = 0 ∨ i = 3 then hand.map (fun h => .chiral h) else none

private structure StructureChecks (m : RawMolecule) : Prop where
  domain : saturatedWithHalogens m = true
  carbons : RingCarbonReport.carbons m = carbonIds
  hydrogens : ∀ i ∈ methylenes, (RingCarbonReport.hydrogens? m i).isSome = true

private def reversed (mass : Nat) : RawMolecule :=
  {molecule mass with bonds := (molecule mass).bonds.reverse}

private theorem checks12 : StructureChecks (molecule 12) := by constructor <;> decide +kernel
private theorem checks13 : StructureChecks (molecule 13) := by constructor <;> decide +kernel
private theorem reversed12 : StructureChecks (reversed 12) := by constructor <;> decide +kernel
private theorem reversed13 : StructureChecks (reversed 13) := by constructor <;> decide +kernel

/-- Six CH₂ rows follow on every geometry from the incident identical hydrogen pair.
The only molecular stereochemistry computations in the assembly are the three
independently proved rows passed as arguments. -/
private theorem assemble {m : RawMolecule} {g : Geometry} (checks : StructureChecks m)
    (hand : Option RS)
    (c0 : row m g 0 = some (expected hand 0))
    (c3 : row m g 3 = some (expected hand 3))
    (c14 : row m g 14 = some none) :
    labels m g = some (carbonIds.map fun i => (i,expected hand i)) := by
  have hydrogen (i : Nat) (member : i ∈ methylenes) (carbon : i ∈ RingCarbonReport.carbons m) :
      row m g i = some none :=
    RingCarbonReport.atCarbon?_label_of_hydrogens checks.domain
      (RingCarbonReport.mem_carbons.mp carbon).2 (checks.hydrogens i member)
  have result := Engine.classifyRingCarbons?_labels_of_rows
    (g := g) (fuel := 2) (hint := fun _ => none) (radius := fun _ => 1)
    (expected hand) checks.domain (by
      intro i member
      have original := member
      rw [checks.carbons] at member
      simp only [carbonIds,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact c0
      · exact c3
      · exact hydrogen _ (by decide) original
      · exact hydrogen _ (by decide) original
      · exact hydrogen _ (by decide) original
      · exact c14
      · exact hydrogen _ (by decide) original
      · exact hydrogen _ (by decide) original
      · exact hydrogen _ (by decide) original)
  rw [checks.carbons] at result
  exact result

private theorem equalCenter {g : Geometry} (h : reading 12 g [0] 2 = some none) :
    row (molecule 12) g 0 = some none := by
  unfold row
  rw [RingCarbonReport.atCarbon?_label_of_no_hydrogens (i := 0) checks12.domain (by decide +kernel)
    (by decide +kernel)]
  have projected := congrArg (fun x : Option (Option Reading) => x.map (fun y => y.bind Reading.label)) h
  simpa only [reading,atSite,Option.map_map,Function.comp_def,Option.map_some] using projected

private theorem equalAt3 : row (molecule 12) geometry 3 = some none := by
  decide +kernel

private theorem equalAt14 : row (molecule 12) geometry 14 = some none := by
  decide +kernel

private theorem equalMirrorAt3 : row (molecule 12) (mirror geometry) 3 = some none := by
  decide +kernel

private theorem equalMirrorAt14 : row (molecule 12) (mirror geometry) 14 = some none := by
  decide +kernel

private theorem isotopeAt0 : row (molecule 13) geometry 0 = some (some (.chiral .S)) := by
  decide +kernel

private theorem isotopeAt3 : row (molecule 13) geometry 3 = some (some (.chiral .S)) := by
  decide +kernel

private theorem isotopeAt14 : row (molecule 13) geometry 14 = some none := by
  decide +kernel

private theorem isotopeMirrorAt0 : row (molecule 13) (mirror geometry) 0 = some (some (.chiral .R)) := by
  decide +kernel

private theorem isotopeMirrorAt3 : row (molecule 13) (mirror geometry) 3 = some (some (.chiral .R)) := by
  decide +kernel

private theorem isotopeMirrorAt14 : row (molecule 13) (mirror geometry) 14 = some none := by
  decide +kernel

private theorem reverseEqualAt0 : row (reversed 12) geometry 0 = some none := by
  decide +kernel

private theorem reverseEqualAt3 : row (reversed 12) geometry 3 = some none := by
  decide +kernel

private theorem reverseEqualAt14 : row (reversed 12) geometry 14 = some none := by
  decide +kernel

private theorem reverseIsotopeAt0 : row (reversed 13) geometry 0 = some (some (.chiral .S)) := by
  decide +kernel

private theorem reverseIsotopeAt3 : row (reversed 13) geometry 3 = some (some (.chiral .S)) := by
  decide +kernel

private theorem reverseIsotopeAt14 : row (reversed 13) geometry 14 = some none := by
  decide +kernel

/-- All nine carbons lack a descriptor at equal isotope mass. Each CH₂ row
follows from its hydrogen pair on both geometries. -/
theorem equal_mass_report :
    labels (molecule 12) geometry = some allAbsent ∧
    labels (molecule 12) (mirror geometry) = some allAbsent := by
  exact ⟨assemble checks12 none (equalCenter nested_absences.2.2.2.1) equalAt3 equalAt14,
    assemble checks12 none (equalCenter nested_absences.2.2.2.2) equalMirrorAt3 equalMirrorAt14⟩

/-- The two freshly rooted orders at C0 and C3 give uppercase S on the
source geometry and uppercase R after reflection. -/
theorem one_isotope_report :
    labels (molecule 13) geometry = some (labelled .S) ∧
    labels (molecule 13) (mirror geometry) = some (labelled .R) := by
  exact ⟨assemble checks13 (some .S) isotopeAt0 isotopeAt3 isotopeAt14,
    assemble checks13 (some .R) isotopeMirrorAt0 isotopeMirrorAt3 isotopeMirrorAt14⟩

/-- Reversing bond enumeration preserves every freshly rooted decision. -/
theorem reversed_bond_reports :
    labels {molecule 12 with bonds := (molecule 12).bonds.reverse} geometry = some allAbsent ∧
    labels {molecule 13 with bonds := (molecule 13).bonds.reverse} geometry = some (labelled .S) := by
  exact ⟨assemble reversed12 none reverseEqualAt0 reverseEqualAt3 reverseEqualAt14,
    assemble reversed13 (some .S) reverseIsotopeAt0 reverseIsotopeAt3 reverseIsotopeAt14⟩

private theorem no_report_at_zero {m : RawMolecule} {g : Geometry} {fuel : Nat}
    (member : 0 ∈ RingCarbonReport.carbons m)
    (failure : (RingCarbonReport.atCarbon? m g fuel (fun _ => none) (fun _ => 1) 0).isSome = false) :
    (Engine.classifyRingCarbons? m g fuel (fun _ => none) (fun _ => 1)).isNone = true := by
  cases found : Engine.classifyRingCarbons? m g fuel (fun _ => none) (fun _ => 1) with
  | none => rfl
  | some r =>
    have hasReport : (Engine.classifyRingCarbons? m g fuel (fun _ => none) (fun _ => 1)).isSome = true := by
      rw [found]; rfl
    have present := (Engine.classifyRingCarbons?_isSome.mp hasReport).2 0 member
    rw [failure] at present
    contradiction

/-- Exhausting the budget at the nested C0 absence or removing the F
coordinate required at isotope-resolved C0 prevents report emission. -/
theorem incomplete_inputs :
    (Engine.classifyRingCarbons? (molecule 12) geometry 1 (fun _ => none) (fun _ => 1)).isNone =
        true ∧
    (report (molecule 13) (fun i => if i = 1 then none else geometry i)).isNone = true := by
  constructor
  · exact no_report_at_zero (by rw [checks12.carbons]; decide) (by decide +kernel)
  · exact no_report_at_zero (by rw [checks13.carbons]; decide) (by decide +kernel)

end TetraStereo.Examples.RingNestedReport

assert_kernel_only TetraStereo.Examples.RingNestedReport.equal_mass_report
assert_kernel_only TetraStereo.Examples.RingNestedReport.one_isotope_report
assert_kernel_only TetraStereo.Examples.RingNestedReport.reversed_bond_reports
assert_kernel_only TetraStereo.Examples.RingNestedReport.incomplete_inputs
