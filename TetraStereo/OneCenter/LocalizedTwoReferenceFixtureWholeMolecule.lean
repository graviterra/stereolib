import TetraStereo.OneCenter.LocalizedOrderedReferencePipeline
import TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory
import TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters
import TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarativeCenters
import TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarative
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Complete ordered report for the 33-atom, nine-centre fixture

The callable ordered reference pipeline returns all nine actual detected centres, with their
unique independently specified geometric letters and Rule-5 case classification.  The auxiliary
interpretation in that specification is explicitly `actualReferenceDescriptorMap input`; the
accepted root theorem supplies its required physical readback, and the eight other centres are
decided by Rule 1a independently of any auxiliary map.

This is concrete whole-report correctness, alongside the ordered runtime's operational fixed
point.  It does not assert a chemical `CIPSpec` fixed point at every auxiliary occurrence, or
extend the molecular domain to rings.  The proof uses the local final-occurrence theorems; it
does not evaluate the full occurrence carrier.
-/

namespace TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixturePhysicalInstance
open LocalizedTwoReferenceFixtureWholeInventory
open LocalizedTwoReferenceFixtureDeclarativeCenters
open Rule4aTableBridge.ActualCentrePhysicalSetup

/-- Labels are indexed by the actual zero-based atom indices. -/
def expectedLabel (center : Center) : LocalizedAuxiliaryLabel :=
  match center.1.1 with
  | 0 => .pseudoasymmetric .r
  | 11 | 19 | 22 | 29 => .chiral .S
  | _ => .chiral .R

def expectedReport : LocalizedOrderedReference.Report :=
  [(0, some (.pseudoasymmetric .r)), (4, some (.chiral .R)),
    (7, some (.chiral .R)), (11, some (.chiral .S)), (14, some (.chiral .R)),
    (19, some (.chiral .S)), (22, some (.chiral .S)), (26, some (.chiral .R)),
    (29, some (.chiral .S))]

noncomputable section

/-- Independent meaning at a centre's own final molecular unit, including case. -/
abbrev FinalCorrect (center : Center) (label : LocalizedAuxiliaryLabel) : Prop :=
  FinalTetrahedralAssignment fixtureProblem fixtureMap
    (input.certified.topUnit center) label

theorem root_independent :
    FinalCorrect rootCenter (.pseudoasymmetric .r) := by
  have h := LocalizedTwoReferenceFixtureDeclarative.fixture_descriptorJudgment
  refine ⟨RS.R, h.1, ?_⟩
  change (.pseudoasymmetric .r : LocalizedAuxiliaryLabel) =
    classifyTetrahedralRSPseudo RS.R setup.declarativeRule5PairCount
  rw [h.2.2.1]
  rfl

theorem root_independent_unique (label : LocalizedAuxiliaryLabel)
    (hlabel : FinalCorrect rootCenter label) :
    label = .pseudoasymmetric .r := by
  have h := LocalizedTwoReferenceFixtureDeclarative.fixture_descriptorJudgment
  have hu := finalTetrahedralAssignment_existsUnique fixtureProblem fixtureMap
    (input.certified.topUnit rootCenter) RS.R h.1 h.2.1
  exact hu.unique hlabel root_independent

private theorem chiral_independent
    (center : Center) (rs : RS)
    (h : CenterAssignment (input.certified.topUnit center) rs) :
    FinalCorrect center (.chiral rs) ∧
      ∀ label, FinalCorrect center label → label = .chiral rs :=
  ⟨h.2.2.2.1, fun _ hl => h.2.2.2.2.unique hl h.2.2.2.1⟩

/-- Every detected centre has exactly this independently justified final assignment. -/
theorem all_centers_independent (center : Center) :
    FinalCorrect center (expectedLabel center) ∧
      ∀ label, FinalCorrect center label → label = expectedLabel center := by
  have hmem := all_detected_centers center
  simp only [centers, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨root_independent, root_independent_unique⟩
  · exact chiral_independent _ _ center4_judgment
  · exact chiral_independent _ _ center7_judgment
  · exact chiral_independent _ _ center11_judgment
  · exact chiral_independent _ _ center14_judgment
  · exact chiral_independent _ _ center19_judgment
  · exact chiral_independent _ _ center22_judgment
  · exact chiral_independent _ _ center26_judgment
  · exact chiral_independent _ _ center29_judgment

/-- Each result is at that centre's own final occurrence, not an auxiliary reading under root 0. -/
theorem all_centers_ordered (center : Center) :
    input.certified.orderedReferenceState (LocalizedOrderedReference.carrierFuel input)
      (input.certified.localizedFinalOccurrenceExecutable
        (LocalizedOrderedReference.carrierFuel input) center) =
      some (expectedLabel center) := by
  rw [input.certified.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence]
  have hmem := all_detected_centers center
  simp only [centers, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LocalizedTwoReferenceFixtureRootLetter.root_letter
  · exact LocalizedTwoReferenceFixtureFinalCenters.orderedTop4
  · exact LocalizedTwoReferenceFixtureFinalCenters.orderedTop7
  · exact LocalizedTwoReferenceFixtureFinalCenters.orderedTop11
  · exact LocalizedTwoReferenceFixtureFinalCenters.orderedTop14
  · exact LocalizedTwoReferenceFixtureFinalCenters.orderedTop19
  · exact LocalizedTwoReferenceFixtureFinalCenters.orderedTop22
  · exact LocalizedTwoReferenceFixtureFinalCenters.orderedTop26
  · exact LocalizedTwoReferenceFixtureFinalCenters.orderedTop29

theorem report_as_labels :
    LocalizedOrderedReference.analyze input =
      input.certified.canonicalTetrahedralCenters.map
        (fun center => (center.1.1, some (expectedLabel center))) := by
  rw [LocalizedOrderedReference.analyze_eq_orderedReferenceReport]
  apply List.map_congr_left
  intro center _
  rw [all_centers_ordered center]

/-- The complete output of the actual callable ordered pipeline. -/
theorem exact_report :
    LocalizedOrderedReference.analyze input = expectedReport := by
  rw [report_as_labels, canonicalCenters]
  rfl

theorem report_count : (LocalizedOrderedReference.analyze input).length = 9 := by
  rw [exact_report]
  rfl

theorem report_no_duplicate_centers :
    ((LocalizedOrderedReference.analyze input).map Prod.fst).Nodup := by
  rw [report_as_labels]
  simpa only [List.map_map, Function.comp_def] using center_indices_nodup

/-- Every actually detected centre is present with its proved label. -/
theorem report_complete (center : Center) :
    (center.1.1, some (expectedLabel center)) ∈ LocalizedOrderedReference.analyze input := by
  rw [report_as_labels]
  exact List.mem_map_of_mem
    ((input.certified.mem_canonicalTetrahedralCenters_iff center).2 center.2)

/-- Every reported descriptor has the unique independent final-assignment meaning. -/
theorem report_sound (atom : Nat) (label : LocalizedAuxiliaryLabel)
    (hmem : (atom, some label) ∈ LocalizedOrderedReference.analyze input) :
    ∃ center : Center, center.1.1 = atom ∧ FinalCorrect center label ∧
      ∀ other, FinalCorrect center other → other = label := by
  rw [report_as_labels] at hmem
  obtain ⟨center, _, heq⟩ := List.mem_map.1 hmem
  have hatom : center.1.1 = atom := congrArg Prod.fst heq
  have hlabel : expectedLabel center = label := Option.some.inj (congrArg Prod.snd heq)
  subst label
  exact ⟨center, hatom, (all_centers_independent center).1,
    (all_centers_independent center).2⟩

/-- A single end-to-end statement: exact output, detector completeness and unique chemical
meaning under the specified independent auxiliary interpretation. -/
theorem whole_molecule_correct :
    LocalizedOrderedReference.analyze input = expectedReport ∧
      ((LocalizedOrderedReference.analyze input).map Prod.fst).Nodup ∧
      ∀ center : Center,
        (center.1.1, some (expectedLabel center)) ∈ LocalizedOrderedReference.analyze input ∧
        FinalCorrect center (expectedLabel center) ∧
        ∀ label, FinalCorrect center label → label = expectedLabel center :=
  ⟨exact_report, report_no_duplicate_centers,
    fun center => ⟨report_complete center, all_centers_independent center⟩⟩

end
end TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.root_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.root_independent_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.all_centers_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.all_centers_ordered
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.report_as_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.exact_report
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.report_count
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.report_no_duplicate_centers
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.report_complete
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.report_sound
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule.whole_molecule_correct
