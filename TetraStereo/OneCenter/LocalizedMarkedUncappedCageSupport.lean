import TetraStereo.OneCenter.LocalizedMarkedUncappedOperations
import TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The accepted dependent-center cage meets uncapped operation applicability

The natural intake hypotheses of the general reached-frame theorem hold for the actual accepted
15-atom cyclic molecule. No frame, label or comparator output is supplied. This proves successful
partition/ranking execution at all its reached frames for arbitrary auxiliary states, not equality
with the former capped path, a unique ranking, or the complete recalculated root descriptor.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedCageSupport

open LocalizedHiddenParityMarkedProbe LocalizedMarkedReachableConfigurations
open LocalizedMarkedUncappedOperations AuthoritativeCIPMancudeTotality
open LocalizedGenericMarkedRecalculation (frameAtomsOf)

theorem cage_wellFormed : cageRaw.WellFormed :=
  (cageRaw.wellFormed_iff_all_bondEndpointsOK).mpr (by decide +kernel)

theorem cage_unique : cageRaw.BondRecordsUnique :=
  (cageRaw.bondRecordsUnique?_eq_true_iff).mp (by decide +kernel)

theorem cage_valence : cageRaw.ValenceOK :=
  (cageRaw.valenceOK?_eq_true_iff).mp (by decide +kernel)

theorem cage_kekule : LocalizedMancudeKekuleAdmissible cageRaw := by
  have empty : cageRaw.localizedMancudeEdges = [] := by decide +kernel
  simp [LocalizedMancudeKekuleAdmissible, RawMolecule.localizedMancudeComponentEdges, empty,
    RawMolecule.IsMaximumMancudeEdgeMatching, RawMolecule.IsMancudeEdgeMatching]

/-- Every reached actual cage frame has operationally total uncapped ordinary and marked steps. -/
theorem all_reached_frame_operations (state : OccurrenceAuxState) (node : Node)
    (reached : Reached cageRaw node) (roots : List CanonicalRerootCursor)
    (frame : occurrenceLigandFrame? cageRaw node = some roots) :
    (∃ sorted adjacent, ordinary? cageRaw state node = some (sorted, adjacent) ∧
      sorted.Perm [0, 1, 2, 3] ∧ adjacent.length = 3) ∧
    (∀ mark ∈ frameAtomsOf roots, ∃ ranking, marked? cageRaw state node mark = some ranking ∧
      ranking.positions.Perm [0, 1, 2, 3]) :=
  operations_exist cageRaw cage_wellFormed cage_unique cage_valence cage_kekule
    state node reached roots frame

end TetraStereo.OneCenter.LocalizedMarkedUncappedCageSupport

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageSupport.cage_wellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageSupport.cage_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageSupport.cage_valence
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageSupport.cage_kekule
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageSupport.all_reached_frame_operations
