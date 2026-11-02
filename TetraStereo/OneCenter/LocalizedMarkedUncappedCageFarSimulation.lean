import TetraStereo.OneCenter.LocalizedMarkedOperationSimulation
import TetraStereo.OneCenter.LocalizedMarkedUncappedCagePhysicalReadback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Uncapped recursive generation at the far cage occurrences

The far centers are the base of the dependent-center recalculation, not supplied auxiliary
facts. Their actual uncapped recursive raw and mirror-cased results agree with the accepted
constructor for every depth and every geometry of the family, including refusal.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedCageFarSimulation

open LocalizedMarkedOperationEvaluator LocalizedMarkedOperationSimulation
open LocalizedHiddenParityMarkedProbe LocalizedHiddenParityPromotedReadback
open LocalizedGenericMarkedRecalculationCage
  (geomOf geomOf_mirror gFrame_eq farA_leafy farB_leafy)
open LocalizedGenericMarkedRecalculation
  (Geometry frameAtoms? appendFacts? eligibleOf flatMap_congr_mem)

abbrev uncapped : Operations := LocalizedMarkedUncappedEvaluator.operations cageRaw
abbrev bounded : Operations := boundedOperations cageRaw 16

/-- No comparison operation can create a fact below the far terminal layer. -/
theorem under_leafy (ops : Operations) (depth : Nat) (geom : Geometry)
    (node : Node) (mark : Nat)
    (leafy : ∀ child ∈ cageRaw.canonicalChildren node, frameAtoms? cageRaw child = none ∧
      ∀ deeper ∈ cageRaw.canonicalChildren child, deeper.forcedLeaf = true) :
    underWith cageRaw ops geom [] node (facts cageRaw ops depth) mark = [] := by
  unfold underWith
  exact flatMap_facts_eq_nil cageRaw ops depth geom [] (some mark) _ fun child member =>
    leafy child (mem_tiedChildren_actual cageRaw ops [] node child member)

theorem marked_eq_bounded (P : List CartesianPoint3) (len : P.length = 15)
    (state : OccurrenceAuxState) (node : Node) (mark : Nat)
    (ranking : LocalizedMarkedUncappedCageAgreement.rankedAtoms? state node mark =
      rankedAtomsWith? state node mark) :
    markedReading? cageRaw uncapped (geomOf P len) state node mark =
      markedReading? cageRaw bounded (geomOf P len) state node mark := by
  exact (LocalizedMarkedUncappedCagePhysicalReadback.markedReading_eq_accepted
    P len state node mark ranking).trans
      (LocalizedGenericMarkedRecalculationCage.markedReadback_eq P len state node mark).symm

private theorem raw_leafy_eq (P : List CartesianPoint3) (len : P.length = 15)
    (depth : Nat) (ctx : Option Nat) (node : Node) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (marks : List Nat)
    (frame : frameAtoms? cageRaw node = some atoms)
    (ordinary : LocalizedMarkedUncappedOperations.ordinary? cageRaw [] node =
      LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] node)
    (order : LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] node =
      some (sorted, adjacent))
    (leafy : ∀ child ∈ cageRaw.canonicalChildren node, frameAtoms? cageRaw child = none ∧
      ∀ deeper ∈ cageRaw.canonicalChildren child, deeper.forcedLeaf = true)
    (rankings : ∀ mark ∈ marks,
      LocalizedMarkedUncappedCageAgreement.rankedAtoms? [] node mark =
        rankedAtomsWith? [] node mark)
    (chosen : ∀ mark, (ctx = some mark ∧ mark ∈ atoms) ∨
      mark ∈ eligibleOf atoms sorted adjacent → mark ∈ marks) :
    rawWith? cageRaw uncapped (geomOf P len) [] ctx node (facts cageRaw uncapped depth) =
      rawWith? cageRaw bounded (geomOf P len) [] ctx node (facts cageRaw bounded depth) := by
  unfold rawWith?
  apply rawStep_eq_of_selected cageRaw uncapped bounded (geomOf P len) [] ctx node _ _
    atoms sorted adjacent frame (ordinary.trans order) order
  intro mark selected
  rw [under_leafy uncapped depth (geomOf P len) node mark leafy,
    under_leafy bounded depth (geomOf P len) node mark leafy]
  exact marked_eq_bounded P len [] node mark (rankings mark (chosen mark selected))

theorem farA_raw_eq (P : List CartesianPoint3) (len : P.length = 15) (depth o r : Nat)
    (ho : o ∈ [5, 6, 7]) (hr : r ∈ [3, 9, 5, 6, 7]) :
    rawWith? cageRaw uncapped (geomOf P len) [] (some r) (farA o)
        (facts cageRaw uncapped depth) =
      rawWith? cageRaw bounded (geomOf P len) [] (some r) (farA o)
        (facts cageRaw bounded depth) := by
  have frame : frameAtoms? cageRaw (farA o) = some (o :: 4 :: ([5, 6, 7].erase o)) := by
    have cases : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using ho
    rcases cases with rfl | rfl | rfl
    · simpa only [gFrame_eq] using farA5_frameAtoms
    · simpa only [gFrame_eq] using farA6_frameAtoms
    · simpa only [gFrame_eq] using farA7_frameAtoms
  apply raw_leafy_eq P len depth (some r) (farA o) _ [0, 2, 3, 1]
    [some .gt, some .eq, some .gt] [5, 6, 7] frame
    (LocalizedMarkedUncappedCageAgreement.ordinary_farA o ho)
    (LocalizedGenericMarkedRecalculationCage.farA_ordinary o ho) (farA_leafy o ho)
  · intro mark member
    exact LocalizedMarkedUncappedCageAgreement.farA_ranked o mark ho member
  · intro mark chosen
    have cases : o = 5 ∨ o = 6 ∨ o = 7 := by simpa using ho
    rcases cases with rfl | rfl | rfl <;>
      simp [eligibleOf, LocalizedGenericMarkedRecalculation.atomsAt,
        LocalizedGenericMarkedRecalculation.tiedPositions] at chosen hr ⊢ <;> omega

theorem farB_raw_eq (P : List CartesianPoint3) (len : P.length = 15) (depth o r : Nat)
    (ho : o ∈ [11, 12, 13]) (hr : r ∈ [3, 9, 11, 12, 13]) :
    rawWith? cageRaw uncapped (geomOf P len) [] (some r) (farB o)
        (facts cageRaw uncapped depth) =
      rawWith? cageRaw bounded (geomOf P len) [] (some r) (farB o)
        (facts cageRaw bounded depth) := by
  have frame : frameAtoms? cageRaw (farB o) = some (o :: 10 :: ([11, 12, 13].erase o)) := by
    have cases : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using ho
    rcases cases with rfl | rfl | rfl
    · simpa only [gFrame_eq] using farB11_frameAtoms
    · simpa only [gFrame_eq] using farB12_frameAtoms
    · simpa only [gFrame_eq] using farB13_frameAtoms
  apply raw_leafy_eq P len depth (some r) (farB o) _ [0, 2, 3, 1]
    [some .gt, some .eq, some .gt] [11, 12, 13] frame
    (LocalizedMarkedUncappedCageAgreement.ordinary_farB o ho)
    (LocalizedGenericMarkedRecalculationCage.farB_ordinary o ho) (farB_leafy o ho)
  · intro mark member
    exact LocalizedMarkedUncappedCageAgreement.farB_ranked o mark ho member
  · intro mark chosen
    have cases : o = 11 ∨ o = 12 ∨ o = 13 := by simpa using ho
    rcases cases with rfl | rfl | rfl <;>
      simp [eligibleOf, LocalizedGenericMarkedRecalculation.atomsAt,
        LocalizedGenericMarkedRecalculation.tiedPositions] at chosen hr ⊢ <;> omega

theorem farA_descriptor_eq (P : List CartesianPoint3) (len : P.length = 15) (depth o r : Nat)
    (ho : o ∈ [5, 6, 7]) (hr : r ∈ [3, 9, 5, 6, 7]) :
    descriptor? cageRaw uncapped depth (geomOf P len) [] (some r) (farA o) =
      LocalizedGenericMarkedRecalculation.descriptor? cageRaw 16 depth (geomOf P len)
        [] (some r) (farA o) := by
  rw [← bounded_descriptor_eq_original]
  unfold descriptor? descriptorWith?
  rw [farA_raw_eq P len depth o r ho hr, geomOf_mirror,
    farA_raw_eq _ _ depth o r ho hr]

theorem farB_descriptor_eq (P : List CartesianPoint3) (len : P.length = 15) (depth o r : Nat)
    (ho : o ∈ [11, 12, 13]) (hr : r ∈ [3, 9, 11, 12, 13]) :
    descriptor? cageRaw uncapped depth (geomOf P len) [] (some r) (farB o) =
      LocalizedGenericMarkedRecalculation.descriptor? cageRaw 16 depth (geomOf P len)
        [] (some r) (farB o) := by
  rw [← bounded_descriptor_eq_original]
  unfold descriptor? descriptorWith?
  rw [farB_raw_eq P len depth o r ho hr, geomOf_mirror,
    farB_raw_eq _ _ depth o r ho hr]

end TetraStereo.OneCenter.LocalizedMarkedUncappedCageFarSimulation

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageFarSimulation.under_leafy
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageFarSimulation.farA_raw_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageFarSimulation.farB_raw_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageFarSimulation.farA_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedCageFarSimulation.farB_descriptor_eq
