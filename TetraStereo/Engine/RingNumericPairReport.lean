import TetraStereo.Engine.RingTetrahedralNumericRows
import TetraStereo.Engine.RingPyramidalNumericRows
import TetraStereo.Engine.RingConstitutionalResidual
import TetraStereo.Engine.RingUniversalLigandOrder

/-! Execute the molecular report with arbitrary-precision numeric score comparisons
at every tetrahedral and pyramidal occurrence, including all marking trials. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingNumericPairReport
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Rule View)
open RingUniversalLigandOrder (Observation interpret observe)
open RingConstitutionalResidual (publications)

def observations (i : Input) (q : Site i) (r : View i) : Observation i q :=
  match RingPyramidalPublication.focusP i q with
  | some a => .pyramidal a (RingPyramidalNumericRows.data i q r)
  | none => .tetra (match RingNestedActivePair.frame? i q with
    | none => some none
    | some fr => (RingTetrahedralNumericRows.data? fr r).map fun d => some (fr,d))

theorem observations_exact {i : Input} {q : Site i} {r : View i} (ready : RingGroupedStereo.Ready q r) :
    observations i q r = observe i q r := by
  unfold observations observe
  cases p : RingPyramidalPublication.focusP i q with
  | some a => rw [RingPyramidalNumericRows.data_exact i q r ready]
  | none =>
    unfold RingPairwisePublication.extract?
    cases fr : RingNestedActivePair.frame? i q with
    | none => rfl
    | some frame => simp only [RingTetrahedralNumericRows.data_exact frame ready]

def procedure (i : Input) : Rule i := fun q r => interpret (observations i q r)
abbrev rows (i : Input) := RingGlobalComparison.rows (publications i) (procedure i)
abbrev report (i : Input) := RingGlobalComparison.report (publications i) (procedure i)

theorem stores_and_reports {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    (∀ a k, k ≤ RingActiveDistanceSchedule.height i + 1 → rows i a k = RingSphereStore.rows i a k) ∧
      ∀ atoms, report i atoms = RingChemicalReport.report? i atoms := by
  have no (a k q) : ¬ RingGlobalComparison.Difference (publications i) (procedure i) a k q := by
    intro d
    apply d.2.2.2
    change interpret (observations i q (RingGlobalComparison.prior i a k)) = _
    rw [RingGlobalComparison.prior_exact d.1,
      observations_exact (RingChemicalGraphProof.ready ok q)]
    exact (RingUniversalLigandOrder.interface i ok).reachable q
  constructor
  · intro a k bound
    exact (RingGlobalComparison.rows_or_difference (publications i) (procedure i) a k bound).resolve_right
      (by rintro ⟨n,_,q,d⟩; exact no a n q d)
  · intro atoms
    by_contra bad
    obtain ⟨a,_,k,_,q,d⟩ :=
      RingGlobalComparison.report_disagreement (publications i) (procedure i) atoms bad
    exact no a k q d

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms ok
  exact (stores_and_reports ok).2 atoms

end TetraStereo.Engine.RingNumericPairReport
assert_kernel_only TetraStereo.Engine.RingNumericPairReport.observations_exact
assert_kernel_only TetraStereo.Engine.RingNumericPairReport.stores_and_reports
assert_kernel_only TetraStereo.Engine.RingNumericPairReport.raw_exact
