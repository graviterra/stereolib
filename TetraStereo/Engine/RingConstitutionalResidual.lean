import TetraStereo.Engine.RingResidualPriority
import TetraStereo.Engine.RingPyramidalEarly
import TetraStereo.Engine.RingStrictStereoPublication
import TetraStereo.Engine.RingGlobalComparison
import TetraStereo.Engine.RingRawComparisonLift

/-! Eliminate constitutionally separated tetrahedral and pyramidal occurrences at arbitrary
depth before asking an independent residual rule for any stereochemical word. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingConstitutionalResidual
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell Rule evaluate frozen)
open RingNestedActivePair (Frame)
attribute [local instance] lexOrd

def keys {i : Input} {q : Site i} (fr : Frame i q) :=
  fun k => RingRetainedChemicalPreorder.orderWord (RingZeroDuplicateMass.rebuiltFor (fr.direction k))

/-- A residual site is requested only after both the whole constitutional
comparison and the direct graph decision leave it unresolved. -/
def direct (i : Input) (q : Site i) : Option Cell :=
  match RingZeroMassReport.zeroEarly? i q with
  | some sig => some (some sig.letters)
  | none => match RingPyramidalEarly.early? i q with
    | some v => some (some v)
    | none => RingResidualPriority.graphCell? i q

/-- The gate tests distinct complete, rebuilt constitutional priorities. It
cannot break a tie by slot or by any stereochemical word. -/
theorem reaches_residual_iff {i : Input} {q : Site i} {fr : Frame i q}
    (frame : RingNestedActivePair.frame? i q = some fr) :
    direct i q = none ↔ ¬ Function.Injective (keys fr) ∧ RingResidualPriority.graphCell? i q = none := by
  have noP : RingPyramidalEarly.early? i q = none := by
    simp [RingPyramidalEarly.early?,RingStrictStereoPublication.focusP_none fr]
  by_cases zero : RingOrientation.orientation (keys fr) = 0
  · have tied := (RingOrientation.orientation_zero _).mp zero
    unfold keys at zero
    simp [direct,RingZeroMassReport.zeroEarly?,frame,zero,tied,noP]
  · have strict : Function.Injective (keys fr) := by
      by_contra h
      exact zero ((RingOrientation.orientation_zero _).mpr h)
    unfold keys at zero
    simp [direct,RingZeroMassReport.zeroEarly?,frame,zero,strict]

theorem sound {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (cell : Cell) (hit : direct i q = some cell) : cell = RingChemicalGraphProof.state i q := by
  unfold direct at hit
  cases found : RingZeroMassReport.zeroEarly? i q with
  | none =>
    cases hp : RingPyramidalEarly.early? i q with
    | none => exact RingResidualPriority.graphCell_sound i ok q cell (by simpa only [found,hp] using hit)
    | some v =>
      simp only [found,hp,Option.some.injEq] at hit
      exact hit ▸ (RingPyramidalEarly.early_state ok hp).symm
  | some sig =>
    simp only [found,Option.some.injEq] at hit
    subst cell
    obtain ⟨fr,_,_⟩ := Option.bind_eq_some_iff.mp found
    rw [RingChemicalGraphProof.state_eq]
    simp [RingPyramidalPublication.publish,RingStrictStereoPublication.focusP_none fr,
      RingFullPathConstitution.fastPublish,found]

/-- If the residual procedure is called, both constitutional gates and the
direct graph solver have deferred the occurrence. -/
theorem misses {i : Input} {q : Site i} (h : direct i q = none) :
    RingZeroMassReport.zeroEarly? i q = none ∧ RingPyramidalEarly.early? i q = none ∧
      RingResidualPriority.graphCell? i q = none := by
  unfold direct at h
  cases ht : RingZeroMassReport.zeroEarly? i q <;> simp_all
  cases hp : RingPyramidalEarly.early? i q <;> simp_all

/-- A tetrahedral residual has a pair of distinct slots with equal full-depth
keys. Every other residual is a selected pyramidal occurrence whose gate deferred. -/
theorem unresolved_frame {i : Input} {q : Site i} (miss : direct i q = none) :
    (∃ fr : Frame i q, RingNestedActivePair.frame? i q = some fr ∧
      ∃ j k, j ≠ k ∧ keys fr j = keys fr k) ∨
    (∃ a, RingPyramidalPublication.focusP i q = some a ∧ RingPyramidalEarly.early? i q = none) := by
  have fails := misses miss
  have selected : RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q := by
    by_contra off
    have contradiction := fails.2.2
    simp [RingResidualPriority.graphCell?,off] at contradiction
  obtain ⟨real,a,current,allowed⟩ := selected
  simp only [RingPyramidalPublication.eligible,Bool.or_eq_true,decide_eq_true_eq] at allowed
  rcases allowed with four | pyramid
  · let c : i.certified.TetrahedralCenter :=
      ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet a).mpr four⟩
    have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨real,current⟩
    obtain ⟨fr,frame⟩ := RingGroupedGeometry.frame_exists recognized
    obtain ⟨j,k,same,ne⟩ := Function.not_injective_iff.mp ((reaches_residual_iff frame).mp miss).1
    exact Or.inl ⟨fr,frame,j,k,ne,same⟩
  · exact Or.inr ⟨a,by simp [RingPyramidalPublication.focusP,real,current,pyramid],fails.2.1⟩

/-- For every input and occurrence reaching the remaining rule, exhibit two
physically distinct slots with equal complete constitutional words. No frame,
key, successful read, coordinate sign, or final descriptor is a premise. -/
theorem unresolved_ligands {i : Input} {q : Site i} (miss : direct i q = none) :
    (∃ fr : Frame i q, RingNestedActivePair.frame? i q = some fr ∧
      ∃ j k, j ≠ k ∧ keys fr j = keys fr k) ∨
    (∃ a, RingPyramidalPublication.focusP i q = some a ∧
      ∃ u v : RingActivePairs.Arm i, ∃ ku kv : RingRetainedChemicalTrace.Key,
        u ≠ v ∧ u ∈ RingRetainedAuxiliary.frame i.certified q ∧ v ∈ RingRetainedAuxiliary.frame i.certified q ∧
        RingRetainedChemicalTrace.key? i u = some ku ∧ RingRetainedChemicalTrace.key? i v = some kv ∧
        RingRetainedChemicalPreorder.orderWord ku = RingRetainedChemicalPreorder.orderWord kv) := by
  rcases unresolved_frame miss with tetra | ⟨a,selected,deferred⟩
  · exact Or.inl tetra
  · obtain ⟨u,v,ku,kv,ne,_,_,hu,hv,_,_,x,y,tied⟩ := RingPyramidalEarly.selected_miss_tie selected deferred
    exact Or.inr ⟨a,selected,u,v,ku,kv,ne,hu,hv,x,y,tied⟩

/-- Necessary and sufficient for the entire state on all roots and all depths.
The residual rule can be arbitrary on every site that the graph solves. -/
theorem state_iff {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (residual : Rule i) :
    evaluate (RingResidualPriority.splice (direct i) residual) = RingChemicalGraphProof.state i ↔
      RingResidualPriority.ResidualAgreement (direct i) residual :=
  RingResidualPriority.splice_state_iff (direct i) residual (sound ok)

def publications (i : Input) : RingGlobalComparison.Interface i where
  Data := fun _ => Cell
  native := RingPyramidalPublication.publish i
  interpret := fun _ v => v
  reachable _ := rfl

def procedure (i : Input) (residual : Rule i) : RingGlobalComparison.Source (publications i) :=
  RingResidualPriority.splice (direct i) residual

abbrev rows (i : Input) (residual : Rule i) := RingGlobalComparison.rows (publications i) (procedure i residual)
abbrev report (i : Input) (residual : Rule i) := RingGlobalComparison.report (publications i) (procedure i residual)

/-- The two procedures construct their own addressed rows. Agreement at
unresolved native readers suffices for literal equality of every list prefix. -/
theorem stores_and_reports {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (residual : Rule i) (agree : RingResidualPriority.ResidualAgreement (direct i) residual) :
    (∀ a k, k ≤ RingActiveDistanceSchedule.height i + 1 → rows i residual a k = RingSphereStore.rows i a k) ∧
      ∀ atoms, report i residual atoms = RingChemicalReport.report? i atoms := by
  have same := (state_iff ok residual).mpr agree
  have no (a k q) : ¬ RingGlobalComparison.Difference (publications i) (procedure i residual) a k q := by
    intro d
    apply d.2.2.2
    change RingResidualPriority.splice (direct i) residual q (RingGlobalComparison.prior i a k) = _
    rw [RingGlobalComparison.prior_exact d.1]
    have localEq := RingActiveDistanceSchedule.evaluate_eq (RingResidualPriority.splice (direct i) residual) q
    rw [same] at localEq
    exact localEq.symm.trans (RingChemicalGraphProof.state_eq i q)
  constructor
  · intro a k bound
    exact (RingGlobalComparison.rows_or_difference (publications i) (procedure i residual) a k bound).resolve_right
      (by rintro ⟨n,_,q,d⟩; exact no a n q d)
  · intro atoms
    by_contra bad
    obtain ⟨a,_,k,_,q,d⟩ := RingGlobalComparison.report_disagreement (publications i) (procedure i residual) atoms bad
    exact no a k q d

def fromRaw? (residual : (i : Input) → Rule i) := RingRawComparisonLift.fromRaw (fun i => report i (residual i))

theorem raw_exact (residual : (i : Input) → Rule i)
    (agree : ∀ i, LocalizedChemicalRing.coordinatesAdmitted i = true →
      RingResidualPriority.ResidualAgreement (direct i) (residual i)) :
    fromRaw? residual = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms ok
  exact (stores_and_reports ok _ (agree i ok)).2 atoms

/-- The actual public procedure can replace every covered constitutional read
unconditionally, including during recursive auxiliary assignment. -/
theorem native_raw : fromRaw? RingPyramidalPublication.publish = RingHydrogenReport.fromRaw? :=
  raw_exact _ (fun _ _ _ _ => rfl)

end TetraStereo.Engine.RingConstitutionalResidual
assert_kernel_only TetraStereo.Engine.RingConstitutionalResidual.reaches_residual_iff
assert_kernel_only TetraStereo.Engine.RingConstitutionalResidual.state_iff
assert_kernel_only TetraStereo.Engine.RingConstitutionalResidual.stores_and_reports
assert_kernel_only TetraStereo.Engine.RingConstitutionalResidual.native_raw
assert_kernel_only TetraStereo.Engine.RingConstitutionalResidual.unresolved_frame
assert_kernel_only TetraStereo.Engine.RingConstitutionalResidual.unresolved_ligands
