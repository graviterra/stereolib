import TetraStereo.Engine.RingConstitutionalResidual
import TetraStereo.Engine.RingTetrahedralPrefix
import TetraStereo.Engine.RingPyramidalUnitEarly

/-! Global reduction to ligand ties that survive the complete Rule 4a pass.
Each procedure reads the auxiliary state it constructed at earlier spheres. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStereoUnitResidual
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View Rule evaluate frozen)
open RingChemicalGraphProof (state)
open RingPyramidalPublication (publish)
open RingConstitutionalResidual (publications)
attribute [local instance] lexOrd

/-- Written-center selection and missing-hydrogen completion use the same
chemical record predicate for P/As/Sb. Pyramidal nitrogen additionally requires
the structural constraint. Degree is measured after hydrogen completion. -/
theorem pyramidal_record {i : Input} (a : i.certified.Atom) (record : AtomSpec)
    (written : i.molecule.atoms[a.val]? = some record) :
    RingPyramidalPublication.phosphorus i a = true ↔
      (RingPyramidalChoices.eligibleAtom record = true ∨
        (record.element = .N ∧ RingPyramidalNitrogen.constrained i a = true ∧
          record.charge = 0 ∧ record.aromatic = false)) ∧
      Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3 := by
  simp only [RingPyramidalPublication.phosphorus,RingPyramidalChoices.eligibleAtom,written,
    Option.any_some,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq]
  aesop

/-- Two independently derived ligand rows fix the first comparison of the full
trial. A strict result survives every possible pair of promotion marks. A tie
removes exactly this prefix, leaving the complete later-rule comparison. -/
theorem all_ligand_comparisons {i : Input} {q : Site i} {r : View i}
    (ready : RingGroupedStereo.Ready q r) (rev : Bool) (a b : RingActivePairs.Arm i)
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = q.val.root) (rb : b.occurrence.val.root = q.val.root) :
    ∃ ka kb, RingFullPathEligibility.key? i r rev a = some ka ∧
      RingFullPathEligibility.key? i r rev b = some kb ∧
      ∀ ua ub, RingRetainedUnitPass.Reading i r rev a ua → RingRetainedUnitPass.Reading i r rev b ub →
      ∀ ma mb, compare (RingFullPathTrialReadings.trialKey ka ma) (RingFullPathTrialReadings.trialKey kb mb) =
        (compare ua.deep ub.deep).then (compare (RingFullPathTrialReadings.trialKey ka ma).tail
          (RingFullPathTrialReadings.trialKey kb mb).tail) := by
  obtain ⟨ka,kaFound,ha⟩ := RingFullPathEligibility.key_exact ready rev a va ra
  obtain ⟨kb,kbFound,hb⟩ := RingFullPathEligibility.key_exact ready rev b vb rb
  refine ⟨ka,kb,kaFound,kbFound,?_⟩
  intro ua ub uaRead ubRead ma mb
  obtain ⟨xa,_,_,_,_,xRead,_,_,_,_,ax⟩ := (ha ka).mpr rfl
  obtain ⟨xb,_,_,_,_,yRead,_,_,_,_,bx⟩ := (hb kb).mpr rfl
  cases RingRetainedUnitPass.Reading.unique uaRead xRead
  cases RingRetainedUnitPass.Reading.unique ubRead yRead
  subst ka
  subst kb
  exact List.compare_cons_cons ..

def direct (i : Input) (q : Site i) (r : View i) : Option Cell :=
  (RingConstitutionalResidual.direct i q).orElse fun _ =>
    ((RingTetrahedralPrefix.early? i q r).orElse fun _ =>
      RingPyramidalUnitEarly.early? i q r).map some

def procedure (i : Input) (residual : Rule i) : Rule i := fun q r =>
  match direct i q r with
  | some cell => cell
  | none => residual q r

abbrev prior (i : Input) (q : Site i) := frozen (state i) q

def Agreement (i : Input) (residual : Rule i) : Prop :=
  ∀ q, direct i q (prior i q) = none → residual q (prior i q) = publish i q (prior i q)

theorem sound {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (cell : Cell) (hit : direct i q (prior i q) = some cell) : state i q = cell := by
  cases c : RingConstitutionalResidual.direct i q with
  | some v =>
    have equal : v = cell := by simpa [direct,c] using hit
    exact (RingConstitutionalResidual.sound ok q v c).symm.trans equal
  | none =>
    rw [RingChemicalGraphProof.state_eq]
    have ready := RingChemicalGraphProof.ready ok q
    cases t : RingTetrahedralPrefix.early? i q (prior i q) with
    | some v =>
      have h : some v = cell := by simpa [direct,c,t] using hit
      exact (RingTetrahedralPrefix.early_sound ok ready t).trans h
    | none =>
      cases p : RingPyramidalUnitEarly.early? i q (prior i q) with
      | none => simp [direct,c,t,p] at hit
      | some v =>
        have h : some v = cell := by simpa [direct,c,t,p] using hit
        exact (RingPyramidalUnitEarly.early_local ready p).trans h

/-- Every remaining call has two distinct ligands whose complete through-4a
keys tie on the actual reader. This includes incoming arms during rerooting. -/
theorem unresolved {i : Input} {q : Site i} {r : View i} (ready : RingGroupedStereo.Ready q r)
    (miss : direct i q r = none) :
    (∃ fr : RingNestedActivePair.Frame i q, RingNestedActivePair.frame? i q = some fr ∧
      ∃ ks, RingTetrahedralPrefix.keys? fr r = some ks ∧ ∃ a b, a ≠ b ∧ ks a = ks b) ∨
    (∃ a, RingPyramidalPublication.focusP i q = some a ∧
      ∃ u v : RingActivePairs.Arm i, ∃ ku kv : RingFullPathEligibility.Key,
      u ≠ v ∧ u ∈ RingRetainedAuxiliary.frame i.certified q ∧ v ∈ RingRetainedAuxiliary.frame i.certified q ∧
      RingFullPathEligibility.Reads i r false u ku ∧ RingFullPathEligibility.Reads i r false v kv ∧
      ku.throughFourA = kv.throughFourA) := by
  cases c : RingConstitutionalResidual.direct i q with
  | some v => simp [direct,c] at miss
  | none =>
    cases t : RingTetrahedralPrefix.early? i q r with
    | some v => simp [direct,c,t] at miss
    | none =>
      have p : RingPyramidalUnitEarly.early? i q r = none := by
        cases h : RingPyramidalUnitEarly.early? i q r <;> simp_all [direct]
      rcases RingConstitutionalResidual.unresolved_frame c with ⟨fr,frame,_⟩ | ⟨a,selected,_⟩
      · exact Or.inl ⟨fr,frame,RingTetrahedralPrefix.missed_tie fr ready t⟩
      · obtain ⟨u,v,ku,kv,ne,_,_,hu,hv,_,_,x,y,tie⟩ :=
          RingPyramidalUnitEarly.selected_miss_tie selected ready p
        exact Or.inr ⟨a,selected,u,v,ku,kv,ne,hu,hv,x,y,tie⟩

theorem state_iff {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (residual : Rule i) :
    evaluate (procedure i residual) = state i ↔ Agreement i residual := by
  constructor
  · intro same q miss
    have eqn := RingActiveDistanceSchedule.evaluate_eq (procedure i residual) q
    rw [same] at eqn
    unfold procedure at eqn
    change state i q = (match direct i q (prior i q) with | some v => v | none => residual q (prior i q)) at eqn
    rw [miss] at eqn
    exact eqn.symm.trans (RingChemicalGraphProof.state_eq i q)
  · intro agree
    apply Eq.symm
    apply RingActiveDistanceSchedule.unique
    intro q
    change state i q = (match direct i q (prior i q) with | some v => v | none => residual q (prior i q))
    cases hit : direct i q (prior i q) with
    | none => exact (RingChemicalGraphProof.state_eq i q).trans (agree q hit).symm
    | some cell => exact sound ok q cell hit

abbrev rows (i : Input) (residual : Rule i) := RingGlobalComparison.rows (publications i) (procedure i residual)
abbrev report (i : Input) (residual : Rule i) := RingGlobalComparison.report (publications i) (procedure i residual)

/-- The public evaluator constructs the same addressed rows after every sphere
and returns the same exact list of assignments as the independent execution. -/
theorem stores_and_reports {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (residual : Rule i) (agree : Agreement i residual) :
    (∀ a k, k ≤ RingActiveDistanceSchedule.height i + 1 → rows i residual a k = RingSphereStore.rows i a k) ∧
      ∀ atoms, report i residual atoms = RingChemicalReport.report? i atoms := by
  have same := (state_iff ok residual).mpr agree
  have no (a k q) : ¬ RingGlobalComparison.Difference (publications i) (procedure i residual) a k q := by
    intro d
    apply d.2.2.2
    change procedure i residual q (RingGlobalComparison.prior i a k) = _
    rw [RingGlobalComparison.prior_exact d.1]
    have eqn := RingActiveDistanceSchedule.evaluate_eq (procedure i residual) q
    rw [same] at eqn
    exact eqn.symm.trans (RingChemicalGraphProof.state_eq i q)
  constructor
  · intro a k bound
    exact (RingGlobalComparison.rows_or_difference (publications i) (procedure i residual) a k bound).resolve_right
      (by rintro ⟨n,_,q,d⟩; exact no a n q d)
  · intro atoms
    by_contra bad
    obtain ⟨a,_,k,_,q,d⟩ := RingGlobalComparison.report_disagreement (publications i) (procedure i residual) atoms bad
    exact no a k q d

/-- An actual report disagreement locates a deferred stereochemical decision
on precisely the same prior addressed store in the two executions. Together
with `unresolved` it exhibits physical ligands still tied through Rule 4a. -/
theorem report_disagreement {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (residual : Rule i) (atoms : List i.certified.Atom)
    (different : report i residual atoms ≠ RingChemicalReport.report? i atoms) :
    ∃ a ∈ atoms, ∃ k ≤ RingActiveDistanceSchedule.height i + 1, ∃ q,
      RingGlobalComparison.Called i a k q ∧ rows i residual a k = RingSphereStore.rows i a k ∧
      direct i q (RingGlobalComparison.prior i a k) = none ∧
      residual q (RingGlobalComparison.prior i a k) ≠ publish i q (RingGlobalComparison.prior i a k) := by
  obtain ⟨a,mem,k,bound,q,call,eqRows,disagree,_⟩ :=
    RingGlobalComparison.report_disagreement (publications i) (procedure i residual) atoms different
  refine ⟨a,mem,k,bound,q,call,eqRows,?_⟩
  rw [RingGlobalComparison.prior_exact call] at disagree ⊢
  change procedure i residual q (prior i q) ≠ publish i q (prior i q) at disagree
  cases found : direct i q (prior i q) with
  | none => exact ⟨rfl,by simpa only [procedure,found] using disagree⟩
  | some cell =>
    have eqn := (sound ok q cell found).symm.trans (RingChemicalGraphProof.state_eq i q)
    exact False.elim (disagree (by simpa only [procedure,found] using eqn))

def fromRaw? (residual : (i : Input) → Rule i) := RingRawComparisonLift.fromRaw (fun i => report i (residual i))

theorem raw_exact (residual : (i : Input) → Rule i)
    (agree : ∀ i, LocalizedChemicalRing.coordinatesAdmitted i = true → Agreement i (residual i)) :
    fromRaw? residual = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms ok
  exact (stores_and_reports ok _ (agree i ok)).2 atoms

theorem public_stores {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    ∀ a k, k ≤ RingActiveDistanceSchedule.height i + 1 →
      rows i (publish i) a k = RingSphereStore.rows i a k :=
  (stores_and_reports ok (publish i) (fun _ _ => rfl)).1

theorem native_raw : fromRaw? publish = RingHydrogenReport.fromRaw? :=
  raw_exact _ (fun _ _ _ _ => rfl)

end TetraStereo.Engine.RingStereoUnitResidual
assert_kernel_only TetraStereo.Engine.RingStereoUnitResidual.unresolved
assert_kernel_only TetraStereo.Engine.RingStereoUnitResidual.state_iff
assert_kernel_only TetraStereo.Engine.RingStereoUnitResidual.public_stores
assert_kernel_only TetraStereo.Engine.RingStereoUnitResidual.raw_exact
assert_kernel_only TetraStereo.Engine.RingStereoUnitResidual.native_raw
assert_kernel_only TetraStereo.Engine.RingStereoUnitResidual.all_ligand_comparisons
assert_kernel_only TetraStereo.Engine.RingStereoUnitResidual.report_disagreement
assert_kernel_only TetraStereo.Engine.RingStereoUnitResidual.pyramidal_record
