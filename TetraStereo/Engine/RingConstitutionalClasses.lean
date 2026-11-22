import TetraStereo.Engine.RingConstitutionalPartition
import TetraStereo.Engine.RingStrictConstitution

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition

open OneCenter CertifiedLocalizedCIPInput

private theorem outcome_key (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair) :
    (constitutional i c p).outcome = RingStrictConstitution.constitution i.certified c p.1 p.2 := by
  simpa [constitutional_read i c p] using
    RingStrictConstitution.constitutional_outcome i.certified c p.1 p.2

private def Same (i : Input) (c : i.certified.TetrahedralCenter) (a b : Fin 4) :=
  RingStrictConstitution.constitution i.certified c a b = Ordering.eq

private instance {i c a b} : Decidable (Same i c a b) := by unfold Same; infer_instance

private theorem same_equivalence (i : Input) (c : i.certified.TetrahedralCenter) :
    Equivalence (Same i c) := by
  letI := ExactOfficialRuleMajorKey.compare_transCmp i.certified.moleculeGraph
  have h (a b : Fin 4) : Same i c a b ↔ ExactOfficialRuleMajorKey.compare i.certified.moleculeGraph
      (RingStrictConstitution.key i.certified c a) (RingStrictConstitution.key i.certified c b) = .eq := by
    unfold Same RingStrictConstitution.constitution
    rw [ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact _ _ i.certified.executableExactOfficialRule1aObservation_correct, ExactOfficialRuleMajorKey.compareTrace_outcome]
  refine ⟨fun a => (h a a).mpr Std.ReflCmp.compare_self, fun eqv => (h _ _).mpr (Std.OrientedCmp.eq_symm ((h _ _).mp eqv)), fun eqv eqw => (h _ _).mpr (Std.TransCmp.eq_trans ((h _ _).mp eqv) ((h _ _).mp eqw))⟩
/-- Each ligand is represented by the first occurrence in its full constitutional class. -/
def representative (i : Input) (c : i.certified.TetrahedralCenter) (a : Fin 4) : Fin 4 :=
  (Finset.univ.filter (Same i c a)).min' ⟨a,by simp [(same_equivalence i c).refl a]⟩

theorem representative_spec (i : Input) (c : i.certified.TetrahedralCenter) (a b : Fin 4) :
    (constitutional i c (a,b)).outcome = .eq ↔ representative i c a = representative i c b := by
  rw [outcome_key]
  change Same i c a b ↔ _
  have equiv := same_equivalence i c
  constructor
  · intro h
    have classes : Finset.univ.filter (Same i c a) = Finset.univ.filter (Same i c b) := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨equiv.trans (equiv.symm h),equiv.trans h⟩
    unfold representative
    congr 1
  · intro e
    have own (k : Fin 4) : Same i c k (representative i c k) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
    exact equiv.trans (e ▸ own a : Same i c a (representative i c b)) (equiv.symm (own b))

private def pairsOf (f : Fin 4 → Fin 4) := pairs.filter fun p => f p.1 == f p.2

private def ends (ps : List Pair) :=
  (List.finRange 4).filter fun x => ps.any fun p => x == p.1 || x == p.2

private theorem residual_eq (i : Input) (c : i.certified.TetrahedralCenter) :
    residual i c = pairsOf (representative i c) := by
  unfold residual pairsOf
  congr 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simpa using representative_spec i c p.1 p.2

private def separate (p q : Pair) : Prop :=
  p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

private instance {p q} : Decidable (separate p q) := by unfold separate; infer_instance

private def classification (ps : List Pair) : Prop :=
  (ps.length,(ends ps).length) ∈ ([(0,0),(1,2),(2,4),(3,3),(6,4)] : List (Nat × Nat)) ∧
    (ps.length = 2 → ps.Pairwise separate)

private instance {ps} : Decidable (classification ps) := by unfold classification; infer_instance

private theorem four_classes (f : Fin 4 → Fin 4) : classification (pairsOf f) := by
  have finite : ∀ a b c d : Fin 4, classification (pairsOf ![a,b,c,d]) := by decide +kernel
  have eta : f = ![f 0,f 1,f 2,f 3] := by funext k; fin_cases k <;> rfl
  exact eta.symm ▸ finite (f 0) (f 1) (f 2) (f 3)

/-- Exhaustive sizes of the residual comparison problem and its minimal ligand support.
Precisely two ties necessarily concern disjoint pairs. -/
theorem five_shapes (i : Input) (c : i.certified.TetrahedralCenter) :
    ((residual i c).length,(neededLigands i c).length) ∈
        ([(0,0),(1,2),(2,4),(3,3),(6,4)] : List (Nat × Nat)) ∧
    ((residual i c).length = 2 → (residual i c).Pairwise
      (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)) := by
  change classification (residual i c)
  rw [residual_eq]
  exact four_classes _

/-- The positive strict-order theorem and the minimal residual inventory have exactly the
same boundary, including reverse-directed comparisons used by the actual sorter. -/
theorem strict_iff_empty (i : Input) (c : i.certified.TetrahedralCenter) :
    RingStrictConstitution.Strict i.certified c ↔ residual i c = [] := by
  constructor
  · intro strict
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    obtain ⟨ord,tied⟩ := (mem_residual i c p).mp hp
    exact strict _ _ (ne_of_lt ord) ((outcome_key i c p).symm.trans tied)
  · intro empty a b ne tied
    have absent (x y : Fin 4) (xy : x < y) (eqv : Same i c x y) : False := by
      have h := (mem_residual i c (x,y)).mpr ⟨xy,(outcome_key i c (x,y)).trans eqv⟩
      simp [empty] at h
    rcases lt_or_gt_of_ne ne with h | h
    · exact absent _ _ h tied
    · exact absent _ _ h ((same_equivalence i c).symm tied)

/-- The constitutional pass at a public center either assigns an uppercase hand or returns
the exact ligand pairs that require the stereochemical rules. -/
inductive Result where
  | assigned (hand : RS)
  | geometryUnavailable
  | needsStereo (ligands : List Pair)
  deriving DecidableEq, Repr

def classify (i : Input) (c : i.certified.TetrahedralCenter) : Result :=
  match residual i c with
  | p :: ps => .needsStereo (p :: ps)
  | [] => match RingStrictConstitution.assign? i c with
    | some hand => .assigned hand
    | none => .geometryUnavailable

theorem needsStereo_iff (i : Input) (c : i.certified.TetrahedralCenter) (ps : List Pair) :
    classify i c = .needsStereo ps ↔ ps = residual i c ∧ ps ≠ [] := by
  cases h : residual i c with
  | nil =>
    cases found : RingStrictConstitution.assign? i c <;> simp only [classify,h,found,reduceCtorEq,false_iff,not_and]
    all_goals exact fun e n => n e
  | cons p rest =>
    simp only [classify,h,Result.needsStereo.injEq]
    exact ⟨fun e => ⟨e.symm,e ▸ List.cons_ne_nil p rest⟩,fun e => e.1.symm⟩

theorem calibrated (i : Input) (admitted : coordinatesAdmitted i = true) (c : i.certified.TetrahedralCenter) :
    classify i c ≠ .geometryUnavailable := by
  cases h : residual i c with
  | nil =>
    have ok := (RingStrictConstitution.assign?_isSome_iff i admitted c).mpr ((strict_iff_empty i c).mpr h)
    obtain ⟨hand,found⟩ := Option.isSome_iff_exists.mp ok
    simp only [classify,h,found,ne_eq,reduceCtorEq,not_false_eq_true]
  | cons p rest => simp only [classify,h,ne_eq,reduceCtorEq,not_false_eq_true]

/-- Executable constitutional report, with a row at every detected tetrahedral center. -/
def report (i : Input) : List (i.certified.TetrahedralCenter × Result) :=
  i.certified.canonicalTetrahedralCenters.map fun c => (c,classify i c)

theorem report_exact (i : Input) (c : i.certified.TetrahedralCenter) (r : Result) :
    (c,r) ∈ report i ↔ r = classify i c := by
  constructor
  · intro h
    obtain ⟨a,_,e⟩ := List.mem_map.mp h
    cases e
    rfl
  · rintro rfl
    exact List.mem_map.mpr ⟨c,(i.certified.mem_canonicalTetrahedralCenters_iff c).mpr c.2,rfl⟩

theorem assigned_row (i : Input) (admitted : coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) (hand : RS) (row : (c,.assigned hand) ∈ report i) :
    let ci := i.certified
    let g := LocalizedChemicalRingPhysicalSense.inputGeometry ci
    let slots := RingStrictConstitution.order ci c
    let atoms := RingStrictConstitution.atomIds ci c slots
    (∀ ctx, ci.ruleMajorLigandOrderAt? c ctx = some slots ∧ ci.DeclarativeRuleMajorPriorityOrder c ctx slots) ∧
      LocalizedGenericMarkedRecalculation.readback? g atoms = some hand ∧
      LocalizedGenericMarkedRecalculation.readback? (LocalizedGenericMarkedRecalculation.mirror g) atoms = some hand.swap ∧
      (RingChemicalPriority.Recursive.geometric g atoms atoms).bind RingChemicalPriority.Recursive.Reading.label =
        some (.chiral hand) := by
  have found : RingStrictConstitution.assign? i c = some hand := by
    have e := (report_exact i c _).mp row
    cases hr : residual i c <;> cases h : RingStrictConstitution.assign? i c <;>
      simp only [classify,hr,h,reduceCtorEq,Result.assigned.injEq] at e
    exact congrArg some e.symm
  have strict := (RingStrictConstitution.assign?_isSome_iff i admitted c).mp (by rw [found]; rfl)
  obtain ⟨computed,ordered,raw,reflected,label⟩ := RingStrictConstitution.assigned i admitted c strict
  have same : computed = hand := by simpa [RingStrictConstitution.assign?,strict,raw] using found
  exact same ▸ ⟨ordered,raw,reflected,label⟩

end TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.representative_spec
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.five_shapes
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.strict_iff_empty

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.needsStereo_iff
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.report_exact

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.assigned_row

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.calibrated
