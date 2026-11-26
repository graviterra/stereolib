import TetraStereo.Engine.RingEligibleGraph
import TetraStereo.Engine.RingPyramidalSource

set_option autoImplicit false
namespace TetraStereo.Engine.RingChemicalGraphProof
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Labels consistent)
open RingActiveDistanceSchedule (View frozen evaluate Visible distance height)
open RingPyramidalPublication

theorem skips (i : Input) : RingEligibleGraph.SkipsIneligible (eligible i) (publish i) := by
  intro q r no
  have hp : focusP i q = none := by
    unfold focusP
    split
    · rename_i real
      cases h : q.val.node.current? with
      | none => rfl
      | some a =>
        have off : phosphorus i a = false := by
          cases he : phosphorus i a
          · rfl
          · exact (no ⟨real,a,h,by simp [eligible,he]⟩).elim
        simp [Option.filter,off]
    · rfl
  have absent : i.certified.localizedOccurrenceDescriptorCenter? q = none := by
    cases h : i.certified.localizedOccurrenceDescriptorCenter? q with
    | none => rfl
    | some c =>
      obtain ⟨real,atom⟩ := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp h
      exact (no ⟨real,c.val,atom,by
        simp only [eligible, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl ((i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property)⟩).elim
  simpa [publish,hp] using RingFullPathConstitution.fast_skips i q r absent

def state (i : Input) : View i := evaluate (publish i)
theorem state_eq (i : Input) (q : Site i) : state i q = publish i q (frozen (state i) q) :=
  RingActiveDistanceSchedule.evaluate_eq _ _

private theorem issued {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {r : View i} (ready : RingGroupedStereo.Ready q r) {v}
    (got : publish i q r = some v) : v.all consistent = true ∧
      (∀ t : Arm i, t.occurrence = q → i.certified.executableLocalizedRerootChildren t = [] → v = none) := by
  cases hp : focusP i q with
  | some a =>
    have eqn : v = pLabels i q r a := Option.some.inj (by simpa [publish,hp] using got.symm)
    subst v
    refine ⟨pLabels_consistent i q r a,?_⟩
    intro t same empty
    have bound := RingFrontierProfileShape.cut_frame t
    change i.certified.executableLocalizedRerootChildren t = [] at empty
    rw [same,empty] at bound
    have ne : (RingRetainedAuxiliary.frame i.certified q).length ≠ 3 := by simp only [List.length_nil] at bound; omega
    simp [pLabels,ne,guard]
  | none =>
    have full : RingFullPathPublication.publish? i q r = some v :=
      (RingFullPathConstitution.fast_local geom ready).symm.trans (by simpa [publish,hp] using got)
    refine ⟨RingFullPathPublication.issued_consistent full,?_⟩
    intro t same empty
    cases v with
    | none => rfl
    | some labels =>
      have four := RingFullPathPublication.issued_four full
      have bound := RingFrontierProfileShape.cut_frame t
      change i.certified.executableLocalizedRerootChildren t = [] at empty
      rw [same,four,empty] at bound
      contradiction

private theorem observed {i : Input}
    {q : Site i} (known : ∀ t, Visible q t → ∃ v, state i t = some v ∧
      v.all consistent = true ∧ (∀ s : Arm i, s.occurrence = t → i.certified.executableLocalizedRerootChildren s = [] → v = none)) :
    RingGroupedStereo.Ready q (frozen (state i) q) := by
  intro t on
  by_cases vis : Visible q t.occurrence
  · obtain ⟨v,hv,hc,ht⟩ := known t.occurrence vis
    exact ⟨v,by simp [frozen,on,vis.2.1,vis.2.2,hv],hc,ht t rfl⟩
  · have masked : ¬(distance q < distance t.occurrence ∧ t.occurrence.val.node.current? ≠ some q.val.root) := fun h => vis ⟨on,h⟩
    exact ⟨none,by simp [frozen,on,masked],rfl,fun _ => rfl⟩

theorem total {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) :
    ∃ v, state i q = some v ∧ v.all consistent = true ∧
      (∀ t : Arm i, t.occurrence = q → i.certified.executableLocalizedRerootChildren t = [] → v = none) := by
  suffices ∀ n (t : Site i), height i - distance t = n → ∃ v, state i t = some v ∧ v.all consistent = true ∧
      (∀ s : Arm i, s.occurrence = t → i.certified.executableLocalizedRerootChildren s = [] → v = none) from this _ q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t depth
    have ready := observed (q := t) (fun s vis => by
      have upper := RingActiveDistanceSchedule.distance_bound s
      exact ih _ (by have deeper := vis.2.1; omega) s rfl)
    have localTotal : ∃ v, publish i t (frozen (state i) t) = some v := by
      cases hp : focusP i t with
      | some a => exact ⟨pLabels i t (frozen (state i) t) a,by simp [publish,hp]⟩
      | none =>
        obtain ⟨v,hv,_⟩ := RingFullPathPublication.source_exact geom ready
        exact ⟨v,by simpa [publish,hp,RingFullPathConstitution.fast_local geom ready] using hv⟩
    obtain ⟨v,hv⟩ := localTotal
    exact ⟨v,(state_eq i t).trans hv,issued geom ready hv⟩

theorem complete {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) : (state i q).isSome = true :=
  Option.isSome_iff_exists.mpr ⟨_,(total geom q).choose_spec.1⟩
theorem ready {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) : RingGroupedStereo.Ready q (frozen (state i) q) :=
  observed (fun t _ => total geom t)

/-- Both centre types have independent ligand and geometry derivations at every occurrence. -/
def Local (i : Input) (q : Site i) (r : View i) (v : Option Labels) : Prop :=
  match focusP i q with
  | some a => RingPyramidalSource.Framed i q r a v
  | none => RingFullPathPublication.TwoGeometry i q r v

theorem local_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) (v : Option Labels) :
    Local i q (frozen (state i) q) v ↔ state i q = some v := by
  rw [state_eq]
  cases hp : focusP i q with
  | some a =>
    simp only [Local,publish,hp,Option.some.injEq]
    exact RingPyramidalSource.selected_iff hp (ready geom q) v
  | none =>
    simp only [Local,publish,hp]
    rw [RingFullPathConstitution.fast_local geom (ready geom q)]
    exact (RingFullPathPublication.two_geometry_iff geom q (state i) (ready geom q) v).symm

theorem path_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r h a} (p : RingGraphPaths.Path i r h a) (v : Option Labels) :
    state i (RingGraphPaths.site p) = some v ↔ RingEligibleGraph.Derives (eligible i) (Local i) r p v := by
  symm
  apply RingEligibleGraph.derives_iff_store (state i) _ (complete geom) (local_iff geom) p v
  intro q no
  exact (state_eq i q).trans (skips i q _ no)

def root (i : Input) (a : i.certified.Atom) := RingEligibleGraph.root i (eligible i) (publish i) a

/-- A constitutional early result avoids construction of the auxiliary queue. -/
def fastRoot (i : Input) (a : i.certified.Atom) :=
  let q := RingGroupedReport.origin i a
  match focusP i q with
  | some _ => RingEligibleGraph.root i (eligible i) (publish i) a
  | none => match RingZeroMassReport.zeroEarly? i q with
    | some s => some s.letters
    | none => RingEligibleGraph.root i (eligible i) (publish i) a

theorem fastRoot_exact (i : Input) (a : i.certified.Atom) : fastRoot i a = root i a := by
  unfold fastRoot
  dsimp only
  cases hp : focusP i (RingGroupedReport.origin i a) with
  | some p => simp [root]
  | none =>
    cases hit : RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i a) with
    | none => simp [root]
    | some s =>
      rw [root,RingEligibleGraph.root_exact _ (skips i),← state]
      rw [state_eq]
      simp [publish,hp,RingFullPathConstitution.fastPublish,hit]

@[csimp] theorem root_fast : @root = @fastRoot := by
  funext i a
  exact (fastRoot_exact i a).symm

theorem root_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (v : Option Labels) : root i a = some v ↔
      RingEligibleGraph.Derives (eligible i) (Local i) a (.origin : RingGraphPaths.Path i a [a] a) v := by
  rw [root,RingEligibleGraph.root_exact _ (skips i)]
  exact path_iff geom .origin v
end TetraStereo.Engine.RingChemicalGraphProof
assert_kernel_only TetraStereo.Engine.RingChemicalGraphProof.root_iff
