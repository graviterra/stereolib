import TetraStereo.Engine.RingSingleCycleComparison

/-! Atomic columns depend only on atomic observations, including staged levels
and failed recursive reads. Duplicate metrics may vary independently at each node. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAtomicMetricIndependence
open OneCenter RingRetainedChemicalTrace
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingRetainedChemicalPreorder (Direction keyFor)
open RingSingleCycleComparison (rebuilt native active)
open private shallow deep byDescending makeColumn mergeLayers rulePrefix from
  TetraStereo.Engine.RingRetainedChemicalTrace
open private native_build from TetraStereo.Engine.RingSingleCycleComparison

private def project (k : Key) : Nat × Column := (k.root.atomic,k.atomic)

private theorem sorted_project {κ : Type} [LinearOrder κ]
    (v : Key → κ) (w : Nat × Column → κ)
    (same : ∀ k, v k = w (project k)) (xs : List Key) :
    (byDescending v xs).map project =
      byDescending w (xs.map project) := by
  unfold byDescending
  apply List.map_mergeSort
  intro a _ b _
  simp only [same]

private theorem assemble_atomic (o p : Observation) (xs ys : List Key)
    (root : o.atomic = p.atomic) (kids : xs.map project = ys.map project) :
    (assemble o xs).atomic = (assemble p ys).atomic := by
  have sh (ks : List Key) := sorted_project (shallow .atomic)
    (fun k : Nat × Column => [k.1]) (fun _ => rfl) ks
  have de (ks : List Key) := sorted_project (deep .atomic)
    (fun k : Nat × Column => [k.2.word]) (fun _ => rfl) ks
  have rows (ks : List Key) :
      ks.map (fun k => k.root.atomic) = (ks.map project).map Prod.fst := by simp [List.map_map,project]
  have forest (ks : List Key) :
      ks.foldr (fun k acc => mergeLayers (k.column .atomic).levels acc) [] =
      (ks.map project).foldr (fun k acc => mergeLayers k.2.levels acc) [] := by
    induction ks with
    | nil => rfl
    | cons k ks ih =>
        simpa only [List.map_cons,List.foldr_cons] using congrArg
          (mergeLayers k.atomic.levels) ih
  change makeColumn o xs .atomic = makeColumn p ys .atomic
  simp only [makeColumn,Observation.atStage]
  simp only [rows,forest,sh,de,kids,root]

/-- Arbitrary readers with equal atomic observations give the same atomic root
and complete column, at every fuel depth and for arbitrary child lists. -/
theorem build_project {α : Type} (x y : α → Option Observation)
    (same : ∀ q, (x q).map Observation.atomic = (y q).map Observation.atomic)
    (children : α → List α) (n : Nat) (q : α) :
    (RingDuplicateScale.build x children n q).map project =
      (RingDuplicateScale.build y children n q).map project := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have maps (qs : List α) :
        (qs.mapM (RingDuplicateScale.build x children n)).map (List.map project) =
        (qs.mapM (RingDuplicateScale.build y children n)).map (List.map project) := by
      induction qs with
      | nil => rfl
      | cons a qs hi =>
        simp only [List.mapM_cons]
        have ha := ih a
        cases hx : RingDuplicateScale.build x children n a <;>
          cases hy : RingDuplicateScale.build y children n a <;>
          cases hxs : qs.mapM (RingDuplicateScale.build x children n) <;>
          cases hys : qs.mapM (RingDuplicateScale.build y children n) <;>
          simp_all
    have hr := same q
    have hc := maps (children q)
    simp only [RingDuplicateScale.build]
    cases hx : x q <;> cases hy : y q <;>
      cases hxs : (children q).mapM (RingDuplicateScale.build x children n) <;>
      cases hys : (children q).mapM (RingDuplicateScale.build y children n) <;>
      simp_all
    change project (assemble _ _) = project (assemble _ _)
    exact Prod.ext hr (assemble_atomic _ _ _ _ hr hc)

/-- Equality includes every level and retains failures. -/
theorem build_atomic {α : Type} (x y : α → Option Observation)
    (same : ∀ q, (x q).map Observation.atomic = (y q).map Observation.atomic)
    (children : α → List α) (n : Nat) (q : α) :
    (RingDuplicateScale.build x children n q).map (fun k => k.atomic) =
      (RingDuplicateScale.build y children n q).map (fun k => k.atomic) := by
  have h := congrArg (Option.map Prod.snd) (build_project x y same children n q)
  simpa only [Option.map_map] using h

/-- Active-focus distance changes preserve the public direction's atomic column. -/
theorem direction_atomic {i : Input} {f : Site i} (a : Direction i f) :
    (rebuilt i f ⟨a.val,some f⟩).map (fun k => k.atomic) = some (keyFor a).atomic := by
  have same (q : RingActivePairs.Arm i) :
      (active i f.val.node.history.reverse q).map Observation.atomic =
        (native i q).map Observation.atomic := by
    unfold active
    cases native i q with
    | none => rfl
    | some o => cases q.occurrence.val.node.provenance <;> rfl
  have h := build_atomic _ _ same i.certified.executableLocalizedRerootChildren
    (2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1) ⟨a.val,some f⟩
  rw [native_build] at h
  change _ = (RingRetainedChemicalTrace.key? i ⟨a.val,some f⟩).map (fun k => k.atomic) at h
  rw [RingRetainedChemicalPreorder.read_key a] at h
  exact h
end TetraStereo.Engine.RingAtomicMetricIndependence

assert_kernel_only TetraStereo.Engine.RingAtomicMetricIndependence.build_project
assert_kernel_only TetraStereo.Engine.RingAtomicMetricIndependence.build_atomic
assert_kernel_only TetraStereo.Engine.RingAtomicMetricIndependence.direction_atomic
