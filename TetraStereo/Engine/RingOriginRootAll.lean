import TetraStereo.Engine.RingOriginMetricReport

/-! At the original root, active duplicate distances are a strictly increasing
recoding of native distances on every admitted graph. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginRootAll
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingSingleCycleComparison (native active rebuilt weight)
open RingSingleCycleOrigin (originPath pathDistance shared)
open RingRetainedChemicalTrace (Key key? compareKeys)
open RingNestedActivePair (Reader)
open private observed from TetraStereo.Engine.RingTerminalLigandOrder
open private congr_build native_build from TetraStereo.Engine.RingSingleCycleComparison
open private of_scale from TetraStereo.Engine.RingOriginFullKeys
open private build_congr change project from TetraStereo.Engine.RingOriginMarkWords
open private orientation_congr from TetraStereo.Engine.RingZeroMassReport
open private word from TetraStereo.Engine.RingOriginPriorityStore
attribute [local instance] lexOrd

def shift (n : Nat) (v : Nat) := if v = 0 then 0 else v + n

theorem shift_strictMono (n : Nat) : StrictMono (shift n) := by
  intro a b lt
  unfold shift
  split_ifs <;> omega

private theorem distance_support {i : Input} {r w : i.certified.Atom}
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w) :
    pathDistance [r] p.support = p.length := by
  cases p <;> simp [pathDistance,shared]

theorem observations {i : Input} (f : Site i)
    (root : f.val.node.history.reverse = [f.val.root])
    (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    active i f.val.node.history.reverse q =
      (native i q).map (RingDuplicateScale.observation (shift i.molecule.atomCount)) := by
  cases hit : native i q with
  | none => simp [active,hit]
  | some o =>
    rcases i.certified.carrierOccurrence_provenance_simple_or_ring i.single q.occurrence with real | ⟨d,dup⟩
    · have zero := (RingRetainedChemicalTrace.real_source real hit).1
      cases o
      simp_all [active,RingDuplicateScale.observation,shift]
    · obtain ⟨w,p,t,_,_,_,path,depth⟩ := RingSingleCycleOrigin.closure_access
        (i.certified.carrierOccurrence_legitimate i.single q.occurrence) dup
      have dist : pathDistance f.val.node.history.reverse (originPath q.occurrence.val.node d) = d := by
        rw [root,←on,path,depth]
        exact distance_support p
      have val := (observed hit).1
      have bound := (observed hit).2 d dup
      change o.duplicate = RingTerminalLigandOrder.duplicate i.molecule.atomCount _ at val
      rw [dup] at val
      change o.duplicate = i.molecule.atomCount + 1 - d at val
      have positive : o.duplicate ≠ 0 := by omega
      have same : weight i f.val.node.history.reverse (originPath q.occurrence.val.node d) =
          shift i.molecule.atomCount o.duplicate := by
        unfold weight shift
        rw [dist,if_neg positive,val]
        omega
      cases o
      simp_all [active,RingDuplicateScale.observation]

theorem keys {i : Input} (f : Site i) (root : f.val.node.history.reverse = [f.val.root])
    (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    rebuilt i f q = (key? i q).map (RingDuplicateScale.key (shift i.molecule.atomCount)) := by
  unfold rebuilt
  exact (congr_build i f.val.root _ _ (observations f root) _ q on).trans
    ((RingDuplicateScale.build_natural (shift_strictMono _) _ _ _ _).trans
      (congrArg (Option.map _) (native_build i _ q)))

theorem all_ligands {i : Input} (f : Site i) (root : f.val.node.history.reverse = [f.val.root])
    (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let u ← rebuilt i f ⟨x.val,some f⟩
        let v ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys u v)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y := by
  rw [keys f root _ x.property.1,keys f root _ y.property.1,
    RingRetainedChemicalPreorder.read_key x,RingRetainedChemicalPreorder.read_key y,
    RingRetainedChemicalPreorder.table_order,←RingRetainedChemicalPreorder.compare_word]
  exact congrArg some (RingDuplicateScale.compare_keys (shift_strictMono _) _ _)

private theorem word_compare {i : Input} (f : Site i) (root : f.val.node.history.reverse = [f.val.root])
    (a b : RingRetainedChemicalPreorder.Direction i f) :
    compare (word a) (word b) = compare (RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor a))
      (RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor b)) := by
  have eqn := (all_ligands f root a b).trans (RingRetainedChemicalPreorder.table_order a b)
  cases ha : rebuilt i f ⟨a.val,some f⟩ <;> cases hb : rebuilt i f ⟨b.val,some f⟩ <;>
    simp [ha,hb,word,RingRetainedChemicalPreorder.compare_word] at eqn ⊢
  exact eqn

theorem early_exact {i : Input} (f : Site i) (root : f.val.node.history.reverse = [f.val.root]) :
    RingOriginPriorityStore.early? i f = RingZeroMassReport.zeroEarly? i f := by
  rw [RingZeroMassReport.zero_early_exact]
  unfold RingOriginPriorityStore.early? RingSphereQueue.early?
  apply congrArg (fun next => (RingNestedActivePair.frame? i f).bind next)
  funext fr
  exact congrArg (fun parity : Int => if parity = 0 then none else
    some (⟨RingOrientation.baseline fr * parity,0⟩ : RingGeometryCriterion.Signature))
    (orientation_congr _ _ (fun j k => word_compare f root (fr.direction j) (fr.direction k)))

theorem ranks {i : Input} (f : Site i) (root : f.val.node.history.reverse = [f.val.root])
    (read : Reader i) (rev : Bool) (stages : List RingRetainedStereoRefinement.Observation)
    (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    RingOriginStereoRanking.priorityWith i (rebuilt i f) read rev stages q =
      (RingRetainedStereoRefinement.priority i read rev stages q).map
        (RingOriginStereoRanking.recode (shift i.molecule.atomCount)) := by
  rw [←RingOriginStereoRanking.priorityWith_native]
  exact (RingOriginStereoRanking.priorityWith_congr i f.val.root _ _ (keys f root)
    read rev stages q on).trans
      (RingOriginStereoRanking.priorityWith_natural i _ read rev (shift_strictMono _) stages q)

theorem full_keys {i : Input} (f : Site i) (root : f.val.node.history.reverse = [f.val.root])
    (read : Reader i) (rev : Bool) (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    RingOriginFullKeys.active i f read rev q =
      (RingFullPathEligibility.key? i read rev q).map
        (RingOriginFullKeys.recodeKey (shift i.molecule.atomCount)) := by
  rw [RingOriginFullKeys.native]
  apply of_scale read rev q _ _
    (fun s c k h => RingOriginStereoRanking.priorityWith_shaped i (key? i) read rev s c k
      ((RingOriginStereoRanking.priorityWith_native i read rev s c).trans h))
    _ (shift_strictMono _)
  intro s c hc
  exact ranks f root read rev s c (hc.trans on)

theorem marked_word {i : Input} (f : Site i) (root : f.val.node.history.reverse = [f.val.root])
    (read : Reader i) (atom : Nat) (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    RingOriginMarkWords.word? i f read atom q =
      (RingGroupedMark.arm? i read atom q).map (fun e => e.2.word) := by
  have alt := (build_congr i f.val.root read atom _ _ (keys f root) _ q on).trans
    (RingOriginMarkWords.build_natural i read atom (key? i) (shift_strictMono _)
      (i.certified.localizedRerootCursorBudget q + 1) q)
  unfold RingOriginMarkWords.word?
  rw [alt]
  have source := RingOriginMarkWords.build_project i read atom (key? i)
    (i.certified.localizedRerootCursorBudget q + 1) q
  have out := congrArg (fun o : Option RingOriginMarkWords.Entry => o.map (fun e => e.2.2.word)) source
  simpa only [Option.map_map,Function.comp_def,change,project,RingOriginStereoRanking.recode,
    RingStereoSiblingPass.Branch.word,RingGroupedMark.arm?] using out

theorem marks {i : Input} (f : Site i) (root : f.val.node.history.reverse = [f.val.root])
    (read : Reader i) (mark : Option Nat) (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    RingOriginMetricReport.marks i f read mark q = RingFrameTransport.markWord? i read mark q := by
  cases mark with
  | none => rfl
  | some a => exact marked_word f root read a q on

/-- On any admitted graph the two full local publishers agree at the original
root on the same arbitrary prior store. -/
theorem publish_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (root : f.val.node.history.reverse = [f.val.root]) (read : Reader i) :
    RingOriginMetricReport.publish i f read = RingPyramidalPublication.publish i f read := by
  have rooted (arm : Arm i) (h : arm ∈ RingRetainedAuxiliary.frame i.certified f) :
      arm.occurrence.val.root = f.val.root :=
    i.certified.localizedRerootChildren_root_eq (⟨f,none⟩ : Arm i) arm _
      (i.certified.executableLocalizedRerootChildren_declarative _) h
  have ident (rev : Bool) (q : Arm i) : RingFullPathEligibility.key? i read rev q =
      (RingFullPathEligibility.key? i read rev q).map (RingOriginFullKeys.recodeKey id) := by
    have second_id {α : Type} (xs : List α) : RingPriorityCoordinate.second id xs = xs := by
      cases xs with
      | nil => rfl
      | cons a xs => cases xs <;> rfl
    cases RingFullPathEligibility.key? i read rev q <;> simp [RingOriginFullKeys.recodeKey,
      RingPriorityCoordinate.fullKey,second_id]
  cases sel : RingPyramidalPublication.focusP i f with
  | some centre =>
    simp only [RingOriginMetricReport.publish,RingPyramidalPublication.publish,sel,Option.some.injEq]
    exact (RingOriginPyramidalTrials.pLabels_raw i f read centre (RingFullPathEligibility.key? i read) _ _
      id (shift i.molecule.atomCount) (fun _ _ h => h) (shift_strictMono _)
      (fun rev q _ => ident rev q)
      (fun rev q h => full_keys f root read rev q (rooted q h))
      (fun m q h => marks f root read m q (rooted q h))).symm
  | none =>
    simp only [RingOriginMetricReport.publish,RingPyramidalPublication.publish,sel,
      RingFullPathConstitution.fastPublish,early_exact f root]
    cases hit : RingZeroMassReport.zeroEarly? i f with
    | some s => rfl
    | none =>
      exact RingOriginTetrahedralTrials.publish_raw geom f read (RingFullPathEligibility.key? i read) _ _
        id (shift i.molecule.atomCount) (fun _ _ h => h) (shift_strictMono _)
        (fun rev q _ => ident rev q) (fun rev q on => full_keys f root read rev q on)
        (marks f root read)

/-- The concrete original-root site satisfies the singleton-history condition. -/
theorem publish_origin {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (read : Reader i) :
    RingOriginMetricReport.publish i (RingGroupedReport.origin i r) read =
      RingPyramidalPublication.publish i (RingGroupedReport.origin i r) read :=
  publish_exact geom _ rfl read

end TetraStereo.Engine.RingOriginRootAll
assert_kernel_only TetraStereo.Engine.RingOriginRootAll.all_ligands
assert_kernel_only TetraStereo.Engine.RingOriginRootAll.early_exact

assert_kernel_only TetraStereo.Engine.RingOriginRootAll.publish_exact
