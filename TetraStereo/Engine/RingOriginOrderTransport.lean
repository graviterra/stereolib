import TetraStereo.Engine.RingOriginRootAll

/-! Order transport from shared constitutional observations, without a common-origin premise. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginOrderTransport
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Key Observation key? compareKeys)
open RingSingleCycleComparison (native active rebuilt)
open RingOriginStereoRanking (priorityWith recode)
open private congr_build native_build from TetraStereo.Engine.RingSingleCycleComparison
open private of_scale from TetraStereo.Engine.RingOriginFullKeys
open private build_congr change project from TetraStereo.Engine.RingOriginMarkWords
open private orientation_congr from TetraStereo.Engine.RingZeroMassReport
open private word from TetraStereo.Engine.RingOriginPriorityStore
attribute [local instance] lexOrd

/-- Only observed coordinates need fit the two increasing encodings; the
common base can have gaps and failed observations are retained. -/
def Observations (i : Input) (f : Site i) : Prop :=
  ∃ (base : Arm i → Option Observation) (g h : Nat → Nat), StrictMono g ∧ StrictMono h ∧
    ∀ q : Arm i, q.occurrence.val.root = f.val.root →
      native i q = (base q).map (RingDuplicateScale.observation g) ∧
      active i f.val.node.history.reverse q = (base q).map (RingDuplicateScale.observation h)

theorem keys {i : Input} (f : Site i) (factor : Observations i f) :
    ∃ (base : Arm i → Option Key) (g h : Nat → Nat), StrictMono g ∧ StrictMono h ∧
      ∀ q : Arm i, q.occurrence.val.root = f.val.root →
        key? i q = (base q).map (RingDuplicateScale.key g) ∧
        rebuilt i f q = (base q).map (RingDuplicateScale.key h) := by
  obtain ⟨base,g,h,hg,hh,reads⟩ := factor
  let n := 2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1
  let cs := i.certified.executableLocalizedRerootChildren (fuel := i.certified.certified.input.molecule.atomCount + 1)
  refine ⟨RingDuplicateScale.build base cs n,g,h,hg,hh,?_⟩
  intro q on
  constructor
  · exact (native_build i n q).symm.trans
      ((congr_build i f.val.root _ _ (fun t ht => (reads t ht).1) n q on).trans
        (RingDuplicateScale.build_natural hg _ _ _ _))
  · exact (congr_build i f.val.root _ _ (fun t ht => (reads t ht).2) n q on).trans
      (RingDuplicateScale.build_natural hh _ _ _ _)

theorem full_keys {i : Input} (f : Site i) (factor : Observations i f) :
    ∃ (base : Reader i → Bool → Arm i → Option RingFullPathEligibility.Key)
      (g h : Nat → Nat), StrictMono g ∧ StrictMono h ∧ ∀ read rev q,
        q.occurrence.val.root = f.val.root →
        RingFullPathEligibility.key? i read rev q = (base read rev q).map (RingOriginFullKeys.recodeKey g) ∧
        RingOriginFullKeys.active i f read rev q = (base read rev q).map (RingOriginFullKeys.recodeKey h) := by
  obtain ⟨base,g,h,hg,hh,reads⟩ := keys f factor
  refine ⟨fun read rev => RingOriginFullKeys.fullKey i read rev (priorityWith i base read rev),g,h,hg,hh,?_⟩
  intro read rev q on
  have ranks (v : Nat → Nat) (hv : StrictMono v) (ks : Arm i → Option Key)
      (same : ∀ c, c.occurrence.val.root = f.val.root → ks c = (base c).map (RingDuplicateScale.key v)) :
      ∀ stages c, c.occurrence.val.root = q.occurrence.val.root →
        priorityWith i ks read rev stages c = (priorityWith i base read rev stages c).map (recode v) := by
    intro stages c hc
    exact (RingOriginStereoRanking.priorityWith_congr i f.val.root _ _ same read rev stages c (hc.trans on)).trans
      (RingOriginStereoRanking.priorityWith_natural i base read rev hv stages c)
  constructor
  · rw [RingOriginFullKeys.native]
    exact of_scale read rev q _ _ (RingOriginStereoRanking.priorityWith_shaped i base read rev) g hg
      (fun stages c hc => (RingOriginStereoRanking.priorityWith_native i read rev stages c).symm.trans
        (ranks g hg _ (fun t ht => (reads t ht).1) stages c hc))
  · exact of_scale read rev q _ _ (RingOriginStereoRanking.priorityWith_shaped i base read rev) h hh
      (ranks h hh _ (fun t ht => (reads t ht).2))

theorem marked_word {i : Input} (focus : Site i) (factor : Observations i focus)
    (read : Reader i) (atom : Nat) (q : Arm i) (on : q.occurrence.val.root = focus.val.root) :
    RingOriginMarkWords.word? i focus read atom q = (RingGroupedMark.arm? i read atom q).map (fun e => e.2.word) := by
  obtain ⟨base,a,b,ha,hb,reads⟩ := keys focus factor
  have eqn (v : Nat → Nat) (pos : StrictMono v) (reader : Arm i → Option Key)
      (same : ∀ c, c.occurrence.val.root = focus.val.root → reader c = (base c).map (RingDuplicateScale.key v)) :
      RingOriginMarkWords.build i read atom reader (i.certified.localizedRerootCursorBudget q + 1) q =
        (RingOriginMarkWords.build i read atom base (i.certified.localizedRerootCursorBudget q + 1) q).map (change v) :=
    (build_congr i focus.val.root read atom _ _ same _ q on).trans
      (RingOriginMarkWords.build_natural i read atom base pos _ q)
  have orig := eqn a ha _ (fun c h => (reads c h).1)
  have alt := eqn b hb _ (fun c h => (reads c h).2)
  unfold RingOriginMarkWords.word?
  rw [alt]
  have source := RingOriginMarkWords.build_project i read atom (key? i) (i.certified.localizedRerootCursorBudget q + 1) q
  rw [orig] at source
  have out := congrArg (fun o : Option RingOriginMarkWords.Entry => o.map (fun e => e.2.2.word)) source
  simpa only [Option.map_map,Function.comp_def,change,project,recode,RingStereoSiblingPass.Branch.word,
    RingGroupedMark.arm?] using out


private theorem all_ligands {i : Input} (f : Site i) (factor : Observations i f)
    (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let u ← rebuilt i f ⟨x.val,some f⟩
        let v ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys u v)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y := by
  obtain ⟨base,a,b,ha,hb,reads⟩ := keys f factor
  have arm (z : RingRetainedChemicalPreorder.Direction i f) :
      ∃ k, RingRetainedChemicalPreorder.keyFor z = RingDuplicateScale.key a k ∧
        rebuilt i f ⟨z.val,some f⟩ = some (RingDuplicateScale.key b k) := by
    let q : Arm i := ⟨z.val,some f⟩
    have orig := (reads q z.property.1).1
    have alt := (reads q z.property.1).2
    rw [RingRetainedChemicalPreorder.read_key z] at orig
    cases found : base q with
    | none => simp [found] at orig
    | some k =>
      refine ⟨k,by simpa only [found,Option.map_some,Option.some.injEq] using orig,?_⟩
      exact alt.trans (by rw [found]; rfl)
  obtain ⟨k,kx,ax⟩ := arm x
  obtain ⟨l,ky,ay⟩ := arm y
  rw [RingRetainedChemicalPreorder.table_order, ← RingRetainedChemicalPreorder.compare_word]
  change (do let u ← rebuilt i f ⟨x.val,some f⟩
             let v ← rebuilt i f ⟨y.val,some f⟩
             pure (compareKeys u v)) = some (compareKeys _ _)
  rw [ax,ay]
  rw [kx,ky]
  change some (compareKeys (RingDuplicateScale.key b k) (RingDuplicateScale.key b l)) =
    some (compareKeys (RingDuplicateScale.key a k) (RingDuplicateScale.key a l))
  rw [RingDuplicateScale.compare_keys ha,
    RingDuplicateScale.compare_keys hb]

private theorem word_compare {i : Input} (f : Site i) (factor : Observations i f)
    (a b : RingRetainedChemicalPreorder.Direction i f) :
    compare (word a) (word b) = compare (RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor a))
      (RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor b)) := by
  have eqn := (all_ligands f factor a b).trans (RingRetainedChemicalPreorder.table_order a b)
  cases ha : rebuilt i f ⟨a.val,some f⟩ <;> cases hb : rebuilt i f ⟨b.val,some f⟩ <;>
    simp [ha,hb,word,RingRetainedChemicalPreorder.compare_word] at eqn ⊢
  exact eqn

theorem early_exact {i : Input} (f : Site i) (factor : Observations i f) :
    RingOriginPriorityStore.early? i f = RingZeroMassReport.zeroEarly? i f := by
  rw [RingZeroMassReport.zero_early_exact]
  unfold RingOriginPriorityStore.early? RingSphereQueue.early?
  apply congrArg (fun next => (RingNestedActivePair.frame? i f).bind next)
  funext fr
  exact congrArg (fun parity : Int => if parity = 0 then none else
    some (⟨RingOrientation.baseline fr * parity,0⟩ : RingGeometryCriterion.Signature))
    (orientation_congr _ _ (fun j k => word_compare f factor (fr.direction j) (fr.direction k)))

theorem marks {i : Input} (f : Site i) (factor : Observations i f)
    (read : Reader i) (mark : Option Nat) (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    RingOriginMetricReport.marks i f read mark q = RingFrameTransport.markWord? i read mark q := by
  cases mark with
  | none => rfl
  | some a => exact marked_word f factor read a q on

theorem publish_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (factor : Observations i f) (read : Reader i) :
    RingOriginMetricReport.publish i f read = RingPyramidalPublication.publish i f read := by
  obtain ⟨base,a,b,ha,hb,pair⟩ := full_keys f factor
  have rooted (arm : Arm i) (inFrame : arm ∈ RingRetainedAuxiliary.frame i.certified f) :
      arm.occurrence.val.root = f.val.root :=
    i.certified.localizedRerootChildren_root_eq (⟨f,none⟩ : Arm i) arm _
      (i.certified.executableLocalizedRerootChildren_declarative _) inFrame
  cases sel : RingPyramidalPublication.focusP i f with
  | some centre =>
    simp only [RingOriginMetricReport.publish,RingPyramidalPublication.publish,sel,Option.some.injEq]
    exact (RingOriginPyramidalTrials.pLabels_raw i f read centre (base read) _ _
      a b ha
      hb
      (fun rev q h => (pair read rev q (rooted q h)).1)
      (fun rev q h => (pair read rev q (rooted q h)).2)
      (fun m q h => marks f factor read m q (rooted q h))).symm
  | none =>
    simp only [RingOriginMetricReport.publish,RingPyramidalPublication.publish,sel,RingFullPathConstitution.fastPublish,
      early_exact f factor]
    cases hit : RingZeroMassReport.zeroEarly? i f with
    | some s => rfl
    | none =>
      exact RingOriginTetrahedralTrials.publish_raw geom f read (base read) _ _
        a b ha
        hb
        (fun rev q on => (pair read rev q on).1)
        (fun rev q on => (pair read rev q on).2) (marks f factor read)

/-- The hypothesis is required only at sites actually processed by the queue. -/
def Queued (i : Input) (r : i.certified.Atom) : Prop :=
  ∀ d q, q ∈ RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) r d → Observations i q

theorem rows_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (factor : Queued i r) (batches : Nat) :
    RingOriginMetricReport.rows i r batches = RingSphereStore.rows i r batches := by
  unfold RingOriginMetricReport.rows RingSphereStore.rows
  induction batches with
  | zero => rfl
  | succ n ih =>
    simp only [RingSphereQueue.stored,ih]
    congr 1
    apply List.map_congr_left
    intro q mem
    rw [publish_exact geom q (factor _ q mem)]

theorem root_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (factor : Queued i r) :
    RingOriginMetricReport.root i r = RingChemicalGraphProof.root i r := by
  unfold RingOriginMetricReport.root
  rw [rows_exact geom r factor,RingOriginRootAll.publish_origin geom]
  unfold RingSphereStore.rows
  rw [RingSphereQueue.stored_eq]
  rfl

theorem report_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (factor : ∀ r ∈ atoms, Queued i r) :
    RingOriginMetricReport.report i atoms = RingChemicalReport.report? i atoms := by
  unfold RingOriginMetricReport.report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r mem
  rw [root_exact geom r (factor r mem)]
  rfl

theorem raw_exact (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (factor : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms → ∀ r ∈ atoms, Queued i r) :
    RingOriginMetricReport.fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids :=
  RingRawComparisonLift.eq_native RingOriginMetricReport.report m g ids (fun i atoms trace =>
    report_exact trace.admitted atoms (factor i atoms trace))

end TetraStereo.Engine.RingOriginOrderTransport
assert_kernel_only TetraStereo.Engine.RingOriginOrderTransport.publish_exact
assert_kernel_only TetraStereo.Engine.RingOriginOrderTransport.rows_exact
assert_kernel_only TetraStereo.Engine.RingOriginOrderTransport.raw_exact
