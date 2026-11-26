import TetraStereo.Engine.RingOriginMetricRenumber
import TetraStereo.Engine.RingOriginMarkWords
import TetraStereo.Engine.RingChemicalRenumbering

/-! Atom covariance of active-origin marked words, including failed reads. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginMarkRenumber
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingRawRenumbering (AtomMap)
open RingNestedActivePair (Reader Labels consistent)
open RingRetainedChemicalTrace (Key Framed)
open RingStereoSiblingPass (Branch order rows legal_order)
open RingOriginMarkWords (Entry build word?)
open private join unit lower mark extend from TetraStereo.Engine.RingOriginMarkWords
open private mapM_perm from TetraStereo.Engine.RingOriginMetricRenumber
open private rowsTransport from TetraStereo.Engine.RingGeometryExchange
open private site_path from TetraStereo.Engine.RingRawRenumbering

private def Formed (e : Entry) : Prop :=
  Framed 2 e.1.levels ∧ Framed 2 e.2.1.levels ∧ Framed 2 e.2.2.levels

private theorem formed_rows (cs : List Entry) (p : Entry → Branch)
    (h : ∀ e ∈ cs, Framed 2 (p e).levels) :
    Framed 2 (rows (order Branch.shallow (cs.map p)) (order Branch.deep (cs.map p))) := by
  apply RingStereoSiblingPass.rows_framed (legal_order _ _).perm (legal_order _ _).perm
  intro b hb
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
  exact h e he

private theorem join_formed {i : Input} (atom : Nat) (q : Arm i) (k : Key) (v : Option Labels)
    (cs : List Entry) (h : ∀ e ∈ cs, Formed e) : Formed (join atom q k v cs) := by
  exact ⟨formed_rows cs unit (fun e he => (h e he).1),
    formed_rows cs lower (fun e he => (h e he).2.1),
    formed_rows cs mark (fun e he => (h e he).2.2)⟩

private theorem build_formed (i : Input) (read : Reader i) (atom : Nat)
    (keys : Arm i → Option Key) (n : Nat) (q : Arm i) {e : Entry}
    (h : build i read atom keys n q = some e) : Formed e := by
  induction n generalizing q e with
  | zero => contradiction
  | succ n ih =>
    simp only [build] at h
    obtain ⟨v,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨k,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs,hcs,h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    apply join_formed
    intro e he
    obtain ⟨t,_,hit⟩ := RingRetainedUnitPass.forOutput hcs he
    exact ih t hit

private theorem rows_perm {cs ds : List Entry} (p : cs.Perm ds)
    (get : Entry → Branch) (h : ∀ e ∈ cs, Framed 2 (get e).levels) :
    rows (order Branch.shallow (cs.map get)) (order Branch.deep (cs.map get)) =
    rows (order Branch.shallow (ds.map get)) (order Branch.deep (ds.map get)) := by
  apply rowsTransport (p.map get) (legal_order _ _) (legal_order _ _)
    (legal_order _ _) (legal_order _ _)
  intro b hb
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
  exact h e he

private theorem join_map {i j : Input} (r : AtomMap i j) (atom : Nat) (q : Arm i)
    (aligned : i.certified.cursorPreviousRootAligned q) (k : Key) (v : Option Labels)
    {cs ds : List Entry} (p : cs.Perm ds) (h : ∀ e ∈ cs, Formed e) :
    join atom q k v cs = join (RingReportRenumber.renameId r atom) (r.arm q) k v ds := by
  have u := rows_perm p unit (fun e he => (h e he).1)
  have l := rows_perm p lower (fun e he => (h e he).2.1)
  have m := rows_perm p mark (fun e he => (h e he).2.2)
  have bit : RingGroupedMark.bit atom q =
      RingGroupedMark.bit (RingReportRenumber.renameId r atom) (r.arm q) :=
    RingReportRenumber.marked_nat r atom q aligned
  dsimp only [join,extend,RingRetainedUnitPass.branch,RingRetainedStereoRefinement.extend]
  rw [u,l,m,bit]

/-- The supplied frozen readers agree on all aligned molecular cursors. -/
theorem build_map {i j : Input} (r : AtomMap i j) (focus : Site i)
    (read : Reader i) (other : Reader j)
    (same : RingGeometryExchange.Frozen r.carrier read other)
    (atom n : Nat) (q : Arm i) (aligned : i.certified.cursorPreviousRootAligned q) :
    build i read atom (RingSingleCycleComparison.rebuilt i focus) n q =
    build j other (RingReportRenumber.renameId r atom)
      (RingSingleCycleComparison.rebuilt j (r.site focus)) n (r.arm q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have kids : ((i.certified.executableLocalizedRerootChildren q).map r.arm).Perm
        (j.certified.executableLocalizedRerootChildren (r.arm q)) := r.carrier.children q aligned
    have empty : (i.certified.executableLocalizedRerootChildren q = []) ↔
        (j.certified.executableLocalizedRerootChildren (r.arm q) = []) := by
      have len := kids.length_eq
      simp only [List.length_map] at len
      simp only [← List.length_eq_zero_iff, len]
    have key := RingOriginMetricRenumber.rebuilt_map r focus q aligned
    have seen : read q.occurrence = other (r.arm q).occurrence := same q aligned
    have each : (i.certified.executableLocalizedRerootChildren q).mapM
        (build i read atom (RingSingleCycleComparison.rebuilt i focus) n) =
        ((i.certified.executableLocalizedRerootChildren q).map r.arm).mapM
        (build j other (RingReportRenumber.renameId r atom)
          (RingSingleCycleComparison.rebuilt j (r.site focus)) n) := by
      rw [List.mapM_map]
      apply RingFrameTransport.mapM_congr_mem
      intro t ht
      exact ih t (r.carrier.below q aligned t ht)
    simp only [build,seen,key,empty]
    rw [each]
    rcases mapM_perm (build j other (RingReportRenumber.renameId r atom)
      (RingSingleCycleComparison.rebuilt j (r.site focus)) n) kids with
      ⟨ha,hb⟩ | ⟨as,bs,ha,hb,hp⟩
    · rw [ha,hb]
      simp
    · rw [ha,hb]
      have formed : ∀ e ∈ as, Formed e := by
        intro e he
        obtain ⟨t,_,hit⟩ := RingRetainedUnitPass.forOutput (each.trans ha) he
        exact build_formed i read atom _ n t hit
      have joins : ∀ k v, join atom q k v as =
          join (RingReportRenumber.renameId r atom) (r.arm q) k v bs :=
        fun k v => join_map r atom q aligned k v hp formed
      simp only [Option.bind_eq_bind,Option.bind_some,joins]


theorem budget_map {i j : Input} (r : AtomMap i j) (q : Arm i) :
    i.certified.localizedRerootCursorBudget q =
      j.certified.localizedRerootCursorBudget (r.arm q) := by
  have card : i.certified.certified.input.molecule.atomCount =
      j.certified.certified.input.molecule.atomCount := by
    simpa using Fintype.card_congr r.atoms
  have len (f : Site i) : (r.site f).val.address.length = f.val.address.length :=
    (site_path r f).2
  have rem : (r.site q.occurrence).val.remaining = q.occurrence.val.remaining := by
    have a := i.certified.localizedCIPOccurrence_depthGrade q.occurrence
    have b := j.certified.localizedCIPOccurrence_depthGrade (r.site q.occurrence)
    rw [len] at b
    omega
  unfold CertifiedLocalizedCIPInput.localizedRerootCursorBudget
  cases hp : q.previous? with
  | none => simp [RingRawRenumbering.AtomMap.arm,hp,len,card]
  | some f => simp [RingRawRenumbering.AtomMap.arm,hp,len,card,rem]

/-- Both successful words and failures are equivariant under atom renumbering. -/
theorem word_map {i j : Input} (r : AtomMap i j) (focus : Site i)
    (read : Reader i) (other : Reader j)
    (same : RingGeometryExchange.Frozen r.carrier read other)
    (atom : Nat) (q : Arm i) (aligned : i.certified.cursorPreviousRootAligned q) :
    word? i focus read atom q =
    word? j (r.site focus) other (RingReportRenumber.renameId r atom) (r.arm q) := by
  unfold word?
  rw [build_map r focus read other same atom _ q aligned]
  simp only [budget_map r q]

end TetraStereo.Engine.RingOriginMarkRenumber
assert_kernel_only TetraStereo.Engine.RingOriginMarkRenumber.build_map

assert_kernel_only TetraStereo.Engine.RingOriginMarkRenumber.budget_map
assert_kernel_only TetraStereo.Engine.RingOriginMarkRenumber.word_map
