import TetraStereo.Engine.RingOriginFullKeys
import TetraStereo.Engine.RingOriginMarkWords
import TetraStereo.Engine.RingAtomicMetricIndependence

/-! Active-origin metric readers are total on ready focus slices, without any
assumption that their order agrees with the native distance metric. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginMetricTotal
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Key Observation)
open RingStereoSiblingPass (Branch order)
open RingOriginStereoRanking (priorityWith unitWith)
open RingSingleCycleComparison (rebuilt native active)
open private join from TetraStereo.Engine.RingOriginMarkWords
open private native_build from TetraStereo.Engine.RingSingleCycleComparison
open private children_total budget kids from TetraStereo.Engine.RingOccurrenceStereo

/-- Changing only duplicate-distance observations preserves successful coverage. -/
theorem rebuilt_total (i : Input) (f : Site i) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) : ∃ k, rebuilt i f q = some k := by
  have same (c : Arm i) :
      (active i f.val.node.history.reverse c).map Observation.atomic =
      (native i c).map Observation.atomic := by
    unfold active
    cases native i c with
    | none => rfl
    | some o => cases c.occurrence.val.node.provenance <;> rfl
  have eqn := RingAtomicMetricIndependence.build_project _ _ same
    i.certified.executableLocalizedRerootChildren
    (2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1) q
  rw [native_build] at eqn
  obtain ⟨k,hk⟩ := RingRetainedChemicalCoverage.key_total i
    (RingRetainedChemicalCoverage.admitted_atoms i) q valid
  change (rebuilt i f q).map _ = (RingRetainedChemicalTrace.key? i q).map _ at eqn
  rw [hk] at eqn
  cases hit : rebuilt i f q with
  | none => simp [hit] at eqn
  | some k => exact ⟨k,rfl⟩

theorem priority_total {i : Input} {f : Site i} {read : Reader i}
    (ready : RingGroupedStereo.Ready f read) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) :
    ∀ q : Arm i, i.certified.LocalizedRerootCursorValid q →
      q.occurrence.val.root = f.val.root →
      ∃ b, priorityWith i (rebuilt i f) read rev stages q = some b := by
  induction stages with
  | nil =>
    suffices ∀ n (q : Arm i), i.certified.LocalizedRerootCursorValid q →
        q.occurrence.val.root = f.val.root → budget i q < n →
        ∃ b, unitWith i (rebuilt i f) read n q = some b from
      fun q v on => this _ q v on (Nat.lt_succ_self _)
    intro n; induction n with
    | zero => intros; omega
    | succ n ih =>
      intro q valid on enough
      obtain ⟨x,hx⟩ := rebuilt_total i f q valid
      obtain ⟨v,hv,ok,leaf⟩ := ready q on
      have gate : (guard (v.all RingNestedActivePair.consistent = true ∧
          (kids i q = [] → v = none)) : Option Unit) = some () := if_pos ⟨ok,leaf⟩
      obtain ⟨ks,hks⟩ := children_total _ valid on enough ih
      exact ⟨RingRetainedUnitPass.branch x (RingNestedActivePair.unit (v.map Prod.fst))
        (order Branch.shallow ks) (order Branch.deep ks),by simp only [unitWith,hx,hv,gate,hks,Option.bind_eq_bind,Option.bind_some,Option.pure_def]⟩
  | cons o os prior =>
    let fn := priorityWith i (rebuilt i f) read rev os
    suffices ∀ n (q : Arm i), i.certified.LocalizedRerootCursorValid q →
        q.occurrence.val.root = f.val.root → budget i q < n →
        ∃ b, RingRetainedStereoRefinement.build i fn read o rev n q = some b from
      fun q v on => this _ q v on (Nat.lt_succ_self _)
    intro n; induction n with
    | zero => intros; omega
    | succ n ih =>
      intro q valid on enough
      obtain ⟨p,hp⟩ := prior q valid on
      change fn q = some p at hp
      obtain ⟨v,hv,_,_⟩ := ready q on
      obtain ⟨ks,hks⟩ := children_total _ valid on enough ih
      exact ⟨RingRetainedStereoRefinement.extend p (o.value v rev)
        (order Branch.shallow ks) (order Branch.deep ks),by simp only [RingRetainedStereoRefinement.build,hp,hv,hks,
        Option.bind_eq_bind,Option.bind_some,Option.pure_def]⟩

/-- The BFS oracle can use its own successful rank equation as its source relation. -/
theorem wordWith_total {i : Input} {f : Site i} {read : Reader i}
    (ready : RingGroupedStereo.Ready f read) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) (seed : RS)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    ∃ w, RingFullPathPairs.wordWith read rev i.certified.executableLocalizedRerootChildren
      (priorityWith i (rebuilt i f) read rev stages) seed q = some w := by
  let rank := priorityWith i (rebuilt i f) read rev stages
  let oracle : RingFullPathPairs.Oracle i :=
    ⟨fun c b => rank c = some b, rank, fun _ _ h => h,
      fun _ _ _ a b => Option.some.inj (a.symm.trans b)⟩
  obtain ⟨bits,hit,_⟩ := oracle.source_exact (RingFullPathPairs.likeAt i read rev seed)
    (priority_total ready rev stages) q valid on
  exact ⟨bits,hit⟩

theorem active_total {i : Input} {f : Site i} {read : Reader i}
    (ready : RingGroupedStereo.Ready f read) (rev : Bool) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    ∃ k, RingOriginFullKeys.active i f read rev q = some k := by
  obtain ⟨u,hu⟩ := priority_total ready rev [] q valid on
  obtain ⟨l,hl⟩ := priority_total ready rev [.lowercase] q valid on
  obtain ⟨r,hr⟩ := wordWith_total ready rev [] .R q valid on
  obtain ⟨s,hs⟩ := wordWith_total ready rev [] .S q valid on
  obtain ⟨fixed,hfixed⟩ := wordWith_total ready rev [.lowercase] .R q valid on
  exact ⟨⟨u.deep,max r s,l.word,fixed⟩,by simp [RingOriginFullKeys.active,RingOriginFullKeys.fullKey,hu,hl,hr,hs,hfixed]⟩

theorem mark_total {i : Input} {f : Site i} {read : Reader i}
    (ready : RingGroupedStereo.Ready f read) (atom : Nat) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    ∃ w, RingOriginMarkWords.word? i f read atom q = some w := by
  suffices ∀ n (t : Arm i), i.certified.LocalizedRerootCursorValid t →
      t.occurrence.val.root = f.val.root → budget i t < n →
      ∃ e, RingOriginMarkWords.build i read atom (rebuilt i f) n t = some e by
    obtain ⟨e,he⟩ := this _ q valid on (Nat.lt_succ_self _)
    exact ⟨e.2.2.word,by simp [RingOriginMarkWords.word?,he]⟩
  intro n; induction n with
  | zero => intro t _ _ h; omega
  | succ n ih =>
    intro t vt rt enough
    obtain ⟨v,hv,ok,absent⟩ := ready t rt
    have gate : (guard (v.all RingNestedActivePair.consistent = true ∧
        (kids i t = [] → v = none)) : Option Unit) = some () := if_pos ⟨ok,absent⟩
    obtain ⟨k,hk⟩ := rebuilt_total i f t vt
    obtain ⟨cs,hcs⟩ := children_total _ vt rt enough ih
    exact ⟨join atom t k v cs,by simp only [RingOriginMarkWords.build,hv,gate,hk,hcs,
      Option.bind_eq_bind,Option.bind_some,Option.pure_def]⟩

assert_kernel_only rebuilt_total
assert_kernel_only priority_total
assert_kernel_only wordWith_total
assert_kernel_only active_total
assert_kernel_only mark_total
end TetraStereo.Engine.RingOriginMetricTotal
