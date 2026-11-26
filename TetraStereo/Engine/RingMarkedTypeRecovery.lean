import TetraStereo.Engine.RingGroupedMark
import TetraStereo.Engine.RingRule5Shape

/-! Complete native marked keys recover their hereditary child population. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedTypeRecovery
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingGroupedMark (OnGeometry)
open RingRetainedChemicalTrace (Word Framed)

abbrev kids (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q
abbrev Valid {i : Input} (q : Arm i) := i.certified.LocalizedRerootCursorValid q
abbrev On {i : Input} (f : Site i) (q : Arm i) := q.occurrence.val.root = f.val.root

def key (i : Input) (r : Reader i) (atom : Nat) (q : Arm i) : List Word :=
  ((RingGroupedMark.arm? i r atom q).map fun e => e.2.deep).getD []

private theorem key_read {i r atom q b} (h : OnGeometry i r false atom q b)
    {f : Site i} (ready : RingGroupedStereo.Ready f r) (valid : Valid q) (on : On f q) :
    key i r atom q = b.deep := by
  obtain ⟨e,he⟩ := RingGroupedMark.arm_ready ready atom q valid on
  have same := OnGeometry.unique (RingGroupedMark.arm_source he).2 h
  simp [key,he,same]

private theorem prior_read {i r atom q b} (h : OnGeometry i r false atom q b)
    {f : Site i} (ready : RingGroupedStereo.Ready f r) (valid : Valid q) (on : On f q) :
    b.priorDeep = RingRule5Shape.key i r false q ∧ b.priorDeep.length = 5 ∧ b.value = RingGroupedMark.bit atom q := by
  cases h with
  | node before look all sub sh de =>
    obtain ⟨p,hp⟩ := RingOccurrenceStereo.rank_total ready false [.lowercase] q valid on
    change RingRetainedStereoRefinement.priority i r false [.lowercase] q = some p at hp
    have eqn := RingRetainedStereoRefinement.unique [.lowercase] _ _ _ before
      (RingRetainedStereoRefinement.source _ _ hp)
    subst p
    exact ⟨by simp [RingRetainedStereoRefinement.extend,RingRule5Shape.key,hp],
      (RingRetainedSeedFrames.sizes [.lowercase] _ _ before).2,rfl⟩

private theorem mapped {α β γ : Type} {xs : List α} {ys : List β} {look : α → Option β}
    (all : xs.mapM look = some ys) (p : β → γ) (k : α → γ)
    (each : ∀ x ∈ xs, ∀ b, look x = some b → p b = k x) : ys.map p = xs.map k := by
  have pairs := TerminalTie.mapM_forall₂ _ _ _ all
  clear all
  induction pairs with
  | nil => rfl
  | @cons a b as bs hit tail ih =>
    exact congrArg₂ List.cons (each a List.mem_cons_self b hit)
      (ih (fun x hx v hv => each x (.tail _ hx) v hv))

private theorem row_data {i r atom q b} (h : OnGeometry i r false atom q b)
    {f : Site i} (ready : RingGroupedStereo.Ready f r) (_valid : Valid q) (on : On f q) :
    ∃ sh de, b.levels = rows sh de ∧
      (de.map Branch.deep).Perm ((kids i q).map (key i r atom)) ∧
      (de.map Branch.priorDeep).Perm ((kids i q).map (RingRule5Shape.key i r false)) ∧
      (de.map Branch.priorDeep).Pairwise (· ≥ ·) ∧
      (∀ c ∈ de, Framed 2 c.levels) := by
  cases h with
  | @node q prior cs sh de before look all sub first second =>
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    have vc (c : Arm i) (hc : c ∈ kids i q) : Valid c :=
      i.certified.localizedRerootChild_valid _ _ _ frame hc
    have oc (c : Arm i) (hc : c ∈ kids i q) : On f c :=
      (i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans on
    have get (c : Branch) (hc : c ∈ cs) := RingRetainedUnitPass.forOutput all hc
    have pkey := mapped all Branch.priorDeep (RingRule5Shape.key i r false)
      (fun c hc v hv => (prior_read (sub c hc hv) ready (vc c hc) (oc c hc)).1)
    have mkey := mapped all Branch.deep (key i r atom)
      (fun c hc v hv => (key_read (sub c hc hv) ready (vc c hc) (oc c hc)).symm)
    have width (c : Branch) (hc : c ∈ cs) : c.priorDeep.length = 5 := by
      obtain ⟨a,ha,hit⟩ := get c hc
      exact (prior_read (sub a ha hit) ready (vc a ha) (oc a ha)).2.1
    refine ⟨_,_,rfl,(second.perm.map _).trans (List.Perm.of_eq mkey),
      (second.perm.map _).trans (List.Perm.of_eq pkey),?_,?_⟩
    · apply List.pairwise_map.mpr
      apply (List.pairwise_map.mp second.descending).imp_of_mem
      intro a b ha hb less
      have wa := width a (second.perm.mem_iff.mp ha)
      have wb := width b (second.perm.mem_iff.mp hb)
      have ka : a.deep.take 5 = a.priorDeep := by simp only [← wa,Branch.deep,List.take_left]
      have kb : b.deep.take 5 = b.priorDeep := by simp only [← wb,Branch.deep,List.take_left]
      simpa only [ka,kb] using RingChildKeyRecovery.take_le less 5
    · intro c hc
      obtain ⟨a,ha,hit⟩ := get c (second.perm.mem_iff.mp hc)
      exact (sub a ha hit).framed

/-- The promoted atoms may differ. Equality includes the previous through-4c
key, the own mark, and every marked child deep key with multiplicity. -/
theorem same_children {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (atomA atomB : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : key i r atomA a = key i r atomB b) :
    (((kids i a).map (key i r atomA)).Perm ((kids i b).map (key i r atomB))) ∧
      RingRule5Shape.key i r false a = RingRule5Shape.key i r false b ∧
      RingGroupedMark.bit atomA a = RingGroupedMark.bit atomB b := by
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready atomA a va oa
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready atomB b vb ob
  have sx := (RingGroupedMark.arm_source hx).2
  have sy := (RingGroupedMark.arm_source hy).2
  have full : x.2.deep = y.2.deep := by simpa [key,hx,hy] using tie
  have prior : x.2.priorDeep = y.2.priorDeep := by
    simpa [Branch.deep] using congrArg List.dropLast full
  have word : x.2.word = y.2.word := by
    simpa [Branch.deep] using congrArg List.getLast? full
  have px := prior_read sx ready va oa
  have py := prior_read sy ready vb ob
  have earlier := px.1.symm.trans (prior.trans py.1)
  have value : x.2.value = y.2.value := by
    simpa [Branch.word] using congrArg (fun w : Word => w.head?.bind List.head?) word
  have levels := Framed.unique sx.framed sy.framed (List.cons.inj word).2
  obtain ⟨sa,da,la,ma,pa,oa',fa⟩ := row_data sx ready va oa
  obtain ⟨sb,db,lb,mb,pb,ob',fb⟩ := row_data sy ready vb ob
  have bag := (RingRule5Shape.same_children ready false a b va vb oa ob earlier).1
  have priors : da.map Branch.priorDeep = db.map Branch.priorDeep :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab) oa' ob'
      (pa.trans (bag.trans pb.symm))
  have words := recover_words fa fb (la.symm.trans (levels.trans lb))
  have same : da.map Branch.deep = db.map Branch.deep := by
    apply List.ext_getElem
    · simpa using congrArg List.length priors
    · intro j hj hk
      have p := List.getElem_of_eq priors (i := j) (by simpa using hj)
      have w := List.getElem_of_eq words (i := j) (by simpa using hj)
      simp only [List.getElem_map] at p w ⊢
      exact congrArg₂ List.append p (congrArg List.singleton w)
  exact ⟨ma.symm.trans ((List.Perm.of_eq same).trans mb),earlier,px.2.2.symm.trans (value.trans py.2.2)⟩
end TetraStereo.Engine.RingMarkedTypeRecovery
assert_kernel_only TetraStereo.Engine.RingMarkedTypeRecovery.same_children
