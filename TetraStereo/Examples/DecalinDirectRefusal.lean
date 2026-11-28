import TetraStereo.Examples.DecalinDirectJunction
import TetraStereo.Examples.DecalinEarlierTie
import TetraStereo.Examples.DecalinJunctionStore

/-! Exact public refusal at the directly reached opposite fusion atom. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinDirectRefusal
open Engine OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingGroupedReport (origin)
open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open RingActiveDistanceSchedule (frozen distance Visible)
open DecalinAuxiliary (history advance child_history)
open DecalinFrames (molecule)
open DecalinDirectJunction (direct left right direction classOf)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
open RingSplitLigandTie (markingReader)
open private aut image fixed image_root image_history site_eq normalized_frozen visible_erase erase
  from TetraStereo.Examples.DecalinEarlierTie
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie
open private cursorKey read_valid from TetraStereo.Engine.RingAtomicProfileShape
open private graph_rows frame_perm from TetraStereo.Examples.DecalinFrames
open private head_and_kind from TetraStereo.Examples.DecalinAuxiliary
attribute [local instance] lexOrd

private def idAt (r : Fin 2) (k : Fin 4) := (direction r k).headD 28

private theorem ids : ∀ r : Fin 2,
    ((List.finRange 4).map (idAt r)).Perm (DecalinFrames.junctionRow (1-r.val)) ∧
    Function.Injective (idAt r) ∧
    (∀ k : Fin 4, advance (direct r) (idAt r k) = direction r k) ∧
    (direct r).map DecalinPathSwap.exchange = direct r ∧
    (left r).map DecalinPathSwap.exchange = right r := by decide +kernel

private theorem kind {i : Input} {f : Site i} {r : Fin 2} (focus : history f = direct r) :
    f.val.node.provenance = .realAtom ∧ (RingAllLigandTwoShell.siteAtom i f).val = 1-r.val := by
  obtain ⟨t,ht,real⟩ := head_and_kind f (RingAllLigandTwoShell.site_current i f)
  rw [focus] at ht
  obtain ⟨e,tail⟩ := List.cons.inj ht
  refine ⟨real.mpr ?_,e.symm⟩
  rw [←e,←tail]
  have := r.isLt
  simp
  omega

private theorem layout {i : Input} (graph : i.molecule = molecule)
    {f : Site i} {r : Fin 2} (focus : history f = direct r) (fr : RingNestedActivePair.Frame i f) :
    ∃ e : Equiv.Perm (Fin 4), ∀ k, history (cursor fr (e k)).occurrence = direction r k := by
  have atC := ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  have center : fr.center.val.val = 1-r.val := by
    simpa [RingAllLigandTwoShell.siteAtom,atC] using (kind focus).2
  have phys := frame_perm fr
  rw [graph,center] at phys
  have perm := ((ids r).1.trans ((phys.trans (graph_rows ⟨1-r.val,by omega⟩)).symm))
  change ((List.finRange 4).map (idAt r)).Perm ((List.finRange 4).map (atom fr)) at perm
  have atEach (k : Fin 4) : ∃ s, atom fr s = idAt r k := by
    obtain ⟨s,_,v⟩ := List.mem_map.mp (perm.mem_iff.mp (List.mem_map_of_mem (List.mem_finRange k)))
    exact ⟨s,v⟩
  choose chooseSlot slot using atEach
  have inj : Function.Injective chooseSlot := fun a b h => (ids r).2.1 ((slot a).symm.trans (h ▸ slot b))
  let e := Equiv.ofBijective chooseSlot ⟨inj,Finite.surjective_of_injective inj⟩
  refine ⟨e,fun k => ?_⟩
  have mem : fr.arm (e k) ∈ i.certified.executableLocalizedRerootChildren ⟨f,none⟩ := List.get_mem ..
  obtain ⟨w,cur,step⟩ := child_history (q := ⟨f,none⟩) (kind focus).1 atC mem
  have ident := fr.point_at (e k)
  rw [cur] at ident
  have v : w.val = idAt r k := (Option.some.inj ident).trans (slot k)
  exact step.trans (by rw [focus,v,(ids r).2.2.1])

private theorem fusion_keys {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (f : Site i) (r : Fin 2)
    (root : f.val.root.val = r.val) (focus : history f = direct r)
    (fr : RingNestedActivePair.Frame i f) (a b : Fin 4)
    (leftA : history (cursor fr a).occurrence = left r) (rightB : history (cursor fr b).occurrence = right r)
    (rev : Bool) (ks : Fin 4 → Key)
    (got : RingFullPathPublication.keys? fr (frozen (RingChemicalGraphProof.state i) f) rev = some ks) :
    ks a = ks b := by
  let j := f.val.root
  have small : j.val < 2 := root ▸ r.isLt
  let read := frozen (RingChemicalGraphProof.state i) f
  let c := DecalinEarlierTie.carrier i graph
  have stable : image graph f = f := by
    apply site_eq (image_root graph rfl small)
    rw [image_history,focus,(ids r).2.2.2.1]
  have dest : c.image (cursor fr a) = cursor fr b := by
    have here : image graph (cursor fr a).occurrence = (cursor fr b).occurrence := by
      apply site_eq ((image_root graph (fr.direction a).property.1 small).trans (fr.direction b).property.1.symm)
      rw [image_history]
      change (history (cursor fr a).occurrence).map _ = history (cursor fr b).occurrence
      rw [leftA,rightB,(ids r).2.2.2.2]
    change (⟨image graph (cursor fr a).occurrence,some (image graph f)⟩ : Arm i) = _
    rw [here,stable]
    rfl
  have same : RingGeometryExchange.Frozen c (markingReader read) (markingReader read) := by
    intro q _
    rw [normalized_frozen,normalized_frozen]
    have vis (t : Site i) (v : Visible f t) :
        erase (RingChemicalGraphProof.state i t) = erase (RingChemicalGraphProof.state i (image graph t)) :=
      visible_erase graph ok j small t ⟨v.1,by change 0 < distance t; have := v.2.1; omega,v.2.2⟩
    have h := RingGeometryAutomorphism.frozen_transport (aut i graph) f q.occurrence
      (s := fun v => erase (RingChemicalGraphProof.state i v))
      (t := fun v => erase (RingChemicalGraphProof.state i v)) vis
    change _ = frozen _ (image graph f) (image graph q.occurrence) at h
    rw [stable] at h
    exact h
  have dom : c.domain (cursor fr a) := by
    intro p hp
    obtain rfl := Option.some.inj hp
    exact (fr.direction a).property.1.symm
  have read_key (s : Fin 4) : RingFullPathEligibility.Reads i read rev (cursor fr s) (ks s) := by
    obtain ⟨x,hx,eq⟩ := RingFullPathEligibility.key_exact (RingChemicalGraphProof.ready ok f)
      rev _ (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    exact (eq _).mpr (Option.some.inj ((RingActivePairReport.four_at got s).symm.trans hx))
  obtain ⟨u,l,ar,as',ar5,du,dl,_,_,_,A⟩ := read_key a
  obtain ⟨v,m,br,bs,br5,dv,dm,_,_,_,B⟩ := read_key b
  have unit := c.unit same dom (normalized_unit du) (dest.symm ▸ normalized_unit dv)
  have lower := c.refinement same [.lowercase] (cursor fr a) dom _ _ (normalized_lower dl) (dest.symm ▸ normalized_lower dm)
  have silent (s : Fin 4) (side : history (cursor fr s).occurrence = left r ∨ history (cursor fr s).occurrence = right r) :
      (ks s).bestFourB = [] ∧ (ks s).fixedR = [] := by
    have words := DecalinDirectJunction.empty_stage graph ok f r root focus (cursor fr s) rfl
      (RingGroupedCentre.valid fr s) (fr.direction s).property.1 side rev
    have gotS := RingActivePairReport.four_at got s
    change RingFullPathEligibility.key? i read rev (cursor fr s) = some (ks s) at gotS
    unfold RingFullPathEligibility.key? RingFullPathPairs.pairs? RingFullPathRule5.word? at gotS
    simp only [read,words] at gotS
    cases U : RingRetainedStereoRefinement.priority i read rev [] (cursor fr s) <;>
      cases L : RingRetainedStereoRefinement.priority i read rev [.lowercase] (cursor fr s) <;>
      simp [read] at U L <;> simp [U,L] at gotS
    rw [←gotS]
    exact ⟨rfl,rfl⟩
  have sa := silent a (Or.inl leftA)
  have sb := silent b (Or.inr rightB)
  rw [A] at sa
  rw [B] at sb
  change max ar as' = [] ∧ ar5 = [] at sa
  change max br bs = [] ∧ br5 = [] at sb
  rw [A,B,sa.1,sa.2,sb.1,sb.2]
  exact congrArg₂ (fun x y => (⟨x,[],y,[]⟩ : Key)) (congrArg RingStereoSiblingPass.Branch.deep unit)
    (congrArg RingStereoSiblingPass.Branch.word lower)

open RingFullPathEligibility (tiedSlots candidates)
open RingFullPathTrialReadings (trials readTrial readingsWith markWords?)
open private keys_exact from TetraStereo.Engine.RingFullPathPublication

private theorem pair_only : ∀ a b : Fin 4, a ≠ b → classOf a = classOf b → a = 1 ∨ a = 2 := by decide

/-- Only the two outward arms can tie. Consequently the public eligibility
test offers no promotion, and its single ordinary ballot is a refusal. -/
theorem public_state {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (f : Site i) (r : Fin 2)
    (root : f.val.root.val = r.val) (focus : history f = direct r) :
    RingChemicalGraphProof.state i f = some none := by
  obtain ⟨real,id⟩ := kind focus
  let v := RingAllLigandTwoShell.siteAtom i f
  have current := RingAllLigandTwoShell.site_current i f
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph,show v.val = 1-r.val from id]
    exact (graph_rows ⟨1-r.val,by omega⟩).length_eq.trans (by unfold DecalinFrames.junctionRow; split <;> rfl)
  let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have center := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f c).mpr ⟨real,current⟩
  obtain ⟨fr,frame⟩ := RingGroupedGeometry.frame_exists center
  obtain ⟨e,atDir⟩ := layout graph focus fr
  let read := frozen (RingChemicalGraphProof.state i) f
  have ready := RingChemicalGraphProof.ready ok f
  obtain ⟨ks,K,unique⟩ := keys_exact fr ready false
  obtain ⟨ms,M,_⟩ := keys_exact fr ready true
  have accepted := (unique ks).mpr rfl
  have same := fusion_keys graph ok f r root focus fr (e 1) (e 2) (atDir 1) (atDir 2) false ks K
  have ne : e 1 ≠ e 2 := e.injective.ne (by decide)
  have few : (tiedSlots ks).length ≤ 2 := by
    let both : Finset (Fin 4) := {e 1,e 2}
    have sub : (tiedSlots ks).toFinset ⊆ both := by
      intro a mem
      obtain ⟨s,rfl⟩ := e.surjective a
      obtain ⟨_,hit⟩ := List.mem_filter.mp (List.mem_toFinset.mp mem)
      obtain ⟨b,_,test⟩ := List.any_eq_true.mp hit
      obtain ⟨t,rfl⟩ := e.surjective b
      have diff : s ≠ t := fun eq => (bne_iff_ne.mp (Bool.and_eq_true_iff.mp test).1) (congrArg e eq)
      have equal : ks (e s) = ks (e t) := beq_iff_eq.mp (Bool.and_eq_true_iff.mp test).2
      have first (k : Fin 4) : (ks k).throughFourA.head? = some (cursorKey i (cursor fr k)).atomic.word := by
        obtain ⟨u,word⟩ := RingFullPathConstitution.through_extends fr (accepted k)
        have actual := Option.some.inj ((read_valid (RingGroupedCentre.valid fr k)).symm.trans
          (RingRetainedChemicalPreorder.read_key (fr.direction k)))
        rw [word,actual]
        rfl
      have atomic := Option.some.inj ((first (e s)).symm.trans ((congrArg (fun z : Key => z.throughFourA.head?)
        equal).trans (first (e t))))
      have cmp := DecalinDirectJunction.atomic_comparison graph r f focus s t _ _ rfl rfl
        (RingGroupedCentre.valid fr (e s)) (RingGroupedCentre.valid fr (e t)) (atDir s) (atDir t)
      rw [atomic] at cmp
      have self : compare (cursorKey i (cursor fr (e t))).atomic.word (cursorKey i (cursor fr (e t))).atomic.word = .eq := Std.ReflCmp.compare_self
      rw [self] at cmp
      rcases pair_only s t diff (compare_eq_iff_eq.mp cmp.symm) with eq|eq <;> simp [both,eq]
    have card := Finset.card_le_card sub
    have nd : (tiedSlots ks).Nodup := (List.nodup_finRange 4).filter _
    rw [List.toFinset_card_of_nodup nd] at card
    exact card.trans (by simp [both,ne])
  have trial : trials ks = [none] := by
    simp [trials,candidates,show ¬3 ≤ (tiedSlots ks).length by omega]
  have ballot : readTrial fr false (fun k => trialKey (ks k) []) = none :=
    ((RingFullPathTrialReadings.read_exact ok fr false _ none).mp (.tie ne (congrArg (fun z => trialKey z []) same))).symm
  have votes : RingFullPathTrialReadings.readings? fr read false = some [(none,none)] := by
    change (RingFullPathPublication.keys? fr read false >>= readingsWith fr read false) = _
    simp [K,read,readingsWith,trial,markWords?,ballot,List.mapM_cons]
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) v degree
  have noP : RingPyramidalPublication.focusP i f = none := by
    simp [RingPyramidalPublication.focusP,real,current,v] at off ⊢
    exact off
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local ok ready,RingFullPathPublication.publish?,frame]
  change RingFullPathPublication.centre? fr read = _
  unfold RingFullPathPublication.centre?
  rw [show RingFullPathPublication.keys? fr read false = _ from K,
    show RingFullPathPublication.keys? fr read true = _ from M]
  simp only [Option.bind_some,votes,Option.map_some]
  rfl

open DecalinJunctionStore (cells hands shortPath)
open private paths length_at from TetraStereo.Examples.DecalinJunctionStore

private theorem cells_eq_hands {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2) (q : Site i)
    (onRoot : q.val.root.val = r.val) : cells i r q = hands i r q := by
  by_cases short : history q = shortPath r
  · have refused := public_state graph ok q r onRoot short
    have len := length_at q
    rw [short,(paths r).2.1] at len
    have exact := DecalinJunctionStore.positive_reader graph ok r q onRoot (by omega)
    have published := RingChemicalGraphProof.state_eq i q
    rw [exact,refused] at published
    have off (s : Fin 2) (long : (DecalinAuxiliary.route r s).length = 6) :
        history q ≠ DecalinAuxiliary.route r s := by
      intro eq
      have same := congrArg List.length (short.symm.trans eq)
      rw [(paths r).2.1,long] at same
      contradiction
    simp only [cells,if_pos short,←published,hands,if_neg (off 0 (paths r).2.2.1),
      if_neg (off 1 (paths r).2.2.2.1)]
  · simp [cells,short]

/-- At every sphere, the public rows agree in address, order, and value
with writing only the two opposite determinant readings and refusals. No
auxiliary publication or comparison is used on the physical side. -/
theorem sphere_snapshot {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2)
    (a : i.certified.Atom) (root : a.val = r.val) (k : Nat) (bound : k ≤ RingActiveDistanceSchedule.height i + 1) :
    RingSphereStore.rows i a k = RingSphereQueue.stored (fun q _ => hands i r q)
      a (RingGlobalComparison.queue i a) (RingActiveDistanceSchedule.height i) k := by
  rw [DecalinJunctionStore.public_rows graph ok r a root k bound]
  induction k with
  | zero => rfl
  | succ k ih =>
    apply congrArg₂ List.append _ (ih (by omega))
    apply List.map_congr_left
    intro q mem
    have active := ((RingEligibleGraph.inventory i (RingPyramidalPublication.eligible i) a) _ q).mp mem
    exact congrArg (Prod.mk q) (cells_eq_hands graph ok r q ((congrArg Fin.val active.1.1).trans root))

end TetraStereo.Examples.DecalinDirectRefusal
assert_kernel_only TetraStereo.Examples.DecalinDirectRefusal.public_state
assert_kernel_only TetraStereo.Examples.DecalinDirectRefusal.sphere_snapshot
