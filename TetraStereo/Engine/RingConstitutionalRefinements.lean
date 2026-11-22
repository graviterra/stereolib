import TetraStereo.Engine.RingConstitutionalClasses
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalRefinements

open OneCenter CertifiedLocalizedCIPInput CIPRuleEngine ConstitutionalPartition

/-- Positions run from highest to lowest priority. The four explicit contexts use
a like/unlike Rule 4b pair followed by the R/S Rule 5 sense. -/
def positionContext : Fin 4 → OfficialLigandRuleContext :=
  ![(OfficialLigandRuleContext.ofRS .R).withRule4bPair .like,
    (OfficialLigandRuleContext.ofRS .S).withRule4bPair .like,
    (OfficialLigandRuleContext.ofRS .R).withRule4bPair .unlike,
    (OfficialLigandRuleContext.ofRS .S).withRule4bPair .unlike]

private def priority (a b : Fin 4) : Ordering :=
  if a < b then .gt else if b < a then .lt else .eq

private theorem position_contexts (a b : Fin 4) :
    cipTraceOutcome (compareOfficialContextTrace (positionContext a) (positionContext b)) = priority a b := by
  revert a b
  decide +kernel

private theorem constitutional_key (i : Input) (c : i.certified.TetrahedralCenter) (a b : Fin 4) :
    (constitutional i c (a,b)).outcome = ExactOfficialRuleMajorKey.compare i.certified.moleculeGraph
      (RingStrictConstitution.key i.certified c a) (RingStrictConstitution.key i.certified c b) := by
  have h := RingStrictConstitution.constitutional_outcome i.certified c a b
  calc
    _ = RingStrictConstitution.constitution i.certified c a b := by simpa [constitutional_read i c (a,b)] using h
    _ = _ := by
      unfold RingStrictConstitution.constitution
      rw [ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact _ _ i.certified.executableExactOfficialRule1aObservation_correct,ExactOfficialRuleMajorKey.compareTrace_outcome]

private theorem dual (i : Input) (c : i.certified.TetrahedralCenter) (a b : Fin 4) :
    (constitutional i c (a,b)).outcome = (constitutional i c (b,a)).outcome.swap := by
  simp only [constitutional_key]
  letI := ExactOfficialRuleMajorKey.compare_transCmp i.certified.moleculeGraph
  exact Std.OrientedCmp.eq_swap

private theorem context_outcome (i : Input) (c : i.certified.TetrahedralCenter) (ctx : Context) (a b : Fin 4) :
    (i.certified.compareRuleMajorAt? c ctx a b).map CIPTraceCertificate.outcome = some
      (if (constitutional i c (a,b)).outcome = .eq then
        cipTraceOutcome (compareOfficialContextTrace (ctx a) (ctx b))
       else (constitutional i c (a,b)).outcome) := by
  by_cases tied : (constitutional i c (a,b)).outcome = .eq
  · have h := (constitutional i c (a,b)).sound.trans tied
    simp [compareRuleMajorAt?,constitutional_read i c (a,b),tied,compareDigraphThenOfficialTrace_outcome_of_digraph_eq h]
  · have h : cipTraceOutcome (constitutional i c (a,b)).trace ≠ .eq := by rwa [(constitutional i c (a,b)).sound]
    simp [compareRuleMajorAt?,constitutional_read i c (a,b),tied,compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq h,(constitutional i c (a,b)).sound]

/-- The permutation maps positions to ligand slots. Every earlier slot must be
at least as high constitutionally as every later slot. -/
def Extends (i : Input) (c : i.certified.TetrahedralCenter) (slots : Equiv.Perm (Fin 4)) : Prop :=
  ∀ ⦃x y : Fin 4⦄, x < y → (constitutional i c (slots x,slots y)).outcome ≠ .lt

/-- An executable explicit context tuple for a proposed permutation. -/
def realization (slots : Equiv.Perm (Fin 4)) : Context := fun a => positionContext (slots.symm a)

private theorem outcome_of_extends {i : Input} {c : i.certified.TetrahedralCenter} {s : Equiv.Perm (Fin 4)}
    (h : Extends i c s) (a b : Fin 4) :
    (i.certified.compareRuleMajorAt? c (realization s) a b).map CIPTraceCertificate.outcome =
      some (priority (s.symm a) (s.symm b)) := by
  obtain ⟨x,rfl⟩ := s.surjective a
  obtain ⟨y,rfl⟩ := s.surjective b
  simp only [context_outcome,realization,Equiv.symm_apply_apply,position_contexts]
  by_cases tie : (constitutional i c (s x,s y)).outcome = .eq
  · simp [tie]
  · rw [if_neg tie]
    rcases lt_trichotomy x y with lt | eq | gt
    · have ne := h lt
      cases v : (constitutional i c (s x,s y)).outcome <;> simp_all [priority]
    · subst y
      exfalso
      apply tie
      rw [constitutional_key]
      letI := ExactOfficialRuleMajorKey.compare_transCmp i.certified.moleculeGraph
      exact Std.ReflCmp.compare_self
    · have ne := h gt
      have flip := dual i c (s y) (s x)
      cases v : (constitutional i c (s x,s y)).outcome <;> simp_all [priority,not_lt_of_ge (le_of_lt gt)]

/-- The checked sorter actually emits the proposed order under the constructed tuple. -/
theorem checked_realization {i : Input} {c : i.certified.TetrahedralCenter} {s : Equiv.Perm (Fin 4)}
    (h : Extends i c s) : i.certified.ruleMajorLigandOrderAt? c (realization s) = some (List.ofFn s) := by
  let r (a b : Fin 4) := decide (s.symm a ≤ s.symm b)
  have before : i.certified.ruleMajorLigandBeforeAt c (realization s) = r := by
    funext a b
    obtain ⟨cert,read,exactOut⟩ := Option.map_eq_some_iff.mp (outcome_of_extends h a b)
    simp only [ruleMajorLigandBeforeAt,read,exactOut,priority]
    rcases lt_trichotomy (s.symm a) (s.symm b) with lt | eq | gt
    · simp [lt,r,le_of_lt lt]
    · have ab := s.symm.injective eq
      simp [ab,r]
    · simp [not_lt_of_ge (le_of_lt gt),gt,r,not_le_of_gt gt]
  have sorted : i.certified.ruleMajorLigandOrderAt c (realization s) = List.ofFn s := by
    unfold ruleMajorLigandOrderAt
    rw [before]
    apply List.Perm.eq_of_pairwise (le := fun a b => s.symm a ≤ s.symm b)
      (fun a b _ _ ab ba => s.symm.injective (le_antisymm ab ba))
    · have sorted := List.pairwise_mergeSort (le := r)
          (fun a b d h k => by simpa [r] using le_trans (of_decide_eq_true h) (of_decide_eq_true k))
          (fun a b => by simpa [r] using le_total (s.symm a) (s.symm b)) (List.finRange 4)
      simpa [r] using sorted
    · exact List.pairwise_ofFn.mpr (fun _ _ lt => by simpa using le_of_lt lt)
    · exact (List.mergeSort_perm ..).trans (by simpa [List.ofFn_eq_map] using s.map_finRange_perm.symm)
  apply (i.certified.ruleMajorLigandOrderAt?_eq_some_iff ..).mpr
  refine ⟨?_,?_,sorted⟩
  · apply List.all_eq_true.mpr
    intro a _
    apply List.all_eq_true.mpr
    intro b _
    by_cases ab : a = b
    · simp [ab]
    · obtain ⟨cert,read,out⟩ := Option.map_eq_some_iff.mp (outcome_of_extends h a b)
      have ne := fun e => ab (s.symm.injective e)
      rcases lt_or_gt_of_ne ne with lt | gt
      · simp [ruleMajorPairResolvedAt?,read,out,priority,lt,ab]
      · simp [ruleMajorPairResolvedAt?,read,out,priority,gt,not_lt_of_ge (le_of_lt gt),ab]
  · unfold ruleMajorOrderCoherentAt?
    rw [sorted,i.certified.ruleMajorOrderCoherentListAt?_eq_true_iff,List.pairwise_ofFn]
    intro x y lt
    apply Option.map_eq_some_iff.mp
    simpa [priority,lt] using outcome_of_extends h (s x) (s y)

/-- Complete image of the explicit context interface, with one joint tuple for all
six comparisons, quantified over arbitrary finite ring inputs and permutations. -/
theorem attainable_iff_extends (i : Input) (c : i.certified.TetrahedralCenter) (s : Equiv.Perm (Fin 4)) :
    (∃ ctx : Context, i.certified.ruleMajorLigandOrderAt? c ctx = some (List.ofFn s)) ↔ Extends i c s := by
  refine ⟨?_,fun h => ⟨realization s,checked_realization h⟩⟩
  rintro ⟨ctx,found⟩ x y h lt
  obtain ⟨_,checked,sort⟩ := (i.certified.ruleMajorLigandOrderAt?_eq_some_iff ..).mp found
  unfold ruleMajorOrderCoherentAt? at checked
  rw [sort,i.certified.ruleMajorOrderCoherentListAt?_eq_true_iff,List.pairwise_ofFn] at checked
  obtain ⟨cert,read,out⟩ := checked h
  have contra := context_outcome i c ctx (s x) (s y)
  simp [read,out,lt] at contra

/-- List-level form: exactly the permutations of the four slots respecting every
strict constitutional comparison occur as successful checked output. -/
theorem attainable_list (i : Input) (c : i.certified.TetrahedralCenter) (xs : List (Fin 4)) :
    (∃ ctx : Context, i.certified.ruleMajorLigandOrderAt? c ctx = some xs) ↔
    xs.Perm (List.finRange 4) ∧ xs.Pairwise (fun a b => (constitutional i c (a,b)).outcome ≠ .lt) := by
  constructor
  · rintro ⟨ctx,found⟩
    obtain ⟨_,checked,sort⟩ := (i.certified.ruleMajorLigandOrderAt?_eq_some_iff ..).mp found
    unfold ruleMajorOrderCoherentAt? at checked
    rw [sort,i.certified.ruleMajorOrderCoherentListAt?_eq_true_iff] at checked
    refine ⟨(i.certified.ruleMajorLigandOrderAt?_sound_declarative _ _ _ found).1,checked.imp ?_⟩
    rintro a b ⟨cert,read,out⟩ lt
    have contra := context_outcome i c ctx a b
    simp [read,out,lt] at contra
  · rintro ⟨perm,pairs⟩
    have len : xs.length = 4 := by simpa using perm.length_eq
    have nodup := perm.nodup_iff.mpr (List.nodup_finRange 4)
    let s : Equiv.Perm (Fin 4) := (finCongr len.symm).trans
      (nodup.getEquivOfForallMemList xs (fun x => perm.mem_iff.mpr (List.mem_finRange _)))
    have exactList : List.ofFn s = xs := by
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using len.symm
      · intro n hn hn'
        rw [List.getElem_ofFn]
        rfl
    rw [← exactList] at pairs ⊢
    exact (attainable_iff_extends i c s).mpr (List.pairwise_ofFn.mp pairs)

private theorem weak_order_exists (i : Input) (c : i.certified.TetrahedralCenter) :
    ∃ xs : List (Fin 4), xs.Perm (List.finRange 4) ∧
      xs.Pairwise (fun a b => (constitutional i c (a,b)).outcome ≠ .lt) := by
  let cmp := ExactOfficialRuleMajorKey.compare i.certified.moleculeGraph
  letI : Std.TransCmp cmp := ExactOfficialRuleMajorKey.compare_transCmp _
  let key := RingStrictConstitution.key i.certified c
  let r (a b : Fin 4) := (cmp (key a) (key b)).isGE
  refine ⟨(List.finRange 4).mergeSort r,List.mergeSort_perm ..,?_⟩
  have sorted := List.pairwise_mergeSort (le := r)
    (fun _ _ _ => Std.TransCmp.isGE_trans (cmp := cmp))
    (fun a b => by
      unfold r
      rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := key a) (b := key b)]
      cases cmp (key b) (key a) <;> rfl) (List.finRange 4)
  apply sorted.imp
  intro a b h
  rw [constitutional_key]
  change cmp (key a) (key b) ≠ .lt
  intro v
  change (cmp (key a) (key b)).isGE = true at h
  simp [v] at h

private theorem swap_preserves {i : Input} {c : i.certified.TetrahedralCenter} {a b : Fin 4}
    (tie : (constitutional i c (a,b)).outcome = .eq) (x y : Fin 4) :
    (constitutional i c (Equiv.swap a b x,Equiv.swap a b y)).outcome =
    (constitutional i c (x,y)).outcome := by
  let cmp := ExactOfficialRuleMajorKey.compare i.certified.moleculeGraph
  letI : Std.TransCmp cmp := ExactOfficialRuleMajorKey.compare_transCmp _
  let key := RingStrictConstitution.key i.certified c
  rw [constitutional_key] at tie
  have same (u : Fin 4) : cmp (key (Equiv.swap a b u)) (key u) = .eq := by
    by_cases ua : u = a
    · subst u; simpa using Std.OrientedCmp.eq_symm (cmp := cmp) tie
    · by_cases ub : u = b
      · subst u; simpa using tie
      · rw [Equiv.swap_apply_of_ne_of_ne ua ub]
        exact Std.ReflCmp.compare_self
  simp only [constitutional_key]
  exact (Std.TransCmp.congr_left (same x)).trans (Std.TransCmp.congr_right (same y))

open LocalizedGenericMarkedRecalculation LocalizedMarkedTerminalGaugeSwap
open LocalizedChemicalRingPhysicalSense (inputGeometry inputGeometry_val)

/-- When the exact constitutional prefix ties on a distinct pair, there are two
joint explicit context assignments whose checked orders give opposite raw
coordinate hands on the very same geometry. These assignments realize the
interface possibilities; neither is asserted to be the molecular publication. -/
theorem opposite_hands_of_tie (i : Input) (admitted : coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) {a b : Fin 4} (distinct : a ≠ b)
    (tie : (constitutional i c (a,b)).outcome = .eq) :
    ∃ (f g : Context) (xs ys : List (Fin 4)) (hand : RS),
      i.certified.ruleMajorLigandOrderAt? c f = some xs ∧
      i.certified.ruleMajorLigandOrderAt? c g = some ys ∧ ys = xs.map (Equiv.swap a b) ∧
      readback? (inputGeometry i.certified) (RingStrictConstitution.atomIds i.certified c xs) = some hand ∧
      readback? (inputGeometry i.certified) (RingStrictConstitution.atomIds i.certified c ys) = some hand.swap := by
  obtain ⟨xs,perm,sorted⟩ := weak_order_exists i c
  let swap := Equiv.swap a b
  let ys := xs.map swap
  have perm' : ys.Perm (List.finRange 4) := (perm.map swap).trans swap.map_finRange_perm
  have sorted' : ys.Pairwise (fun x y => (constitutional i c (x,y)).outcome ≠ .lt) := by
    apply List.pairwise_map.mpr
    apply sorted.imp
    intro x y h
    simpa [swap,swap_preserves tie] using h
  obtain ⟨f,raw⟩ := (attainable_list i c xs).mpr ⟨perm,sorted⟩
  obtain ⟨g,other⟩ := (attainable_list i c ys).mpr ⟨perm',sorted'⟩
  let atom := fun k : Fin 4 => (i.certified.canonicalLigandAtom c k).val
  have injective : Function.Injective atom := Fin.val_injective.comp (i.certified.canonicalLigandAtom_injective c)
  have ids : (xs.map atom).Perm ((List.finRange 4).map atom) := perm.map atom
  have nodup := (List.nodup_finRange 4).map injective
  have four : ((List.finRange 4).map atom).length = 4 := rfl
  let geom := inputGeometry i.certified
  obtain ⟨pt,points,nonzero,_⟩ := LocalizedChemicalRingPhysicalAdmission.canonical_all_calibrated i.certified admitted c
  have canonical : ((List.finRange 4).map atom) = [atom 0,atom 1,atom 2,atom 3] := rfl
  have seen : (readback? geom ((List.finRange 4).map atom)).isSome = true := by
    have observe (k : Fin 4) : geom (atom k) = some (pt k) := (inputGeometry_val i.certified _).trans (points k)
    rw [canonical]
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · simp [readback?,observe,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,neg]
    · simp [readback?,observe,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,pos,not_lt.mpr pos.le]
  obtain ⟨hand,seen⟩ := Option.isSome_iff_exists.mp
    (RingChemicalPriority.ReferenceFrame.readback_all_permutations nodup four seen _ ids)
  refine ⟨f,g,xs,ys,hand,raw,other,rfl,seen,?_⟩
  have commute (x : Fin 4) : atom (swap x) = swapAtom (atom a) (atom b) (atom x) := by
    by_cases xa : x = a
    · subst x; simp [swap,swapAtom]
    · by_cases xb : x = b
      · subst x; simp [swap,swapAtom,injective.ne distinct.symm]
      · simp [swap,swapAtom,Equiv.swap_apply_of_ne_of_ne xa xb,injective.ne xa,injective.ne xb]
  have atoms : ys.map atom = (xs.map atom).map (swapAtom (atom a) (atom b)) := by
    simp only [ys,List.map_map]
    exact List.map_congr_left fun x _ => commute x
  have mem (u : Fin 4) : atom u ∈ xs.map atom := List.mem_map.mpr ⟨u,perm.mem_iff.mpr (List.mem_finRange _),rfl⟩
  change readback? geom (ys.map atom) = _
  rw [atoms,readback_swapAtom geom _ _ (injective.ne distinct) _ (ids.nodup_iff.mpr nodup) (ids.length_eq.trans four) (mem a) (mem b),seen]
  rfl

/-- Exact geometric consequence of a nonempty residual. At an admitted center
both raw hands occur among all successful explicit context tuples if and only
if the molecular constitutional comparisons leave at least one pair tied. -/
theorem opposite_hands_iff_residual (i : Input) (admitted : coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) :
    (∃ (f g : Context) (xs ys : List (Fin 4)) (hand : RS),
      i.certified.ruleMajorLigandOrderAt? c f = some xs ∧
      i.certified.ruleMajorLigandOrderAt? c g = some ys ∧
      readback? (inputGeometry i.certified) (RingStrictConstitution.atomIds i.certified c xs) = some hand ∧
      readback? (inputGeometry i.certified) (RingStrictConstitution.atomIds i.certified c ys) = some hand.swap) ↔
      residual i c ≠ [] := by
  constructor
  · rintro ⟨f,g,xs,ys,hand,fx,gy,rx,ry⟩ empty
    have unique := (strict_iff_empty i c).mpr empty
    have x := Option.some.inj (fx.symm.trans (RingStrictConstitution.checked_order unique f))
    have y := Option.some.inj (gy.symm.trans (RingStrictConstitution.checked_order unique g))
    rw [x.trans y.symm,ry] at rx
    cases hand <;> contradiction
  · intro nonempty
    obtain ⟨p,mem⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨ordered,tie⟩ := (mem_residual i c p).mp mem
    obtain ⟨f,g,xs,ys,hand,fx,gy,_,rx,ry⟩ := opposite_hands_of_tie i admitted c (ne_of_lt ordered) tie
    exact ⟨f,g,xs,ys,hand,fx,gy,rx,ry⟩

end TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalRefinements

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalRefinements.checked_realization
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalRefinements.attainable_iff_extends
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalRefinements.attainable_list
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalRefinements.opposite_hands_of_tie
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalRefinements.opposite_hands_iff_residual
