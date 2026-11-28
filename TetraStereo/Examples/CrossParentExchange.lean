import TetraStereo.Examples.CrossParentFaces

/-! A complete test for an exchange of the nitrogen arms preserving raw atom
records, bonds, the central root and the eight donor hands. -/
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
namespace TetraStereo.Examples.CrossParentExchange
open OneCenter Engine
open CrossParentDonorStore (molecule)
open CrossParentRootOrder (donor)
open CrossParentFaces (maskHand spatial)
open private bonded topology from TetraStereo.Examples.CrossParentClasses

private def tip (j : Fin 8) : Fin 41 := ⟨7+j.val,by omega⟩
private def branch (j : Fin 4) : Fin 41 := ⟨3+j.val/2,by omega⟩

/-- Donor hands are measured on the Cl,F,N,H frame. Its four elements
are distinct, so every record-preserving correspondence respects this order. -/
structure Exchange (hands : Fin 8 → RS) where
  atoms : Equiv.Perm (Fin 41)
  root : atoms 0 = 0
  swapLeft : atoms 1 = 2
  swapRight : atoms 2 = 1
  records : ∀ a, molecule.atoms[(atoms a).val]? = molecule.atoms[a.val]?
  bonds : ∀ a b, molecule.bondOrder (atoms a).val (atoms b).val = molecule.bondOrder a.val b.val
  signed : ∀ j k, atoms (tip j) = tip k → hands j = hands k

/-- The three bits exchange the parent pair and independently exchange the
two children of each left parent. -/
private def toggle (on : Bool) (b : Nat) := if on then 1-b else b
private def across (s : Fin 8) (j : Fin 4) : Fin 4 :=
  Fin.ofNat 4 (2 * toggle (s.val.testBit 0) (j.val/2) +
    toggle (s.val.testBit (1+j.val/2)) (j.val%2))

private def accepts (hands : Fin 8 → RS) (s : Fin 8) :=
  (List.finRange 4).all fun j => hands (donor true j) == hands (donor false (across s j))

def hasExchange (hands : Fin 8 → RS) := (List.finRange 8).any (accepts hands)

private def imageDonor (s : Fin 8) (j : Nat) : Nat :=
  if j < 4 then 4+(across s (Fin.ofNat 4 j)).val else
    let k := j-4
    let p := toggle (s.val.testBit 0) (k/2)
    2*p + toggle (s.val.testBit (1+p)) (k%2)

private def image (s : Fin 8) (a : Nat) :=
  if a = 0 then 0 else if a < 3 then 3-a else if a < 7 then 3 + imageDonor s (2*(a-3))/2
  else if a < 15 then 7+imageDonor s (a-7)
  else if a < 39 then 15+3*imageDonor s ((a-15)/3)+(a-15)%3 else a

private theorem facts : ∀ (s : Fin 8) (a : Fin 41), image s a.val < 41 ∧ image s (image s a.val) = a.val ∧
    molecule.atoms[image s a.val]? = molecule.atoms[a.val]? ∧
    ∀ b : Fin 41, bonded (image s a.val) (image s b.val) = bonded a.val b.val := by decide +kernel

private def perm (s : Fin 8) : Equiv.Perm (Fin 41) :=
  let f (a : Fin 41) : Fin 41 := ⟨image s a.val,(facts s a).1⟩
  let inv : Function.Involutive f := fun a => Fin.ext (facts s a).2.1
  ⟨f,f,inv,inv⟩

private theorem extension (s : Fin 8) (hands : Fin 8 → RS) (yes : accepts hands s = true) :
    Nonempty (Exchange hands) := by
  have matched (j : Fin 4) : hands (donor true j) = hands (donor false (across s j)) :=
    eq_of_beq (List.all_eq_true.mp yes j (List.mem_finRange _))
  have state : ∀ (s : Fin 8) (j k : Fin 8), image s (tip j).val = (tip k).val →
      ∃ t : Fin 4, (j = donor true t ∧ k = donor false (across s t)) ∨
        (k = donor true t ∧ j = donor false (across s t)) := by decide +kernel
  refine ⟨⟨perm s,rfl,rfl,rfl,fun a => (facts s a).2.2.1,?_,?_⟩⟩
  · intro a b
    rw [topology,topology a b]
    exact congrArg Bool.toNat ((facts s a).2.2.2 b)
  · intro j k hk
    obtain ⟨t,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := state s j k (congrArg Fin.val hk)
    · exact matched t
    · exact (matched t).symm

private theorem possibilities (f : Fin 4 → Fin 4) (inj : Function.Injective f)
    (one : (f 0).val/2 = (f 1).val/2) (two : (f 2).val/2 = (f 3).val/2) :
    ∃ s : Fin 8, ∀ j, across s j = f j := by
  have finite : ∀ a b c d : Fin 4, [a,b,c,d].Nodup → a.val/2=b.val/2 → c.val/2=d.val/2 →
      ∃ s : Fin 8, across s 0 = a ∧ across s 1 = b ∧ across s 2 = c ∧ across s 3 = d := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel
  have nd : ([f 0,f 1,f 2,f 3] : List (Fin 4)).Nodup :=
    (show ([0,1,2,3] : List (Fin 4)).Nodup by decide).map inj
  obtain ⟨s,h⟩ := finite _ _ _ _ nd one two
  exact ⟨s,fun j => by fin_cases j <;> first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2⟩

private theorem necessary {hands : Fin 8 → RS} (e : Exchange hands) : hasExchange hands = true := by
  have links : ∀ j : Fin 4, bonded 1 (branch j).val = true ∧
      bonded (branch j).val (tip (donor true j)).val = true := by decide +kernel
  have next : ∀ a b : Fin 41, bonded 2 a.val = true → a ≠ 0 → bonded a.val b.val = true → b ≠ 2 →
      ∃ j : Fin 4, a.val = 5+j.val/2 ∧ b = tip (donor false j) := by decide +kernel
  have maps (a b : Fin 41) : bonded (e.atoms a).val (e.atoms b).val = bonded a.val b.val := by
    have bond := e.bonds a b
    rw [topology,topology a b] at bond
    exact (show Function.Injective Bool.toNat by intro u v; cases u <;> cases v <;> decide) bond
  have children (j : Fin 4) : ∃ k : Fin 4, (e.atoms (branch j)).val = 5+k.val/2 ∧
      e.atoms (tip (donor true j)) = tip (donor false k) := by
    have first := (maps 1 (branch j)).trans (links j).1
    rw [e.swapLeft] at first
    apply next _ _ first _ ((maps _ _).trans (links j).2)
    · intro eqn
      have wrong := e.atoms.injective (eqn.trans e.swapLeft.symm)
      have impossible : ∀ j : Fin 4, tip (donor true j) ≠ 1 := by decide +kernel
      exact impossible j wrong
    · intro eqn
      have wrong := e.atoms.injective (eqn.trans e.root.symm)
      have impossible : ∀ j : Fin 4, branch j ≠ 0 := by decide +kernel
      exact impossible j wrong
  choose f parent child using children
  have injective : Function.Injective f := by
    intro a b eqn
    have same := e.atoms.injective ((child a).trans ((eqn ▸ child b).symm))
    have unique : ∀ a b : Fin 4, tip (donor true a) = tip (donor true b) → a = b := by decide +kernel
    exact unique a b same
  have siblings (a b : Fin 4) (ab : branch a = branch b) : (f a).val/2 = (f b).val/2 := by
    have eqn := parent a
    rw [ab,parent b] at eqn
    omega
  obtain ⟨s,matchAll⟩ := possibilities f injective (siblings 0 1 rfl) (siblings 2 3 rfl)
  apply List.any_eq_true.mpr
  refine ⟨s,List.mem_finRange _,List.all_eq_true.mpr ?_⟩
  intro j _
  exact beq_iff_eq.mpr ((matchAll j).symm ▸ e.signed _ _ (child j))

theorem exact_exchange (hands : Fin 8 → RS) : hasExchange hands = true ↔ Nonempty (Exchange hands) := by
  constructor
  · intro yes
    obtain ⟨s,_,found⟩ := List.any_eq_true.mp yes
    exact extension s hands found
  · rintro ⟨e⟩
    exact necessary e

def tiedWithoutExchange (m : Fin 256) :=
  (CrossParentFaces.maskOutcome m).isNone && !(hasExchange (maskHand m))

/-- With two R donors on each side, an arm can put both under one parent
or split them between the two parents. Exactly this mismatch excludes exchange. -/
theorem parent_groups : ∀ m : Fin 256, let h := maskHand m
    tiedWithoutExchange m = (CrossParentRootOrder.rCount h true false == 2 &&
      CrossParentRootOrder.rCount h false false == 2 && ((h 0 == h 1) != (h 4 == h 5))) := by decide +kernel

theorem distribution :
    ((List.finRange 256).filter tiedWithoutExchange).length = 16 ∧
    ((List.finRange 256).filter (fun m => hasExchange (maskHand m))).length = 54 ∧
    (∀ m : Fin 256, hasExchange (maskHand m) = true → CrossParentFaces.maskOutcome m = none) := by decide +kernel

/-- Among profiles with no signed graph exchange, count the actual native
report pairs on the numbered root and its reflection, including refusals. -/
theorem without_exchange_reports :
    let ms := (List.finRange 256).filter (fun m => !(hasExchange (maskHand m)))
    let reports := ms.map fun m => RingHydrogenReport.fromRaw? molecule (spatial (maskHand m)) [0]
    [reports.count (some [(0,some (.chiral .R,.chiral .S))]),
     reports.count (some [(0,some (.chiral .S,.chiral .R))]),
     reports.count (some [(0,some (.pseudoasymmetric .r,.pseudoasymmetric .r))]),
     reports.count (some [(0,some (.pseudoasymmetric .s,.pseudoasymmetric .s))]),
     reports.count (some [(0,none)])] = [76,76,17,17,16] := by
  simp only [CrossParentFaces.raw_mask]
  decide +kernel

/-- Every one of the sixteen selected coordinate tables produces an actual
completed refusal at the center, while no hand-preserving graph exchange exists. -/
theorem raw_refusal {m : Fin 256} (yes : tiedWithoutExchange m = true) :
    RingHydrogenReport.fromRaw? molecule (spatial (maskHand m)) [0] = some [(0,none)] ∧
      ¬ Nonempty (Exchange (maskHand m)) := by
  obtain ⟨h,off⟩ := Bool.and_eq_true_iff.mp yes
  have absent := Option.isNone_iff_eq_none.mp h
  rw [CrossParentFaces.raw_mask,absent]
  exact ⟨rfl,fun ex => by simp [(exact_exchange _).2 ex] at off⟩

end TetraStereo.Examples.CrossParentExchange
assert_kernel_only TetraStereo.Examples.CrossParentExchange.exact_exchange
assert_kernel_only TetraStereo.Examples.CrossParentExchange.distribution
assert_kernel_only TetraStereo.Examples.CrossParentExchange.raw_refusal
assert_kernel_only TetraStereo.Examples.CrossParentExchange.parent_groups
assert_kernel_only TetraStereo.Examples.CrossParentExchange.without_exchange_reports
