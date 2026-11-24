import TetraStereo.Engine.RingBridgedPairs

set_option autoImplicit false

namespace TetraStereo.Engine.RingMarkedIncidence
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open RingActivePairs (Arm)
open RingActivePairReport (Slot)
open RingGroupedCentre (Arms cursor)
open RingGroupedMark (bit Reading)
open RingRetainedChemicalTrace (Word)
open RingNestedActivePair (Frame)
attribute [local instance] lexOrd

private abbrev kids {i : LocalizedChemicalRing.Input} (q : Arm i) := i.certified.executableLocalizedRerootChildren q

private theorem root_value {i read atom q b} (h : Reading i read atom q b) : b.value = bit atom q := by cases h; rfl

private theorem values {α β γ : Type} {R : α → β → Prop} {u : α → γ} {v : β → γ}
    {xs ys} (ps : List.Forall₂ R xs ys) (h : ∀ x ∈ xs, ∀ y, R x y → v y = u x) :
    ys.map v = xs.map u := by
  induction ps with
  | nil => rfl
  | cons head _ ih =>
    exact congrArg₂ List.cons (h _ List.mem_cons_self _ head)
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- The first two comparisons of a marked arm read the mark at its own atom
and the mark bits on its immediate children, in a legal sibling order. -/
theorem prefix_rows {i read atom q b} (h : Reading i read atom q b) :
    ∃ row rest, b.word = [bit atom q] :: row :: rest ∧ row.Perm ((kids q).map (bit atom)) := by
  cases h with
  | node before get all sub sh de =>
    refine ⟨_,_,rfl,(sh.perm.map Branch.value).trans (List.Perm.of_eq ?_)⟩
    have listed := TerminalTie.mapM_forall₂ _ _ _ all
    exact values listed (fun c hc v found => root_value (sub c hc found))

private theorem compare_zero_row {xs ys : List Nat} (size : xs.length = ys.length)
    (one : 1 ∈ xs) (zero : ∀ n ∈ ys, n = 0) : compare xs ys = .gt := by
  induction xs generalizing ys with
  | nil => contradiction
  | cons x xs ih =>
    cases ys with
    | nil => simp at size
    | cons y ys =>
      obtain rfl := zero y List.mem_cons_self
      cases x with
      | zero =>
        have tail := ih (Nat.succ.inj size) (by simpa using one) (fun n hn => zero n (List.mem_cons_of_mem _ hn))
        simpa only [List.compare_cons_cons,Std.ReflCmp.compare_self,Ordering.eq_then] using tail
      | succ n =>
        have gt : compare (n+1) 0 = .gt := Nat.compare_eq_gt.mpr (Nat.zero_lt_succ n)
        simp only [List.compare_cons_cons,gt,Ordering.gt_then]

theorem head_wins {i read atom q t b d} (a : Reading i read atom q b) (e : Reading i read atom t d)
    (head : bit atom q = 1) (other : bit atom t = 0) : compare b.word d.word = .gt := by
  obtain ⟨_,_,x,_⟩ := prefix_rows a
  obtain ⟨_,_,y,_⟩ := prefix_rows e
  rw [x,y,head,other,List.compare_cons_cons]
  rfl

/-- If the marked atom occurs just across a bond in only one arm, this arm
wins before any more distant occurrence can influence the comparison. -/
theorem neighbor_wins {i read atom q t b d} (a : Reading i read atom q b) (e : Reading i read atom t d)
    (heads : bit atom q = bit atom t) (arity : (kids q).length = (kids t).length)
    (adjacent : ∃ x ∈ kids q, bit atom x = 1)
    (separated : ∀ x ∈ kids t, bit atom x = 0) : compare b.word d.word = .gt := by
  obtain ⟨l,_,x,hx⟩ := prefix_rows a
  obtain ⟨r,_,y,hy⟩ := prefix_rows e
  have size : l.length = r.length := by simpa using hx.length_eq.trans (by simpa [arity] using hy.length_eq.symm)
  obtain ⟨c,hc,h⟩ := adjacent
  have present : 1 ∈ l := hx.mem_iff.mpr (List.mem_map.mpr ⟨c,hc,h⟩)
  have absent (n) (hn : n ∈ r) : n = 0 := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (hy.mem_iff.mp hn)
    exact separated t ht
  simp only [x,y,heads,List.compare_cons_cons,Std.ReflCmp.compare_self,Ordering.eq_then,compare_zero_row size present absent,Ordering.gt_then]

abbrev selected {i f} (fr : Frame i f) (s : Slot) := RingGroupedTrials.atom fr s

/-- Evidence for a within-pair victory using the first atom or its first
sphere. All premises are observations of the retained molecular carrier. -/
inductive Nearer {i f} (fr : Frame i f) (s j k : Slot) : Prop where
  | head (own : bit (selected fr s) (cursor fr j) = 1)
      (other : bit (selected fr s) (cursor fr k) = 0) : Nearer fr s j k
  | neighbor (heads : bit (selected fr s) (cursor fr j) = bit (selected fr s) (cursor fr k))
      (arity : (kids (cursor fr j)).length = (kids (cursor fr k)).length)
      (adjacent : ∃ t ∈ kids (cursor fr j), bit (selected fr s) t = 1)
      (separated : ∀ t ∈ kids (cursor fr k), bit (selected fr s) t = 0) : Nearer fr s j k

instance {i f} (fr : Frame i f) (s j k : Slot) : Decidable (Nearer fr s j k) :=
  decidable_of_iff
    ((bit (selected fr s) (cursor fr j) = 1 ∧ bit (selected fr s) (cursor fr k) = 0) ∨
      (bit (selected fr s) (cursor fr j) = bit (selected fr s) (cursor fr k) ∧
       (kids (cursor fr j)).length = (kids (cursor fr k)).length ∧
       (∃ t ∈ kids (cursor fr j), bit (selected fr s) t = 1) ∧
       (∀ t ∈ kids (cursor fr k), bit (selected fr s) t = 0))) (by
    constructor
    · rintro (⟨a,b⟩ | ⟨a,b,c,d⟩)
      · exact .head a b
      · exact .neighbor a b c d
    · intro h
      cases h with
      | head a b => exact Or.inl ⟨a,b⟩
      | neighbor a b c d => exact Or.inr ⟨a,b,c,d⟩)

theorem Nearer.wins {i f read} {fr : Frame i f} (ready : RingGroupedStereo.Ready f read)
    {s j k} (near : Nearer fr s j k) :
    compare (RingOrientation.markedWord fr read s j) (RingOrientation.markedWord fr read s k) = .gt := by
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready (selected fr s) (cursor fr j) (RingGroupedCentre.valid fr j) (fr.direction j).property.1
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready (selected fr s) (cursor fr k) (RingGroupedCentre.valid fr k) (fr.direction k).property.1
  have a := (RingGroupedMark.arm_source hx).2
  have b := (RingGroupedMark.arm_source hy).2
  simp only [RingOrientation.markedWord,hx,hy,Option.map_some,Option.getD_some]
  cases near with
  | head own other => exact head_wins a b own other
  | neighbor heads arity adj sep => exact neighbor_wins a b heads arity adj sep

/-- This local incidence pattern may be embedded in a larger bridged graph.
Both pairs point to the same side for each of the four marks. -/
def Coupled {i f fr read arms} (p : @RingBridgedPairs.Pairs i f fr read arms) :=
  ∀ s : Slot, (Nearer fr s p.a p.b ∧ Nearer fr s p.c p.d) ∨
    (Nearer fr s p.b p.a ∧ Nearer fr s p.d p.c)

/-- Certify the proposed partition and both bond preferences for every mark. -/
def classify? {i f fr read} (arms : @Arms i f fr read) (a b c d : Slot) :
    Option {p : RingBridgedPairs.Pairs arms // Coupled p} := do
  if shape : [a,b,c,d].isPerm (List.finRange 4) = true ∧ (arms.key false a == arms.key false b) = true ∧
      (arms.key false c == arms.key false d) = true ∧ compare (arms.key false a) (arms.key false c) = .gt then
    let p : RingBridgedPairs.Pairs arms := ⟨a,b,c,d,List.isPerm_iff.mp shape.1,beq_iff_eq.mp shape.2.1,beq_iff_eq.mp shape.2.2.1,shape.2.2.2⟩
    letI : Decidable (Coupled p) := by unfold Coupled; infer_instance
    if h : Coupled p then return ⟨p,h⟩ else none
  else none

theorem coupled_index {i f fr read arms} (p : @RingBridgedPairs.Pairs i f fr read arms)
    (ready : RingGroupedStereo.Ready f read) (coupled : Coupled p) :
    RingOrientation.index arms = p.sign * 4 := by
  have each (s : Slot) : p.coupling s = 1 := by
    unfold RingBridgedPairs.Pairs.coupling
    rcases coupled s with ⟨a,b⟩ | ⟨a,b⟩
    · simp [a.wins ready,b.wins ready,RingBridgedPairs.contribution]
    · have flip {x y : Word} (h : compare y x = .gt) : compare x y = .lt := by
        rw [Std.OrientedCmp.eq_swap (cmp := compare),h]; rfl
      simp [flip (a.wins ready),flip (b.wins ready),RingBridgedPairs.contribution]
  have total : ((List.finRange 4).map p.coupling).sum = 4 := by rw [funext each]; decide
  rw [p.index,total]

theorem coupled_descriptor {i f fr read arms m} (p : @RingBridgedPairs.Pairs i f fr read arms)
    (d : RingGroupedTrials.Decision arms m) (ready : RingGroupedStereo.Ready f read)
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (coupled : Coupled p) :
    d.letters.isSome = true ∧ d.balance false = RingOrientation.baseline fr * (p.sign * 4) := by
  have index := coupled_index p ready coupled
  refine ⟨?_,by rw [RingOrientation.balance_from_geometry d ready,index]⟩
  apply Option.ne_none_iff_isSome.mp
  intro no
  have zero := (RingOrientation.refusal_iff d ready coords).mp no
  rw [index,mul_eq_zero] at zero
  rcases zero with z | z
  · unfold RingBridgedPairs.Pairs.sign at z
    split at z <;> contradiction
  · contradiction

end TetraStereo.Engine.RingMarkedIncidence
assert_kernel_only TetraStereo.Engine.RingMarkedIncidence.coupled_descriptor
assert_kernel_only TetraStereo.Engine.RingMarkedIncidence.classify?
