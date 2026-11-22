import TetraStereo.Engine.RingTwoPairOrientation

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority
open OneCenter LocalizedGenericMarkedRecalculation Recursive

/-- A division of the written molecular graph into two sides. Only bonds
incident to the chosen spiro atom may cross between the sides. -/
def BondCut (m : RawMolecule) (root : Nat) (side : Nat → Bool) : Prop :=
  ∀ b ∈ m.bonds, b.source ≠ root → b.target ≠ root → side b.source = side b.target

private structure Inside (root : Nat) (side : Nat → Bool) (color : Bool)
    (n : RawMolecule.CanonicalBranchNode) : Prop where
  visited : root ∈ n.history
  terminal : n.atom = root → n.forcedLeaf = true
  colored : n.atom ≠ root → side n.atom = color

private theorem child_inside {m root side color n} (cut : BondCut m root side)
    (parent : Inside root side color n) {c} (child : c ∈ m.canonicalChildren n) :
    Inside root side color c := by
  unfold RawMolecule.canonicalChildren at child
  split at child
  · contradiction
  rename_i nonterminal
  obtain ⟨copy,generated,rfl⟩ := List.mem_map.mp child
  have different : n.atom ≠ root := fun h => nonterminal (parent.terminal h)
  obtain ⟨bond,bound,edge,_⟩ := m.canonicalChildCopies_source n copy generated
  constructor
  · exact List.mem_cons_of_mem _ parent.visited
  · intro returned
    change copy.1 = root at returned
    have occurs : copy.1 ∈ n.history := returned ▸ parent.visited
    cases copy.2 <;> simp [RawMolecule.CanonicalBranchNode.forcedLeaf,occurs]
  · intro other
    change copy.1 ≠ root at other
    change side copy.1 = color
    rcases edge with forward | backward
    · have h := cut bond bound (forward.1 ▸ different) (forward.2 ▸ other)
      rw [forward.1,forward.2] at h
      exact h.symm.trans (parent.colored different)
    · have h := cut bond bound (backward.2 ▸ other) (backward.1 ▸ different)
      rw [backward.1,backward.2] at h
      exact h.trans (parent.colored different)

private theorem mapM_source {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (done : xs.mapM f = some ys) {y : β} (inside : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => cases Option.some.inj done; exact False.elim (List.not_mem_nil inside)
  | cons x xs ih =>
    cases h : f x with
    | none => simp [List.mapM_cons,h] at done
    | some v =>
      cases t : xs.mapM f with
      | none => simp [List.mapM_cons,h,t] at done
      | some tail =>
        have eqn : v :: tail = ys := by simpa [List.mapM_cons,h,t] using done
        rw [← eqn] at inside
        rcases List.mem_cons.mp inside with rfl | later
        · exact ⟨x,by simp,h⟩
        · obtain ⟨z,hz,found⟩ := ih t later
          exact ⟨z,List.mem_cons_of_mem _ hz,found⟩

private theorem sites_stay {m root side color} (cut : BondCut m root side) (fuel : Nat)
    {n d rank fixed ss} (here : Inside root side color n)
    (found : sites m fuel n d rank fixed = some ss) {s : Site} (member : s ∈ ss) :
    s.atom = root ∨ side s.atom = color := by
  induction fuel generalizing n d rank fixed ss with
  | zero => simp [sites] at found
  | succ fuel ih =>
    unfold sites at found
    obtain ⟨kids,keys,rest⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨layers,subtrees,allSites⟩ := Option.bind_eq_some_iff.mp rest
    have assembled : (⟨n.history.reverse,n.atom,d,rank⟩ : Site) :: layers.flatten = ss :=
      Option.some.inj allSites
    rw [← assembled] at member
    rcases List.mem_cons.mp member with head | below
    · subst s
      exact or_iff_not_imp_left.mpr here.colored
    · obtain ⟨layer,inLayers,inLayer⟩ := List.mem_flatten.mp below
      obtain ⟨⟨child,z⟩,inKids,foundLayer⟩ := mapM_source subtrees inLayers
      obtain ⟨node,edge,entry⟩ := mapM_source keys inKids
      obtain ⟨atom,_,entry⟩ := Option.bind_eq_some_iff.mp entry
      have eqNode : node = child := congrArg Prod.fst (Option.some.inj entry)
      subst child
      exact ih (child_inside cut here edge) foundLayer inLayer

private theorem layout_zero {m ss} (layout : Layout m ss) {mark : Nat} (absent : ∀ s ∈ ss, s.atom ≠ mark) :
    ∀ row ∈ layout.read mark, ∀ bit ∈ row, bit = false := by
  intro row member bit inside
  obtain ⟨block,hb,rfl⟩ := List.mem_map.mp member
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp inside
  exact beq_eq_false_iff_ne.mpr (absent s (layout.complete.mem_iff.mp (List.mem_flatten.mpr ⟨block,hb,hs⟩)))

private theorem distant_arm_zero {m p omitted} {e : Experiment m p omitted} {root side}
    (cut : BondCut m root side) (focus : e.focus = canonicalCenterRoot root)
    (arm : Arm m e.focus omitted) {mark : Nat} (different : side arm.ligand ≠ side mark)
    (fresh : mark ≠ root) (armFresh : arm.ligand ≠ root) {o : Observation}
    (observed : (arm.observe p e.depth (some mark)).bind Prod.snd = some o) :
    ∀ row ∈ o.spheres, ∀ bit ∈ row, bit = false := by
  unfold Arm.observe at observed
  cases start : arm.start with
  | none => simp [start,Option.bind_assoc] at observed
  | some n =>
    have edge := arm.bound
    simp only [start] at edge
    have address := m.canonicalChildren_history e.focus n edge.1
    rw [focus] at address
    have here : Inside root side (side arm.ligand) n := ⟨by simp [address,canonicalCenterRoot],
      fun same => (armFresh (edge.2.symm.trans same)).elim,fun _ => congrArg side edge.2⟩
    simp only [start,Option.bind_eq_bind,Option.bind_assoc] at observed
    obtain ⟨_,_,tail⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨_,_,tail⟩ := Option.bind_eq_some_iff.mp tail
    obtain ⟨ss,found,tail⟩ := Option.bind_eq_some_iff.mp tail
    obtain ⟨layout,_,tail⟩ := Option.bind_eq_some_iff.mp tail
    obtain ⟨_,_,read⟩ := Option.bind_eq_some_iff.mp tail
    cases Option.some.inj read
    apply layout_zero layout
    intro s member same
    rcases sites_stay cut (m.atomCount+1) here found member with rootCase | colorCase
    · exact fresh (same ▸ rootCase)
    · exact different (colorCase.symm.trans (congrArg side same))

private theorem zero_row_le {xs ys : List Bool} (shape : xs.length = ys.length)
    (zero : ∀ x ∈ xs, x = false) : xs.map Bool.toNat ≤ ys.map Bool.toNat := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at shape
    | cons y ys =>
      have z := zero x (by simp)
      have tail := ih (by simpa using shape) (fun a h => zero a (List.mem_cons_of_mem _ h))
      subst x
      cases y
      · exact List.cons_le_cons 0 tail
      · exact le_of_lt (List.cons_lt_cons_iff.mpr (.inl (by decide)))

private theorem zero_layers_le {xs ys : PairSpheres.Layers} (shape : xs.map List.length = ys.map List.length)
    (zero : ∀ row ∈ xs, ∀ bit ∈ row, bit = false) : PairSpheres.ranks xs ≤ PairSpheres.ranks ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [PairSpheres.ranks]
  | cons x xs ih =>
    cases ys with
    | nil => simp at shape
    | cons y ys =>
      obtain ⟨h,t⟩ := List.cons.inj shape
      exact PairSpheres.cons_mono (zero_row_le h (zero x (by simp))) (ih t (fun r hr => zero r (by simp [hr])))

private theorem MarkedOrder.shape {m p omitted} {e : Experiment m p omitted} {a b}
    (w : MarkedOrder e a b) : w.left.spheres.map List.length = w.right.spheres.map List.length := by
  by_contra different
  have checked := w.checked
  have neq := w.different
  by_cases after : w.left.after = w.right.after <;>
    simp [compare?,w.same.1,w.same.2,after,PairSpheres.seniorLeft?,different] at checked
  · exact neq checked.symm

/-- An arm in the other component contains no copy of the marked atom.
Every complete ranking therefore puts it below its strictly distinguished
partner, on either geometry. -/
theorem MarkedOrder.loses_across_cut {m p omitted} {e : Experiment m p omitted} {root side a b}
    (cut : BondCut m root side) (focus : e.focus = canonicalCenterRoot root) (w : MarkedOrder e a b)
    (different : side a.ligand ≠ side w.mark) (fresh : w.mark ≠ root) (armFresh : a.ligand ≠ root) :
    w.ordering = .lt := by
  have noBits := distant_arm_zero cut focus a different fresh armFresh w.leftAt
  have bounded := zero_layers_le w.shape noBits
  rcases w.all_completions _ _ (List.forall₂_same.mpr (fun _ _ => .refl _))
      (List.forall₂_same.mpr (fun _ _ => .refl _)) with larger | smaller
  · exact (not_lt_of_ge bounded larger.2).elim
  · exact smaller.1

variable {m : RawMolecule} {p : List Nat} {omitted : List (List Nat)}
    {e : Experiment m p omitted} {mat : Matrix e} {root : Nat} {side : Nat → Bool}

private theorem strict_false_on_far_side (cut : BondCut m root side)
    (focus : e.focus = canonicalCenterRoot root) {i j k : Nat}
    (eligible : k ∈ e.arms.map Arm.ligand) (fresh : k ≠ root) (armFresh : i ≠ root)
    (different : side i ≠ side k) (tied : (mat.row? i j).map Row.unmarked = some .eq) :
    mat.strict k false i j = false := by
  obtain ⟨row,lookup,base⟩ := Option.map_eq_some_iff.mp tied
  obtain ⟨w,mark,order⟩ := row.marked_witness eligible base
  have address : row.address = (i,j) := eq_of_beq
    (List.find?_some (p := fun t : Row e => t.address == (i,j)) lookup)
  have left : row.left.ligand = i := congrArg Prod.fst address
  have loses := w.loses_across_cut cut focus (by simpa only [left,mark] using different)
    (by simpa only [mark] using fresh) (by simpa only [left] using armFresh)
  simp [Matrix.strict,lookup,order,loses]

/-- In an unmarked tied pair split by the cut, the member on the marked
atom's side wins. The proof uses the absence of that atom from every
complete sphere word of the opposite arm. -/
theorem Matrix.strict_of_cut (cut : BondCut m root side) (focus : e.focus = canonicalCenterRoot root)
    {i j k : Nat} (eligible : k ∈ e.arms.map Arm.ligand) (fresh : k ≠ root)
    (left : i ≠ root) (right : j ≠ root) (separate : side i ≠ side j)
    (forward : (mat.row? i j).map Row.unmarked = some .eq)
    (backward : (mat.row? j i).map Row.unmarked = some .eq) :
    mat.strict k false i j = (side i == side k) := by
  by_cases near : side i = side k
  · have other : side j ≠ side k := fun h => separate (near.trans h.symm)
    have loses := strict_false_on_far_side cut focus eligible fresh right other backward
    rcases mat.tied_pair_directions eligible forward backward with yes | no
    · simpa [near] using (yes false).1
    · exact False.elim (Bool.false_ne_true (loses.symm.trans (no false).2))
  · rw [beq_eq_false_iff_ne.mpr near]
    exact strict_false_on_far_side cut focus eligible fresh left near forward

/-- A classified tie must cross every cut with eligible ligands on both
sides. Otherwise a mark on the far side leaves the complete sphere words
of both arms zero, contradicting their strict distinction. -/
theorem Matrix.tied_endpoints_separated (cut : BondCut m root side)
    (focus : e.focus = canonicalCenterRoot root) (fresh : root ∉ e.arms.map Arm.ligand)
    {i j : Nat} (left : i ≠ root) (right : j ≠ root)
    (both : ∀ color : Bool, ∃ k ∈ e.arms.map Arm.ligand, side k = color)
    (forward : (mat.row? i j).map Row.unmarked = some .eq)
    (backward : (mat.row? j i).map Row.unmarked = some .eq) : side i ≠ side j := by
  intro same
  obtain ⟨k,eligible,opposite⟩ := both (!side i)
  have far : side i ≠ side k := by rw [opposite]; cases side i <;> decide
  have kFresh : k ≠ root := fun h => fresh (h ▸ eligible)
  have f := strict_false_on_far_side cut focus eligible kFresh left far forward
  have r := strict_false_on_far_side cut focus eligible kFresh right (same ▸ far) backward
  rcases mat.tied_pair_directions eligible forward backward with h | h
  · exact Bool.false_ne_true (f.symm.trans (h false).1)
  · exact Bool.false_ne_true (r.symm.trans (h false).2)

private theorem Partition.pair_rows (part : Partition mat) {a b c d : Nat}
    (slots : part.order = [a,b,c,d]) :
    let tie := fun i j => (mat.row? i j).map Row.unmarked = some .eq
    (tie a b ∧ tie b a) ∧ (tie c d ∧ tie d c) := by
  have cls : mat.partitionOK [a,b,c,d] = true := slots ▸ part.classes
  have same := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp cls).1
  have ids : [a,b,c,d].Perm (e.arms.map Arm.ligand) := slots ▸ part.incident
  have unique := ids.nodup_iff.mpr e.distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at unique
  have pair {i j : Nat} (ne : i ≠ j)
      (checked : (directedPairs [i,j] id).all (fun (u,v) => ((mat.row? u v).map Row.unmarked) == some .eq) = true) :=
    And.intro (eq_of_beq (List.all_eq_true.mp checked (i,j) (by simp [directedPairs,ne,Ne.symm ne])))
      (eq_of_beq (List.all_eq_true.mp checked (j,i) (by simp [directedPairs,ne,Ne.symm ne])))
  exact ⟨pair unique.1.1 same.1,pair unique.2.2.1 same.2⟩

theorem Partition.split_by_cut (part : Partition mat) (cut : BondCut m root side)
    (focus : e.focus = canonicalCenterRoot root) (fresh : root ∉ e.arms.map Arm.ligand)
    {a b c d : Nat} (slots : part.order = [a,b,c,d])
    (both : ∀ color : Bool, ∃ k ∈ e.arms.map Arm.ligand, side k = color) :
    side a ≠ side b ∧ side c ≠ side d := by
  have ids : [a,b,c,d].Perm (e.arms.map Arm.ligand) := slots ▸ part.incident
  have distinct (i) (member : i ∈ [a,b,c,d]) : i ≠ root := fun h => fresh (h ▸ ids.mem_iff.mp member)
  obtain ⟨ab,cd⟩ := part.pair_rows slots
  exact ⟨mat.tied_endpoints_separated cut focus fresh (distinct a (by simp)) (distinct b (by simp)) both ab.1 ab.2,
    mat.tied_endpoints_separated cut focus fresh (distinct c (by simp)) (distinct d (by simp)) both cd.1 cd.2⟩

/-- For a spiro cut that separates the members of each of the two tied
pairs, their parity is independent of which eligible ligand was marked. -/
theorem Partition.preserves_of_cut (part : Partition mat) (cut : BondCut m root side)
    (focus : e.focus = canonicalCenterRoot root) (fresh : root ∉ e.arms.map Arm.ligand)
    {a b c d : Nat} (slots : part.order = [a,b,c,d])
    (high : side a ≠ side b) (low : side c ≠ side d) {k : Nat} (eligible : k ∈ e.arms.map Arm.ligand) :
    part.preserves k = (side a == side c) := by
  have ids : [a,b,c,d].Perm (e.arms.map Arm.ligand) := slots ▸ part.incident
  have distinct (i) (member : i ∈ [a,b,c,d]) : i ≠ root := fun h => fresh (h ▸ ids.mem_iff.mp member)
  obtain ⟨ab,cd⟩ := part.pair_rows slots
  have kFresh : k ≠ root := fun h => fresh (h ▸ eligible)
  rw [Partition.preserves,slots]
  simp only [Matrix.aligned,mat.strict_of_cut cut focus eligible kFresh
    (distinct a (by simp)) (distinct b (by simp)) high ab.1 ab.2,
    mat.strict_of_cut cut focus eligible kFresh (distinct c (by simp)) (distinct d (by simp)) low cd.1 cd.2]
  cases side a <;> cases side c <;> cases side k <;> rfl

/-- Both molecular pairs cross the same spiro cut. Every eligible choice
therefore gives one common reading, determined by the reference geometry
and the sides of the first member of each pair. -/
theorem PopulationReading.certificate_of_cut {classified : Classified e} {g : Geometry}
    (s : PopulationReading classified g) (cut : BondCut m root side)
    (focus : e.focus = canonicalCenterRoot root) (fresh : root ∉ e.arms.map Arm.ligand)
    {a b c d : Nat} (slots : classified.partition.order = [a,b,c,d])
    (high : side a ≠ side b) (low : side c ≠ side d) :
    let hand := if side a == side c then s.reference else s.reference.swap
    (classified.certificate? g).map Certificate.reading = some ⟨hand,hand.swap⟩ := by
  apply (s.certificate_iff _).mpr
  intro k eligible
  simp only [PopulationReading.atMark,classified.partition.preserves_of_cut cut focus fresh slots high low eligible]

end TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrder.loses_across_cut

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.PopulationReading.certificate_of_cut
