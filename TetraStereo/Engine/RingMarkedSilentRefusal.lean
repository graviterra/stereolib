import TetraStereo.Engine.RingSharedArmRefusal

set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedSilentRefusal
open OneCenter CertifiedLocalizedCIPInput RingChemicalPriority LocalizedGenericMarkedRecalculation
open ReferenceDistance

abbrev Cursor := CanonicalRerootCursor

/-- At every sphere (including the ligand itself and ring closure copies), the
actual atom selected for promotion is absent. -/
def Clear (m : RawMolecule) (mark : Nat) (c : Cursor) : Prop :=
  ∀ route k (s : AtomSite), s ∈ shell m k ⟨c,route⟩ → s.cursor.node.atom ≠ mark

def clearAt (m : RawMolecule) (mark : Nat) : Nat → Cursor → Bool
  | 0,_ => false
  | n+1,c => c.node.atom != mark && (c.children m).all (clearAt m mark n)

theorem clearAt_sound {m k n c} (found : clearAt m k n c = true) : Clear m k c := by
  induction n generalizing c with
  | zero => contradiction
  | succ n ih =>
    obtain ⟨here,below⟩ := Bool.and_eq_true_iff.mp found
    intro route j s hs
    cases j with
    | zero =>
      obtain rfl := List.mem_singleton.mp hs
      exact bne_iff_ne.mp here
    | succ j =>
      obtain ⟨u,edge,inside⟩ := List.mem_flatMap.mp hs
      exact ih (List.all_eq_true.mp below u edge) _ _ _ inside

private theorem Clear.atRoot {m k c} (h : Clear m k c) : c.node.atom ≠ k :=
  h [] 0 ⟨c,[]⟩ (List.mem_singleton_self _)

private theorem Clear.child {m k c} (h : Clear m k c) {x} (mem : x ∈ c.children m) : Clear m k x := by
  intro route n s hs
  -- The carrier and its descendants do not depend on the incoming route annotation.
  have transfer {n : Nat} {u : Cursor} {r : List RawMolecule.CanonicalBranchNode} {v : AtomSite}
      (hv : v ∈ shell m n ⟨u,r⟩) (r' : List RawMolecule.CanonicalBranchNode) :
      ∃ w ∈ shell m n ⟨u,r'⟩, w.cursor = v.cursor := by
    induction n generalizing u r v r' with
    | zero =>
      obtain rfl := List.mem_singleton.mp hv
      exact ⟨_,List.mem_singleton_self _,rfl⟩
    | succ n ih =>
      obtain ⟨u',edge,below⟩ := List.mem_flatMap.mp hv
      obtain ⟨w,attached,eqn⟩ := ih below (r' ++ [u'.node])
      exact ⟨w,List.mem_flatMap.mpr ⟨u',edge,attached⟩,eqn⟩
  obtain ⟨w,below,eqn⟩ := transfer hs [x.node]
  have avoid := h [] (n+1) w (List.mem_flatMap.mpr ⟨x,mem,below⟩)
  simpa only [eqn] using avoid

private theorem forall₂_mem {α β : Type} {R S : α → β → Prop} {xs ys}
    (given : List.Forall₂ R xs ys) (step : ∀ x ∈ xs, ∀ y ∈ ys, R x y → S x y) : List.Forall₂ S xs ys := by
  induction given with
  | nil => exact .nil
  | cons xy _ ih =>
    exact .cons (step _ List.mem_cons_self _ List.mem_cons_self xy)
      (ih (fun x hx y hy => step x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)))

/-- The *same* complete earlier-rule correspondence still matches after attaching
the actual mark bit to every retained occurrence. -/
theorem matched_with_mark {ω : Type} {m : RawMolecule} {obs : Cursor → Option ω}
    {n a b k} (matched : IsotopePriority.TreesMatch m obs n a b) (left : Clear m k a) (right : Clear m k b) :
    IsotopePriority.TreesMatch m (withMark obs k) n a b := by
  induction n generalizing a b with
  | zero => contradiction
  | succ n ih =>
    obtain ⟨o,hl,hr,order,perm,sub⟩ := matched
    refine ⟨(o,false),?_,?_,order,perm,?_⟩
    · simp [withMark,hl,left.atRoot]
    · simp [withMark,hr,right.atRoot]
    · exact forall₂_mem sub (fun x hx y hy s => ih s (left.child hx) (right.child (perm.mem_iff.mp hy)))

/-- Every accepted strict Rule 6 comparison requires a concrete occurrence of the
mark, including the hierarchy case where the decisive sites lie in ordered blocks. -/
theorem no_strict {m a b k} (left : Clear m k a) (right : Clear m k b) :
    IsEmpty (Strict m a b k) := by
  constructor
  intro d
  have noHit {u s j} (clear : Clear m k u) (mem : s ∈ sitesAt m u j) : hits k s = false :=
    beq_eq_false_iff_ne.mpr (clear _ _ _ mem)
  cases d with
  | distance d =>
    have yes := d.marked
    have edge := d.member
    cases h : d.leftWins with
    | true =>
      have off := noHit left (d.sphere.leftAt.symm ▸ (by simpa [h] using edge : d.occurrence ∈ d.sphere.left))
      simp [off] at yes
    | false =>
      have off := noHit right (d.sphere.rightAt.symm ▸ (by simpa [h] using edge : d.occurrence ∈ d.sphere.right))
      simp [off] at yes
  | hierarchy d =>
    have l := noHit left (d.sphere.leftAt.symm ▸ (d.left.legal.1.mem_iff.mpr (List.mem_of_getElem? d.leftSiteAt)))
    have r := noHit right (d.sphere.rightAt.symm ▸ (d.right.legal.1.mem_iff.mpr (List.mem_of_getElem? d.rightSiteAt)))
    have yes := d.decisive
    cases h : d.leftWins <;> simp [l,r,h] at yes

/-- The actual comparison after promotion is present and exactly equal. The
failed strict search follows from the impossibility of either kind of strict
molecular witness. It is independent of all internal search orders. -/
theorem pair_atMark_equal {m p i j} (pair : Pair m p i j) (k : Nat)
    (fixed : pair.flip = false) (incident : k ∈ (occurrenceLigandCursors m pair.focus).map (·.node.atom))
    (left : Clear m k ⟨pair.left.node,some pair.focus⟩) (right : Clear m k ⟨pair.right.node,some pair.focus⟩) :
    (pair.atMark? k).map (fun c => c.verdict.ordering) = some .eq := by
  have aligned := matched_with_mark pair.matched left right
  rw [fixed] at aligned
  have found := IsotopePriority.treesMatch_complete aligned
  simp only [Pair.atMark?,dif_pos fixed,dif_pos incident]
  split
  · rename_i d _
    exact False.elim ((no_strict left right).false d)
  · simp [found,Verdict.ordering]



/-- A source-indexed transport maps the atom at one actual occurrence to
the atom at another. An occurrence can be a real or a duplicate vertex. -/
def Carries {m : RawMolecule} (e : Equiv.Perm (RingSilentPair.Atom m)) (x y : Cursor) : Prop :=
  ∃ h : x.node.atom < m.atomCount, (e ⟨x.node.atom,h⟩).val = y.node.atom

private theorem carried_hit {m : RawMolecule} {e : Equiv.Perm (RingSilentPair.Atom m)}
    {mark : RingSilentPair.Atom m} (fix : e mark = mark) {x y : Cursor} (h : Carries e x y) :
    (x.node.atom == mark.val) = (y.node.atom == mark.val) := by
  obtain ⟨bound,eqn⟩ := h
  let a : RingSilentPair.Atom m := ⟨x.node.atom,bound⟩
  have image : (e a).val = y.node.atom := eqn
  have same : (e a).val = mark.val ↔ a.val = mark.val := by
    constructor
    · intro h
      exact congrArg Fin.val (e.injective ((Fin.ext h).trans fix.symm))
    · intro h
      exact congrArg Fin.val ((congrArg e (Fin.ext h)).trans fix)
  change (a.val == mark.val) = _
  rw [← image]
  by_cases hm : a.val = mark.val <;> simp [same,hm]

/-- A single atom permutation aligns the *entire* provenance-bearing tree,
including each earlier observation. Sorting never substitutes an independent
matching for individual occurrences of the active atom. -/
def CarriedTrees {ω : Type} (m : RawMolecule) (obs : Cursor → Option ω) (e : Equiv.Perm (RingSilentPair.Atom m)) :
    Nat → Cursor → Cursor → Prop
  | 0,_,_ => False
  | n+1,a,b => Carries e a b ∧ ∃ o, obs a = some o ∧ obs b = some o ∧
    ∃ ordered, ordered.Perm (b.children m) ∧ List.Forall₂ (CarriedTrees m obs e n) (a.children m) ordered

theorem CarriedTrees.marked {ω : Type} {m : RawMolecule} {obs : Cursor → Option ω}
    {e : Equiv.Perm (RingSilentPair.Atom m)} {n a b} (h : CarriedTrees m obs e n a b)
    (mark : RingSilentPair.Atom m) (fix : e mark = mark) :
    IsotopePriority.TreesMatch m (withMark obs mark.val) n a b := by
  induction n generalizing a b with
  | zero => contradiction
  | succ n ih =>
    obtain ⟨move,o,hl,hr,order,perm,sub⟩ := h
    refine ⟨(o,a.node.atom == mark.val),?_,?_,order,perm,sub.imp (fun _ _ matched => ih matched)⟩
    · simp [withMark,hl]
    · simp [withMark,hr,carried_hit fix move]

/-- Both sphere orderings respect the actual parent and sibling sequence
priorities. Every matched atom in those orderings has the image prescribed
by the same whole-molecule permutation. This is a condition on occurrences
and legal orders; it does not require equality of any comparator outcome. -/
structure LegalTransport (m : RawMolecule) (a b : Cursor) (e : Equiv.Perm (RingSilentPair.Atom m)) where
  left : Nat → List AtomSite
  right : Nat → List AtomSite
  leftLegal : ∀ n, LegalAt m (sitesAt m a n) (left n)
  rightLegal : ∀ n, LegalAt m (sitesAt m b n) (right n)
  carried : ∀ n, List.Forall₂ (fun x y => Carries e x.cursor y.cursor) (left n) (right n)

theorem LegalTransport.no_strict {m a b e} (t : LegalTransport m a b e)
    (mark : RingSilentPair.Atom m) (fix : e mark = mark) : IsEmpty (Strict m a b mark.val) := by
  have words (n : Nat) : word mark.val (t.left n) = word mark.val (t.right n) := by
    have bits := (t.carried n).imp (fun x y h => congrArg Bool.toNat (carried_hit fix h))
    unfold word
    rw [← List.forall₂_eq_eq_eq]
    exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr bits)
  have prefixEq (n : Nat) : sphereWord mark.val t.left n = sphereWord mark.val t.right n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [sphereWord,ih,words]
  have left (n : Nat) : OrdersThrough m a t.left n := fun k _ => (t.leftLegal k).1
  have right (n : Nat) : OrdersThrough m b t.right n := fun k _ => (t.rightLegal k).1
  constructor
  intro d
  cases d with
  | distance d =>
    have impossible := d.strict_words t.left t.right (left _) (right _) [] []
    cases sign : d.leftWins <;> simp [sign,prefixEq] at impossible
  | hierarchy d =>
    have impossible := d.strict_words t.left t.right (left _) (right _)
      (d.sphere.leftAt ▸ t.leftLegal d.offset) (d.sphere.rightAt ▸ t.rightLegal d.offset) [] []
    cases sign : d.leftWins <;> simp [sign,prefixEq] at impossible

/-- This comparison permits the active mark to occur on *both* sides of a
shared ring. Legal source transport rules out either strict distance/hierarchy
witness; marking the complete aligned trees proves the actual equality. -/
theorem overlapping_atMark {m p i j} (pair : Pair m p i j)
    (e : Equiv.Perm (RingSilentPair.Atom m)) (mark : RingSilentPair.Atom m) (fix : e mark = mark)
    (steady : pair.flip = false)
    (incident : mark.val ∈ (occurrenceLigandCursors m pair.focus).map (·.node.atom))
    (trees : CarriedTrees m (EarlierStereoMatch.observe? m p i j .five false pair.left.entries pair.right.entries) e
      (IsotopePriority.budget m+1) ⟨pair.left.node,some pair.focus⟩ ⟨pair.right.node,some pair.focus⟩)
    (spheres : LegalTransport m ⟨pair.left.node,some pair.focus⟩ ⟨pair.right.node,some pair.focus⟩ e) :
    (pair.atMark? mark.val).map (fun c => c.verdict.ordering) = some .eq := by
  have checked := IsotopePriority.treesMatch_complete (trees.marked mark fix)
  simp only [Pair.atMark?,dif_pos steady,dif_pos incident]
  split
  · rename_i d _
    exact False.elim ((spheres.no_strict mark fix).false d)
  · simp [checked,Verdict.ordering]

open ReferenceFrame

/-- Read the promoted sign of a specific input row through the actual table
constructor. Repeated keys use exactly the first lookup on both sides. -/
theorem promoted_lookup {m g p} (rows : List (Row m g p)) (mark : Nat) (table : Table)
    (built : promoted? rows mark = some table) (a b : Nat) :
    table.lookup (a,b) = (rows.find? (fun r => (r.i,r.j) == (a,b))).bind (fun r => r.basis.promoted? mark) := by
  induction rows generalizing table with
  | nil => simp [promoted?] at built; subst table; rfl
  | cons r rs ih =>
    unfold promoted? at built
    rw [List.mapM_cons] at built
    change (do let v ← (do return ((r.i,r.j),← r.basis.promoted? mark))
               let rest ← promoted? rs mark
               pure (v :: rest)) = some table at built
    cases entry : r.basis.promoted? mark with
    | none => simp [entry] at built
    | some signs =>
      cases rest : promoted? rs mark with
      | none => simp [entry,rest] at built
      | some tail =>
        simp [entry,rest] at built
        subst table
        by_cases eqn : (r.i,r.j) = (a,b)
        · simp [List.lookup,eqn,entry]
        · simp [List.lookup,eqn,beq_eq_false_iff_ne.mpr (Ne.symm eqn),ih tail rest]

/-- The exchanged row is present in the actual molecular frame. The active mark
is absent from both trees and fixed by the exchange of molecular atoms. -/
structure Witness {m g p} (f : Frame m g p) (root mark : Nat) where
  a : Nat
  b : Nat
  pair : Pair m p a b
  ordinary : pair.flip = false
  located : pair.focus = f.focus
  incident : mark ∈ (occurrenceLigandCursors m pair.focus).map (·.node.atom)
  armA : a ∈ f.ids
  armB : b ∈ f.ids
  selected : f.rows.find? (fun r => (r.i,r.j) == (a,b)) = some ⟨a,b,.tied pair ordinary⟩
  clearL : Clear m mark ⟨pair.left.node,some pair.focus⟩
  clearR : Clear m mark ⟨pair.right.node,some pair.focus⟩
  empty : pair.left.entries = [] ∧ pair.right.entries = []
  atRoot : f.focus.atom = root
  idroot : root < m.atomCount
  idmark : mark < m.atomCount
  exchange : Equiv.Perm (RingSilentPair.Atom m)
  preserved : (∀ x, m.atoms.get (exchange x) = m.atoms.get x) ∧ exchange ∈ m.toMoleculeGraph.Aut
  fixes : (exchange ⟨root,idroot⟩).val = root ∧ (exchange ⟨mark,idmark⟩).val = mark
  swaps : ∀ x : RingSilentPair.Atom m, x.val ∈ f.ids →
    (exchange x).val = LocalizedMarkedTerminalGaugeSwap.swapAtom a b x.val


/-- Every real copy, including the atom named by a ring-closure copy, keeps
the active reference bit under this same molecular exchange. -/
theorem Witness.marker_preserved {m g p f root k} (w : @Witness m g p f root k)
    (x : RingSilentPair.Atom m) :
    ((w.exchange x).val == k) = (x.val == k) := by
  have fixed : w.exchange (⟨k,w.idmark⟩ : RingSilentPair.Atom m) = ⟨k,w.idmark⟩ := Fin.ext w.fixes.2
  have eqn : (w.exchange x).val = k ↔ x.val = k := by
    change (w.exchange x).val = (⟨k,w.idmark⟩ : RingSilentPair.Atom m).val ↔ _
    rw [← Fin.ext_iff,← fixed,w.exchange.injective.eq_iff]
    exact Fin.ext_iff
  by_cases h : x.val = k <;> simp [h,eqn]

theorem Witness.hand_exchange {m g p f root k} (w : @Witness m g p f root k)
    (geometry : Geometry) {order : List Nat} (all : order.Perm f.ids) :
    readback? geometry (order.map (LocalizedMarkedTerminalGaugeSwap.swapAtom w.a w.b)) =
      (readback? geometry order).map RS.swap :=
  LocalizedMarkedTerminalGaugeSwap.readback_swapAtom geometry _ _ w.pair.distinct order
    (all.nodup_iff.mpr f.distinct) (all.length_eq.trans f.four)
    (all.mem_iff.mpr w.armA) (all.mem_iff.mpr w.armB)

theorem Witness.signs {m g p f root} (t : @Trial m g p f) (w : Witness f root t.mark) :
    ∀ rev, orderAt t.table rev w.a w.b = some .eq ∧ orderAt t.table rev w.b w.a = some .eq := by
  obtain ⟨answer,read,sign⟩ := Option.map_eq_some_iff.mp (pair_atMark_equal w.pair t.mark w.ordinary w.incident w.clearL w.clearR)
  have stored := promoted_lookup f.rows t.mark t.table t.derived w.a w.b
  simp [w.selected,Basis.promoted?,read,sign] at stored
  intro rev
  have fwd : orderAt t.table rev w.a w.b = some .eq := by
    simp [orderAt,w.pair.distinct,stored]
  have row := List.all_eq_true.mp (t.consistent rev) w.a w.armA
  have cell := List.all_eq_true.mp row w.b w.armB
  have back : orderAt t.table rev w.b w.a = (orderAt t.table rev w.a w.b).map Ordering.swap :=
    eq_of_beq (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp cell).1).2
  exact ⟨fwd,by simp [back,fwd]⟩

private theorem compared {a b : Nat} {xs : List Nat} {R : Nat → Nat → Prop}
    (distinct : a ≠ b) (ordered : xs.Pairwise R) (ha : a ∈ xs) (hb : b ∈ xs) : R a b ∨ R b a := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp ha with rfl | hl
    · exact Or.inl (head _ ((List.mem_cons.mp hb).resolve_left distinct.symm))
    · rcases List.mem_cons.mp hb with rfl | hr
      · exact Or.inr (head _ hl)
      · exact ih tail hl hr

theorem Witness.trial_refusal {m g p f root} (t : @Trial m g p f) (w : Witness f root t.mark) :
    t.outcome.reading? = none := by
  cases out : t.outcome with
  | tied => rfl
  | assigned actual reflected left right reading geom =>
    have listed : actual ∈ orders f.ids t.table false := by simp [left]
    obtain ⟨perm,strict⟩ := List.mem_filter.mp listed
    have hp := List.mem_permutations'.mp perm
    have eqn := w.signs t false
    have cant := compared w.pair.distinct (of_decide_eq_true strict)
      (hp.mem_iff.mpr w.armA) (hp.mem_iff.mpr w.armB)
    rcases cant with yes | no
    · rw [eqn.1] at yes; contradiction
    · rw [eqn.2] at no; contradiction

/-- A separate real molecular exchange can witness each possible reference.
Every trial at either geometry retains a demonstrated equality. -/
theorem all_mark_refusal {m g p} (pop : Population m g p) (root : Nat)
    (w : ∀ t ∈ pop.trials, Nonempty (Witness pop.frame root t.mark)) :
    pop.consensus? = some none := by
  apply (pop.consensus_iff _).mpr
  intro t mem
  obtain ⟨witness⟩ := w t mem
  exact witness.trial_refusal t


private def emptyArm? (m : RawMolecule) (q : List Nat) : Option (Arm m q) := do
  let ⟨c,h⟩ ← (occurrence? m q).attach
  if clear : carbonSites m (m.atomCount+1) c = some [] then
    return ⟨c,h,[],clear,by simp⟩
  none

private def basis? (m : RawMolecule) (g : Geometry) (i d a b : Nat) : Option (Basis m g [i] a b) := do
  let ⟨l,hl⟩ ← (ligandRows? m [i] a d).attach
  let ⟨r,hr⟩ ← (ligandRows? m [i] b d).attach
  if high : r < l then return .atomic d l r hl hr true high
  if low : l < r then return .atomic d l r hl hr false low
  let matched ← pairWith? [i] a b (emptyArm? m)
  if steady : matched.flip = false then return .tied matched steady
  none

/-- Every ordinary comparison is an actual strict Rule 1a witness or a
complete earlier-rule correspondence with an independently empty signed inventory. -/
def population? (m : RawMolecule) (g : Geometry) (i d : Nat) : Option (Population m g [i]) := do
  let ⟨n,root⟩ ← (occurrence? m [i]).attach
  let ids := (occurrenceLigandCursors m n).map (·.node.atom)
  let edges := Promotion.TwoPairPriority.directedPairs ids id
  if h : (m.atoms[n.atom]?).any (fun a => a.element == .C) = true ∧ ids.length = 4 ∧ ids.Nodup then
    let rows ← edges.mapM fun (a,b) => do return (⟨a,b,← basis? m g i d a b⟩ : Row m g [i])
    if complete : rows.map (fun r => (r.i,r.j)) = edges then
      if consistent : ∀ rev, coherent ids (entries rows) rev = true then
        let frame : MolecularFrame m g [i] := ⟨n,root,h.1,ids,rfl,h.2.1,h.2.2,rows,complete,consistent⟩
        return ← (← frame.promotion?).population?
  none

abbrev Hint := RingSharedArmRefusal.Hint

def witness? {m g root} (f : Frame m g [root]) (k : Nat) (hint : Hint) : Option (Witness f root k) := do
  let pred := fun r : Row m g [root] => (r.i,r.j) == (hint.left,hint.right)
  let ⟨row,found⟩ ← (f.rows.find? pred).attach
  match row, found with
  | ⟨a,b,.tied pair ordinary⟩,found =>
    have addr : (a,b) = (hint.left,hint.right) := eq_of_beq (List.find?_some (p:=pred) found)
    have selected : f.rows.find? (fun r => (r.i,r.j) == (a,b)) = some ⟨a,b,.tied pair ordinary⟩ := by
      rw [addr]; exact found
    if data : pair.focus = f.focus ∧ k ∈ (occurrenceLigandCursors m pair.focus).map (·.node.atom) ∧ a ∈ f.ids ∧
        b ∈ f.ids ∧ pair.left.entries = [] ∧ pair.right.entries = [] ∧ f.focus.atom = root ∧ root < m.atomCount ∧ k < m.atomCount then
      let e := RingSharedArmRefusal.permutation m hint.swaps
      let n := IsotopePriority.budget m+1
      if away : clearAt m k n ⟨pair.left.node,some pair.focus⟩ = true ∧ clearAt m k n ⟨pair.right.node,some pair.focus⟩ = true then
        let aRoot : RingSilentPair.Atom m := ⟨root,data.2.2.2.2.2.2.2.1⟩
        let mark : RingSilentPair.Atom m := ⟨k,data.2.2.2.2.2.2.2.2⟩
        if exchange : (∀ x, m.atoms.get (e x) = m.atoms.get x) ∧
            (∀ x, m.toMoleculeGraph.atomMass (e x) = m.toMoleculeGraph.atomMass x) ∧
            (∀ x y, m.toMoleculeGraph.bond (e x) (e y) = m.toMoleculeGraph.bond x y) ∧
            (e aRoot).val = root ∧ (e mark).val = k ∧
            (∀ x : RingSilentPair.Atom m, x.val ∈ f.ids → (e x).val = LocalizedMarkedTerminalGaugeSwap.swapAtom a b x.val) then
          have aut : e ∈ m.toMoleculeGraph.Aut :=
            ⟨fun x => congrArg (fun s : AtomSpec => s.element.atomicNumber) (exchange.1 x),exchange.2.1,
             fun x => congrArg AtomSpec.charge (exchange.1 x),exchange.2.2.1⟩
          return ⟨a,b,pair,ordinary,data.1,data.2.1,data.2.2.1,data.2.2.2.1,selected,clearAt_sound away.1,clearAt_sound away.2,
            ⟨data.2.2.2.2.1,data.2.2.2.2.2.1⟩,data.2.2.2.2.2.2.1,aRoot.isLt,mark.isLt,e,⟨exchange.1,aut⟩,
            ⟨exchange.2.2.2.1,exchange.2.2.2.2.1⟩,exchange.2.2.2.2.2⟩
    none
  | _,_ => none

/-- All actual carbon occurrences other than the trial root have independent
valence or equivalent-terminal-pair proofs. Every raw atom, including a root
copy in a ring closure, is verified untagged for the production reader. -/
def Silent (m : RawMolecule) (root : Nat) : Prop :=
  (∀ x : RingSilentPair.Atom m, x.val ≠ root → RingSharedArmRefusal.Inactive m x.val) ∧
  (∀ x : RingSilentPair.Atom m, (m.atomAt? x.val).any (fun s => s.tetrahedral?.isNone) = true)

instance {m root} : Decidable (Silent m root) := by unfold Silent; infer_instance

structure Certificate (i : LocalizedChemicalRing.Input) (d root : Nat) where
  pop : Population i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [root]
  computed : population? i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) root d = some pop
  ordinary : RingSharedArmRefusal.ValidSigns i.certified root pop.frame.ids (entries pop.frame.rows)
  silent : Silent i.molecule root
  allMarks : ∀ t ∈ pop.trials, Nonempty (Witness pop.frame root t.mark)

private def checkWith? (i : LocalizedChemicalRing.Input) (d root : Nat)
    (select : (f : Frame i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) [root]) →
      (k : Nat) → Option (Witness f root k)) : Option (Certificate i d root) := do
  let ⟨pop,built⟩ ← (population? i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) root d).attach
  if sound : Silent i.molecule root ∧ RingSharedArmRefusal.ValidSigns i.certified root pop.frame.ids (entries pop.frame.rows) then
    if each : ∀ t ∈ pop.trials, (select pop.frame t.mark).isSome = true then
      return ⟨pop,built,sound.2,sound.1,fun t mem => ⟨(select pop.frame t.mark).get (each t mem)⟩⟩
  none

/-- Supply optional explicit exchanges independently for each possible mark.
All molecular checks and the promoted comparisons remain in the verifier. -/
def check? (i : LocalizedChemicalRing.Input) (d root : Nat) (hint : Nat → Hint) : Option (Certificate i d root) :=
  checkWith? i d root (fun f k => witness? f k (hint k))

private def pendants (m : RawMolecule) (a : Nat) :=
  (List.range m.atomCount).filter fun b => m.writtenNeighbors b == [a]

/-- Try exchanging two incident atoms and matching their terminal substituents.
The two arms can rejoin elsewhere in the ring. Shared atoms remain fixed. A
complete check of the proposed permutation screens every atom and bond. -/
def discoverWitness? {m g root} (f : Frame m g [root]) (k : Nat) : Option (Witness f root k) :=
  f.ids.findSome? fun a => f.ids.findSome? fun b => do
    guard (a < b && a != k && b != k && m.atoms[a]? == m.atoms[b]?)
    let left := pendants m a
    let right := pendants m b
    guard (left.length == right.length)
    witness? f k ⟨a,b,(a,b) :: left.zip right⟩

/-- Automatically find and independently check a surviving exchange for each
legal reference. A missing witness for any trial leaves the root unresolved. -/
def discover? (i : LocalizedChemicalRing.Input) (d root : Nat) : Option (Certificate i d root) :=
  checkWith? i d root discoverWitness?

theorem Certificate.refusal {i d root} (c : Certificate i d root) : c.pop.consensus? = some none :=
  all_mark_refusal c.pop root c.allMarks

theorem Certificate.no_publication {i d root} (c : Certificate i d root) (v : RawMolecule.CanonicalBranchNode)
    (source : v.atom < i.molecule.atomCount) (fuel : Nat) (state : OccurrenceAuxState) :
    occurrenceFact? i.molecule fuel state v = none := by
  obtain ⟨atom,read,untagged⟩ := (Option.any_eq_true _ _).mp (c.silent.2 ⟨v.atom,source⟩)
  exact occurrenceFact?_eq_none_of_tetrahedral?_eq_none _ fuel state v atom read (Option.isNone_iff_eq_none.mp untagged)

end TetraStereo.Engine.RingMarkedSilentRefusal
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.clearAt_sound
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.matched_with_mark
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.no_strict
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.pair_atMark_equal

assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.Witness.signs
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.all_mark_refusal

assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.Certificate.refusal
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.Certificate.no_publication

assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.Witness.marker_preserved
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.Witness.hand_exchange

assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.CarriedTrees.marked
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.LegalTransport.no_strict
assert_kernel_only TetraStereo.Engine.RingMarkedSilentRefusal.overlapping_atMark
