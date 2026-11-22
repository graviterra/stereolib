import TetraStereo.Engine.RingAuxiliaryInventory

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceDistance
open OneCenter CertifiedLocalizedCIPInput Recursive Certificate.CanonicalSphereKey

/-- A distinct occurrence in the retained digraph, with its walk from
the proximal ligand. A ring duplicate is included once and has no children. -/
structure AtomSite where
  cursor : CanonicalRerootCursor
  route : List RawMolecule.CanonicalBranchNode
  deriving DecidableEq

def AtomSite.step (s : AtomSite) (c : CanonicalRerootCursor) : AtomSite :=
  ⟨c,s.route ++ [c.node]⟩

def shell (m : RawMolecule) : Nat → AtomSite → List AtomSite
  | 0,s => [s]
  | k+1,s => (s.cursor.children m).flatMap fun c => shell m k (s.step c)

def sitesAt (m : RawMolecule) (c : CanonicalRerootCursor) (k : Nat) :=
  shell m k ⟨c,[c.node]⟩

/-- A walk uses the retained cursor's own children at every step. -/
inductive Walk (m : RawMolecule) : AtomSite → Nat → AtomSite → Prop where
  | here (s) : Walk m s 0 s
  | next {s c k t} (edge : c ∈ s.cursor.children m) (later : Walk m (s.step c) k t) :
      Walk m s (k+1) t

theorem mem_shell_iff {m k s t} : t ∈ shell m k s ↔ Walk m s k t := by
  induction k generalizing s with
  | zero =>
    constructor
    · intro h; obtain rfl := List.mem_singleton.mp h; exact .here _
    · intro h; cases h; simp [shell]
  | succ k ih =>
    constructor
    · intro h
      obtain ⟨c,edge,member⟩ := List.mem_flatMap.mp h
      exact .next edge (ih.mp member)
    · intro h
      cases h with
      | next edge rest => exact List.mem_flatMap.mpr ⟨_,edge,ih.mpr rest⟩

private theorem sum_flat_map {α : Type} (xs : List α) (f : α → List Nat) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs <;> simp_all

/-- Any cursor observation preserved by a full correspondence has the same
total on each pair of matched spheres, independently of sibling order. -/
theorem matched_shell_sum {ω : Type} {m : RawMolecule} {obs : CanonicalRerootCursor → Option ω}
    {d : Nat} {a b : CanonicalRerootCursor} (matched : IsotopePriority.TreesMatch m obs d a b)
    (weight : CanonicalRerootCursor → Nat)
    (congruent : ∀ x y o, obs x = some o → obs y = some o → weight x = weight y)
    (k : Nat) (l r : List RawMolecule.CanonicalBranchNode) :
    ((shell m k ⟨a,l⟩).map (fun s => weight s.cursor)).sum =
      ((shell m k ⟨b,r⟩).map (fun s => weight s.cursor)).sum := by
  induction d generalizing a b k l r with
  | zero => contradiction
  | succ d ih =>
    obtain ⟨o,x,y,ordered,perm,pairs⟩ := matched
    cases k with
    | zero => simpa [shell] using congruent a b o x y
    | succ k =>
      let f (path : List RawMolecule.CanonicalBranchNode) (c : CanonicalRerootCursor) :=
        ((shell m k ⟨c,path ++ [c.node]⟩).map (fun s => weight s.cursor)).sum
      have heads : List.Forall₂ (fun x y => f l x = f r y) (a.children m) ordered :=
        pairs.imp fun x y h => ih h k _ _
      have aligned : (a.children m).map (f l) = ordered.map (f r) := by
        have eqs : List.Forall₂ (· = ·) ((a.children m).map (f l)) (ordered.map (f r)) :=
          List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr heads)
        simpa only [List.forall₂_eq_eq_eq] using eqs
      have sums := (congrArg List.sum aligned).trans (perm.map (f r)).sum_eq
      simpa [shell,AtomSite.step,List.map_flatMap,sum_flat_map,Function.comp_def,f] using sums

theorem matched_widths {ω : Type} {m : RawMolecule} {obs : CanonicalRerootCursor → Option ω}
    {d a b} (matched : IsotopePriority.TreesMatch m obs d a b) (k : Nat) :
    (sitesAt m a k).length = (sitesAt m b k).length := by
  simpa [sitesAt] using matched_shell_sum matched (fun _ => 1) (by simp) k [a.node] [b.node]

def hits (mark : Nat) (s : AtomSite) := s.cursor.node.atom == mark

def word (mark : Nat) (sites : List AtomSite) := sites.map fun s => (hits mark s).toNat

/-- The first k complete spheres in any chosen order within each sphere. -/
def sphereWord (mark : Nat) (rows : Nat → List AtomSite) : Nat → List Nat
  | 0 => []
  | k+1 => sphereWord mark rows k ++ word mark (rows k)

def OrdersThrough (m : RawMolecule) (c : CanonicalRerootCursor) (rows : Nat → List AtomSite) (k : Nat) :=
  ∀ j < k, (sitesAt m c j).Perm (rows j)

structure Sphere (m : RawMolecule) (a b : CanonicalRerootCursor) (k : Nat) where
  left : List AtomSite
  right : List AtomSite
  leftAt : sitesAt m a k = left
  rightAt : sitesAt m b k = right
  width : left.length = right.length

abbrev emptyOf (mark : Nat) (ss : List AtomSite) := ss.any (hits mark) = false

def Earlier (m : RawMolecule) (a b : CanonicalRerootCursor) (mark k : Nat) : Prop :=
  ∀ j < k, ∃ s : Sphere m a b j, emptyOf mark s.left ∧ emptyOf mark s.right

/-- The first marked sphere, a particular occurrence of the chosen atom on
the winning side and the complete unmarked opposite sphere. -/
structure Difference (m : RawMolecule) (a b : CanonicalRerootCursor) (mark : Nat) where
  offset : Nat
  earlier : Earlier m a b mark offset
  sphere : Sphere m a b offset
  leftWins : Bool
  occurrence : AtomSite
  marked : hits mark occurrence = true
  member : occurrence ∈ (if leftWins then sphere.left else sphere.right)
  absent : emptyOf mark (if leftWins then sphere.right else sphere.left)

private theorem empty_word {mark ss} (empty : emptyOf mark ss) :
    word mark ss = List.replicate ss.length 0 := by
  induction ss with
  | nil => rfl
  | cons x xs ih =>
    have no := List.any_eq_false.mp empty
    simp [word,List.replicate_succ,no x (by simp)]
    exact ih (List.any_eq_false.mpr (fun a h => no a (List.mem_cons_of_mem _ h)))

private theorem zero_lt {mark} (ss : List AtomSite) (present : ∃ s ∈ ss, hits mark s = true) :
    List.replicate ss.length 0 < word mark ss := by
  induction ss with
  | nil => simp at present
  | cons x xs ih =>
    change List.replicate (xs.length+1) 0 < (hits mark x).toNat :: word mark xs
    rw [List.replicate_succ]
    by_cases h : hits mark x = true
    · exact List.cons_lt_cons_iff.mpr (.inl (by simp [h]))
    · apply List.cons_lt_cons_iff.mpr
      refine .inr ⟨by simp [Bool.eq_false_iff.mpr h],ih ?_⟩
      obtain ⟨s,hs,yes⟩ := present
      rcases List.mem_cons.mp hs with rfl | below
      · contradiction
      · exact ⟨s,below,yes⟩

private theorem empty_perm {mark l r} (h : l.Perm r) (empty : emptyOf mark l) : emptyOf mark r :=
  List.any_eq_false.mpr (fun x hx => List.any_eq_false.mp empty x (h.mem_iff.mpr hx))

private theorem earlier_words {m a b mark k x y}
    (prior : Earlier m a b mark k) (left : OrdersThrough m a x k) (right : OrdersThrough m b y k) :
    sphereWord mark x k = sphereWord mark y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨s,le,re⟩ := prior k (by omega)
    have lp := s.leftAt ▸ left k (by omega)
    have rp := s.rightAt ▸ right k (by omega)
    have prev := ih (fun j h => prior j (by omega)) (fun j h => left j (by omega))
      (fun j h => right j (by omega))
    simp only [sphereWord,prev,empty_word (empty_perm lp le),empty_word (empty_perm rp re),
      ← lp.length_eq,← rp.length_eq,s.width]

private theorem common_prefix (p : List Nat) {l r : List Nat} (h : l < r) : p ++ l < p ++ r := by
  induction p with
  | nil => exact h
  | cons a _ ih => exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,ih⟩)

private theorem strict_word {mark} {l r x y : List AtomSite} (lp : l.Perm x) (rp : r.Perm y) (width : l.length = r.length)
    (found : ∃ s ∈ l, hits mark s = true) (absent : emptyOf mark r) (tailX tailY : List Nat) :
    word mark y ++ tailY < word mark x ++ tailX := by
  obtain ⟨s,member,yes⟩ := found
  have size : y.length = x.length := rp.length_eq.symm.trans (width.symm.trans lp.length_eq)
  apply Hierarchy.append_strict (by simpa [word] using size)
  rw [empty_word (empty_perm rp absent),size]
  exact zero_lt x ⟨s,lp.mem_iff.mp member,yes⟩

/-- Every within-sphere order gives the same strict sign, for arbitrary
later observations. In particular this holds for every order permitted by
all preceding molecular parent and sibling priorities. -/
theorem Difference.strict_words {m a b mark} (d : Difference m a b mark)
    (x y : Nat → List AtomSite) (left : OrdersThrough m a x (d.offset+1))
    (right : OrdersThrough m b y (d.offset+1)) (tailX tailY : List Nat) :
    let l := sphereWord mark x (d.offset+1) ++ tailX
    let r := sphereWord mark y (d.offset+1) ++ tailY
    if d.leftWins then r < l else l < r := by
  have prev := earlier_words d.earlier (fun j h => left j (by omega)) (fun j h => right j (by omega))
  have lp := d.sphere.leftAt ▸ left d.offset (by omega)
  have rp := d.sphere.rightAt ▸ right d.offset (by omega)
  have member := d.member
  have absent := d.absent
  simp only [sphereWord,List.append_assoc,prev]
  cases side : d.leftWins <;> simp only [side,Bool.false_eq_true,if_false,if_true] at member absent ⊢
  · exact common_prefix _ (strict_word rp lp d.sphere.width.symm ⟨_,member,d.marked⟩ absent tailY tailX)
  · exact common_prefix _ (strict_word lp rp d.sphere.width ⟨_,member,d.marked⟩ absent tailX tailY)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- First unequal occurrences, including their common immediate predecessor.
All steps after the split are immaterial to the parent priority. -/
def routeSplit (parent : Option Node) : List Node → List Node → Option (Option Node × Node × Node)
  | a :: as,b :: bs => if a = b then routeSplit (some a) as bs else some (parent,a,b)
  | _,_ => none

theorem routeSplit_self (p : Option Node) (xs : List Node) : routeSplit p xs xs = none := by
  induction xs generalizing p <;> simp_all [routeSplit]

theorem routeSplit_siblings (common : List Node) (parent a b : Node) (as bs : List Node)
    (different : a ≠ b) (prior : Option Node) :
    routeSplit prior (common ++ parent :: a :: as) (common ++ parent :: b :: bs) = some (some parent,a,b) := by
  induction common generalizing prior <;> simp_all [routeSplit]

/-- Both divergent occurrences are incident to the stated molecular parent.
Follow the retained cursor away from that parent, including on an inward
step of the original digraph, and certify the complete Rule 1a ordering. -/
structure RootedPriority (m : RawMolecule) (p a b : Node) where
  reached : occurrence? m p.history.reverse = some p
  incident : ⟨a,some p⟩ ∈ occurrenceLigandCursors m p ∧ ⟨b,some p⟩ ∈ occurrenceLigandCursors m p
  complete : SiblingConstitution.exhausted m (IsotopePriority.budget m) ⟨a,some p⟩ = true ∧
    SiblingConstitution.exhausted m (IsotopePriority.budget m) ⟨b,some p⟩ = true
  left : HTree Nat
  right : HTree Nat
  leftAt : atomicTree m 3 (IsotopePriority.budget m) ⟨a,some p⟩ = some left
  rightAt : atomicTree m 3 (IsotopePriority.budget m) ⟨b,some p⟩ = some right

def RootedPriority.depth {m p a b} (c : RootedPriority m p a b) :=
  max (SiblingConstitution.height c.left) (SiblingConstitution.height c.right)

def RootedPriority.ordering {m p a b} (c : RootedPriority m p a b) :=
  LocalizedPhysicalMarkedSparseMarker.compareMarker (SiblingConstitution.key 3 c.depth c.left)
    (SiblingConstitution.key 3 c.depth c.right)

theorem RootedPriority.first_difference {m p a b} (c : RootedPriority m p a b) :
    c.ordering = .gt ↔ ∃ k slot,
      Certificate.CanonicalSphereKey.observation 3 c.depth c.right k slot <
        Certificate.CanonicalSphereKey.observation 3 c.depth c.left k slot ∧
      (∀ j < k, ∀ s, Certificate.CanonicalSphereKey.observation 3 c.depth c.right j s =
        Certificate.CanonicalSphereKey.observation 3 c.depth c.left j s) ∧
      (∀ s < slot, Certificate.CanonicalSphereKey.observation 3 c.depth c.right k s =
        Certificate.CanonicalSphereKey.observation 3 c.depth c.left k s) := by
  rw [RootedPriority.ordering,SiblingConstitution.compare_gt_iff]
  exact Certificate.CanonicalSphereKey.ckey_lt_iff_first_difference _ _ _ _

def rootedPriority? (m : RawMolecule) (p a b : Node) : Option (RootedPriority m p a b) := do
  if reached : occurrence? m p.history.reverse = some p then
    let l : CanonicalRerootCursor := ⟨a,some p⟩
    let r : CanonicalRerootCursor := ⟨b,some p⟩
    if edge : l ∈ occurrenceLigandCursors m p ∧ r ∈ occurrenceLigandCursors m p then
      if complete : SiblingConstitution.exhausted m (IsotopePriority.budget m) l = true ∧
          SiblingConstitution.exhausted m (IsotopePriority.budget m) r = true then
        let ⟨lt,lh⟩ ← (atomicTree m 3 (IsotopePriority.budget m) l).attach
        let ⟨rt,rh⟩ ← (atomicTree m 3 (IsotopePriority.budget m) r).attach
        return ⟨reached,edge,complete,lt,rt,lh,rh⟩
  none

/-- A shorter molecular order test suffices when nuclear charges differ.
With equal charges, full constitutional priority at the original split
comes before any comparison involving the chosen reference atom. -/
def routeBefore (m : RawMolecule) (xs ys : List Node) : Bool :=
  match routeSplit none xs ys with
  | some (parent,x,y) =>
    let zx := (m.atoms[x.atom]?).map (·.element.atomicNumber)
    let zy := (m.atoms[y.atom]?).map (·.element.atomicNumber)
    match zx, zy with
    | some lx,some ry => if lx != ry then lx > ry else
      parent.any fun p => (rootedPriority? m p x y).any (fun c => c.ordering == .gt)
    | _,_ => false
  | none => false

def Before (m : RawMolecule) (a b : AtomSite) := routeBefore m a.route b.route = true

theorem routeBefore_self (m : RawMolecule) (xs : List Node) : routeBefore m xs xs = false := by
  simp [routeBefore,routeSplit_self]

theorem routeBefore_of_rooted {m p x y} (common xs ys : List Node)
    (different : x ≠ y) (c : RootedPriority m p x y) (found : rootedPriority? m p x y = some c)
    {z : Nat} (left : (m.atoms[x.atom]?).map (·.element.atomicNumber) = some z)
    (right : (m.atoms[y.atom]?).map (·.element.atomicNumber) = some z) (strict : c.ordering = .gt) :
    routeBefore m (common ++ p :: x :: xs) (common ++ p :: y :: ys) = true := by
  simp [routeBefore,routeSplit_siblings _ _ _ _ _ _ different,left,right,found,strict]

def LegalAt (m : RawMolecule) (ss order : List AtomSite) :=
  ss.Perm order ∧ order.Pairwise fun a b => ¬ Before m b a

structure Blocks (m : RawMolecule) (ss : List AtomSite) where
  rows : List (List AtomSite)
  complete : rows.flatten.Perm ss
  separated : rows.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, Before m a b)
  witness : List AtomSite
  legal : LegalAt m ss witness

def Blocks.bits {m ss} (b : Blocks m ss) (k : Nat) := b.rows.map (List.map (hits k))

private def blocks? (m : RawMolecule) (ss : List AtomSite) (depth : Nat)
    (rooted : Bool) : Option (Blocks m ss) := do
  -- Counts propose a partition of the shell. The separate all-pairs check
  -- establishes the actual molecular priority across each block boundary.
  let key (s : AtomSite) := if rooted then
    [(ss.countP fun t => routeBefore m (s.route.take depth) (t.route.take depth))]
    else (s.route.take depth).map fun n => ((m.atoms[n.atom]?).map (·.element.atomicNumber)).getD 0
  let scored := ss.map fun s => (s,key s)
  let keys := ((scored.map Prod.snd).eraseDups).insertionSort (fun a b => b ≤ a)
  let groups : List (List AtomSite) := keys.map fun k => (scored.filter (fun p => p.2 == k)).map Prod.fst
  let witness := ss.insertionSort fun (a b : AtomSite) => !(routeBefore m b.route a.route)
  if legal : witness.Pairwise (fun (a b : AtomSite) => routeBefore m b.route a.route ≠ true) then
    if complete : groups.flatten.Perm ss then
      if valid : groups.Pairwise (fun (l r : List AtomSite) => ∀ a ∈ l, ∀ b ∈ r,
          routeBefore m a.route b.route = true) then
        return ⟨groups,complete,valid,witness,⟨(List.perm_insertionSort _ _).symm,legal⟩⟩
  none

private theorem Blocks.words {m ss} (b : Blocks m ss) (k : Nat) {order} (legal : LegalAt m ss order) :
    ∃ rows, List.Forall₂ List.Perm (b.bits k) rows ∧ (PairSpheres.ranks rows).flatten = word k order := by
  obtain ⟨parts,perms,flat⟩ := Hierarchy.split_linearization (Before m)
    (by intro a; simp [Before,routeBefore_self]) b.rows order b.separated
    (b.complete.trans legal.1) legal.2
  refine ⟨parts.map (List.map (hits k)),List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
    (perms.imp fun _ _ h => h.map _)),?_⟩
  simp [PairSpheres.ranks,word,← flat,List.map_flatten,List.map_map,Function.comp_def]

structure RankedDifference (m : RawMolecule) (a b : CanonicalRerootCursor) (mark : Nat) where
  offset : Nat
  earlier : Earlier m a b mark offset
  sphere : Sphere m a b offset
  left : Blocks m sphere.left
  right : Blocks m sphere.right
  leftWins : Bool
  checked : PairSpheres.seniorLeft? (left.bits mark) (right.bits mark) = some leftWins
  index : Nat
  leftSite : AtomSite
  rightSite : AtomSite
  leftSiteAt : left.witness[index]? = some leftSite
  rightSiteAt : right.witness[index]? = some rightSite
  before : word mark (left.witness.take index) = word mark (right.witness.take index)
  decisive : hits mark leftSite = leftWins ∧ hits mark rightSite = !leftWins

theorem RankedDifference.strict_words {m a b mark} (d : RankedDifference m a b mark)
    (x y : Nat → List AtomSite) (left : OrdersThrough m a x (d.offset+1))
    (right : OrdersThrough m b y (d.offset+1))
    (lx : LegalAt m d.sphere.left (x d.offset)) (ry : LegalAt m d.sphere.right (y d.offset))
    (tailX tailY : List Nat) :
    let l := sphereWord mark x (d.offset+1) ++ tailX
    let r := sphereWord mark y (d.offset+1) ++ tailY
    if d.leftWins then r < l else l < r := by
  obtain ⟨ls,lp,lw⟩ := d.left.words mark lx
  obtain ⟨rs,rp,rwds⟩ := d.right.words mark ry
  have h := PairSpheres.seniorLeft_sound d.checked lp rp
  have shape : (d.left.bits mark).map List.length = (d.right.bits mark).map List.length := by
    by_contra diff
    have check := d.checked
    simp [PairSpheres.seniorLeft?,diff] at check
  have widths {u v : List (List Bool)} (h : List.Forall₂ List.Perm u v) :
      u.map List.length = v.map List.length := by
    induction h with
    | nil => rfl
    | cons p _ ih => exact congrArg₂ List.cons p.length_eq ih
  have lens : (PairSpheres.ranks ls).map List.length = (PairSpheres.ranks rs).map List.length := by
    simpa [PairSpheres.ranks,List.map_map,Function.comp_def] using
      (widths lp).symm.trans (shape.trans (widths rp))
  have sameWidth : (word mark (x d.offset)).length = (word mark (y d.offset)).length := by
    simpa [word] using lx.1.length_eq.symm.trans (d.sphere.width.trans ry.1.length_eq)
  have prev := earlier_words d.earlier (fun j hj => left j (by omega)) (fun j hj => right j (by omega))
  simp only [sphereWord,List.append_assoc,prev]
  cases side : d.leftWins <;> simp only [side,Bool.false_eq_true,if_false,if_true] at h ⊢
  · apply common_prefix _ (Hierarchy.append_strict sameWidth _ tailX tailY)
    rw [← lw,← rwds]
    exact Hierarchy.flatten_strict lens h
  · apply common_prefix _ (Hierarchy.append_strict sameWidth.symm _ tailY tailX)
    rw [← lw,← rwds]
    exact Hierarchy.flatten_strict lens.symm h

inductive Strict (m : RawMolecule) (a b : CanonicalRerootCursor) (mark : Nat) where
  | distance (d : Difference m a b mark)
  | hierarchy (d : RankedDifference m a b mark)

private def ranked? {m a b k mark} (earlier : Earlier m a b mark k) (s : Sphere m a b k) :
    Option (RankedDifference m a b mark) := do
  [false,true].findSome? fun rooted => (List.range (k+2)).reverse.findSome? fun depth => do
    let l ← blocks? m s.left depth rooted
    let r ← blocks? m s.right depth rooted
    let ⟨wins,checked⟩ ← (PairSpheres.seniorLeft? (l.bits mark) (r.bits mark)).attach
    let idx ← (List.range l.witness.length).find? fun j =>
      l.witness[j]?.map (hits mark) != r.witness[j]?.map (hits mark)
    let ⟨x,hx⟩ ← l.witness[idx]?.attach
    let ⟨y,hy⟩ ← r.witness[idx]?.attach
    if first : word mark (l.witness.take idx) = word mark (r.witness.take idx) then
      if decisive : hits mark x = wins ∧ hits mark y = !wins then
        return ⟨k,earlier,s,l,r,wins,checked,idx,x,y,hx,hy,first,decisive⟩
    none

private def search (m : RawMolecule) (a b : CanonicalRerootCursor) (mark : Nat)
    (widths : ∀ k, (sitesAt m a k).length = (sitesAt m b k).length) :
    Nat → (k : Nat) → Earlier m a b mark k → Option (Strict m a b mark)
  | 0,_,_ => none
  | fuel+1,k,earlier => do
    let ls := sitesAt m a k
    let rs := sitesAt m b k
    let sphere : Sphere m a b k := ⟨ls,rs,rfl,rfl,widths k⟩
    if l : emptyOf mark ls then
      if r : emptyOf mark rs then
        if ls.isEmpty then return ← none
        return ← search m a b mark widths fuel (k+1) (fun j hj => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with prev | rfl
          · exact earlier j prev
          · exact ⟨sphere,l,r⟩)
      let ⟨s,h⟩ ← (rs.find? (hits mark)).attach
      return .distance ⟨k,earlier,sphere,false,s,List.find?_some h,List.mem_of_find?_eq_some h,l⟩
    if r : emptyOf mark rs then
      let ⟨s,h⟩ ← (ls.find? (hits mark)).attach
      return .distance ⟨k,earlier,sphere,true,s,List.find?_some h,List.mem_of_find?_eq_some h,r⟩
    return .hierarchy (← ranked? earlier sphere)

def difference? {ω : Type} {m : RawMolecule} {obs : CanonicalRerootCursor → Option ω}
    {d a b} (matched : IsotopePriority.TreesMatch m obs d a b) (mark : Nat) :=
  search m a b mark (matched_widths matched) (IsotopePriority.budget m+1) 0 (by intro j h; omega)

/-- Keep every earlier observation unchanged and add the same active atom
to both retained trees. Ring duplicates carry the index of the copied atom. -/
def withMark {ω : Type} (observe : CanonicalRerootCursor → Option ω) (mark : Nat)
    (c : CanonicalRerootCursor) : Option (ω × Bool) := do
  return (← observe c,c.node.atom == mark)

inductive Verdict {ω : Type} (m : RawMolecule) (observe : CanonicalRerootCursor → Option ω)
    (a b : CanonicalRerootCursor) (mark : Nat) where
  | strict (difference : Strict m a b mark)
  | equal (matched : IsotopePriority.TreesMatch m (withMark observe mark) (IsotopePriority.budget m+1) a b)

def Verdict.ordering {ω m observe a b mark} : @Verdict ω m observe a b mark → Ordering
  | .strict (.distance d) => if d.leftWins then .gt else .lt
  | .strict (.hierarchy d) => if d.leftWins then .gt else .lt
  | .equal _ => .eq

/-- The deciding source route includes the proximal ligand and the final
occurrence, even when the latter is a ring-closure duplicate. -/
def Verdict.route? {ω m observe a b mark} : @Verdict ω m observe a b mark → Option (List Nat)
  | .strict (.distance d) => some (d.occurrence.route.map (·.atom))
  | .strict (.hierarchy d) => some ((if d.leftWins then d.leftSite else d.rightSite).route.map (·.atom))
  | .equal _ => none

/-- The signed readings in a complete outward branch, prior to attaching
the derivations of the individual readings. -/
structure Arm (m : RawMolecule) (p : List Nat) where
  node : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p = some node
  entries : InventoryPriority.Entries
  coverage : carbonSites m (m.atomCount+1) node = some (entries.map Prod.fst)
  unique : (entries.map Prod.fst).Nodup

def structuralArm {m g p} (a : RingAuxiliaryInventory.ArmInventory m g p) : Arm m p :=
  ⟨a.node,a.reached,a.entries,a.coverage,a.unique⟩

structure Pair (m : RawMolecule) (p : List Nat) (i j : Nat) where
  left : Arm m (p ++ [i])
  right : Arm m (p ++ [j])
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p = some focus
  distinct : i ≠ j
  leftAt : (⟨left.node,some focus⟩ : CanonicalRerootCursor) ∈ occurrenceLigandCursors m focus ∧
    left.node.history.reverse = p ++ [i]
  rightAt : (⟨right.node,some focus⟩ : CanonicalRerootCursor) ∈ occurrenceLigandCursors m focus ∧
    right.node.history.reverse = p ++ [j]
  unique : ((left.entries ++ right.entries).map Prod.fst).Nodup
  flip : Bool
  matched : IsotopePriority.TreesMatch m (EarlierStereoMatch.observe? m p i j .five flip left.entries right.entries)
    (IsotopePriority.budget m+1) ⟨left.node,some focus⟩ ⟨right.node,some focus⟩

def pairOfArms? {m p i j} (left : Arm m (p ++ [i])) (right : Arm m (p ++ [j])) : Option (Pair m p i j) := do
  let ⟨f,hf⟩ ← (occurrence? m p).attach
  let a : CanonicalRerootCursor := ⟨left.node,some f⟩
  let b : CanonicalRerootCursor := ⟨right.node,some f⟩
  if ne : i ≠ j then
    if ha : a ∈ occurrenceLigandCursors m f ∧ left.node.history.reverse = p ++ [i] then
      if hb : b ∈ occurrenceLigandCursors m f ∧ right.node.history.reverse = p ++ [j] then
        if unique : ((left.entries ++ right.entries).map Prod.fst).Nodup then
          let attempt (flip : Bool) : Option (Pair m p i j) :=
            if h : IsotopePriority.treesMatch m (EarlierStereoMatch.observe? m p i j .five flip left.entries right.entries)
                (IsotopePriority.budget m+1) a b = true then
              some ⟨left,right,f,hf,ne,ha,hb,unique,flip,IsotopePriority.treesMatch_sound h⟩
            else none
          return ← (attempt false).orElse fun _ => attempt true
  none

def pairWith? {m : RawMolecule} (p : List Nat) (i j : Nat)
    (arm : (q : List Nat) → Option (Arm m q)) : Option (Pair m p i j) := do
  pairOfArms? (← arm (p ++ [i])) (← arm (p ++ [j]))

structure Comparison (m : RawMolecule) (p : List Nat) (i j mark : Nat) extends Pair m p i j where
  unchangedHands : flip = false
  incidentMark : mark ∈ (occurrenceLigandCursors m focus).map (·.node.atom)
  verdict : Verdict m (EarlierStereoMatch.observe? m p i j .five false left.entries right.entries)
    ⟨left.node,some focus⟩ ⟨right.node,some focus⟩ mark

def Pair.atMark? {m p i j} (pair : Pair m p i j) (mark : Nat) :
    Option (Comparison m p i j mark) := do
  if fixed : pair.flip = false then
    if incident : mark ∈ (occurrenceLigandCursors m pair.focus).map (·.node.atom) then
      let a : CanonicalRerootCursor := ⟨pair.left.node,some pair.focus⟩
      let b : CanonicalRerootCursor := ⟨pair.right.node,some pair.focus⟩
      if let some d := difference? pair.matched mark then
        return ⟨pair,fixed,incident,.strict d⟩
      let obs := EarlierStereoMatch.observe? m p i j .five false pair.left.entries pair.right.entries
      if tied : IsotopePriority.treesMatch m (withMark obs mark) (IsotopePriority.budget m+1) a b = true then
        return ⟨pair,fixed,incident,.equal (IsotopePriority.treesMatch_sound tied)⟩
  none

structure SupportedComparison (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (p : List Nat) (i j mark : Nat) extends Comparison m p i j mark where
  leftSupport : RingAuxiliaryInventory.ArmInventory m g (p ++ [i])
  rightSupport : RingAuxiliaryInventory.ArmInventory m g (p ++ [j])
  leftInputs : left.entries = leftSupport.entries
  rightInputs : right.entries = rightSupport.entries

/-- Compare under a specified incident reference atom. Each arm supplies
its own derived positive and negative occurrences. A common correspondence
must preserve all earlier hands on both geometries. -/
def compare? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (p : List Nat) (i j mark depth : Nat) : Option (SupportedComparison m g p i j mark) := do
  guard (saturatedWithHalogens m)
  let arm (id : Nat) := RingAuxiliaryInventory.arm? m g (p ++ [id]) (m.atomCount+1)
    (fun _ => none) (fun _ => depth)
  let left ← arm i
  let right ← arm j
  let pair ← pairOfArms? (structuralArm left) (structuralArm right)
  let c ← pair.atMark? mark
  if bound : c.left.entries = left.entries ∧ c.right.entries = right.entries then
    return ⟨c,left,right,bound.1,bound.2⟩
  none

theorem Comparison.earlier_trees {m p i j mark} (c : Comparison m p i j mark) :
    IsotopePriority.TreesMatch m (EarlierStereoMatch.observe? m p i j .five false c.left.entries c.right.entries)
      (IsotopePriority.budget m+1) ⟨c.left.node,some c.focus⟩ ⟨c.right.node,some c.focus⟩ := by
  simpa only [c.unchangedHands] using c.matched

end TetraStereo.Engine.RingChemicalPriority.ReferenceDistance

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDistance.routeBefore_of_rooted
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDistance.RootedPriority.first_difference
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDistance.Difference.strict_words
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDistance.Comparison.earlier_trees
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDistance.compare?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDistance.RankedDifference.strict_words
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDistance.mem_shell_iff
