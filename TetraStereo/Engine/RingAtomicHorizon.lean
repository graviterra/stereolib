import TetraStereo.Engine.RingSiblingConstitution
import TetraStereo.Engine.RingConstitutionalCoverage
import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.AtomicHorizon
open OneCenter CertifiedLocalizedCIPInput AuthoritativeCIPMoleculeCursorRanking
open Certificate.CanonicalSphereKey SiblingConstitution

/-- One molecular depth for every orientation of every occurrence in the
fixed-root tree, including the incoming side of an interior occurrence. -/
def horizon (m : RawMolecule) := 2 * m.atomCount + 1

private theorem mapM_congr {α β : Type} (xs : List α) {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons,List.mapM_cons,h x List.mem_cons_self,ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

/-- At the structural cutoff the actual builder is stable as an option:
width overflow, absent source atoms and other failures stay failures. -/
theorem atomicTree_stable {m root} (bound : root < m.atomCount) (wf : m.WellFormed)
    {c : CanonicalRerootCursor} (eligible : CanonicalCenterRerootCursor m root c)
    (w d k : Nat) (enough : moleculeCursorHeight m c ≤ d) :
    atomicTree m w (d+k) c = atomicTree m w d c := by
  induction d generalizing c with
  | zero =>
    have leaf : c.children m = [] := by
      cases cs : c.children m with
      | nil => rfl
      | cons a xs =>
        have lt := moleculeCursorHeight_child_lt bound wf eligible
          (show a ∈ c.children m by simp [cs])
        omega
    cases k with
    | zero => rfl
    | succ k => simp [atomicTree,leaf]
  | succ d ih =>
    have children : (c.children m).mapM (atomicTree m w (d+k)) =
        (c.children m).mapM (atomicTree m w d) := by
      apply mapM_congr
      intro u hu
      have lt := moleculeCursorHeight_child_lt bound wf eligible hu
      exact ih (eligible.child hu) (by omega)
    simp only [Nat.succ_add,atomicTree,children]

theorem all_trees_stable {m root} (bound : root < m.atomCount) (wf : m.WellFormed)
    {n} (generated : CanonicalCenterTreeNode m root n) {c} (incident : c ∈ occurrenceLigandCursors m n)
    (w k : Nat) : atomicTree m w (horizon m+k) c = atomicTree m w (horizon m) c := by
  have eligible := occurrenceLigandCursor_eligible generated incident
  exact atomicTree_stable bound wf eligible _ _ _ (moleculeCursorHeight_le_two_mul_atomCount_add_one bound wf eligible)

private theorem member_mapM {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (read : xs.mapM f = some ys) {y : β} (member : y ∈ ys) : ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at read; subst ys; simp at member
  | cons x xs ih =>
    cases h : f x with
    | none => simp [List.mapM_cons,h] at read
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons,h,ht] at read
      | some bs =>
        obtain rfl : b :: bs = ys := by simpa [List.mapM_cons,h,ht] using read
        rcases List.mem_cons.mp member with rfl | rest
        · exact ⟨x,List.mem_cons_self,h⟩
        · obtain ⟨z,hz,found⟩ := ih ht rest
          exact ⟨z,List.mem_cons_of_mem _ hz,found⟩

private theorem childHeight_le {xs : List (HTree Nat)} {d : Nat}
    (all : ∀ t ∈ xs, height t + 1 ≤ d) : childHeight xs ≤ d := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (all _ List.mem_cons_self) (ih (fun t ht => all t (List.mem_cons_of_mem _ ht)))

private theorem built_height {m w d c t} (ok : atomicTree m w d c = some t) : height t ≤ d := by
  induction d generalizing c t with
  | zero =>
    unfold atomicTree at ok
    cases atom : m.atoms[c.node.atom]? with
    | none => simp [atom] at ok
    | some a =>
      by_cases z : 0 < a.element.atomicNumber <;> simp [atom,guard,z] at ok
      subst t
      exact Nat.zero_le _
  | succ d ih =>
    unfold atomicTree at ok
    cases atom : m.atoms[c.node.atom]? with
    | none => simp [atom] at ok
    | some a =>
      by_cases z : 0 < a.element.atomicNumber <;> simp [atom,guard,z] at ok
      by_cases width : (c.children m).length ≤ w <;> simp [width] at ok
      cases collected : (c.children m).mapM (atomicTree m w d) with
      | none => simp [collected] at ok
      | some cs =>
        simp [collected] at ok
        subst t
        apply childHeight_le
        intro x hx
        obtain ⟨u,_,read⟩ := member_mapM collected hx
        exact Nat.succ_le_succ (ih read)

private theorem lt_append_same {α : Type} [LinearOrder α] {xs ys : List α}
    (len : xs.length = ys.length) (tail : List α) :
    xs ++ tail < ys ++ tail ↔ xs < ys := by
  induction xs generalizing ys with
  | nil =>
    have e : ys = [] := List.length_eq_zero_iff.mp len.symm
    simp [e]
  | cons x xs ih =>
    cases ys with
    | nil => simp at len
    | cons y ys =>
      simp only [List.length_cons,Nat.succ.injEq] at len
      simp only [List.cons_append,List.cons_lt_cons_iff,ih len]

private theorem sort_append (ds : List (Key Nat)) (r : Level Nat) {n : Nat}
    (lengths : ∀ k ∈ ds, k.length = n) :
    sortDesc (ds.map (· ++ [r])) = (sortDesc ds).map (· ++ [r]) := by
  rw [sortDesc_eq_of_perm ((sortDesc_perm ds).map (· ++ [r])).symm]
  apply sortDesc_of_pairwise
  apply List.pairwise_map.mpr
  apply (sortDesc_pairwise ds).imp_of_mem
  intro a b ha hb le
  apply le_of_not_gt
  intro wrong
  exact (not_lt_of_ge le) ((lt_append_same ((lengths a (sortDesc_mem ha)).trans
    (lengths b (sortDesc_mem hb)).symm) [r]).mp wrong)

private theorem pad_next (w d : Nat) :
    (List.range w).flatMap (fun _ => pad (α := Nat) w d) = pad w (d+1) := by
  simp [List.flatMap_def,pad,pow_succ,Nat.mul_comm]

private theorem levels {ks : List (Key Nat)} {d : Nat} (r : Level Nat) {slot i : Nat}
    (hi : i ≤ d) (lengths : ∀ k ∈ ks, k.length = d+1) (default : Level Nat) :
    ((ks.map (· ++ [r])).getD slot []).getD i default = (ks.getD slot []).getD i default := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases hk : ks[slot]? with
  | none => rfl
  | some key =>
    simp only [Option.map_some,Option.getD_some]
    have len := lengths key (List.mem_of_getElem? hk)
    rw [List.getElem?_append_left (by omega : i < key.length)]

/-- Once the input tree's deepest actual atom is included, the next dense
key appends precisely one all-absent sphere. Child priority ties therefore
cannot reorder any earlier observation. -/
theorem ckey_next (w : Nat) (t : HTree Nat) (d : Nat) (enough : height t ≤ d) :
    ckey w (d+1) t = ckey w d t ++ [pad w (d+1)] := by
  induction t using HTree.induction generalizing d with
  | step z cs ih =>
    let ds := cs.map (ckey w d)
    let ks := sortDesc ds
    have below (c : HTree Nat) (hc : c ∈ cs) : height c < d :=
      lt_of_lt_of_le (child_below_height z hc) enough
    have dslen (key : Key Nat) (hk : key ∈ ds) : key.length = d+1 := by
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp hk
      exact (ckey_wellShaped w d c).1
    have kslen (key : Key Nat) (hk : key ∈ ks) : key.length = d+1 := dslen key (sortDesc_mem hk)
    have old_row (key : Key Nat) (hk : key ∈ ks) : key.getD d (pad w d) = pad w d := by
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (sortDesc_mem hk)
      have less := below c hc
      cases d with
      | zero => omega
      | succ d =>
        rw [ih c hc d (by omega)]
        have len := (ckey_wellShaped w d c).1
        simp [List.getD_eq_getElem?_getD,len]
    have grown : cs.map (ckey w (d+1)) = ds.map (· ++ [pad w (d+1)]) := by
      rw [List.map_map]
      exact List.map_congr_left (fun c hc => ih c hc d (Nat.le_of_lt (below c hc)))
    have final (i : Nat) : (ks.getD i []).getD d (pad w d) = pad w d := by
      rw [List.getD_eq_getElem?_getD (l := ks)]
      cases hk : ks[i]? with
      | none => rfl
      | some k => exact old_row k (List.mem_of_getElem? hk)
    rw [ckey_node,ckey_node,grown,sort_append ds _ dslen]
    change assemble w (d+1) z (ks.map (· ++ [pad w (d+1)])) =
      assemble w d z ks ++ [pad w (d+1)]
    simp only [assemble,List.cons_append,List.cons.injEq,true_and,List.range_succ,List.map_append,List.map_cons,List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro j hj
      have h := List.mem_range.mp hj
      simp only [levels _ (Nat.le_of_lt h) kslen]
    · simp only [levels _ (Nat.le_refl d) kslen,final,pad_next]

private def advance (m : RawMolecule) (n : RawMolecule.CanonicalBranchNode) (i : Nat) :=
  (m.canonicalChildren n).find? fun child => child.atom == i && !child.forcedLeaf

private theorem generated_fold {m root} (steps : List Nat) {n u}
    (generated : CanonicalCenterTreeNode m root n) (walk : steps.foldlM (advance m) n = some u) :
    CanonicalCenterTreeNode m root u := by
  induction steps generalizing n with
  | nil => have eqn : n = u := by simpa using walk
           exact eqn ▸ generated
  | cons i steps ih =>
    cases next : advance m n i with
    | none => simp [List.foldlM_cons,next] at walk
    | some v =>
      exact ih (.child generated (List.mem_of_find?_eq_some next)) (by simpa [List.foldlM_cons,next] using walk)

private theorem generated_of_reached {m root steps n} (bound : root < m.atomCount)
    (site : occurrence? m (root::steps) = some n) : CanonicalCenterTreeNode m root n :=
  generated_fold steps .root (by simpa [occurrence?,advance,guard,bound] using site)

private def numbers (k : Key Nat) := k.map (List.map (fun z => (z : Option Nat).getD 0))

-- Expansion of the private proof-carrying atomic arm is used only to show
-- that the public projected rows read exactly the molecular cursor tree.
local macro "unfoldArm" : tactic => do
  let n := Lean.mkIdent (Lean.mkPrivateNameCore `TetraStereo.Engine.RingChemicalPriority
    `TetraStereo.Engine.RingChemicalPriority.arm?)
  `(tactic| unfold $n:ident)

private theorem rows_eq {m path n id d c} (site : occurrence? m path = some n)
    (found : (occurrenceLigandCursors m n).find? (fun a => a.node.atom == id) = some c) :
    ligandRows? m path id d = (atomicTree m 3 d c).map (fun t => numbers (ckey 3 d t)) := by
  simp [ligandRows?,site,found]
  unfoldArm
  split <;> simp_all [numbers]

private theorem rows_length {m path id d rows} (present : ligandRows? m path id d = some rows) :
    rows.length = d+1 := by
  cases site : occurrence? m path with
  | none => simp [ligandRows?,site] at present
  | some n =>
    cases found : (occurrenceLigandCursors m n).find? (fun a => a.node.atom == id) with
    | none => simp [ligandRows?,site,found] at present
    | some c =>
      rw [rows_eq site found] at present
      obtain ⟨t,_,rfl⟩ := Option.map_eq_some_iff.mp present
      simpa [numbers] using (ckey_wellShaped 3 d t).1

/-- Beyond the bound the real public ligand row reader has exactly two
possibilities. A previously missing result remains missing. A successful
read gains one completely empty sphere, common to every ligand. -/
theorem ligandRows?_next {m : RawMolecule} {root : Nat} (wf : m.WellFormed) (steps : List Nat)
    (id d : Nat) (enough : horizon m ≤ d) :
    ligandRows? m (root::steps) id (d+1) =
      (ligandRows? m (root::steps) id d).map (· ++ [List.replicate (3^(d+1)) 0]) := by
  by_cases bound : root < m.atomCount
  · cases site : occurrence? m (root::steps) with
    | none => simp [ligandRows?,site]
    | some n =>
      cases found : (occurrenceLigandCursors m n).find? (fun a => a.node.atom == id) with
      | none => simp [ligandRows?,site,found]
      | some c =>
        have eligible := occurrenceLigandCursor_eligible (generated_of_reached bound site)
          (List.mem_of_find?_eq_some found)
        have low := moleculeCursorHeight_le_two_mul_atomCount_add_one bound wf eligible
        rw [rows_eq site found,rows_eq site found,atomicTree_stable bound wf eligible 3 d 1 (le_trans low enough)]
        cases built : atomicTree m 3 d c with
        | none => rfl
        | some t => simp [ckey_next 3 t d (built_height built),numbers,pad]; rfl
  · have site : occurrence? m (root::steps) = none := by simp [occurrence?,guard,bound]
    simp [ligandRows?,site]

/-- Lexicographic comparison of the actual exported sphere observations.
Missing occurrences or an out-of-width molecular expansion remain unresolved. -/
def compareRows? (m : RawMolecule) (path : List Nat) (a b d : Nat) : Option Ordering := do
  let x ← ligandRows? m path a d
  let y ← ligandRows? m path b d
  return if x = y then .eq else if x < y then .lt else .gt

private theorem comparison_next (m : RawMolecule) (wf : m.WellFormed) (path : List Nat)
    (a b d : Nat) (enough : horizon m ≤ d) :
    compareRows? m path a b (d+1) = compareRows? m path a b d := by
  cases path with
  | nil => rfl
  | cons root steps =>
    simp only [compareRows?,ligandRows?_next wf steps _ d enough]
    cases x : ligandRows? m (root::steps) a d with
    | none => rfl
    | some left =>
      cases y : ligandRows? m (root::steps) b d with
      | none => rfl
      | some right =>
        have lengths := (rows_length x).trans (rows_length y).symm
        simp [lt_append_same lengths]

/-- A single atom-count bound is sufficient for all incident ligand pairs of
all reached occurrences on any well-formed raw molecule, regardless of ring
connectivity. The equality covers all four possible results: strict in either
direction, tied, and unavailable. -/
theorem comparison_stable (m : RawMolecule) (wf : m.WellFormed) (path : List Nat) (a b d : Nat)
    (enough : horizon m ≤ d) : compareRows? m path a b d = compareRows? m path a b (horizon m) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le enough
  induction k with
  | zero => rfl
  | succ k ih => exact (comparison_next m wf path a b _ (Nat.le_add_right _ _)).trans (ih (Nat.le_add_right _ _))


private theorem incident_next {m : RawMolecule} (wf : m.WellFormed) {path n c d}
    (site : occurrence? m path = some n) (member : c ∈ occurrenceLigandCursors m n) (enough : horizon m ≤ d) :
    atomicTree m 3 (d+1) c = atomicTree m 3 d c := by
  cases path with
  | nil => simp [occurrence?] at site
  | cons root steps =>
    by_cases bound : root < m.atomCount
    · have eligible := occurrenceLigandCursor_eligible (generated_of_reached bound site) member
      exact atomicTree_stable bound wf eligible 3 d 1 ((moleculeCursorHeight_le_two_mul_atomCount_add_one bound wf eligible).trans enough)
    · simp [occurrence?,guard,bound] at site

private def extend (d : Nat) (k : Option (Key Nat)) := k.map (· ++ [pad 3 (d+1)])

private theorem extend_injective (d : Nat) : Function.Injective (extend d) := by
  intro x y h
  cases x <;> cases y <;> simp_all [extend]

private theorem keys_next {m : RawMolecule} (wf : m.WellFormed) {path n c d}
    (site : occurrence? m path = some n) (member : c ∈ occurrenceLigandCursors m n) (enough : horizon m ≤ d) :
    molecularAtomicKey? m (d+1) c = extend d (molecularAtomicKey? m d c) := by
  unfold molecularAtomicKey? extend
  rw [incident_next wf site member enough]
  cases hit : atomicTree m 3 d c with
  | none => rfl
  | some t => simp [ckey_next 3 t d (built_height hit)]

private theorem rankable_next {m : RawMolecule} (wf : m.WellFormed) (path : List Nat)
    (d : Nat) (enough : horizon m ≤ d) :
    (atomicRanking? m path (d+1)).isSome = true ↔ (atomicRanking? m path d).isSome = true := by
  rw [atomicRanking?_isSome_iff_keys,atomicRanking?_isSome_iff_keys]
  apply exists_congr
  intro n
  by_cases site : occurrence? m path = some n
  · have all : (∀ c ∈ occurrenceLigandCursors m n, (atomicTree m 3 (d+1) c).isSome = true) ↔
        ∀ c ∈ occurrenceLigandCursors m n, (atomicTree m 3 d c).isSome = true := by
      constructor <;> intro h c hc <;> simpa [incident_next wf site hc enough] using h c hc
    have mapping : (occurrenceLigandCursors m n).map (molecularAtomicKey? m (d+1)) =
        ((occurrenceLigandCursors m n).map (molecularAtomicKey? m d)).map (extend d) := by
      rw [List.map_map]
      exact List.map_congr_left (fun c hc => keys_next wf site hc enough)
    simp only [site,true_and,all,mapping,List.nodup_map_iff (extend_injective d)]
  · simp [site]

private theorem orders_agree {m : RawMolecule} (wf : m.WellFormed) {p d}
    (old : AtomicRanking m p d) (new : AtomicRanking m p (d+1)) (enough : horizon m ≤ d) :
    old.arms.map (·.cursor) = new.arms.map (·.cursor) := by
  let priority (c : CanonicalRerootCursor) := (molecularAtomicKey? m (d+1) c).getD []
  let before (a b : CanonicalRerootCursor) := priority b < priority a
  have same : old.focus = new.focus := Option.some.inj (old.reached.symm.trans new.reached)
  have perm := old.complete.trans (same ▸ new.complete.symm)
  have left : (old.arms.map (·.cursor)).Pairwise before := by
    apply List.pairwise_map.mpr
    apply old.strict.imp_of_mem
    intro a b ha hb less
    have key (x : AtomicArm m d) (hx : x ∈ old.arms) :
        priority x.cursor = x.key ++ [pad 3 (d+1)] := by
      have hc := old.complete.mem_iff.mp (List.mem_map_of_mem (f := AtomicArm.cursor) hx)
      unfold priority
      rw [keys_next wf old.reached hc enough]
      simp [extend,molecularAtomicKey?,x.molecular,x.exactKey]
    change priority b.cursor < priority a.cursor
    rw [key a ha,key b hb]
    apply (lt_append_same _ _).mpr less
    rw [a.exactKey,b.exactKey,(ckey_wellShaped ..).1,(ckey_wellShaped ..).1]
  have right : (new.arms.map (·.cursor)).Pairwise before := by
    apply List.pairwise_map.mpr
    apply new.strict.imp
    intro a b less
    simpa [before,priority,molecularAtomicKey?,a.molecular,b.molecular,a.exactKey,b.exactKey] using less
  exact List.Perm.eq_of_pairwise (fun a b _ _ ab ba => False.elim (lt_asymm ab ba)) left right perm

/-- The actual production sorter returns exactly the same four ligand IDs,
in the same order, or the same absence of an order, at all depths beyond
the bound. The theorem assumes only structural well-formedness. -/
theorem atomicOrder?_stable (m : RawMolecule) (wf : m.WellFormed) (path : List Nat) (d : Nat)
    (enough : horizon m ≤ d) : atomicOrder? m path d = atomicOrder? m path (horizon m) := by
  have step (j : Nat) (ej : horizon m ≤ j) : atomicOrder? m path (j+1) = atomicOrder? m path j := by
    have possible := rankable_next wf path j ej
    cases old : atomicRanking? m path j <;> cases new : atomicRanking? m path (j+1) <;>
      simp [old,new] at possible
    · simp [atomicOrder?,old,new]
    · rename_i a b
      have same := congrArg (List.map (fun c : CanonicalRerootCursor => c.node.atom)) (orders_agree wf a b ej)
      simpa [atomicOrder?,old,new,List.map_map,Function.comp_def] using same.symm
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le enough
  induction k with
  | zero => rfl
  | succ k ih => exact (step _ (Nat.le_add_right _ _)).trans (ih (Nat.le_add_right _ _))

/-- No independent width, successful occurrence, or total-key hypothesis
is needed to stabilize both public observations on any admitted input. -/
theorem admitted_priorities (input : LocalizedChemicalRing.Input) (path : List Nat) (a b d : Nat)
    (enough : horizon input.molecule ≤ d) :
    compareRows? input.molecule path a b d = compareRows? input.molecule path a b (horizon input.molecule) ∧
    atomicOrder? input.molecule path d = atomicOrder? input.molecule path (horizon input.molecule) :=
  ⟨comparison_stable _ input.admissible.1.1 _ _ _ _ enough,
    atomicOrder?_stable _ input.admissible.1.1 _ _ enough⟩

/-- A finite directed walk in the actual fixed-root occurrence tree. -/
inductive Reach (m : RawMolecule) : CanonicalRerootCursor → CanonicalRerootCursor → Prop
  | here (c) : Reach m c c
  | via {c u v} (step : u ∈ c.children m) (rest : Reach m u v) : Reach m c v

def positive (m : RawMolecule) (c : CanonicalRerootCursor) : Prop :=
  ∃ a, m.atoms[c.node.atom]? = some a ∧ 0 < a.element.atomicNumber

/-- Literal molecular requirements for this Rule 1a observation. The width
is the number of forward cursors after omitting the incoming edge. -/
def Supported (m : RawMolecule) (w : Nat) (c : CanonicalRerootCursor) : Prop :=
  ∀ u, Reach m c u → positive m u ∧ (u.children m).length ≤ w

private theorem supported_iff {m w c} : Supported m w c ↔
    positive m c ∧ (c.children m).length ≤ w ∧ ∀ u ∈ c.children m, Supported m w u := by
  constructor
  · intro h
    exact ⟨(h c (.here c)).1,(h c (.here c)).2,fun _ edge v walk => h v (.via edge walk)⟩
  · rintro ⟨atom,width,children⟩ u reached
    cases reached with
    | here => exact ⟨atom,width⟩
    | via step rest => exact children _ step _ rest

private theorem mapM_available {α β : Type} (f : α → Option β) (xs : List α) :
    (xs.mapM f).isSome = true ↔ ∀ x ∈ xs, (f x).isSome = true := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases first : f a <;> cases tail : xs.mapM f <;> simp_all [List.mapM_cons]

private theorem at_zero {m w c} : (atomicTree m w 0 c).isSome = true ↔ positive m c := by
  cases atom : m.atoms[c.node.atom]? with
  | none => simp [atomicTree,positive,atom]
  | some a => by_cases z : 0 < a.element.atomicNumber <;> simp [atomicTree,positive,atom,guard,z]

private theorem at_succ {m w d c} : (atomicTree m w (d+1) c).isSome = true ↔
    positive m c ∧ (c.children m).length ≤ w ∧ ∀ u ∈ c.children m, (atomicTree m w d u).isSome = true := by
  conv_lhs => rw [atomicTree]
  cases atom : m.atoms[c.node.atom]? with
  | none => simp [positive,atom]
  | some a =>
    by_cases z : 0 < a.element.atomicNumber <;> simp [positive,atom,guard,z]
    by_cases fits : (c.children m).length ≤ w
    · have checked := mapM_available (atomicTree m w d) (c.children m)
      cases collected : (c.children m).mapM (atomicTree m w d) <;> simpa [fits,collected] using checked
    · simp [fits]

/-- After the derived structural bound, an absent tree is explained exactly
by a missing/zero atomic observation or an over-width vertex at a reachable
occurrence. No chemical priority comparison is a hypothesis. -/
theorem atomicTree_isSome_iff_supported {m root} (bound : root < m.atomCount) (wf : m.WellFormed)
    {c : CanonicalRerootCursor} (eligible : CanonicalCenterRerootCursor m root c) (w d : Nat)
    (enough : moleculeCursorHeight m c ≤ d) :
    (atomicTree m w d c).isSome = true ↔ Supported m w c := by
  induction d generalizing c with
  | zero =>
    have leaf : c.children m = [] := by
      cases cs : c.children m with
      | nil => rfl
      | cons x xs =>
        have lt := moleculeCursorHeight_child_lt bound wf eligible (show x ∈ c.children m by simp [cs])
        omega
    rw [at_zero,supported_iff]
    simp [leaf]
  | succ j ih =>
    rw [at_succ,supported_iff]
    have each (u) (edge : u ∈ c.children m) :
        (atomicTree m w j u).isSome = true ↔ Supported m w u := by
      have lt := moleculeCursorHeight_child_lt bound wf eligible edge
      exact ih (eligible.child edge) (by omega)
    constructor
    · rintro ⟨a,h,all⟩
      exact ⟨a,h,fun u hu => (each u hu).mp (all u hu)⟩
    · rintro ⟨a,h,all⟩
      exact ⟨a,h,fun u hu => (each u hu).mpr (all u hu)⟩

/-- A failed expansion at the horizon has an identifiable molecular cause at
a reachable occurrence. In particular, missing output cannot be interpreted
as equality of a pair of valid constitutional trees. -/
theorem atomicTree_none_iff_defect {m root} (bound : root < m.atomCount) (wf : m.WellFormed)
    {c : CanonicalRerootCursor} (eligible : CanonicalCenterRerootCursor m root c) (w : Nat) :
    atomicTree m w (horizon m) c = none ↔
      ∃ u, Reach m c u ∧ (¬positive m u ∨ w < (u.children m).length) := by
  classical
  have good := atomicTree_isSome_iff_supported bound wf eligible w (horizon m)
    (moleculeCursorHeight_le_two_mul_atomCount_add_one bound wf eligible)
  have missing : atomicTree m w (horizon m) c = none ↔ ¬Supported m w c := by
    rw [← good]
    cases atomicTree m w (horizon m) c <;> simp
  rw [missing]
  simp only [Supported,not_forall,not_and_or,not_le,exists_prop]

end TetraStereo.Engine.RingChemicalPriority.AtomicHorizon

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicHorizon.all_trees_stable
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicHorizon.ckey_next
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicHorizon.ligandRows?_next
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicHorizon.comparison_stable
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicHorizon.atomicOrder?_stable
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicHorizon.admitted_priorities
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicHorizon.atomicTree_isSome_iff_supported
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicHorizon.atomicTree_none_iff_defect
