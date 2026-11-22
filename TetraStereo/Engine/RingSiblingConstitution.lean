import TetraStereo.Engine.RingChemicalPriority
import TetraStereo.OneCenter.DeclarativeCIPLigandSignatureLayout
import TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.SiblingConstitution
open OneCenter Certificate.CanonicalSphereKey
open OneCenter.DeclarativeCIP.PromotedCanonical (MarkerKey MarkerWellShaped assembleMarker markerPad)
open OneCenter.LocalizedPhysicalMarkedSparseMarker (SparseMarker compareMarker compareMarker_encode_shaped)

/-- An absent slot is zero. Each occupied slot retains its full atomic
number, shifted by one so the encoding also distinguishes atomic number zero. -/
private def cell (v : WithBot Nat) : Nat := WithBot.recBotCoe 0 Nat.succ v

@[simp] private theorem cell_bot : cell ⊥ = 0 := rfl
@[simp] private theorem cell_coe (z : Nat) : cell (z : WithBot Nat) = z+1 := rfl

private theorem cell_strict : StrictMono cell := by
  intro a b h
  cases a using WithBot.recBotCoe <;> cases b using WithBot.recBotCoe <;> simp_all
  · exact Nat.succ_pos _
  · exact Nat.succ_lt_succ h

private theorem map_strict {α β : Type} [LinearOrder α] [LinearOrder β] {f : α → β}
    (strict : StrictMono f) : StrictMono (List.map f) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => exact (lt_irrefl _ h).elim
    | cons y ys => exact List.Lex.nil
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => exact (List.not_lt_nil _ h).elim
    | cons y ys =>
      rcases List.cons_lt_cons_iff.mp h with less | ⟨rfl,tail⟩
      · exact List.cons_lt_cons_iff.mpr (.inl (strict less))
      · exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,ih tail⟩)

private def numbers (key : Key Nat) : MarkerKey := key.map (List.map cell)
private def store (key : Key Nat) : SparseMarker := LocalizedPhysicalMarkedSparseMarker.encode (numbers key)

private theorem numbers_strict : StrictMono numbers := map_strict (map_strict cell_strict)

private theorem numbers_shape {w d : Nat} {k : Key Nat} (shape : WellShaped w d k) :
    MarkerWellShaped w d (numbers k) := by
  refine ⟨by simpa [numbers] using shape.1,?_⟩
  intro i hi
  simpa [numbers] using shape.2 i (by simpa [numbers] using hi)

private theorem natRow_lt (a b : List Nat) : compare a b = .lt ↔ a < b :=
  DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => compare_eq_iff_eq) a b

private theorem natRow_eq (a b : List Nat) : compare a b = .eq ↔ a = b :=
  DeclarativeCIP.compareLex_eq_eq_iff_of compare (fun _ _ => compare_eq_iff_eq) a b

private theorem stored_lt {w d : Nat} {a b : Key Nat} (ha : WellShaped w d a)
    (hb : WellShaped w d b) : compareMarker (store a) (store b) = .lt ↔ a < b := by
  rw [store,store,compareMarker_encode_shaped _ _ (numbers_shape ha) (numbers_shape hb)]
  exact (DeclarativeCIP.compareLex_eq_lt_iff_of compare natRow_lt natRow_eq _ _).trans
    numbers_strict.lt_iff_lt

private theorem stored_eq {w d : Nat} {a b : Key Nat} (ha : WellShaped w d a)
    (hb : WellShaped w d b) : compareMarker (store a) (store b) = .eq ↔ a = b := by
  rw [store,store,compareMarker_encode_shaped _ _ (numbers_shape ha) (numbers_shape hb)]
  exact (DeclarativeCIP.compareLex_eq_eq_iff_of compare natRow_eq _ _).trans
    numbers_strict.injective.eq_iff

private theorem row_at (w k : Nat) (key : Key Nat) :
    (numbers key).getD k (markerPad w k) = (key.getD k (pad w k)).map cell := by
  have padding : (pad w k : Level Nat).map cell = markerPad w k := by simp [pad,markerPad]
  rw [← padding]
  exact List.getD_map key (pad w k) (List.map cell)

private theorem numbers_assemble (w d z : Nat) (ks : List (Key Nat)) :
    numbers (assemble w d z ks) = assembleMarker w d (z+1) (ks.map numbers) := by
  change [z+1] :: ((List.range d).map _).map (List.map cell) =
    [z+1] :: (List.range d).map _
  apply congrArg (List.cons [z+1])
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  change ((List.range w).flatMap _).map cell = (List.range w).flatMap _
  rw [List.map_flatMap]
  congr 1
  funext slot
  have child : (ks.map numbers).getD slot [] = numbers (ks.getD slot []) :=
    List.getD_map ks [] numbers
  change _ = ((ks.map numbers).getD slot []).getD k (markerPad w k)
  rw [child,row_at]

private def sortStored (keys : List SparseMarker) :=
  keys.insertionSort (fun a b => compareMarker a b ≠ .lt)

private theorem sort_store {w d} (keys : List (Key Nat))
    (shaped : ∀ x ∈ keys, WellShaped w d x) :
    sortStored (keys.map store) = (sortDesc keys).map store :=
  (List.map_insertionSort Desc (fun a b => compareMarker a b ≠ .lt) store keys
    fun a ha b hb => by
      change b ≤ a ↔ ¬ compareMarker (store a) (store b) = .lt
      rw [stored_lt (shaped _ ha) (shaped _ hb),not_lt]).symm

mutual
/-- Build up the complete subtree priorities before assigning sibling slots.
Only occupied slots are allocated in each of the requested spheres. -/
def key (w d : Nat) : HTree Nat → SparseMarker
  | .node z cs => LocalizedPhysicalMarkedSparseMarker.assemble w d (z+1) (sortStored (keys w d cs))

def keys (w d : Nat) : List (HTree Nat) → List SparseMarker
  | [] => []
  | t :: ts => key w d t :: keys w d ts
end

private theorem keys_eq_map (w d : Nat) (ts : List (HTree Nat)) :
    keys w d ts = ts.map (key w d) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [keys,ih]

/-- For every width, depth, and finite labelled tree, the sparse computation
returns the occupied slots of precisely the repository's canonical key. -/
theorem key_exact (w d : Nat) (t : HTree Nat) : key w d t = store (ckey w d t) := by
  induction t using HTree.induction with
  | step z cs ih =>
    let ds := cs.map (ckey w d)
    have shaped (x) (hx : x ∈ ds) : WellShaped w d x := by
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
      exact ckey_wellShaped w d t
    have mapped : cs.map (key w d) = ds.map store := by
      unfold ds
      rw [List.map_map]
      exact List.map_congr_left ih
    rw [key,keys_eq_map,mapped,sort_store ds shaped,ckey_node]
    change LocalizedPhysicalMarkedSparseMarker.assemble w d (z+1) ((sortDesc ds).map store) =
      LocalizedPhysicalMarkedSparseMarker.encode (numbers (assemble w d z (sortDesc ds)))
    rw [numbers_assemble]
    have assembled := LocalizedPhysicalMarkedSparseMarker.assemble_eq_encode w d (z+1) ((sortDesc ds).map numbers) (by
      intro m hm
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm
      exact numbers_shape (shaped _ (sortDesc_mem hk)))
    simpa [List.map_map,store,Function.comp_def] using assembled

theorem compare_lt_iff (w d : Nat) (a b : HTree Nat) :
    compareMarker (key w d a) (key w d b) = .lt ↔ ckey w d a < ckey w d b := by
  rw [key_exact,key_exact]
  exact stored_lt (ckey_wellShaped w d a) (ckey_wellShaped w d b)

theorem compare_eq_iff (w d : Nat) (a b : HTree Nat) :
    compareMarker (key w d a) (key w d b) = .eq ↔ ckey w d a = ckey w d b := by
  rw [key_exact,key_exact]
  exact stored_eq (ckey_wellShaped w d a) (ckey_wellShaped w d b)

theorem compare_gt_iff (w d : Nat) (a b : HTree Nat) :
    compareMarker (key w d a) (key w d b) = .gt ↔ ckey w d b < ckey w d a := by
  rcases lt_trichotomy (ckey w d a) (ckey w d b) with h | h | h
  · rw [(compare_lt_iff w d a b).2 h]
    simp [not_lt_of_gt h]
  · rw [(compare_eq_iff w d a b).2 h]
    simp [h]
  · have nonLt := mt (compare_lt_iff w d a b).1 (not_lt_of_gt h)
    have nonEq := mt (compare_eq_iff w d a b).1 (ne_of_gt h)
    cases outcome : compareMarker (key w d a) (key w d b) <;> simp_all

/-- Check that the depth bound actually reaches all descendants. The
existing molecular tree projection can then be used without truncation.
A cursor arriving from the original parent follows outward children only;
a terminal duplicate has no children. -/
def exhausted (m : RawMolecule) : Nat → CanonicalRerootCursor → Bool
  | 0,c => (c.children m).isEmpty
  | n+1,c => (c.children m).all (exhausted m n)

structure Arm (m : RawMolecule) (parent : RawMolecule.CanonicalBranchNode) (path : List Nat) where
  node : RawMolecule.CanonicalBranchNode
  child : node ∈ m.canonicalChildren parent
  address : node.history.reverse = path
  complete : exhausted m (m.atomCount+1) ⟨node,some parent⟩ = true
  tree : HTree Nat
  molecular : atomicTree m 3 (m.atomCount+1) ⟨node,some parent⟩ = some tree

private def arm? (m : RawMolecule) (parent : RawMolecule.CanonicalBranchNode) (p : List Nat) :
    Option (Arm m parent p) := do
  let ⟨n,hn⟩ ← ((m.canonicalChildren parent).find? (fun n => n.history.reverse == p)).attach
  let cursor : CanonicalRerootCursor := ⟨n,some parent⟩
  if complete : exhausted m (m.atomCount+1) cursor = true then
    let ⟨t,built⟩ ← (atomicTree m 3 (m.atomCount+1) cursor).attach
    return ⟨n,List.mem_of_find?_eq_some hn,by simpa using List.find?_some hn,complete,t,built⟩
  none

mutual
/-- The actual deepest occupied sphere, counting the root as sphere zero. -/
def height : HTree Nat → Nat
  | .node _ cs => childHeight cs

def childHeight : List (HTree Nat) → Nat
  | [] => 0
  | c :: cs => max (height c + 1) (childHeight cs)
end

theorem child_below_height (z : Nat) {cs : List (HTree Nat)} {c} (hc : c ∈ cs) :
    height c < height (.node z cs) := by
  change height c < childHeight cs
  induction cs with
  | nil => contradiction
  | cons t ts ih =>
    rcases List.mem_cons.mp hc with rfl | inside
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih inside) (le_max_right _ _)

def depth {m parent p q} (a : Arm m parent p) (b : Arm m parent q) :=
  max (height a.tree) (height b.tree)

/-- Both sibling occurrences are bound to their original digraph parent.
A duplicate endpoint retains its own terminal cursor and original atom. -/
structure Comparison (m : RawMolecule) (p q : List Nat) where
  distinct : p ≠ q
  parent : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p.dropLast = some parent
  left : Arm m parent p
  right : Arm m parent q
  ordering : Ordering
  computed : compareMarker (key 3 (depth left right) left.tree)
    (key 3 (depth left right) right.tree) = ordering

def checked? (m : RawMolecule) (p q : List Nat) : Option (Comparison m p q) := do
  if distinct : p ≠ q then
    let ⟨parent,reached⟩ ← (occurrence? m p.dropLast).attach
    let a ← arm? m parent p
    let b ← arm? m parent q
    let d := depth a b
    return ⟨distinct,parent,reached,a,b,compareMarker (key 3 d a.tree) (key 3 d b.tree),rfl⟩
  none

/-- Compare the complete Rule 1a constitutions of outward siblings on the
addressed original digraph. A greater result gives priority to the first
path. An equal result is a Rule 1a tie. -/
def compare? (m : RawMolecule) (p q : List Nat) : Option Ordering :=
  (checked? m p q).map Comparison.ordering

theorem Comparison.first_difference {m p q} (c : Comparison m p q) :
    c.ordering = .gt ↔ ∃ k slot,
      observation 3 (depth c.left c.right) c.right.tree k slot <
        observation 3 (depth c.left c.right) c.left.tree k slot ∧
      (∀ j < k, ∀ s, observation 3 (depth c.left c.right) c.right.tree j s =
        observation 3 (depth c.left c.right) c.left.tree j s) ∧
      (∀ s < slot, observation 3 (depth c.left c.right) c.right.tree k s =
        observation 3 (depth c.left c.right) c.left.tree k s) := by
  rw [← c.computed,compare_gt_iff]
  exact ckey_lt_iff_first_difference _ _ _ _

theorem Comparison.tie_iff {m p q} (c : Comparison m p q) :
    c.ordering = .eq ↔ ckey 3 (depth c.left c.right) c.left.tree =
      ckey 3 (depth c.left c.right) c.right.tree := by
  rw [← c.computed,compare_eq_iff]

end TetraStereo.Engine.RingChemicalPriority.SiblingConstitution

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SiblingConstitution.key_exact
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SiblingConstitution.compare_lt_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SiblingConstitution.compare_eq_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SiblingConstitution.compare?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SiblingConstitution.Comparison.first_difference
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SiblingConstitution.Comparison.tie_iff
