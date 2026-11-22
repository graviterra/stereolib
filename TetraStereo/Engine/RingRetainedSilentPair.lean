import TetraStereo.Engine.RingRetainedSiblingOrder
import TetraStereo.Engine.RingSharedArmRefusal

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedSilentPair
open OneCenter CertifiedLocalizedCIPInput RingChemicalPriority
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingRetainedConstitution (key)

private def endpoint (i : Input) (a : Arm i) : Nat :=
  (a.occurrence.val.node.current?.map Fin.val).getD i.molecule.atomCount

/-- A molecular symmetry independently found on the whole bond graph. The full
comparison below still has to follow both directed arms in the original digraph. -/
structure Exchange (i : Input) (focus : Nat) where
  left : Nat
  right : Nat
  swap : Equiv.Perm (Fin i.molecule.atomCount)
  graph : (∀ x, i.molecule.atoms.get (swap x) = i.molecule.atoms.get x) ∧ swap ∈ i.molecule.toMoleculeGraph.Aut
  origin : (∃ t : RingTerminalPair.Certificate i.molecule focus,
    left = t.left.val ∧ right = t.right.val ∧ swap = Equiv.swap t.left t.right) ∨
    (∃ (depth : Nat) (t : RingSilentPair.Certificate i.molecule depth focus),
      left = t.left.node.atom ∧ right = t.right.node.atom ∧ swap = t.swap)
  distinct : left ≠ right
  incident : ∀ x : Fin i.molecule.atomCount, x.val ∈ i.molecule.ligandsWithLonePair focus →
    (swap x).val = LocalizedMarkedTerminalGaugeSwap.swapAtom left right x.val

private def attempt? (i : Input) (focus : Nat) : Option (Exchange i focus) := do
  let proposal (a b : Nat) (e : Equiv.Perm (Fin i.molecule.atomCount))
      (aut : (∀ x, i.molecule.atoms.get (e x) = i.molecule.atoms.get x) ∧ e ∈ i.molecule.toMoleculeGraph.Aut)
      (origin : (∃ t : RingTerminalPair.Certificate i.molecule focus,
        a = t.left.val ∧ b = t.right.val ∧ e = Equiv.swap t.left t.right) ∨
        (∃ (depth : Nat) (t : RingSilentPair.Certificate i.molecule depth focus),
          a = t.left.node.atom ∧ b = t.right.node.atom ∧ e = t.swap)) := do
    if ok : a ≠ b ∧ ∀ x : Fin i.molecule.atomCount, x.val ∈ i.molecule.ligandsWithLonePair focus →
        (e x).val = LocalizedMarkedTerminalGaugeSwap.swapAtom a b x.val then
      return (⟨a,b,e,aut,origin,ok.1,ok.2⟩ : Exchange i focus)
    none
  if let some t := RingTerminalPair.check? i.molecule focus then
    return ← proposal t.left.val t.right.val (Equiv.swap t.left t.right) t.swap_symmetry (.inl ⟨t,rfl,rfl,rfl⟩)
  let pendant (depth : Nat) := do
    let s ← RingSilentPair.check? i.molecule depth focus
    proposal s.left.node.atom s.right.node.atom s.swap s.graph_exchange (.inr ⟨depth,s,rfl,rfl,rfl⟩)
  (pendant 1).orElse fun _ => pendant 3

private def transported {i focus} (e : Exchange i focus) (n : Nat) :=
  if h : n < i.molecule.atomCount then (e.swap ⟨n,h⟩).val else i.molecule.atomCount

/-- All moved tree nodes are real molecular occurrences. Each corresponding pair
has the same atom record and isotope by the checked graph symmetry. Every atom
in these arms has an independent valence or equivalent-terminal-ligand proof. -/
def SameSite {i focus} (e : Exchange i focus) (a b : Arm i) : Prop :=
  let x := endpoint i a
  let y := endpoint i b
  a.occurrence.val.node.provenance = .realAtom ∧ b.occurrence.val.node.provenance = .realAtom ∧
  x < i.molecule.atomCount ∧ y < i.molecule.atomCount ∧ transported e x = y ∧
  RingSharedArmRefusal.Inactive i.molecule x ∧ RingSharedArmRefusal.Inactive i.molecule y

instance {i f} {e : Exchange i f} {a b} : Decidable (SameSite e a b) := by unfold SameSite; infer_instance

/-- A total correspondence of the two complete *retained* branches. Equalities
at the incoming branch therefore have to survive the original-root path. -/
def Matched {i f} (e : Exchange i f) : Nat → Arm i → Arm i → Prop
  | 0,_,_ => False
  | n+1,a,b => SameSite e a b ∧ ∃ ys, ys.Perm (i.certified.executableLocalizedRerootChildren b) ∧
      List.Forall₂ (Matched e n) (i.certified.executableLocalizedRerootChildren a) ys

private def matchTrees {i f} (e : Exchange i f) : Nat → Arm i → Arm i → Bool
  | 0,_,_ => false
  | n+1,a,b => decide (SameSite e a b) &&
      (i.certified.executableLocalizedRerootChildren b).permutations'.any fun ys =>
        (i.certified.executableLocalizedRerootChildren a).isEqv ys (matchTrees e n)

private theorem isEqv_sound {α : Type} {xs ys : List α} {p : α → α → Bool}
    (ok : xs.isEqv ys p = true) : List.Forall₂ (fun a b => p a b = true) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | exact .nil | contradiction
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys =>
      simp only [List.isEqv,Bool.and_eq_true] at ok
      exact .cons ok.1 (ih ok.2)

private theorem match_sound {i f} (e : Exchange i f) : ∀ n a b,
    matchTrees e n a b = true → Matched e n a b
  | 0,_,_,h => by contradiction
  | n+1,a,b,h => by
    simp only [matchTrees,Bool.and_eq_true] at h
    obtain ⟨sites,kids⟩ := h
    obtain ⟨ys,p,eqn⟩ := List.any_eq_true.mp kids
    exact ⟨of_decide_eq_true sites,ys,List.mem_permutations'.mp p,
      (isEqv_sound eqn).imp fun x y sub => match_sound e n x y sub⟩

private def bound (i : Input) := 2*(i.certified.certified.input.molecule.atomCount+2)+2
private def arms (i : Input) (q : Site i) := RingRetainedAuxiliary.frame i.certified q
private def ids (i : Input) (q : Site i) := (arms i q).map (endpoint i)

/-- Every untied directed pair reads its own original-carrier Rule 1a projections
and must differ there. The matched pair is the only equality on either geometry. -/
private def signs {i f} (e : Exchange i f) (q : Site i) : Option ReferenceFrame.Table :=
  (Promotion.TwoPairPriority.directedPairs (arms i q) (endpoint i)).mapM fun (a,b) => do
    let x := endpoint i a
    let y := endpoint i b
    let order := if (x = e.left ∧ y = e.right) ∨ (x = e.right ∧ y = e.left) then .eq
      else RingRetainedSiblingOrder.compare1a i a b
    guard (order != .eq || (x == e.left && y == e.right) || (x == e.right && y == e.left))
    return ((x,y),(order,order))

structure Certificate (i : Input) (q : Site i) where
  focus : Nat
  reached : q.val.node.current?.map Fin.val = some focus
  real : q.val.node.provenance = .realAtom
  exchange : Exchange i focus
  four : (ids i q).length = 4
  allAtoms : (ids i q).Perm (i.molecule.ligandsWithLonePair focus)
  unique : (ids i q).Nodup
  left : Arm i
  right : Arm i
  leftAt : left ∈ arms i q ∧ endpoint i left = exchange.left
  rightAt : right ∈ arms i q ∧ endpoint i right = exchange.right
  full : Matched exchange (bound i) left right
  table : ReferenceFrame.Table
  assembled : signs exchange q = some table
  refuses : RingSilentPair.Refuses (ids i q) exchange.left exchange.right table

def find? (i : Input) (q : Site i) : Option (Certificate i q) := do
  let ⟨f,reached⟩ ← (q.val.node.current?.map Fin.val).attach
  if fr : q.val.node.provenance = .realAtom ∧ (ids i q).length = 4 ∧
      (ids i q).Perm (i.molecule.ligandsWithLonePair f) ∧ (ids i q).Nodup then
    let e ← attempt? i f
    let ⟨l,lh⟩ ← ((arms i q).find? (fun x => endpoint i x == e.left)).attach
    let ⟨r,rh⟩ ← ((arms i q).find? (fun x => endpoint i x == e.right)).attach
    if matched : matchTrees e (bound i) l r = true then
      let ⟨t,ht⟩ ← (signs e q).attach
      if refusal : RingSilentPair.Refuses (ids i q) e.left e.right t then
        return ⟨f,reached,fr.1,e,fr.2.1,fr.2.2.1,fr.2.2.2,l,r,
          ⟨List.mem_of_find?_eq_some lh,eq_of_beq (List.find?_some (p := fun x => endpoint i x == e.left) lh)⟩,
          ⟨List.mem_of_find?_eq_some rh,eq_of_beq (List.find?_some (p := fun x => endpoint i x == e.right) rh)⟩,
          match_sound e _ _ _ matched,t,ht,refusal⟩
  none

theorem Certificate.no_order {i q} (c : Certificate i q) :
    (ReferenceFrame.marks (ids i q) c.table).length = 2 ∧ ∀ rev,
      ReferenceFrame.orders (ids i q) c.table rev = [] ∧
      ReferenceFrame.orderAt c.table rev c.exchange.left c.exchange.right = some .eq ∧
      ReferenceFrame.orderAt c.table rev c.exchange.right c.exchange.left = some .eq :=
  ⟨c.refuses.1.length_eq,fun rev => (c.refuses.2 rev).2⟩

/-- The two opposite physical hands would describe the same unmarked molecular
configuration. This statement holds on either geometry for every ordering of the
actual incident atom IDs, including when the old parent is one of the exchanged arms. -/
theorem Certificate.swapped_readback {i q} (c : Certificate i q)
    (g : LocalizedGenericMarkedRecalculation.Geometry) (order : List Nat)
    (all : order.Perm (ids i q)) :
    LocalizedGenericMarkedRecalculation.readback? g
        (order.map (LocalizedMarkedTerminalGaugeSwap.swapAtom c.exchange.left c.exchange.right)) =
      (LocalizedGenericMarkedRecalculation.readback? g order).map RS.swap := by
  apply LocalizedMarkedTerminalGaugeSwap.readback_swapAtom g _ _ c.exchange.distinct order
    (all.nodup_iff.mpr c.unique) (all.length_eq.trans c.four)
  · exact all.mem_iff.mpr (c.leftAt.2 ▸ List.mem_map_of_mem c.leftAt.1)
  · exact all.mem_iff.mpr (c.rightAt.2 ▸ List.mem_map_of_mem c.rightAt.1)

theorem Certificate.no_promotion {i q} (c : Certificate i q) :
    (ReferenceFrame.marks (ids i q) c.table).length ∉ [3,4] := by
  rw [c.no_order.1]
  decide

end TetraStereo.Engine.RingRetainedSilentPair
assert_kernel_only TetraStereo.Engine.RingRetainedSilentPair.find?
assert_kernel_only TetraStereo.Engine.RingRetainedSilentPair.Certificate.swapped_readback
assert_kernel_only TetraStereo.Engine.RingRetainedSilentPair.Certificate.no_order
assert_kernel_only TetraStereo.Engine.RingRetainedSilentPair.Certificate.no_promotion
