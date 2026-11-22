import TetraStereo.Engine.RingTerminalPair
import TetraStereo.Engine.RingCursorTie

set_option autoImplicit false

namespace TetraStereo.Engine.RingSilentPair
open OneCenter CertifiedLocalizedCIPInput RingChemicalPriority LocalizedGenericMarkedRecalculation
open LocalizedMarkedTerminalGaugeSwap

abbrev Atom (m : RawMolecule) := Fin m.atomCount
abbrev Cursor := CanonicalRerootCursor

/-- These are all, and only, the real singly bonded neighbors of the atom. -/
def Neighbors (m : RawMolecule) (i : Nat) (ns : List Nat) : Prop :=
  ns.Nodup ∧ (∀ a ∈ ns, a < m.atomCount) ∧
    ∀ b : Atom m, m.bondOrder i b = if b.val ∈ ns then 1 else 0

instance {m i ns} : Decidable (Neighbors m i ns) := by unfold Neighbors; infer_instance

private def plain (m : RawMolecule) (i : Nat) (e : Element) : Bool :=
  (m.atomAt? i).any fun a => a.element == e && a.charge == 0 && !a.aromatic &&
    a.explicitHydrogens == 0 && a.tetrahedral?.isNone

/-- Every moved atom is a neutral saturated C or terminal H. At a carbon
we require an actual certificate for two identical singly bonded leaves.
The predecessor and the actual cursor children exhaust its molecular bonds. -/
def SilentSite (m : RawMolecule) (c : Cursor) : Prop :=
  let i := c.node.atom
  let ns := c.node.parent :: (c.children m).map (·.node.atom)
  c.node.provenance = .realAtom ∧ i < m.atomCount ∧
    c.previous?.map (·.atom) = some c.node.parent ∧ Neighbors m i ns ∧
    ((plain m i .H = true ∧ ns.length = 1 ∧ (m.ligandsWithLonePair i).length < 4) ∨
     (plain m i .C = true ∧ ns.length = 4 ∧ (RingTerminalPair.check? m i).isSome = true))

instance {m c} : Decidable (SilentSite m c) := by unfold SilentSite; infer_instance

/-- Enumerate the complete actual branch. Exhausted fuel gives no inventory. -/
def walk? (m : RawMolecule) : Nat → Cursor → Option (List Cursor)
  | 0,_ => none
  | n+1,c => do return c :: (← (c.children m).mapM (walk? m n)).flatten

/-- Match the two branches recursively, trying only permutations of siblings.
The final candidate must separately preserve bonds and labels on the whole graph. -/
private def align? (m : RawMolecule) : Nat → Cursor → Cursor → Option (List (Nat × Nat))
  | 0,_,_ => none
  | n+1,a,b => do
    guard (m.atoms[a.node.atom]? == m.atoms[b.node.atom]?)
    let left := a.children m
    let right := b.children m
    guard (left.length == right.length)
    let below ← right.permutations'.findSome? fun order =>
      (left.zip order).mapM fun (x,y) => align? m n x y
    return (a.node.atom,b.node.atom) :: below.flatten

private def exchange (m : RawMolecule) (pairs : List (Nat × Nat)) : Equiv.Perm (Atom m) :=
  pairs.foldr (fun (a,b) rest =>
    if h : a < m.atomCount ∧ b < m.atomCount then
      (Equiv.swap (⟨a,h.1⟩ : Atom m) ⟨b,h.2⟩).trans rest
    else rest) (Equiv.refl _)

private def ids (cs : List Cursor) := cs.map (·.node.atom)

/-- An independent atom permutation exchanges precisely the two incident
ligands, preserves every atom record and bond, and fixes every incident
atom at each remote site outside the two silent branches. -/
def Symmetry (m : RawMolecule) (i a b : Nat) (incident support : List Nat)
    (e : Equiv.Perm (Atom m)) : Prop :=
  (∀ x : Atom m, m.atoms.get (e x) = m.atoms.get x ∧ m.toMoleculeGraph.atomMass (e x) = m.toMoleculeGraph.atomMass x) ∧
  (∀ x y : Atom m, m.toMoleculeGraph.bond (e x) (e y) = m.toMoleculeGraph.bond x y) ∧
  (∀ x : Atom m, x.val ∉ support → e x = x) ∧
  (∀ x : Atom m, x.val ∈ incident → (e x).val = swapAtom a b x.val) ∧
  (∀ k x : Atom m, k.val ≠ i → k.val ∉ support → m.toMoleculeGraph.Adj k x → e x = x)

instance {m i a b incident support e} : Decidable (Symmetry m i a b incident support e) := by
  unfold Symmetry
  infer_instance

private def strict (m : RawMolecule) (i depth a b : Nat) : Bool :=
  match ligandRows? m [i] a depth, ligandRows? m [i] b depth with
  | some x,some y => x != y
  | _,_ => false

def OthersStrict (m : RawMolecule) (i depth : Nat) (arms : List Nat) (a b : Nat) : Prop :=
  ∀ x ∈ arms, ∀ y ∈ arms, x ≠ y → ¬ (x = a ∧ y = b) → ¬ (x = b ∧ y = a) →
    strict m i depth x y = true

instance {m i depth arms a b} : Decidable (OthersStrict m i depth arms a b) := by
  unfold OthersStrict
  infer_instance

/-- Construct both geometric comparison signs from the same molecular data.
The exchanged pair is equal. Each other comparison reads two strict Rule 1a keys. -/
def ordinary? (m : RawMolecule) (depth i : Nat) (arms : List Nat) (a b : Nat) : Option ReferenceFrame.Table :=
  (Promotion.TwoPairPriority.directedPairs arms id).mapM fun (x,y) => do
    let sign ← if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then some Ordering.eq else do
      let l ← ligandRows? m [i] x depth
      let r ← ligandRows? m [i] y depth
      if l < r then some .lt else if r < l then some .gt else none
    return ((x,y),(sign,sign))

def Refuses (arms : List Nat) (a b : Nat) (t : ReferenceFrame.Table) : Prop :=
  (ReferenceFrame.marks arms t).Perm [a,b] ∧ ∀ rev : Bool,
    ReferenceFrame.coherent arms t rev = true ∧ ReferenceFrame.orders arms t rev = [] ∧
    ReferenceFrame.orderAt t rev a b = some .eq ∧ ReferenceFrame.orderAt t rev b a = some .eq

instance {arms a b t} : Decidable (Refuses arms a b t) := by unfold Refuses; infer_instance

structure Certificate (m : RawMolecule) (depth i : Nat) where
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m [i] = some focus
  center : (m.atoms[i]?).any (fun a => a.element == .C) = true
  bounded : i < m.atomCount
  four : (ids (occurrenceLigandCursors m focus)).length = 4
  neighbors : Neighbors m i (ids (occurrenceLigandCursors m focus))
  left : Cursor
  right : Cursor
  leftAt : left ∈ occurrenceLigandCursors m focus
  rightAt : right ∈ occurrenceLigandCursors m focus
  distinct : left.node.atom ≠ right.node.atom
  attached : left.node.parent = i ∧ right.node.parent = i
  ls : List Cursor
  rs : List Cursor
  full : walk? m (IsotopePriority.budget m+1) left = some ls ∧
    walk? m (IsotopePriority.budget m+1) right = some rs
  acyclic : (ids (ls ++ rs)).Nodup ∧ i ∉ ids (ls ++ rs)
  silent : ∀ site ∈ ls ++ rs, SilentSite m site
  empty : carbonSites m (m.atomCount+1) left.node = some [] ∧ carbonSites m (m.atomCount+1) right.node = some []
  tied : IsotopePriority.TreesMatch m (CursorTie.observe? m [i] []) (IsotopePriority.budget m+1) left right
  other : OthersStrict m i depth (ids (occurrenceLigandCursors m focus)) left.node.atom right.node.atom
  table : ReferenceFrame.Table
  assembled : ordinary? m depth i (ids (occurrenceLigandCursors m focus)) left.node.atom right.node.atom = some table
  refuses : Refuses (ids (occurrenceLigandCursors m focus)) left.node.atom right.node.atom table
  swap : Equiv.Perm (Atom m)
  symmetry : Symmetry m i left.node.atom right.node.atom (ids (occurrenceLigandCursors m focus)) (ids (ls ++ rs)) swap

def check? (m : RawMolecule) (depth i : Nat) : Option (Certificate m depth i) := do
  let ⟨focus,reached⟩ ← (occurrence? m [i]).attach
  let cs := occurrenceLigandCursors m focus
  if root : (m.atoms[i]?).any (fun a => a.element == .C) = true ∧ i < m.atomCount ∧
      (ids cs).length = 4 ∧ Neighbors m i (ids cs) then
    return ← cs.attach.findSome? fun l => cs.attach.findSome? fun r => do
      let a := l.val.node.atom
      let b := r.val.node.atom
      if pair : a < b ∧ l.val.node.parent = i ∧ r.val.node.parent = i then
        if other : OthersStrict m i depth (ids cs) a b then
          if empty : carbonSites m (m.atomCount+1) l.val.node = some [] ∧ carbonSites m (m.atomCount+1) r.val.node = some [] then
            let limit := IsotopePriority.budget m+1
            let ⟨ls,left⟩ ← (walk? m limit l.val).attach
            let ⟨rs,right⟩ ← (walk? m limit r.val).attach
            if localData : (ids (ls ++ rs)).Nodup ∧ i ∉ ids (ls ++ rs) ∧ ∀ site ∈ ls ++ rs, SilentSite m site then
              if trees : IsotopePriority.treesMatch m (CursorTie.observe? m [i] []) limit l.val r.val = true then
                let pairing ← align? m limit l.val r.val
                let e := exchange m pairing
                if symm : Symmetry m i a b (ids cs) (ids (ls ++ rs)) e then
                  let ⟨table,assembled⟩ ← (ordinary? m depth i (ids cs) a b).attach
                  if refuses : Refuses (ids cs) a b table then
                    return ⟨focus,reached,root.1,root.2.1,root.2.2.1,root.2.2.2,l.val,r.val,l.property,r.property,
                      Nat.ne_of_lt pair.1,pair.2,ls,rs,⟨left,right⟩,⟨localData.1,localData.2.1⟩,localData.2.2,empty,
                      IsotopePriority.treesMatch_sound trees,other,table,assembled,refuses,e,symm⟩
      none
  none

theorem Certificate.graph_exchange {m depth i} (c : Certificate m depth i) :
    (∀ x : Atom m, m.atoms.get (c.swap x) = m.atoms.get x) ∧ c.swap ∈ m.toMoleculeGraph.Aut :=
  ⟨fun x => (c.symmetry.1 x).1,fun x => congrArg (fun a : AtomSpec => a.element.atomicNumber) (c.symmetry.1 x).1,
    fun x => (c.symmetry.1 x).2,fun x => congrArg AtomSpec.charge (c.symmetry.1 x).1,c.symmetry.2.1⟩

theorem Certificate.site_nonbearing {m depth i} (c : Certificate m depth i) {site}
    (inside : site ∈ c.ls ++ c.rs) :
    (∀ fuel state, occurrenceFact? m fuel state site.node = none) ∨
      ∃ t : RingTerminalPair.Certificate m site.node.atom, RingTerminalPair.check? m site.node.atom = some t := by
  rcases (c.silent site inside).2.2.2.2 with h | h
  · exact Or.inl (fun fuel state => occurrenceFact?_eq_none_of_ligandCount_lt_four m fuel state site.node h.2.2)
  · exact Or.inr (Option.isSome_iff_exists.mp h.2.2)

private theorem plain_record {m : RawMolecule} {i e} (ok : plain m i e = true) :
    ∃ a, m.atomAt? i = some a ∧ a.tetrahedral? = none := by
  obtain ⟨a,read,data⟩ := (Option.any_eq_true _ _).mp ok
  refine ⟨a,read,Option.isNone_iff_eq_none.mp ?_⟩
  simp only [Bool.and_eq_true] at data
  tauto

/-- At every actual occurrence of either branch the annotated production
auxiliary reader returns no fact at every fuel and in every publication state. -/
theorem Certificate.all_occurrences_unpublished {m depth i} (c : Certificate m depth i)
    {site} (inside : site ∈ c.ls ++ c.rs) (fuel : Nat) (state : OccurrenceAuxState) :
    occurrenceFact? m fuel state site.node = none := by
  rcases (c.silent site inside).2.2.2.2 with h | h
  all_goals obtain ⟨a,read,untagged⟩ := plain_record h.1
  all_goals exact occurrenceFact?_eq_none_of_tetrahedral?_eq_none m fuel state site.node a read untagged

theorem Certificate.other_strict {m depth i} (c : Certificate m depth i) {x y}
    (hx : x ∈ ids (occurrenceLigandCursors m c.focus)) (hy : y ∈ ids (occurrenceLigandCursors m c.focus))
    (ne : x ≠ y) (fwd : ¬ (x = c.left.node.atom ∧ y = c.right.node.atom))
    (rev : ¬ (x = c.right.node.atom ∧ y = c.left.node.atom)) :
    ∃ a b, ligandRows? m [i] x depth = some a ∧ ligandRows? m [i] y depth = some b ∧ (a < b ∨ b < a) := by
  have h := c.other x hx y hy ne fwd rev
  cases ha : ligandRows? m [i] x depth <;> cases hb : ligandRows? m [i] y depth <;> simp_all [strict]

/-- On any geometry the molecular exchange reverses a nondegenerate hand
at the target. The same conclusion applies separately to its reflection. -/
theorem Certificate.readback_exchange {m depth i} (c : Certificate m depth i) (g : Geometry)
    {order : List Nat} (all : order.Perm (ids (occurrenceLigandCursors m c.focus))) :
    readback? g (order.map (swapAtom c.left.node.atom c.right.node.atom)) = (readback? g order).map RS.swap :=
  readback_swapAtom g _ _ c.distinct order (all.nodup_iff.mpr c.neighbors.1)
    (all.length_eq.trans c.four) (all.mem_iff.mpr (List.mem_map_of_mem c.leftAt))
    (all.mem_iff.mpr (List.mem_map_of_mem c.rightAt))

/-- Neither geometry has a strict order, and exactly two ligands are
eligible for a mark. The ordinary refusal precedes the three-mark threshold. -/
theorem Certificate.refusal {m depth i} (c : Certificate m depth i) :
    let arms := ids (occurrenceLigandCursors m c.focus)
    (ReferenceFrame.marks arms c.table).length = 2 ∧ ∀ rev,
      ReferenceFrame.orders arms c.table rev = [] ∧
      ReferenceFrame.orderAt c.table rev c.left.node.atom c.right.node.atom = some .eq ∧
      ReferenceFrame.orderAt c.table rev c.right.node.atom c.left.node.atom = some .eq :=
  ⟨c.refuses.1.length_eq,fun rev => (c.refuses.2 rev).2⟩

end TetraStereo.Engine.RingSilentPair

assert_kernel_only TetraStereo.Engine.RingSilentPair.check?
assert_kernel_only TetraStereo.Engine.RingSilentPair.Certificate.graph_exchange
assert_kernel_only TetraStereo.Engine.RingSilentPair.Certificate.site_nonbearing
assert_kernel_only TetraStereo.Engine.RingSilentPair.Certificate.other_strict
assert_kernel_only TetraStereo.Engine.RingSilentPair.Certificate.readback_exchange
assert_kernel_only TetraStereo.Engine.RingSilentPair.Certificate.refusal
assert_kernel_only TetraStereo.Engine.RingSilentPair.Certificate.all_occurrences_unpublished
