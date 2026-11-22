import TetraStereo.Certificate.CanonicalSphereKey
import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Certificate.CanonicalSphereKey

/-- Follow an outward address in the original digraph. A ring duplicate cannot
be used as the site of a new auxiliary assignment. -/
def occurrence? (m : RawMolecule) : List Nat → Option RawMolecule.CanonicalBranchNode
  | [] => none
  | a :: path => do
    guard (a < m.atomCount)
    path.foldlM (fun n i => (m.canonicalChildren n).find? fun child =>
      child.atom == i && !child.forcedLeaf) (canonicalCenterRoot a)

/-- Atomic-number observations of one rerooted arm, down to the requested
sphere. A real site may be traversed towards its original parent. Ring closure
copies carry the copied Z and end the branch. Exceeding the width fails. -/
def atomicTree (m : RawMolecule) (width : Nat) :
    Nat → CanonicalRerootCursor → Option (HTree Nat)
  | depth,c => do
    let atom ← m.atoms[c.node.atom]?
    let z := atom.element.atomicNumber
    guard (0 < z)
    match depth with
    | 0 => return .node z []
    | n+1 =>
      let cs := c.children m
      guard (cs.length ≤ width)
      return .node z (← cs.mapM (atomicTree m width n))

/-- A constitutional arm retains the molecular cursor and the successful
projection onto its sphere tree. Its key is cached for the ordering pass. -/
structure AtomicArm (m : RawMolecule) (depth : Nat) where
  cursor : CanonicalRerootCursor
  tree : HTree Nat
  molecular : atomicTree m 3 depth cursor = some tree
  key : Key Nat
  exactKey : key = ckey 3 depth tree

private def arm? (m : RawMolecule) (depth : Nat) (c : CanonicalRerootCursor) :
    Option (AtomicArm m depth) :=
  match eq : atomicTree m 3 depth c with
  | none => none
  | some tree => some ⟨c,tree,eq,ckey 3 depth tree,rfl⟩

private def arms? (m : RawMolecule) (depth : Nat) :
    (cs : List CanonicalRerootCursor) →
      Option {rs : List (AtomicArm m depth) // rs.map (·.cursor) = cs}
  | [] => some ⟨[],rfl⟩
  | c :: cs => do
    let rest ← arms? m depth cs
    match eq : atomicTree m 3 depth c with
    | none => none
    | some tree =>
      let row : AtomicArm m depth := ⟨c,tree,eq,ckey 3 depth tree,rfl⟩
      return ⟨row :: rest.val,by simp [row,rest.property]⟩

/-- Every returned order is a permutation of the actual four incident
occurrences and every ordered pair has a strict atomic-number key difference. -/
structure AtomicRanking (m : RawMolecule) (path : List Nat) (depth : Nat) where
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m path = some focus
  four : (occurrenceLigandCursors m focus).length = 4
  arms : List (AtomicArm m depth)
  complete : (arms.map (·.cursor)).Perm (occurrenceLigandCursors m focus)
  strict : arms.Pairwise (fun a b => b.key < a.key)

def atomicRanking? (m : RawMolecule) (path : List Nat) (depth : Nat) :
    Option (AtomicRanking m path depth) := do
  match reached : occurrence? m path with
  | none => none
  | some n =>
    let cs := occurrenceLigandCursors m n
    if h : cs.length = 4 then
      let rs ← arms? m depth cs
      let le (a b : AtomicArm m depth) := b.key ≤ a.key
      let sorted := rs.val.insertionSort le
      if strict : sorted.Pairwise (fun a b => b.key < a.key) then
        return ⟨n,reached,h,sorted,by
          have perm := (List.perm_insertionSort le rs.val).map AtomicArm.cursor
          simpa only [rs.property] using perm,strict⟩
      else none
    else none

def atomicOrder? (m : RawMolecule) (path : List Nat) (depth : Nat) : Option (List Nat) :=
  (atomicRanking? m path depth).map fun r => r.arms.map (·.cursor.node.atom)

/-- Sphere rows in a selected incident arm. Used to expose the exact deciding
atomic numbers at a published occurrence. -/
def ligandRows? (m : RawMolecule) (path : List Nat) (ligand depth : Nat) :
    Option (List (List Nat)) := do
  let n ← occurrence? m path
  let c ← (occurrenceLigandCursors m n).find? (fun c => c.node.atom == ligand)
  let a ← arm? m depth c
  return a.key.map (List.map (fun z => (z : Option Nat).getD 0))

/-- For any two such arms, a strict comparison is equivalent to a first
strictly different atomic number (or an occupied slot versus an empty one),
with every previous sphere and every earlier position in that sphere tied. -/
theorem rule1a_first_difference (m : RawMolecule) (left right : CanonicalRerootCursor)
    (width depth : Nat) {a b : HTree Nat}
    (_left : atomicTree m width depth left = some a)
    (_right : atomicTree m width depth right = some b) :
    ckey width depth b < ckey width depth a ↔ ∃ k slot,
      observation width depth b k slot < observation width depth a k slot ∧
      (∀ j < k, ∀ s, observation width depth b j s = observation width depth a j s) ∧
      (∀ s < slot, observation width depth b k s = observation width depth a k s) :=
  ckey_lt_iff_first_difference width depth b a

/-- Every pair of arms in a computed priority order has an identified
first deciding sphere and position. All preceding observations are equal. -/
theorem AtomicRanking.decisions {m path depth} (ranking : AtomicRanking m path depth) :
    ranking.arms.Pairwise (fun a b => ∃ k slot,
      observation 3 depth b.tree k slot < observation 3 depth a.tree k slot ∧
      (∀ j < k, ∀ s, observation 3 depth b.tree j s = observation 3 depth a.tree j s) ∧
      (∀ s < slot, observation 3 depth b.tree k s = observation 3 depth a.tree k s)) := by
  apply ranking.strict.imp
  intro a b less
  exact (ckey_lt_iff_first_difference 3 depth b.tree a.tree).mp
    (by simpa only [a.exactKey,b.exactKey] using less)

private def rootZ : HTree Nat → Nat | .node z _ => z

/-- Choose a uniform sibling presentation for sharing tree certificates.
Canonical priority is invariant under every sibling permutation, including
unresolved ties in this presentation. -/
def normalizeShape : Nat → HTree Nat → HTree Nat
  | 0,t => t
  | n+1,.node z cs => .node z ((cs.map (normalizeShape n)).insertionSort
      (fun a b => decide (rootZ b ≤ rootZ a)))

theorem ckey_normalizeShape (w d n : Nat) (t : HTree Nat) :
    ckey w d (normalizeShape n t) = ckey w d t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    cases t with
    | node z cs =>
      simp only [normalizeShape]
      rw [ckey_perm w d z (List.perm_insertionSort _ _),ckey_node,ckey_node,List.map_map]
      simp only [Function.comp_def,ih]

/-- Factor a constitutional order into the four addressed molecular trees and
a strict comparison of those trees. Identical tree comparisons may be proved
once and shared by different occurrences. -/
def checkedShapes? (m : RawMolecule) (path order : List Nat) (depth : Nat) :
    Option {shapes : List (HTree Nat) //
      shapes.Pairwise (fun a b => ckey 3 depth b < ckey 3 depth a) →
      ∃ ranking : AtomicRanking m path depth, ranking.arms.map (·.cursor.node.atom) = order} := do
  let ⟨n,reached⟩ ← (occurrence? m path).attach
  let incident := occurrenceLigandCursors m n
  if four : incident.length = 4 then
    let chosen ← order.mapM fun i => incident.find? (fun c => c.node.atom == i)
    if complete : chosen.Perm incident then
      let ⟨rows,cs⟩ ← arms? m depth chosen
      if same : rows.map (·.cursor.node.atom) = order then
        return ⟨rows.map (fun a => normalizeShape depth a.tree),fun strict => by
          have h := List.pairwise_map.mp strict
          have sorted : rows.Pairwise (fun a b => b.key < a.key) := h.imp fun {a b} ab => by
            simpa only [a.exactKey,b.exactKey,ckey_normalizeShape] using ab
          exact ⟨⟨n,reached,four,rows,cs ▸ complete,sorted⟩,same⟩⟩
      else none
    else none
  else none

def atomicAux? (m : RawMolecule) (g : Geometry) (path : List Nat) (depth : Nat) : Option RS :=
  (atomicOrder? m path depth).bind (readback? g)

/-- A Rule-1a-resolved auxiliary has uppercase reflection behavior. -/
theorem atomicAux_mirror (m : RawMolecule) (g : Geometry) (path : List Nat) (depth : Nat) :
    atomicAux? m (mirror g) path depth = (atomicAux? m g path depth).map RS.swap := by
  unfold atomicAux?
  cases atomicOrder? m path depth with
  | none => rfl
  | some order => exact readback_mirror g order

/-- Rule 5 for a single pair of enantiomorphic ligands. The outer two
ligands have already been ordered constitutionally. -/
def pairedOrder? (hi a b lo : Nat) : Option RS → Option RS → Option (List Nat)
  | some .R, some .S => some [hi,a,b,lo]
  | some .S, some .R => some [hi,b,a,lo]
  | _, _ => none

def pairedReading (g : Geometry) (hi a b lo : Nat) (u v : Option RS) : Option RS :=
  (pairedOrder? hi a b lo u v).bind (readback? g)

/-- Reflection interchanges the two auxiliary hands and reverses the spatial
hand. The two reversals cancel, including missing-coordinate and tie cases. -/
theorem pairedReading_mirror (g : Geometry) (hi a b lo : Nat) (u v : Option RS) :
    pairedReading (mirror g) hi a b lo (u.map RS.swap) (v.map RS.swap) =
      pairedReading g hi a b lo u v := by
  rcases u with _ | x <;> rcases v with _ | y <;> try cases x <;> try cases y <;>
    simp [pairedReading,pairedOrder?,RS.swap,readback_mirror,
      LocalizedMarkedTerminalGaugeSwap.readback_swap23 g hi a b lo,Option.map_map,Function.comp_def]
  all_goals cases h : readback? g [hi,a,b,lo] with
    | none => rfl
    | some r => cases r <;> rfl

/-- Composition at the next stereocenter uses separately rerooted Rule-1a
occurrences on the two arms. No supplied hand or sort comparison enters. -/
def fromAux (m : RawMolecule) (g : Geometry) (hi a b lo : Nat)
    (leftPath rightPath : List Nat) (depth : Nat) :=
  pairedReading g hi a b lo (atomicAux? m g leftPath depth) (atomicAux? m g rightPath depth)

theorem fromAux_mirror (m : RawMolecule) (g : Geometry) (hi a b lo : Nat)
    (p q : List Nat) (depth : Nat) :
    fromAux m (mirror g) hi a b lo p q depth = fromAux m g hi a b lo p q depth := by
  simp only [fromAux,atomicAux_mirror,pairedReading_mirror]

end TetraStereo.Engine.RingChemicalPriority
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.rule1a_first_difference
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.atomicAux_mirror
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.fromAux_mirror
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.AtomicRanking.decisions
