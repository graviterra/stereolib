import TetraStereo.Engine.RingReferenceFrame

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.CursorTie
open OneCenter CertifiedLocalizedCIPInput Recursive
open InventoryPriority (Entries)

/-- Keep the normalized atom, mass, unit class and both stereochemical tags.
Rule 1b reads the original depth of a duplicate's origin. Original depths of
real vertices supply provenance but do not distinguish two real atoms. -/
private def normalize (o : EarlierStereoMatch.Observation) :=
  { o with constitutional.prior := DuplicatePriority.originalView o.constitutional.prior }

def observe? (m : RawMolecule) (p : List Nat) (es : Entries) (c : CanonicalRerootCursor) :
    Option EarlierStereoMatch.Observation := do
  let o ← EarlierStereoMatch.onSide? m p .five false es c
  return normalize o

/-- The equality test still reads the source atom and its mass at the
actual retained vertex. In particular it does not erase duplicate origins. -/
theorem observe?_source {m p es c o} (read : observe? m p es c = some o) :
    ∃ src : IsotopePriority.FullObservation,
      IsotopePriority.fullObservation? m p c = some src ∧
      o.constitutional.prior = DuplicatePriority.originalView src.prior ∧
      o.constitutional.atom = src.atom ∧ o.constitutional.sourceMass = src.sourceMass ∧
      UnitClasses.classAt? m es ⟨c,[c.node],[],true⟩ = some o.unitClass ∧
      o.stereo = EarlierStereoMatch.tags .five false (es.lookup c.node.history.reverse).join := by
  cases h : EarlierStereoMatch.onSide? m p .five false es c with
  | none => simp [observe?,h] at read
  | some row =>
    obtain rfl : normalize row = o := by simpa [observe?,h] using read
    obtain ⟨source,unit,tag⟩ := EarlierStereoMatch.onSide?_sound h
    exact ⟨_,source,rfl,rfl,rfl,unit,tag⟩

/-- Earlier-rule separation at a pair other than the two putative tied
ligands. Both keys must be present and lexicographically distinct. -/
private def separated (m : RawMolecule) (p : List Nat) (depth a b : Nat) : Bool :=
  match ligandRows? m p a depth, ligandRows? m p b depth with
  | some x,some y => x != y
  | _,_ => false

private def otherPairs (m : RawMolecule) (p : List Nat) (depth : Nat) (ids : List Nat) (i j : Nat) : Bool :=
  ids.all fun a => ids.all fun b =>
    a == b || (a == i && b == j) || (a == j && b == i) || separated m p depth a b

/-- Only one pair can be tied. Its complete retained branches agree on every
earlier observation in the fixed digraph, including published auxiliary
readings on both geometries; one branch enters the original parent. -/
structure SinglePair (m : RawMolecule) (p : List Nat) (depth : Nat) (es : Entries) where
  domain : saturatedWithHalogens m = true
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p = some focus
  carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true
  left : CanonicalRerootCursor
  right : CanonicalRerootCursor
  leftAt : left ∈ occurrenceLigandCursors m focus
  rightAt : right ∈ occurrenceLigandCursors m focus
  incoming : canonicalOriginalParent? focus = some left.node
  distinct : left.node.atom ≠ right.node.atom
  four : (occurrenceLigandCursors m focus).length = 4
  unique : ((occurrenceLigandCursors m focus).map (·.node.atom)).Nodup
  earlier : otherPairs m p depth ((occurrenceLigandCursors m focus).map (·.node.atom))
    left.node.atom right.node.atom = true
  matched : IsotopePriority.TreesMatch m (observe? m p es) (IsotopePriority.budget m+1) left right

def singlePair? (m : RawMolecule) (p : List Nat) (depth : Nat) (es : Entries) : Option (SinglePair m p depth es) := do
  let ⟨focus,reached⟩ ← (occurrence? m p).attach
  let ⟨parent,up⟩ ← (canonicalOriginalParent? focus).attach
  let cs := occurrenceLigandCursors m focus
  let ids := cs.map (·.node.atom)
  if evidence : saturatedWithHalogens m = true ∧ (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true ∧
      cs.length = 4 ∧ ids.Nodup then
    let ⟨l,found⟩ ← (cs.find? fun (c : CanonicalRerootCursor) => c.node == parent).attach
    have same : l.node = parent := eq_of_beq (List.find?_some (p := fun (c : CanonicalRerootCursor) => c.node == parent) found)
    return ← cs.attach.findSome? fun r => do
      if ok : l.node.atom ≠ r.val.node.atom ∧ otherPairs m p depth ids l.node.atom r.val.node.atom = true then
        if eqn : IsotopePriority.treesMatch m (observe? m p es) (IsotopePriority.budget m+1) l r.val = true then
          return ⟨evidence.1,focus,reached,evidence.2.1,l,r.val,List.mem_of_find?_eq_some found,r.property,
            same.symm ▸ up,ok.1,evidence.2.2.1,evidence.2.2.2,ok.2,IsotopePriority.treesMatch_sound eqn⟩
      none
  none

theorem SinglePair.other_strict {m p depth es} (s : SinglePair m p depth es) {a b}
    (aAt : a ∈ (occurrenceLigandCursors m s.focus).map (·.node.atom))
    (bAt : b ∈ (occurrenceLigandCursors m s.focus).map (·.node.atom))
    (distinct : a ≠ b)
    (forward : ¬ (a = s.left.node.atom ∧ b = s.right.node.atom))
    (reverse : ¬ (a = s.right.node.atom ∧ b = s.left.node.atom)) :
    ∃ x y, ligandRows? m p a depth = some x ∧ ligandRows? m p b depth = some y ∧
      (x < y ∨ y < x) := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp s.earlier a aAt) b bAt
  have yes : separated m p depth a b = true := by
    simpa [Bool.or_eq_true,Bool.and_eq_true,distinct,forward,reverse] using h
  cases hx : ligandRows? m p a depth <;> cases hy : ligandRows? m p b depth <;> simp_all [separated]

theorem SinglePair.equal_observer {m p depth es} (s : SinglePair m p depth es) {α : Type}
    (read : Nat → CanonicalRerootCursor → α)
    (combine : EarlierStereoMatch.Observation → List α → α)
    (node : ∀ n c o, observe? m p es c = some o →
      read (n+1) c = combine o ((c.children m).map (read n)))
    (perm : ∀ o {xs ys : List α}, xs.Perm ys → combine o xs = combine o ys) :
    read (IsotopePriority.budget m+1) s.left = read (IsotopePriority.budget m+1) s.right :=
  IsotopePriority.TreesMatch.observer_eq s.matched read combine node perm

end TetraStereo.Engine.RingChemicalPriority.CursorTie

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorTie.observe?_source
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorTie.SinglePair.other_strict
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorTie.SinglePair.equal_observer
