import TetraStereo.Engine.RingRetainedSiblingOrder
import TetraStereo.Engine.RingTerminalPair
import TetraStereo.Engine.RingReferenceFrame

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedTerminalClass
open OneCenter CertifiedLocalizedCIPInput RingChemicalPriority
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)

abbrev Atom (i : Input) := Fin i.molecule.atomCount

private def arms (i : Input) (q : Site i) := RingRetainedAuxiliary.frame i.certified q
private def atomId? {i : Input} (a : Arm i) := a.occurrence.val.node.current?.map Fin.val

/-- Both terminal ligands belong to the actual retained frame. Each source
node is a real atom with no outgoing edge after removal of the focus. -/
structure Pair (i : Input) (q : Site i) (focus a b : Atom i) where
  raw : RingTerminalPair.Certificate i.molecule focus.val
  leftId : raw.left = a
  rightId : raw.right = b
  left : Arm i
  right : Arm i
  leftAt : left ∈ arms i q ∧ atomId? left = some a.val
  rightAt : right ∈ arms i q ∧ atomId? right = some b.val
  leaves : left.occurrence.val.node.provenance = .realAtom ∧ right.occurrence.val.node.provenance = .realAtom ∧
    i.certified.executableLocalizedRerootChildren left = [] ∧ i.certified.executableLocalizedRerootChildren right = []

theorem Pair.distinct {i q f a b} (p : Pair i q f a b) : a ≠ b := by
  exact fun eqn => p.raw.equivalent.1 (p.leftId.trans (eqn.trans p.rightId.symm))

/-- A molecular exchange preserves both real terminal sightings and every
atom record and bond. Any reference assignment constant on this pair survives
the exchange, including a mark carried from an earlier comparison. -/
theorem Pair.exchange {i q f a b} (p : Pair i q f a b) {α : Type} (mark : Atom i → α)
    (same : mark a = mark b) :
    (∀ x, i.molecule.atoms.get (Equiv.swap a b x) = i.molecule.atoms.get x) ∧
    Equiv.swap a b ∈ i.molecule.toMoleculeGraph.Aut ∧ ∀ x, mark (Equiv.swap a b x) = mark x := by
  have aut := p.raw.swap_symmetry
  rw [p.leftId,p.rightId] at aut
  refine ⟨aut.1,aut.2,?_⟩
  intro x
  by_cases l : x = a
  · subst x; simpa using same.symm
  by_cases r : x = b
  · subst x; simpa using same
  rw [Equiv.swap_apply_of_ne_of_ne l r]

private def pair? (i : Input) (q : Site i) (f a b : Atom i) (focus : RingTerminalPair.Focus i.molecule f.val) :
    Option (Pair i q f a b) := do
  if eqv : RingTerminalPair.Equivalent i.molecule f a b then
    let ⟨l,hl⟩ ← ((arms i q).find? fun x => atomId? x == some a.val).attach
    let ⟨r,hr⟩ ← ((arms i q).find? fun x => atomId? x == some b.val).attach
    if leaves : l.occurrence.val.node.provenance = .realAtom ∧ r.occurrence.val.node.provenance = .realAtom ∧
        i.certified.executableLocalizedRerootChildren l = [] ∧ i.certified.executableLocalizedRerootChildren r = [] then
      let cert : RingTerminalPair.Certificate i.molecule f.val := ⟨f.isLt,focus,a,b,eqv⟩
      return ⟨cert,rfl,rfl,l,r,⟨List.mem_of_find?_eq_some hl,
        eq_of_beq (List.find?_some (p := fun x => atomId? x == some a.val) hl)⟩,
        ⟨List.mem_of_find?_eq_some hr,eq_of_beq (List.find?_some (p := fun x => atomId? x == some b.val) hr)⟩,leaves⟩
  none

/-- Three exchangeable terminal substituents at the actual carbon. The fourth
may be different or may be another member of the same class. -/
structure Certificate (i : Input) (q : Site i) where
  focus : Atom i
  real : q.val.node.provenance = .realAtom
  atFocus : q.val.node.current?.map Fin.val = some focus.val
  ids : List Nat
  actual : (arms i q).mapM atomId? = some ids
  physical : ids.Perm (i.molecule.ligandsWithLonePair focus.val)
  a : Atom i
  b : Atom i
  c : Atom i
  ab : Pair i q focus a b
  ac : Pair i q focus a c
  bc : Pair i q focus b c

def find? (i : Input) (q : Site i) : Option (Certificate i q) := do
  let ⟨k,hk⟩ ← (q.val.node.current?.map Fin.val).attach
  if bound : k < i.molecule.atomCount then
    let f : Atom i := ⟨k,bound⟩
    let ⟨ns,actual⟩ ← ((arms i q).mapM atomId?).attach
    if source : q.val.node.provenance = .realAtom ∧ RingTerminalPair.Focus i.molecule k ∧
        ns.Perm (i.molecule.ligandsWithLonePair k) then
      let candidates := (List.finRange i.molecule.atomCount).filter fun a => a.val ∈ ns
      return ← candidates.findSome? fun a => candidates.findSome? fun b => do
        guard (a < b)
        let ab ← pair? i q f a b source.2.1
        candidates.findSome? fun c => do
          guard (b < c)
          let ac ← pair? i q f a c source.2.1
          let bc ← pair? i q f b c source.2.1
          return ⟨f,source.1,hk,ns,actual,source.2.2,a,b,c,ab,ac,bc⟩
  none

/-- For every chosen atom one molecular terminal transposition survives. The
same conclusion holds with the mark off the original four-ligand frame. -/
theorem Certificate.surviving {i q} (t : Certificate i q) (mark : Atom i) :
    ∃ a b : Atom i, Nonempty (Pair i q t.focus a b) ∧ a ≠ mark ∧ b ≠ mark := by
  by_cases sameA : t.a = mark
  · subst mark
    exact ⟨t.b,t.c,⟨t.bc⟩,Ne.symm t.ab.distinct,Ne.symm t.ac.distinct⟩
  by_cases sameB : t.b = mark
  · subst mark
    exact ⟨t.a,t.c,⟨t.ac⟩,sameA,Ne.symm t.bc.distinct⟩
  exact ⟨t.a,t.b,⟨t.ab⟩,sameA,sameB⟩

/-- Even after fixing a reference atom, the full atom-and-bond symmetry
exchanges two of the actual incident ligands and leaves the reference fixed. -/
theorem Certificate.fixed_exchange {i q} (t : Certificate i q) (mark : Atom i) :
    ∃ a b : Atom i, Nonempty (Pair i q t.focus a b) ∧ a ≠ b ∧ Equiv.swap a b mark = mark ∧
      Equiv.swap a b ∈ i.molecule.toMoleculeGraph.Aut := by
  obtain ⟨a,b,⟨p⟩,ha,hb⟩ := t.surviving mark
  exact ⟨a,b,⟨p⟩,p.distinct,Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm,
    (p.exchange (fun _ => ()) rfl).2.1⟩

private theorem either_before {α : Type} {p : α → α → Prop} {xs : List α}
    (order : xs.Pairwise p) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (ne : a ≠ b) : p a b ∨ p b a := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    obtain ⟨first,tail⟩ := List.pairwise_cons.mp order
    rcases List.mem_cons.mp ha with rfl | ma
    · rcases List.mem_cons.mp hb with rfl | mb
      · exact (ne rfl).elim
      · exact Or.inl (first _ mb)
    rcases List.mem_cons.mp hb with rfl | mb
    · exact Or.inr (first _ ma)
    · exact ih tail ma mb

/-- No strict order can extend priorities invariant under the surviving
exchange. Applied to either geometry, this also rules out an assigned hand
in every marked trial independently of how the other comparisons resolve. -/
theorem Certificate.no_order {i q} (t : Certificate i q) (mark : Atom i)
    (higher : Atom i → Atom i → Prop)
    (respects : ∀ a b, Pair i q t.focus a b → a ≠ mark → b ≠ mark → ¬higher a b ∧ ¬higher b a)
    (order : List (Atom i)) (all : (order.map Fin.val).Perm t.ids) : ¬order.Pairwise higher := by
  obtain ⟨a,b,⟨p⟩,ha,hb⟩ := t.surviving mark
  have mem (x : Atom i) (hm : x.val ∈ i.molecule.ligandsWithLonePair t.focus.val) : x ∈ order := by
    obtain ⟨v,hv,eqn⟩ := List.mem_map.mp ((all.trans t.physical).mem_iff.mpr hm)
    exact Fin.ext eqn ▸ hv
  have e := p.raw.equivalent
  rw [p.leftId,p.rightId] at e
  intro ranked
  exact (either_before ranked (mem a e.2.1.1) (mem b e.2.2.1.1) p.distinct).elim
    (respects a b p ha hb).1 (respects a b p ha hb).2

/-- Source observations for a real, singly bonded terminal atom. It has no
duplicate distance, descendant or auxiliary-bearing tetrahedral frame. -/
def terminalWord (i : Input) (mark : Option (Atom i)) (x : Atom i) : Nat × Nat × Nat :=
  ((i.molecule.atoms.get x).element.atomicNumber,(i.molecule.atomMassAt? x).getD 0,if some x = mark then 1 else 0)

theorem Pair.unmarked_words {i q f a b} (p : Pair i q f a b) (mark : Option (Atom i))
    (ha : some a ≠ mark) (hb : some b ≠ mark) : terminalWord i mark a = terminalWord i mark b := by
  have e := p.raw.equivalent
  rw [p.leftId,p.rightId] at e
  simp only [terminalWord,if_neg ha,if_neg hb,e.2.2.2.1,e.2.2.2.2.2]

/-- Compare two real terminal ligands by their molecular observations. Every
other pair may be completed by an arbitrary priority relation. -/
def higher (i : Input) (f : Atom i) (mark : Option (Atom i)) (remaining : Atom i → Atom i → Prop) (a b : Atom i) :=
  if RingTerminalPair.Leaf i.molecule f a ∧ RingTerminalPair.Leaf i.molecule f b then
    terminalWord i mark b < terminalWord i mark a else remaining a b

/-- All single-reference trials refuse for this class. Both geometries and
every possible completion on the other edges have no strict ligand order. -/
theorem Certificate.no_completed_order {i q} (t : Certificate i q) (mark : Option (Atom i))
    (remaining : Atom i → Atom i → Prop) (order : List (Atom i)) (all : (order.map Fin.val).Perm t.ids) :
    ¬order.Pairwise (higher i t.focus mark remaining) := by
  apply t.no_order (mark.getD t.focus) _ _ order all
  intro a b p ha hb
  have e := p.raw.equivalent
  rw [p.leftId,p.rightId] at e
  have untouched (x : Atom i) (h : x ≠ mark.getD t.focus) : some x ≠ mark := by
    rintro rfl
    exact h rfl
  have same := p.unmarked_words mark (untouched a ha) (untouched b hb)
  simp [higher,e.2.1,e.2.2.1,same]

end TetraStereo.Engine.RingRetainedTerminalClass
assert_kernel_only TetraStereo.Engine.RingRetainedTerminalClass.find?
assert_kernel_only TetraStereo.Engine.RingRetainedTerminalClass.Certificate.fixed_exchange
assert_kernel_only TetraStereo.Engine.RingRetainedTerminalClass.Certificate.no_order
assert_kernel_only TetraStereo.Engine.RingRetainedTerminalClass.Certificate.no_completed_order
