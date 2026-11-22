import TetraStereo.Engine.RingLocalIsotopeReport

set_option autoImplicit false

namespace TetraStereo.Engine.RingTerminalPair
open OneCenter CertifiedLocalizedCIPInput

abbrev Atom (m : RawMolecule) := Fin m.atomCount

/-- A singly bonded terminal atom at this carbon. The last condition checks
the production ligand list, so a terminal arm cannot supply an auxiliary. -/
def Leaf (m : RawMolecule) (i a : Atom m) : Prop :=
  a.val ∈ m.ligandsWithLonePair i.val ∧ (m.ligandsWithLonePair a.val).length < 4 ∧
    ∀ b : Atom m, m.toMoleculeGraph.bond a b = if b = i then 1 else 0

instance {m i a} : Decidable (Leaf m i a) := by unfold Leaf; infer_instance

/-- A condition on atom records and bonds. It is independent of recursion
depth, geometry, comparison outcomes, and auxiliary publications. -/
def Equivalent (m : RawMolecule) (i a b : Atom m) : Prop :=
  a ≠ b ∧ Leaf m i a ∧ Leaf m i b ∧ m.atoms.get a = m.atoms.get b ∧
    (m.atomMassAt? a).isSome = true ∧ m.atomMassAt? a = m.atomMassAt? b

instance {m i a b} : Decidable (Equivalent m i a b) := by unfold Equivalent; infer_instance

def Focus (m : RawMolecule) (i : Nat) : Prop :=
  (m.atoms[i]?).any (fun a => a.element == .C) = true ∧
    (m.ligandsWithLonePair i).length = 4 ∧ (m.ligandsWithLonePair i).Nodup

instance {m i} : Decidable (Focus m i) := by unfold Focus; infer_instance

structure Certificate (m : RawMolecule) (i : Nat) where
  bound : i < m.atomCount
  focus : Focus m i
  left : Atom m
  right : Atom m
  equivalent : Equivalent m ⟨i,bound⟩ left right

private def candidates (m : RawMolecule) (i : Nat) :=
  let arms := (List.finRange m.atomCount).filter fun a => a.val ∈ m.ligandsWithLonePair i
  arms.flatMap fun a => arms.map fun b => (a,b)

private theorem candidate {m i} {a b : Atom m} (left : a.val ∈ m.ligandsWithLonePair i)
    (right : b.val ∈ m.ligandsWithLonePair i) : (a,b) ∈ candidates m i := by
  simp [candidates,List.mem_flatMap,left,right]

def check? (m : RawMolecule) (i : Nat) : Option (Certificate m i) := do
  if h : i < m.atomCount ∧ Focus m i then
    let test := fun ab : Atom m × Atom m => decide (Equivalent m ⟨i,h.1⟩ ab.1 ab.2)
    let ⟨pair,found⟩ ← ((candidates m i).find? test).attach
    return ⟨h.1,h.2,pair.1,pair.2,of_decide_eq_true (List.find?_some (p := test) found)⟩
  none

theorem check?_isSome_iff (m : RawMolecule) (i : Nat) :
    (check? m i).isSome = true ↔ ∃ h : i < m.atomCount, Focus m i ∧
      ∃ a b : Atom m, Equivalent m ⟨i,h⟩ a b := by
  constructor
  · intro ok
    let cert := (check? m i).get ok
    exact ⟨cert.bound,cert.focus,cert.left,cert.right,cert.equivalent⟩
  · rintro ⟨bound,focus,a,b,eqv⟩
    have h : i < m.atomCount ∧ Focus m i := ⟨bound,focus⟩
    let test := fun ab : Atom m × Atom m => decide (Equivalent m ⟨i,bound⟩ ab.1 ab.2)
    cases found : (candidates m i).find? test with
    | none =>
      have fails := List.find?_eq_none.mp found (a,b) (candidate eqv.2.1.1 eqv.2.2.1.1)
      simp [test,eqv] at fails
    | some pair =>
      dsimp [test] at found
      have att {α : Type} {v : Option α} {x : α} (hx : v = some x) : v.attach = some ⟨x,hx⟩ := by subst v; rfl
      simp [check?,h,att found]

private theorem leaf_data {m i a} (h : Leaf m i a) :
    m.toMoleculeGraph.Adj i a ∧ m.toMoleculeGraph.officialCIPChildren
      (.rootFromEdge i a) = [] := by
  have bond : m.toMoleculeGraph.bond a i = 1 := by simp [h.2.2]
  have neighbors : m.toMoleculeGraph.neighborFinset a = {i} := by
    ext v
    by_cases e : v = i <;> simp [MoleculeGraph.Adj,h.2.2,e]
  constructor
  · exact m.toMoleculeGraph.adj_symm.mp (show m.toMoleculeGraph.Adj a i by
      simp [MoleculeGraph.Adj,bond])
  · simp [MoleculeGraph.officialCIPChildren,MoleculeGraph.officialChildCopies,
      MoleculeGraph.officialNeighborCopies,OfficialCIPNode.rootFromEdge,OfficialCIPNode.parent?,
      OfficialCIPNode.isDuplicateLeaf,OfficialCIPNodeProvenance.isDuplicateLeaf,neighbors,bond]

def Certificate.official {m i} (c : Certificate m i) :
    UniformTerminalArmData m ⟨canonicalCenterRoot i,none⟩ := by
  have distinct := c.equivalent.1
  have ha := c.equivalent.2.1
  have hb := c.equivalent.2.2.1
  have spec := c.equivalent.2.2.2.1
  have mass := c.equivalent.2.2.2.2.2
  have z := congrArg (fun s : AtomSpec => s.element.atomicNumber) spec
  exact ⟨c.bound,c.left,c.right,c.left.isLt,c.right.isLt,ha.1,hb.1,
    fun eqn => distinct (Fin.ext eqn),(leaf_data ha).1,(leaf_data hb).1,
    (leaf_data ha).2,(leaf_data hb).2,
    (atomZAt_eq_toMoleculeGraph_atomZ_of_lt ..).trans (z.trans (toMoleculeGraph_atomZ_eq_atomZAt ..)),
    congrArg (fun v : Option Nat => v.getD 0) mass⟩

theorem Certificate.official_tie {m i} (c : Certificate m i) (fuel : Nat) :
    ∃ trace : CIPTraceCertificate, m.toMoleculeGraph.compareRuleMajorRootsWithFuel
      m.toMoleculeGraph.officialCIPChildren fuel
      (.rootFromEdge ⟨i,c.bound⟩ c.left) (.rootFromEdge ⟨i,c.bound⟩ c.right) .empty .empty =
      some trace ∧ trace.outcome = .eq :=
  uniformTerminalArmData_completedTie m _ c.official fuel

theorem Certificate.no_auxiliary {m i} (c : Certificate m i) (fuel : Nat) (state : OccurrenceAuxState)
    (x y : RawMolecule.CanonicalBranchNode) (hx : x.atom = c.left.val) (hy : y.atom = c.right.val) :
    occurrenceFact? m fuel state x = none ∧ occurrenceFact? m fuel state y = none := by
  exact ⟨occurrenceFact?_eq_none_of_ligandCount_lt_four m fuel state _ (hx ▸ c.equivalent.2.1.2.1),
    occurrenceFact?_eq_none_of_ligandCount_lt_four m fuel state _ (hy ▸ c.equivalent.2.2.1.2.1)⟩

private theorem swap_preserves {α β : Type} [DecidableEq α] {a b : α}
    (f : α → β) (same : f a = f b) (v : α) : f (Equiv.swap a b v) = f v := by
  by_cases left : v = a
  · subst v; simpa only [Equiv.swap_apply_left] using same.symm
  by_cases right : v = b
  · subst v; simpa only [Equiv.swap_apply_right] using same
  rw [Equiv.swap_apply_of_ne_of_ne left right]

/-- The identical atoms can be exchanged while preserving every atom record
and every bond across the molecule, including bonds closing a ring. -/
theorem Certificate.swap_symmetry {m i} (c : Certificate m i) :
    let swap := Equiv.swap c.left c.right
    (∀ a : Atom m, m.atoms.get (swap a) = m.atoms.get a) ∧ swap ∈ m.toMoleculeGraph.Aut := by
  let G := m.toMoleculeGraph
  have specs := swap_preserves m.atoms.get c.equivalent.2.2.2.1
  have masses : G.atomMass c.left = G.atomMass c.right :=
    congrArg (fun v : Option Nat => v.getD 0) c.equivalent.2.2.2.2.2
  have rows (v : Atom m) : G.bond c.left v = G.bond c.right v :=
    (c.equivalent.2.1.2.2 v).trans (c.equivalent.2.2.1.2.2 v).symm
  refine ⟨specs,fun a => congrArg (fun s : AtomSpec => s.element.atomicNumber) (specs a),
    swap_preserves G.atomMass masses,fun a => congrArg AtomSpec.charge (specs a),?_⟩
  intro u v
  let swap := Equiv.swap c.left c.right
  have first := swap_preserves (fun x => G.bond x (swap v)) (rows (swap v)) u
  have cols := (G.bond_symm u c.left).trans ((rows u).trans (G.bond_symm c.right u))
  exact first.trans (swap_preserves (G.bond u) cols v)

/-- At every other focus, the exchange fixes each individual incident
ligand. No remote stereocenter changes its oriented ligand arrangement. -/
theorem Certificate.other_ligands_fixed {m i} (c : Certificate m i)
    {k a : Atom m} (other : k.val ≠ i) (incident : m.toMoleculeGraph.Adj k a) :
    Equiv.swap c.left c.right a = a := by
  have different : k ≠ (⟨i,c.bound⟩ : Atom m) := fun h => other (congrArg Fin.val h)
  have pos := m.toMoleculeGraph.adj_symm.mp incident
  unfold MoleculeGraph.Adj at pos
  apply Equiv.swap_apply_of_ne_of_ne
  · rintro rfl
    simp [c.equivalent.2.1.2.2,different] at pos
  · rintro rfl
    simp [c.equivalent.2.2.1.2.2,different] at pos

end TetraStereo.Engine.RingTerminalPair

assert_kernel_only TetraStereo.Engine.RingTerminalPair.check?_isSome_iff
assert_kernel_only TetraStereo.Engine.RingTerminalPair.Certificate.official_tie
assert_kernel_only TetraStereo.Engine.RingTerminalPair.Certificate.no_auxiliary

assert_kernel_only TetraStereo.Engine.RingTerminalPair.Certificate.swap_symmetry
assert_kernel_only TetraStereo.Engine.RingTerminalPair.Certificate.other_ligands_fixed
