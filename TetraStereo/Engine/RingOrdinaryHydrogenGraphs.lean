import TetraStereo.Engine.RingHydrogenCompletion
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum

/-! Ordinary terminal hydrogen fibers over a fixed heavy-atom graph. -/
set_option autoImplicit false

namespace TetraStereo.OneCenter.OrdinaryHydrogenSpellings
open TetraStereo.Engine.RingHydrogenCompletion (heavyCore)

/-- Left tags identify the ordered retained core; right tags identify a terminal H's parent. -/
def bondTable {k : Nat} (coreBond : Fin k → Fin k → Nat) :
    (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → Nat
  | .inl p, .inl q => coreBond p q
  | .inl p, .inr q => if p = q then 1 else 0
  | .inr p, .inl q => if p = q then 1 else 0
  | .inr _, .inr _ => 0

def atomTable {k : Nat} (coreAtom : Fin k → AtomSpec) : (Fin k ⊕ Fin k) → AtomSpec
  | .inl p => coreAtom p
  | .inr _ => AtomSpec.aliphatic Element.H

/-- A completed raw graph with an arbitrarily interspersed ordered retained core.
Inline H counts are erased using production `heavyCore`; isotope fields remain exact.
Isotopically labeled atoms may be retained in the core. Every noncore vertex is ordinary, neutral, nonaromatic, unlabeled H, with one single bond
exactly to its tagged parent. This certifies local records and bonds, not an isomorphism. -/
structure Completion {k : Nat} (coreAtom : Fin k → AtomSpec)
    (coreBond : Fin k → Fin k → Nat) where
  molecule : RawMolecule
  core : Fin k ↪ Fin molecule.atomCount
  tag : Fin molecule.atomCount → Fin k ⊕ Fin k
  core_tag : ∀ p, tag (core p) = .inl p
  core_only : ∀ v p, tag v = .inl p → v = core p
  retained : ∀ p, heavyCore (coreAtom p) ≠ heavyCore (AtomSpec.aliphatic Element.H)
  records : ∀ v, heavyCore (molecule.atoms.get v) = heavyCore (atomTable coreAtom (tag v))
  bonds : ∀ v w, molecule.bondOrder v.val w.val = bondTable coreBond (tag v) (tag w)

namespace Completion
variable {k : Nat} {coreAtom : Fin k → AtomSpec} {coreBond : Fin k → Fin k → Nat}

abbrev Vertex (a : Completion coreAtom coreBond) := Fin a.molecule.atomCount
abbrev Fiber (a : Completion coreAtom coreBond) (t : Fin k ⊕ Fin k) := {v : a.Vertex // a.tag v = t}

noncomputable def hydrogenCount (a : Completion coreAtom coreBond) (p : Fin k) : Nat := by
  classical
  exact Fintype.card (a.Fiber (.inr p))

/-- The counted fibers are exactly actual ordinary-H neighbors of the requested core parent. -/
theorem hydrogenFiber_iff (a : Completion coreAtom coreBond) (p : Fin k) (v : a.Vertex) :
    a.tag v = .inr p ↔
      heavyCore (a.molecule.atoms.get v) = heavyCore (AtomSpec.aliphatic Element.H) ∧
      a.molecule.bondOrder v.val (a.core p).val = 1 := by
  constructor
  · intro tag
    rw [a.records, a.bonds, tag, a.core_tag]
    simp [atomTable, bondTable]
  · rintro ⟨record, bond⟩
    cases tag : a.tag v with
    | inl q =>
      rw [a.records, tag] at record
      exact False.elim (a.retained q record)
    | inr q =>
      rw [a.bonds, tag, a.core_tag] at bond
      simp only [bondTable] at bond
      have same : q = p := by
        by_contra different
        simp [different] at bond
      simp [same]

/-- The core fibers are canonically singleton, independently of vertex placement. -/
def coreFiberEquiv (a b : Completion coreAtom coreBond) (p : Fin k) :
    a.Fiber (.inl p) ≃ b.Fiber (.inl p) where
  toFun _ := ⟨b.core p, b.core_tag p⟩
  invFun _ := ⟨a.core p, a.core_tag p⟩
  left_inv v := Subtype.ext (a.core_only v.1 p v.2).symm
  right_inv v := Subtype.ext (b.core_only v.1 p v.2).symm

noncomputable def fiberEquiv (a b : Completion coreAtom coreBond)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p)
    (t : Fin k ⊕ Fin k) : a.Fiber t ≃ b.Fiber t := by
  classical
  cases t with
  | inl p => exact coreFiberEquiv a b p
  | inr p => exact Fintype.equivOfCardEq (counts p)

/-- The atom bijection is constructed by matching finite H fibers separately at each parent. -/
noncomputable def atomEquiv (a b : Completion coreAtom coreBond)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p) : a.Vertex ≃ b.Vertex :=
  (Equiv.sigmaFiberEquiv a.tag).symm |>.trans
    ((Equiv.sigmaCongrRight (fiberEquiv a b counts)).trans (Equiv.sigmaFiberEquiv b.tag))

theorem atomEquiv_tag (a b : Completion coreAtom coreBond)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p) (v : a.Vertex) :
    b.tag (atomEquiv a b counts v) = a.tag v :=
  ((fiberEquiv a b counts (a.tag v)) ⟨v, rfl⟩).2

theorem atomEquiv_core (a b : Completion coreAtom coreBond)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p) (p : Fin k) :
    atomEquiv a b counts (a.core p) = b.core p := by
  apply b.core_only
  rw [atomEquiv_tag, a.core_tag]

theorem atomEquiv_records (a b : Completion coreAtom coreBond)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p) (v : a.Vertex) :
    heavyCore (b.molecule.atoms.get (atomEquiv a b counts v)) = heavyCore (a.molecule.atoms.get v) := by
  rw [b.records, a.records, atomEquiv_tag]

theorem atomEquiv_bonds (a b : Completion coreAtom coreBond)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p) (v w : a.Vertex) :
    b.molecule.bondOrder (atomEquiv a b counts v).val (atomEquiv a b counts w).val =
      a.molecule.bondOrder v.val w.val := by
  rw [b.bonds, a.bonds, atomEquiv_tag, atomEquiv_tag]

/-- Same projected heavy records/bonds and ordinary-H totals suffice to construct a record/bond bijection. -/
theorem ordinary_hydrogen_spellings_equivalent (a b : Completion coreAtom coreBond)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p) :
    ∃ e : a.Vertex ≃ b.Vertex,
      (∀ p, e (a.core p) = b.core p) ∧
      (∀ v, heavyCore (b.molecule.atoms.get (e v)) = heavyCore (a.molecule.atoms.get v)) ∧
      (∀ v w, b.molecule.bondOrder (e v).val (e w).val = a.molecule.bondOrder v.val w.val) :=
  ⟨atomEquiv a b counts, atomEquiv_core a b counts, atomEquiv_records a b counts,
    atomEquiv_bonds a b counts⟩

end Completion
namespace Production
open TetraStereo.Engine.RingHydrogenCompletion

/-- Ordinary unlabelled terminal H at an actual parent; inline-H policy is ignored. -/
def ordinaryAtParent (m : RawMolecule) (p j : Nat) : Bool :=
  decide ((m.atoms[j]?).map heavyCore = some (heavyCore (AtomSpec.aliphatic Element.H)) ∧
    m.writtenNeighbors j = [p])

def ordinaryCount (m : RawMolecule) (p : Nat) : Nat :=
  (List.range m.atomCount).countP (ordinaryAtParent m p)

/-- Successful production materialization derives each fresh H's parent tag and exact
ordinary isotope, rather than asking for a guessed classification of appended vertices. -/
theorem prepare?_fresh_tag {m : RawMolecule} {xyz : SpatialConfiguration}
    {r : RawMolecule × SpatialConfiguration} (accepted : prepare? m xyz = some r)
    (t : Nat) (bound : t < r.1.atomCount-m.atomCount) :
    ∃ p, p < m.atomCount ∧ (addedParents m)[t]? = some p ∧
      (r.1.atoms[m.atomCount+t]?).map heavyCore =
        some (heavyCore (AtomSpec.aliphatic Element.H)) ∧
      r.1.writtenNeighbors (m.atomCount+t) = [p] := by
  have cert := prepare?_certified accepted
  have lower : m.atomCount ≤ m.atomCount+t := by omega
  have upper : m.atomCount+t < r.1.atomCount := by omega
  obtain ⟨p, planned, row⟩ := cert.fresh_row lower upper
  have planned' : (addedParents m)[t]? = some p := by simpa using planned
  refine ⟨p, cert.fresh_parent_lt planned', planned', ?_, row⟩
  rw [cert.fresh_atom lower upper]
  rfl

private theorem getCompat {α : Type} (xs : List α) (n : Nat) : listGet? xs n = xs[n]? := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih => cases n with
    | zero => rfl
    | succ n => exact ih n

theorem missing_hydrogen_zero (m : RawMolecule) (j : Nat) (atom : AtomSpec)
    (lookup : m.atoms[j]? = some atom) (hydrogen : atom.element = .H) : missing m j = 0 := by
  simp [missing, closeHydrogenVertices, RawMolecule.hydrogenCountAt,
    RawMolecule.atomAt?, getCompat, lookup, closeAtom, hydrogen]

theorem planned_parent_not_hydrogen (m : RawMolecule) (p : Nat)
    (parent : p ∈ addedParents m) (atom : AtomSpec) (lookup : m.atoms[p]? = some atom) :
    atom.element ≠ .H := by
  intro hydrogen
  obtain ⟨entry, planned, replicated⟩ := List.mem_flatMap.mp parent
  obtain ⟨j, bounded, found⟩ := List.mem_filterMap.mp planned
  unfold plan at planned
  have missingZero := missing_hydrogen_zero m p atom lookup hydrogen
  have notZero : missing m j ≠ 0 := by
    by_contra zero
    simp [zero] at found
  have shape : entry = (j, missing m j) := by
    simpa [notZero] using found.symm
  subst entry
  have parentEq : p = j := (List.mem_replicate.mp replicated).2
  subst p
  exact notZero missingZero

/-- Production never adds an edge to an existing hydrogen, even when its inline-H count
was nonzero in the input. Its full written neighborhood is therefore retained. -/
theorem certified_old_hydrogen_neighbors {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (j : Nat) (old : j < m.atomCount)
    (atom : AtomSpec) (lookup : m.atoms[j]? = some atom) (hydrogen : atom.element = .H) :
    out.writtenNeighbors j = m.writtenNeighbors j := by
  have jOut : j < out.atomCount := lt_of_lt_of_le old cert.atomCount_le
  have exactJ := RawMolecule.WrittenNeighborExact.at out cert.output_admissible.2 ⟨j,jOut⟩
  have allOld : ∀ v ∈ out.writtenNeighbors j, v < m.atomCount := by
    intro v member
    have vOut := exactJ.2.1 v member
    by_contra notOld
    have lower : m.atomCount ≤ v := by omega
    obtain ⟨p, planned, row⟩ := cert.fresh_row lower vOut
    have positive := (exactJ.2.2 ⟨v,vOut⟩).mp member
    have exactV := RawMolecule.WrittenNeighborExact.at out cert.output_admissible.2 ⟨v,vOut⟩
    have reverse : j ∈ out.writtenNeighbors v := (exactV.2.2 ⟨j,jOut⟩).mpr
      (by simpa only [out.bondOrder_symm v j] using positive)
    rw [row, List.mem_singleton] at reverse
    subst p
    exact planned_parent_not_hydrogen m j (List.mem_of_getElem? planned) atom lookup hydrogen
  have filtered := of_decide_eq_true
    (List.all_eq_true.mp cert.writtenNeighbors_original j (List.mem_range.mpr old))
  have noFilter : (out.writtenNeighbors j).filter (fun v => decide (v < m.atomCount)) =
      out.writtenNeighbors j := List.filter_eq_self.mpr (by
        intro v member
        exact decide_eq_true (allOld v member))
  rw [noFilter] at filtered
  exact filtered

theorem certified_old_ordinary_predicate {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (p j : Nat) (old : j < m.atomCount) :
    ordinaryAtParent out p j = ordinaryAtParent m p j := by
  have projection := cert.atom_core old
  cases lookup : m.atoms[j]? with
  | none => simp [ordinaryAtParent, projection, lookup]
  | some atom =>
    by_cases hydrogen : atom.element = .H
    · have row := certified_old_hydrogen_neighbors cert j old atom lookup hydrogen
      simp only [ordinaryAtParent, projection, row]
    · have different : heavyCore atom ≠ heavyCore (AtomSpec.aliphatic .H) := by
        intro eq
        exact hydrogen (congrArg AtomSpec.element eq)
      simp [ordinaryAtParent, projection, lookup, different]



theorem certified_fresh_count {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (p : Nat) :
    (List.range (out.atomCount - m.atomCount)).countP
      (fun t => ordinaryAtParent out p (m.atomCount+t)) = (addedParents m).count p := by
  have rows := congrArg (fun rows : List (List Nat) => rows.count [p]) cert.added_rows
  dsimp only at rows
  have rowCount :
      (List.range (out.atomCount - m.atomCount)).countP
        (fun t => out.writtenNeighbors (m.atomCount+t) == [p]) = (addedParents m).count p := by
    have singleton_inj : Function.Injective (fun p : Nat => [p]) := by
      intro x y eq
      simpa using eq
    rw [List.count_map_of_injective _ (fun p : Nat => [p]) singleton_inj p] at rows
    simpa only [List.count_eq_countP, List.countP_map, Function.comp_def] using rows
  rw [← rowCount]
  apply List.countP_congr
  intro t mem
  have bound := List.mem_range.mp mem
  have atom := cert.fresh_atom (i := m.atomCount+t) (by omega) (by omega)
  simp [ordinaryAtParent, atom]

/-- Existing ordinary-H neighbors plus the per-parent appended count exhaust the output.
The old summand is measured at the retained original indices in the actual completed graph. -/
theorem certified_total_count {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (cert : Certified m xyz out pos) (p : Nat) :
    ordinaryCount out p =
      (List.range m.atomCount).countP (ordinaryAtParent out p) + (addedParents m).count p := by
  unfold ordinaryCount
  have len : out.atomCount = m.atomCount + (out.atomCount-m.atomCount) := by
    have le := cert.atomCount_le
    omega
  conv_lhs => rw [len, List.range_add, List.countP_append, List.countP_map]
  simp only [Function.comp_def]
  rw [certified_fresh_count cert]

/-- A universal connection to the actual successful `prepare?` output. -/
theorem prepare?_ordinary_count {m : RawMolecule} {xyz : SpatialConfiguration}
    {r : RawMolecule × SpatialConfiguration} (accepted : prepare? m xyz = some r) (p : Nat) :
    ordinaryCount r.1 p =
      (List.range m.atomCount).countP (ordinaryAtParent r.1 p) + (addedParents m).count p :=
  certified_total_count (prepare?_certified accepted) p



theorem prepare?_ordinary_count_from_input {m : RawMolecule} {xyz : SpatialConfiguration}
    {r : RawMolecule × SpatialConfiguration} (accepted : prepare? m xyz = some r) (p : Nat)
    (oldNeighborhoods : ∀ j < m.atomCount,
      ordinaryAtParent r.1 p j = ordinaryAtParent m p j) :
    ordinaryCount r.1 p = ordinaryCount m p + (addedParents m).count p := by
  rw [prepare?_ordinary_count accepted]
  congr 1
  apply List.countP_congr
  intro j mem
  rw [oldNeighborhoods j (List.mem_range.mp mem)]

/-- Actual successful materialization preserves every old ordinary-H neighborhood; no
extra singleton-terminal-H premise is needed. The exact total is input H plus planned H. -/
theorem prepare?_ordinary_count_exact {m : RawMolecule} {xyz : SpatialConfiguration}
    {r : RawMolecule × SpatialConfiguration} (accepted : prepare? m xyz = some r) (p : Nat) :
    ordinaryCount r.1 p = ordinaryCount m p + (addedParents m).count p :=
  prepare?_ordinary_count_from_input accepted p
    (fun j old => certified_old_ordinary_predicate (prepare?_certified accepted) p j old)

assert_kernel_only missing_hydrogen_zero
assert_kernel_only planned_parent_not_hydrogen
assert_kernel_only certified_old_hydrogen_neighbors
assert_kernel_only certified_old_ordinary_predicate
assert_kernel_only prepare?_ordinary_count_exact
assert_kernel_only prepare?_fresh_tag
assert_kernel_only certified_fresh_count
assert_kernel_only certified_total_count
assert_kernel_only prepare?_ordinary_count
assert_kernel_only prepare?_ordinary_count_from_input
end Production
end TetraStereo.OneCenter.OrdinaryHydrogenSpellings
