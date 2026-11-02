import TetraStereo.OneCenter.LocalizedMonocyclicDoubleBondPerception
import TetraStereo.OneCenter.FiniteGraphReachabilityExecutable
import TetraStereo.OneCenter.LocalizedCyclePruningExecutable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

private theorem singleton_unique {α : Type*} [DecidableEq α]
    (s : Finset α) (one : s.card = 1) : ∃! a, a ∈ s ∧ True := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp one
  exact ⟨a, by simp, by intro b hb; simpa using hb.1⟩

/-- Extract a singleton without choosing an arbitrary ordering of a finite set. -/
def finiteSingleton? {α : Type*} [DecidableEq α] (s : Finset α) : Option α :=
  if one : s.card = 1 then some (s.choose (fun _ => True) (singleton_unique s one)) else none

private theorem finiteSingleton?_singleton {α : Type*} [DecidableEq α] (a : α) :
    finiteSingleton? ({a} : Finset α) = some a := by
  unfold finiteSingleton?
  rw [dif_pos (by simp)]
  congr 1

/-- Singleton extraction is insensitive to the arbitrary order of `Finset.toList`. -/
theorem finiteSingleton?_eq_toList {α : Type*} [DecidableEq α] (s : Finset α) :
    finiteSingleton? s = (match s.toList with | [a] => some a | _ => none) := by
  cases h : s.toList with
  | nil =>
      have empty : s = ∅ := Finset.toList_eq_nil.mp h
      subst s
      simp [finiteSingleton?]
  | cons a rest =>
      cases rest with
      | nil =>
          have singleton : s = {a} := Finset.toList_eq_singleton_iff.mp h
          rw [singleton, finiteSingleton?_singleton]
      | cons second rest =>
          have length := congrArg List.length h
          have notOne : s.card ≠ 1 := by
            simp only [Finset.length_toList, List.length_cons] at length
            omega
          simp [finiteSingleton?, notOne]

instance covalentGraphAdjDecidable (input : CertifiedLocalizedCIPInput) :
    DecidableRel input.moleculeGraph.underlyingSimpleGraph.Adj := by
  intro a b
  change Decidable (input.moleculeGraph.Adj a b)
  infer_instance

instance inducedCycleGraphAdjDecidable (input : CertifiedLocalizedCIPInput)
    (vertices : Finset input.Atom) :
    DecidableRel (input.localizedInducedCycleGraph vertices).Adj := by
  intro a b
  change Decidable (a ∈ vertices ∧ b ∈ vertices ∧ input.moleculeGraph.Adj a b)
  infer_instance

/-- Bounded closure computes the complete connected component without enumerating walks. -/
def localizedCovalentComponentAtomsExec
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) : Finset input.Atom :=
  FiniteGraphReachability.vertices input.moleculeGraph.underlyingSimpleGraph representative

theorem localizedCovalentComponentAtomsExec_eq_original
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    input.localizedCovalentComponentAtomsExec representative =
      input.localizedCovalentComponentAtoms representative := by
  ext atom
  simp [localizedCovalentComponentAtomsExec, localizedCovalentComponentAtoms,
    FiniteGraphReachability.mem_vertices_iff]

instance simpleCycleVertexSetDecidable (input : CertifiedLocalizedCIPInput)
    (vertices : Finset input.Atom) :
    Decidable (input.DeclarativeLocalizedSimpleCycleVertexSet vertices) := by
  unfold DeclarativeLocalizedSimpleCycleVertexSet
  letI : DecidableRel (input.localizedInducedCycleGraph vertices).Reachable :=
    FiniteGraphReachability.reachableDecidable (input.localizedInducedCycleGraph vertices)
  infer_instance

/-- Exhaustive search over the pruned core. Every declarative cycle survives pruning, so pendant
branches cost no powerset dimension and an empty core rejects every cycle immediately. -/
def localizedSimpleCycleVertexSetsInComponentExec
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    Finset (Finset input.Atom) :=
  input.localizedCycleCore.powerset.filter fun vertices =>
    input.DeclarativeLocalizedSimpleCycleVertexSet vertices ∧
      vertices ⊆ input.localizedCovalentComponentAtomsExec representative

theorem localizedSimpleCycleVertexSetsInComponentExec_eq_original
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    input.localizedSimpleCycleVertexSetsInComponentExec representative =
      input.localizedSimpleCycleVertexSetsInComponent representative := by
  ext vertices
  simp only [localizedSimpleCycleVertexSetsInComponentExec, Finset.mem_filter,
    Finset.mem_powerset, mem_localizedSimpleCycleVertexSetsInComponent_iff,
    localizedCovalentComponentAtomsExec_eq_original]
  exact ⟨fun member => member.2, fun member => ⟨input.cycle_subset_core member.1, member⟩⟩

/-- Executable twin of the complete original monocycle perception, including polycycle refusals. -/
def localizedMonocyclicDoubleBondAtExec?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    Option input.LocalizedMonocyclicDoubleBond := do
  let ring ← finiteSingleton? (input.localizedSimpleCycleVertexSetsInComponentExec left)
  if input.moleculeGraph.bond left right = 2 ∧ left ∈ ring ∧ right ∈ ring ∧
      input.localizedDoubleBondCountIn ring < ring.card then
    some { ring }
  else none

theorem localizedMonocyclicDoubleBondAtExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.localizedMonocyclicDoubleBondAtExec? left right =
      input.localizedMonocyclicDoubleBondAt? left right := by
  unfold localizedMonocyclicDoubleBondAtExec? localizedMonocyclicDoubleBondAt?
  rw [localizedSimpleCycleVertexSetsInComponentExec_eq_original, finiteSingleton?_eq_toList]
  split <;> simp_all

/-- Preserve the original ring-size/count descriptor policy after perception. -/
def localizedMonocyclicDoubleBondPolicyAtExec?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    Option input.LocalizedMonocyclicDoubleBondPolicyResult := do
  let carrier ← input.localizedMonocyclicDoubleBondAtExec? left right
  let doubleBondCount := input.localizedDoubleBondCountIn carrier.ring
  let policy ← BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy carrier.ring.card doubleBondCount
  some { carrier, doubleBondCount, policy }

theorem localizedMonocyclicDoubleBondPolicyAtExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.localizedMonocyclicDoubleBondPolicyAtExec? left right =
      input.localizedMonocyclicDoubleBondPolicyAt? left right := by
  unfold localizedMonocyclicDoubleBondPolicyAtExec? localizedMonocyclicDoubleBondPolicyAt?
  rw [localizedMonocyclicDoubleBondAtExec?_eq_original]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
