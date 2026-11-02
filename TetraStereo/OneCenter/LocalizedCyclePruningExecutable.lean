import TetraStereo.OneCenter.LocalizedMonocyclicDoubleBondPerception

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Remove all vertices with fewer than two neighbors in the retained subgraph. -/
def localizedCyclePrune (input : CertifiedLocalizedCIPInput) (vertices : Finset input.Atom) :
    Finset input.Atom :=
  vertices.filter fun atom => 2 ≤ (input.localizedCycleNeighbors vertices atom).card

def localizedCycleCoreSteps (input : CertifiedLocalizedCIPInput) : Nat → Finset input.Atom
  | 0 => Finset.univ
  | n + 1 => input.localizedCyclePrune (input.localizedCycleCoreSteps n)

def localizedCycleCore (input : CertifiedLocalizedCIPInput) : Finset input.Atom :=
  input.localizedCycleCoreSteps (Fintype.card input.Atom)

theorem localizedCycleNeighbors_mono (input : CertifiedLocalizedCIPInput)
    {left right : Finset input.Atom} (subset : left ⊆ right) (atom : input.Atom) :
    input.localizedCycleNeighbors left atom ⊆ input.localizedCycleNeighbors right atom := by
  intro neighbor member
  rw [mem_localizedCycleNeighbors_iff] at member ⊢
  exact ⟨subset member.1, member.2⟩

theorem cycle_subset_prune (input : CertifiedLocalizedCIPInput)
    {cycle vertices : Finset input.Atom}
    (meaning : input.DeclarativeLocalizedSimpleCycleVertexSet cycle)
    (subset : cycle ⊆ vertices) : cycle ⊆ input.localizedCyclePrune vertices := by
  intro atom member
  apply Finset.mem_filter.mpr
  refine ⟨subset member, ?_⟩
  have count := Finset.card_le_card (input.localizedCycleNeighbors_mono subset atom)
  rw [meaning.2.1 atom member] at count
  exact count

/-- Every declarative cycle survives every pruning round. No assumption of acyclicity is required. -/
theorem cycle_subset_coreSteps (input : CertifiedLocalizedCIPInput)
    {cycle : Finset input.Atom}
    (meaning : input.DeclarativeLocalizedSimpleCycleVertexSet cycle) (n : Nat) :
    cycle ⊆ input.localizedCycleCoreSteps n := by
  induction n with
  | zero => exact Finset.subset_univ cycle
  | succ n ih => exact input.cycle_subset_prune meaning ih

theorem cycle_subset_core (input : CertifiedLocalizedCIPInput)
    {cycle : Finset input.Atom}
    (meaning : input.DeclarativeLocalizedSimpleCycleVertexSet cycle) :
    cycle ⊆ input.localizedCycleCore :=
  input.cycle_subset_coreSteps meaning (Fintype.card input.Atom)

/-- An empty pruning result is a general executable certificate that exhaustive cycle search is
empty. The optimization needs only this direction; it introduces no graph-family admission gate. -/
theorem cycles_empty_of_core_empty (input : CertifiedLocalizedCIPInput)
    (empty : input.localizedCycleCore = ∅) (representative : input.Atom) :
    input.localizedSimpleCycleVertexSetsInComponent representative = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro cycle member
  have meaning := (input.mem_localizedSimpleCycleVertexSetsInComponent_iff
    representative cycle).mp member
  have subset := input.cycle_subset_core meaning.1
  rw [empty, Finset.subset_empty] at subset
  have bound := meaning.1.1
  simp [subset] at bound

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
