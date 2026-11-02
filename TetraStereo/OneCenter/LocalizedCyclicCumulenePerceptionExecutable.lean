import TetraStereo.OneCenter.LocalizedMonocyclicPerceptionExecutable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

instance orderTwoGraphAdjDecidable (input : CertifiedLocalizedCIPInput) :
    DecidableRel input.localizedOrderTwoSimpleGraph.Adj := by
  intro a b
  change Decidable (input.moleculeGraph.bond a b = 2)
  infer_instance

def localizedOrderTwoComponentAtomsExec
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) : Finset input.Atom :=
  FiniteGraphReachability.vertices input.localizedOrderTwoSimpleGraph representative

theorem localizedOrderTwoComponentAtomsExec_eq_original
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    input.localizedOrderTwoComponentAtomsExec representative =
      input.localizedOrderTwoComponentAtoms representative := by
  ext atom
  simp [localizedOrderTwoComponentAtomsExec, localizedOrderTwoComponentAtoms,
    FiniteGraphReachability.mem_vertices_iff]

instance cyclicComponentAtDecidable (input : CertifiedLocalizedCIPInput)
    (representative : input.Atom) :
    Decidable (input.DeclarativeLocalizedCyclicCumuleneComponentAt representative) :=
  decidable_of_iff
    (3 ≤ (input.localizedOrderTwoComponentAtomsExec representative).card ∧
      (∀ atom, atom ∈ input.localizedOrderTwoComponentAtomsExec representative →
        (input.localizedOrderTwoNeighbors atom).length = 2) ∧
      ∀ atom, atom ∈ input.localizedOrderTwoComponentAtomsExec representative →
        representative ≤ atom)
    (by rw [localizedOrderTwoComponentAtomsExec_eq_original]; rfl)

def localizedCyclicCumuleneComponentAtExec?
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    Option input.LocalizedCyclicCumuleneComponent :=
  if input.DeclarativeLocalizedCyclicCumuleneComponentAt representative then
    some { representative } else none

theorem localizedCyclicCumuleneComponentAtExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    input.localizedCyclicCumuleneComponentAtExec? representative =
      input.localizedCyclicCumuleneComponentAt? representative := by
  unfold localizedCyclicCumuleneComponentAtExec? localizedCyclicCumuleneComponentAt?
  split <;> simp_all

def localizedCyclicCumuleneComponentsExec (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedCyclicCumuleneComponent :=
  ((Finset.univ : Finset input.Atom).sort (· ≤ ·)).filterMap
    input.localizedCyclicCumuleneComponentAtExec?

theorem localizedCyclicCumuleneComponentsExec_eq_original
    (input : CertifiedLocalizedCIPInput) :
    input.localizedCyclicCumuleneComponentsExec = input.localizedCyclicCumuleneComponents := by
  unfold localizedCyclicCumuleneComponentsExec localizedCyclicCumuleneComponents
  rw [funext (input.localizedCyclicCumuleneComponentAtExec?_eq_original)]

/-- Finite search replaces the original unique classical witness. -/
def localizedCyclicCumuleneComponentContainingExec?
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    Option input.LocalizedCyclicCumuleneComponent :=
  input.localizedCyclicCumuleneComponentsExec.find? fun component =>
    decide (atom ∈ input.localizedOrderTwoComponentAtomsExec component.representative)

private theorem found_component_contains
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (component : input.LocalizedCyclicCumuleneComponent)
    (found : input.localizedCyclicCumuleneComponentContainingExec? atom = some component) :
    input.DeclarativeLocalizedCyclicCumuleneComponentContains component atom := by
  unfold localizedCyclicCumuleneComponentContainingExec? at found
  have present := List.mem_of_find?_eq_some found
  rw [localizedCyclicCumuleneComponentsExec_eq_original] at present
  refine ⟨(input.mem_localizedCyclicCumuleneComponents_iff component).mp present, ?_⟩
  have member := List.find?_some found
  simpa only [decide_eq_true_eq, localizedOrderTwoComponentAtomsExec_eq_original] using member

theorem localizedCyclicCumuleneComponentContainingExec?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (component : input.LocalizedCyclicCumuleneComponent) :
    input.localizedCyclicCumuleneComponentContainingExec? atom = some component ↔
      input.DeclarativeLocalizedCyclicCumuleneComponentContains component atom := by
  constructor
  · exact found_component_contains input atom component
  · intro derived
    cases found : input.localizedCyclicCumuleneComponentContainingExec? atom with
    | some result =>
        have equal := input.declarativeLocalizedCyclicCumuleneComponentContains_unique atom
          (found_component_contains input atom result found) derived
        simp [equal]
    | none =>
        have present : component ∈ input.localizedCyclicCumuleneComponentsExec := by
          rw [localizedCyclicCumuleneComponentsExec_eq_original]
          exact (input.mem_localizedCyclicCumuleneComponents_iff component).mpr derived.1
        have absent := (List.find?_eq_none.mp found) component present
        exact False.elim (absent (by
          simpa only [decide_eq_true_eq, localizedOrderTwoComponentAtomsExec_eq_original]
            using derived.2))

theorem localizedCyclicCumuleneComponentContainingExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    input.localizedCyclicCumuleneComponentContainingExec? atom =
      input.localizedCyclicCumuleneComponentContaining? atom := by
  apply Option.ext
  intro component
  exact (input.localizedCyclicCumuleneComponentContainingExec?_eq_some_iff atom component).trans
    (input.localizedCyclicCumuleneComponentContaining?_eq_some_iff atom component).symm

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
