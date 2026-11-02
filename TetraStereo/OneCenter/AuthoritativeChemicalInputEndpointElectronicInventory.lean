import TetraStereo.OneCenter.AuthoritativeChemicalInputVirtualEndpointRefinement

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact electronic-position inventory for ordinary-double-bond endpoints

The base semantic atom records formal charge and unpaired-electron count, but intentionally does
not guess implicit hydrogens, lone pairs, or deliberately vacant positions.  This module adds an
independent finite inventory for the two nonpartner positions at a Rule-3 endpoint.

Implicit protium and lone-pair positions refine to the complete six-element multiset space already
understood by the virtual comparator.  A vacancy or an unpaired-electron position is not silently
coerced to a lone pair: it produces an exact refusal.  Thus positive descriptors and negative
classification share one explicit chemical boundary.
-/

/-- Counts of nonrepresented positions at one directed ordinary-double-bond endpoint. -/
structure AromaticCanonicalRule3EndpointElectronicInventory where
  implicitProtia : ℕ
  lonePairs : ℕ
  vacancies : ℕ
  unpairedElectronPositions : ℕ
  deriving DecidableEq, Repr

namespace AromaticCanonicalRule3EndpointElectronicInventory

def totalNonrepresentedPositions
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : ℕ :=
  inventory.implicitProtia + inventory.lonePairs + inventory.vacancies +
    inventory.unpairedElectronPositions

end AromaticCanonicalRule3EndpointElectronicInventory

/-- Exact inventory validity at a directed endpoint.  The two-position equation is independent of
the completion implementation, and the radical count is tied to the semantic atom field rather
than accepted as an unrelated annotation. -/
def CanonicalAromaticCanonicalRule3EndpointElectronicInventory
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  (source.aromaticCanonicalRule3Substituents endpoint partner).length +
      inventory.totalNonrepresentedPositions = 2 ∧
    inventory.unpairedElectronPositions =
      (source.molecule.atoms.get endpoint).unpairedElectrons

/-- Number of implicit-protium positions represented by one supported completion. -/
def AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount :
    AromaticCanonicalRule3EndpointCompletion → ℕ
  | .representedOnly => 0
  | .oneImplicitProtium => 1
  | .twoImplicitProtia => 2
  | .oneLonePair => 0
  | .implicitProtiumAndLonePair => 1
  | .twoLonePairs => 0

/-- Number of lone-pair positions represented by one supported completion. -/
def AromaticCanonicalRule3EndpointCompletion.lonePairCount :
    AromaticCanonicalRule3EndpointCompletion → ℕ
  | .representedOnly => 0
  | .oneImplicitProtium => 0
  | .twoImplicitProtia => 0
  | .oneLonePair => 1
  | .implicitProtiumAndLonePair => 1
  | .twoLonePairs => 2

@[simp] theorem AromaticCanonicalRule3EndpointCompletion.counts_eq_virtualLigands_length
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    completion.implicitProtiumCount + completion.lonePairCount =
      completion.virtualLigands.length := by
  cases completion <;> rfl

/-- Independent refinement relation from an electronic inventory to a supported virtual
completion. Vacancies and radical positions have no positive completion. -/
def AromaticCanonicalRule3EndpointElectronicInventorySupports
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (completion : AromaticCanonicalRule3EndpointCompletion) : Prop :=
  inventory.vacancies = 0 ∧
    inventory.unpairedElectronPositions = 0 ∧
    inventory.implicitProtia = completion.implicitProtiumCount ∧
    inventory.lonePairs = completion.lonePairCount

instance (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    Decidable (AromaticCanonicalRule3EndpointElectronicInventorySupports inventory completion) := by
  unfold AromaticCanonicalRule3EndpointElectronicInventorySupports
  infer_instance

/-- The six virtual completions exhaust the multisets of at most two implicit-protium/lone-pair
positions. -/
def allAromaticCanonicalRule3EndpointCompletions :
    List AromaticCanonicalRule3EndpointCompletion :=
  [.representedOnly, .oneImplicitProtium, .twoImplicitProtia, .oneLonePair,
    .implicitProtiumAndLonePair, .twoLonePairs]

@[simp] theorem mem_allAromaticCanonicalRule3EndpointCompletions
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    completion ∈ allAromaticCanonicalRule3EndpointCompletions := by
  cases completion <;> simp [allAromaticCanonicalRule3EndpointCompletions]

theorem endpointCompletion_eq_of_counts_eq
    {left right : AromaticCanonicalRule3EndpointCompletion}
    (implicitEqual : left.implicitProtiumCount = right.implicitProtiumCount)
    (lonePairEqual : left.lonePairCount = right.lonePairCount) :
    left = right := by
  cases left <;> cases right <;>
    simp [AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount,
      AromaticCanonicalRule3EndpointCompletion.lonePairCount] at *

theorem electronicInventorySupports_subsingleton
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    {left right : AromaticCanonicalRule3EndpointCompletion}
    (leftSupported :
      AromaticCanonicalRule3EndpointElectronicInventorySupports inventory left)
    (rightSupported :
      AromaticCanonicalRule3EndpointElectronicInventorySupports inventory right) :
    left = right := by
  apply endpointCompletion_eq_of_counts_eq
  · exact leftSupported.2.2.1.symm.trans rightSupported.2.2.1
  · exact leftSupported.2.2.2.symm.trans rightSupported.2.2.2

/-- Executable finite refinement of an inventory to its unique supported completion. -/
def aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    Option AromaticCanonicalRule3EndpointCompletion :=
  allAromaticCanonicalRule3EndpointCompletions.find? fun completion =>
    decide (AromaticCanonicalRule3EndpointElectronicInventorySupports inventory completion)

/-- Completion lookup is exact against the independent inventory-refinement relation. -/
@[simp] theorem aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?_eq_some_iff
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    aromaticCanonicalRule3EndpointCompletionOfElectronicInventory? inventory = some completion ↔
      AromaticCanonicalRule3EndpointElectronicInventorySupports inventory completion := by
  constructor
  · intro computed
    have accepted := List.find?_some computed
    exact of_decide_eq_true accepted
  · intro supported
    cases observed : aromaticCanonicalRule3EndpointCompletionOfElectronicInventory? inventory with
    | none =>
        have rejects := List.find?_eq_none.mp observed completion
          (mem_allAromaticCanonicalRule3EndpointCompletions completion)
        exact False.elim (rejects (decide_eq_true supported))
    | some actual =>
        have observedFind :
            allAromaticCanonicalRule3EndpointCompletions.find? (fun completion =>
              decide (AromaticCanonicalRule3EndpointElectronicInventorySupports
                inventory completion)) = some actual := by
          simpa [aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?] using observed
        have actualSupported :
            AromaticCanonicalRule3EndpointElectronicInventorySupports inventory actual := by
          exact of_decide_eq_true (List.find?_some
            (p := fun completion => decide
              (AromaticCanonicalRule3EndpointElectronicInventorySupports inventory completion))
            observedFind)
        have equal := electronicInventorySupports_subsingleton inventory
          actualSupported supported
        exact congrArg some equal

/-- Exact negative meaning of the inventory completion lookup. -/
theorem aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?_eq_none_iff
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    aromaticCanonicalRule3EndpointCompletionOfElectronicInventory? inventory = none ↔
      ¬ ∃ completion,
        AromaticCanonicalRule3EndpointElectronicInventorySupports inventory completion := by
  cases computed : aromaticCanonicalRule3EndpointCompletionOfElectronicInventory? inventory with
  | none =>
      simp only [true_iff]
      rintro ⟨completion, supported⟩
      have positive :=
        (aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?_eq_some_iff
          inventory completion).mpr supported
      rw [computed] at positive
      contradiction
  | some completion =>
      simp only [reduceCtorEq, false_iff]
      intro absent
      exact absent ⟨completion,
        (aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?_eq_some_iff
          inventory completion).mp computed⟩

/-- If the two-position equation holds and there is neither a vacancy nor a radical position, one
of the six H/lone-pair completions exists. -/
theorem exists_electronicInventorySupports_of_no_refusal
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (canonical : source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
      endpoint partner inventory)
    (noVacancy : inventory.vacancies = 0)
    (closedShell : inventory.unpairedElectronPositions = 0) :
    ∃ completion,
      AromaticCanonicalRule3EndpointElectronicInventorySupports inventory completion := by
  have bounded : inventory.implicitProtia + inventory.lonePairs ≤ 2 := by
    unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory at canonical
    unfold AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions at canonical
    omega
  have cases :
      (inventory.implicitProtia = 0 ∧ inventory.lonePairs = 0) ∨
      (inventory.implicitProtia = 0 ∧ inventory.lonePairs = 1) ∨
      (inventory.implicitProtia = 0 ∧ inventory.lonePairs = 2) ∨
      (inventory.implicitProtia = 1 ∧ inventory.lonePairs = 0) ∨
      (inventory.implicitProtia = 1 ∧ inventory.lonePairs = 1) ∨
      (inventory.implicitProtia = 2 ∧ inventory.lonePairs = 0) := by
    omega
  rcases cases with h | h | h | h | h | h
  · exact ⟨AromaticCanonicalRule3EndpointCompletion.representedOnly, by
      simp [AromaticCanonicalRule3EndpointElectronicInventorySupports,
        AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount,
        AromaticCanonicalRule3EndpointCompletion.lonePairCount,
        noVacancy, closedShell, h.1, h.2]⟩
  · exact ⟨AromaticCanonicalRule3EndpointCompletion.oneLonePair, by
      simp [AromaticCanonicalRule3EndpointElectronicInventorySupports,
        AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount,
        AromaticCanonicalRule3EndpointCompletion.lonePairCount,
        noVacancy, closedShell, h.1, h.2]⟩
  · exact ⟨AromaticCanonicalRule3EndpointCompletion.twoLonePairs, by
      simp [AromaticCanonicalRule3EndpointElectronicInventorySupports,
        AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount,
        AromaticCanonicalRule3EndpointCompletion.lonePairCount,
        noVacancy, closedShell, h.1, h.2]⟩
  · exact ⟨AromaticCanonicalRule3EndpointCompletion.oneImplicitProtium, by
      simp [AromaticCanonicalRule3EndpointElectronicInventorySupports,
        AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount,
        AromaticCanonicalRule3EndpointCompletion.lonePairCount,
        noVacancy, closedShell, h.1, h.2]⟩
  · exact ⟨AromaticCanonicalRule3EndpointCompletion.implicitProtiumAndLonePair, by
      simp [AromaticCanonicalRule3EndpointElectronicInventorySupports,
        AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount,
        AromaticCanonicalRule3EndpointCompletion.lonePairCount,
        noVacancy, closedShell, h.1, h.2]⟩
  · exact ⟨AromaticCanonicalRule3EndpointCompletion.twoImplicitProtia, by
      simp [AromaticCanonicalRule3EndpointElectronicInventorySupports,
        AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount,
        AromaticCanonicalRule3EndpointCompletion.lonePairCount,
        noVacancy, closedShell, h.1, h.2]⟩

/-- On a canonical two-position inventory, refusal is exactly a supplied vacancy or an unpaired
electron position. -/
theorem aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (canonical : source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
      endpoint partner inventory) :
    aromaticCanonicalRule3EndpointCompletionOfElectronicInventory? inventory = none ↔
      inventory.vacancies ≠ 0 ∨ inventory.unpairedElectronPositions ≠ 0 := by
  rw [aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?_eq_none_iff]
  constructor
  · intro noCompletion
    by_contra noRefusal
    push_neg at noRefusal
    exact noCompletion (source.exists_electronicInventorySupports_of_no_refusal
      endpoint partner inventory canonical noRefusal.1 noRefusal.2)
  · intro refused
    rintro ⟨completion, supported⟩
    rcases refused with vacancy | radical
    · exact vacancy supported.1
    · exact radical supported.2.1

/-- A supported inventory always gives the endpoint-shape compatibility required by the existing
virtual-aware analyzer. -/
theorem canonicalEndpointCompletion_of_electronicInventorySupports
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (completion : AromaticCanonicalRule3EndpointCompletion)
    (canonical : source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
      endpoint partner inventory)
    (supported :
      AromaticCanonicalRule3EndpointElectronicInventorySupports inventory completion) :
    source.CanonicalAromaticCanonicalRule3EndpointCompletion endpoint partner completion := by
  rcases canonical with ⟨accounted, _radicalConsistent⟩
  rcases supported with ⟨noVacancy, noRadical, implicitEqual, lonePairEqual⟩
  unfold AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions at accounted
  unfold CanonicalAromaticCanonicalRule3EndpointCompletion
  have completionCounts := completion.counts_eq_virtualLigands_length
  have completionTotal := completion.virtualLigands_length_add_representedCount
  omega

/-- A finite total inventory source for every directed individual-double-bond endpoint. -/
structure AromaticCanonicalRule3EndpointElectronicInventorySource
    (source : AuthoritativeChemicalInput) where
  inventory : (endpoint partner : source.AromaticCanonicalAtom) →
    AromaticCanonicalRule3EndpointElectronicInventory
  canonical : ∀ endpoint partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
        endpoint partner (inventory endpoint partner)

/-- Completion map generated directly from the electronic-position inventory. -/
def electronicInventoryCompletionMap
    (source : AuthoritativeChemicalInput)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource) :
    source.AromaticCanonicalRule3EndpointCompletionMap :=
  fun endpoint partner =>
    aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?
      (inventories.inventory endpoint partner)

/-- The generated map returns a completion exactly when the independent inventory supports it. -/
theorem electronicInventoryCompletionMap_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (endpoint partner : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    source.electronicInventoryCompletionMap inventories endpoint partner = some completion ↔
      AromaticCanonicalRule3EndpointElectronicInventorySupports
        (inventories.inventory endpoint partner) completion := by
  exact aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?_eq_some_iff _ _

/-- On every directed endpoint, generated-map refusal is exactly vacancy-or-radical refusal. -/
theorem electronicInventoryCompletionMap_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (endpoint partner : source.AromaticCanonicalAtom)
    (directed : source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner) :
    source.electronicInventoryCompletionMap inventories endpoint partner = none ↔
      (inventories.inventory endpoint partner).vacancies ≠ 0 ∨
        (inventories.inventory endpoint partner).unpairedElectronPositions ≠ 0 := by
  exact source.aromaticCanonicalRule3EndpointCompletionOfElectronicInventory?_eq_none_iff_refusal
    endpoint partner (inventories.inventory endpoint partner)
      (inventories.canonical endpoint partner directed)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
