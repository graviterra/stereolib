import TetraStereo.OneCenter.AuthoritativeMainGroupLewisEndpointElectronicInventory

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Molecule-wide refinement from the Lewis ledger to atom electronic-state records

The endpoint ledger is partner-independent: changing which retained ordinary double bond is viewed
as the partner erases a different member of the same canonical neighbour set, so the represented
nonpartner count is unchanged, while the bond-order/electron equation is atom-level.  We use that
fact to infer one inventory per atom, generate unique finite records, and feed the result through
the exact validated analyzer.
-/

/-- The localized Lewis inventory exists for an atom in at least one retained endpoint direction. -/
def MainGroupClosedValenceLewisAtomInventory
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  ∃ partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint atom partner ∧
      source.MainGroupClosedValenceLewisEndpointInventory atom partner inventory

/-- Endpoint position accounting, and therefore the complete Lewis relation, is independent of
which retained ordinary-double-bond partner is used at the same atom. -/
theorem mainGroupClosedValenceLewisEndpointInventory_partner_independent
    (source : AuthoritativeChemicalInput)
    (atom firstPartner secondPartner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (firstDirected :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint atom firstPartner)
    (firstLewis : source.MainGroupClosedValenceLewisEndpointInventory
      atom firstPartner inventory)
    (secondDirected :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint atom secondPartner) :
    source.MainGroupClosedValenceLewisEndpointInventory atom secondPartner inventory := by
  rcases firstLewis with ⟨firstCanonical, noVacancy, electronLedger⟩
  have firstOrdinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint firstDirected
  have secondOrdinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint secondDirected
  have firstPresent : firstPartner ∈ source.aromaticCanonicalNeighborFinset atom :=
    (source.mem_aromaticCanonicalNeighborFinset_iff atom firstPartner).mpr firstOrdinary.1
  have secondPresent : secondPartner ∈ source.aromaticCanonicalNeighborFinset atom :=
    (source.mem_aromaticCanonicalNeighborFinset_iff atom secondPartner).mpr secondOrdinary.1
  have representedLengthEqual :
      (source.aromaticCanonicalRule3Substituents atom firstPartner).length =
        (source.aromaticCanonicalRule3Substituents atom secondPartner).length := by
    simp [aromaticCanonicalRule3Substituents,
      Finset.card_erase_of_mem firstPresent,
      Finset.card_erase_of_mem secondPresent]
  refine ⟨?_, noVacancy, electronLedger⟩
  unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory at firstCanonical ⊢
  exact ⟨by simpa [representedLengthEqual] using firstCanonical.1, firstCanonical.2⟩

/-- The inferred atom-level inventory is functional. -/
theorem mainGroupClosedValenceLewisAtomInventory_subsingleton
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    {left right : AromaticCanonicalRule3EndpointElectronicInventory}
    (leftLewis : source.MainGroupClosedValenceLewisAtomInventory atom left)
    (rightLewis : source.MainGroupClosedValenceLewisAtomInventory atom right) :
    left = right := by
  rcases leftLewis with ⟨leftPartner, leftDirected, leftEndpointLewis⟩
  rcases rightLewis with ⟨rightPartner, rightDirected, rightEndpointLewis⟩
  have rightAtLeft := source.mainGroupClosedValenceLewisEndpointInventory_partner_independent
    atom rightPartner leftPartner right rightDirected rightEndpointLewis leftDirected
  exact source.mainGroupClosedValenceLewisEndpointInventory_subsingleton
    atom leftPartner leftEndpointLewis rightAtLeft

/-- Exact finite atom-level inference. -/
noncomputable def mainGroupClosedValenceLewisAtomInventory?
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    Option AromaticCanonicalRule3EndpointElectronicInventory := by
  classical
  exact (mainGroupClosedValenceEndpointInventoryCandidates
    (source.molecule.atoms.get atom).unpairedElectrons).find? fun inventory =>
      decide (source.MainGroupClosedValenceLewisAtomInventory atom inventory)

/-- Atom-level inference is exact against existence at any retained endpoint direction. -/
@[simp] theorem mainGroupClosedValenceLewisAtomInventory?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    source.mainGroupClosedValenceLewisAtomInventory? atom = some inventory ↔
      source.MainGroupClosedValenceLewisAtomInventory atom inventory := by
  classical
  constructor
  · intro computed
    have computedFind :
        (mainGroupClosedValenceEndpointInventoryCandidates
          (source.molecule.atoms.get atom).unpairedElectrons).find? (fun inventory =>
            decide (source.MainGroupClosedValenceLewisAtomInventory atom inventory)) =
          some inventory := by
      simpa [mainGroupClosedValenceLewisAtomInventory?] using computed
    exact of_decide_eq_true (List.find?_some
      (p := fun candidate => decide
        (source.MainGroupClosedValenceLewisAtomInventory atom candidate)) computedFind)
  · intro atomLewis
    rcases atomLewis with ⟨partner, directed, endpointLewis⟩
    have candidatePresent :=
      source.mem_mainGroupClosedValenceEndpointInventoryCandidates_of_lewis
        atom partner inventory endpointLewis
    cases observed : source.mainGroupClosedValenceLewisAtomInventory? atom with
    | none =>
        have observedFind :
            (mainGroupClosedValenceEndpointInventoryCandidates
              (source.molecule.atoms.get atom).unpairedElectrons).find? (fun inventory =>
                decide (source.MainGroupClosedValenceLewisAtomInventory atom inventory)) = none := by
          simpa [mainGroupClosedValenceLewisAtomInventory?] using observed
        have rejected := List.find?_eq_none.mp observedFind inventory candidatePresent
        exact False.elim (rejected (decide_eq_true ⟨partner, directed, endpointLewis⟩))
    | some actual =>
        have observedFind :
            (mainGroupClosedValenceEndpointInventoryCandidates
              (source.molecule.atoms.get atom).unpairedElectrons).find? (fun inventory =>
                decide (source.MainGroupClosedValenceLewisAtomInventory atom inventory)) =
              some actual := by
          simpa [mainGroupClosedValenceLewisAtomInventory?] using observed
        have actualLewis : source.MainGroupClosedValenceLewisAtomInventory atom actual :=
          of_decide_eq_true (List.find?_some
            (p := fun candidate => decide
              (source.MainGroupClosedValenceLewisAtomInventory atom candidate)) observedFind)
        have equal := source.mainGroupClosedValenceLewisAtomInventory_subsingleton
          atom actualLewis ⟨partner, directed, endpointLewis⟩
        exact congrArg some equal

/-- A generated record exists precisely when atom-level Lewis inference succeeds. -/
noncomputable def mainGroupLewisAtomElectronicStateRecord?
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalAtomElectronicStateRecord :=
  (source.mainGroupClosedValenceLewisAtomInventory? atom).map fun inventory =>
    { atom := atom, inventory := inventory }

theorem mainGroupLewisAtomElectronicStateRecord?_sound
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (record : source.AromaticCanonicalAtomElectronicStateRecord)
    (computed : source.mainGroupLewisAtomElectronicStateRecord? atom = some record) :
    record.atom = atom ∧
      source.MainGroupClosedValenceLewisAtomInventory atom record.inventory := by
  unfold mainGroupLewisAtomElectronicStateRecord? at computed
  cases observed : source.mainGroupClosedValenceLewisAtomInventory? atom with
  | none => simp [observed] at computed
  | some inventory =>
      have lewis := (source.mainGroupClosedValenceLewisAtomInventory?_eq_some_iff
        atom inventory).mp observed
      simp [observed] at computed
      subst record
      exact ⟨rfl, lewis⟩

theorem mainGroupLewisAtomElectronicStateRecord?_complete
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (lewis : source.MainGroupClosedValenceLewisAtomInventory atom inventory) :
    source.mainGroupLewisAtomElectronicStateRecord? atom =
      some { atom := atom, inventory := inventory } := by
  unfold mainGroupLewisAtomElectronicStateRecord?
  rw [(source.mainGroupClosedValenceLewisAtomInventory?_eq_some_iff atom inventory).mpr lewis]
  rfl

/-- One generated electronic-state record for every atom at which the Lewis inference succeeds. -/
noncomputable def mainGroupLewisAtomElectronicStateRecords
    (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalAtomElectronicStateRecord :=
  source.aromaticCanonicalAtomUniverse.filterMap
    source.mainGroupLewisAtomElectronicStateRecord?

private noncomputable def mainGroupLewisAtomElectronicStateKey?
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) : Option ℕ :=
  (source.mainGroupClosedValenceLewisAtomInventory? atom).map fun _inventory => atom.val

private theorem map_mainGroupLewisRecords_key
    (source : AuthoritativeChemicalInput)
    (atoms : List source.AromaticCanonicalAtom) :
    (atoms.filterMap source.mainGroupLewisAtomElectronicStateRecord?).map
        AromaticCanonicalAtomElectronicStateRecord.key =
      atoms.filterMap source.mainGroupLewisAtomElectronicStateKey? := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      cases observed : source.mainGroupClosedValenceLewisAtomInventory? atom <;>
        simp [mainGroupLewisAtomElectronicStateRecord?,
          mainGroupLewisAtomElectronicStateKey?, observed, inductionHypothesis,
          AromaticCanonicalAtomElectronicStateRecord.key]

/-- Generated atom keys are unique. -/
theorem mainGroupLewisAtomElectronicStateRecords_keys_nodup
    (source : AuthoritativeChemicalInput) :
    ((source.mainGroupLewisAtomElectronicStateRecords).map
      AromaticCanonicalAtomElectronicStateRecord.key).Nodup := by
  classical
  rw [mainGroupLewisAtomElectronicStateRecords,
    source.map_mainGroupLewisRecords_key source.aromaticCanonicalAtomUniverse]
  apply List.Nodup.filterMap
  · intro left right key leftComputed rightComputed
    unfold mainGroupLewisAtomElectronicStateKey? at leftComputed rightComputed
    cases leftObserved : source.mainGroupClosedValenceLewisAtomInventory? left <;>
      simp [leftObserved] at leftComputed
    cases rightObserved : source.mainGroupClosedValenceLewisAtomInventory? right <;>
      simp [rightObserved] at rightComputed
    apply Fin.ext
    omega
  · exact source.aromaticCanonicalAtomUniverse_nodup

/-- Every generated record is a literal Lewis-derived inventory. -/
theorem mem_mainGroupLewisAtomElectronicStateRecords_iff
    (source : AuthoritativeChemicalInput)
    (record : source.AromaticCanonicalAtomElectronicStateRecord) :
    record ∈ source.mainGroupLewisAtomElectronicStateRecords ↔
      source.MainGroupClosedValenceLewisAtomInventory record.atom record.inventory := by
  classical
  rw [mainGroupLewisAtomElectronicStateRecords, List.mem_filterMap]
  constructor
  · rintro ⟨atom, _present, computed⟩
    obtain ⟨atomIdentity, lewis⟩ :=
      source.mainGroupLewisAtomElectronicStateRecord?_sound atom record computed
    simpa [atomIdentity] using lewis
  · intro lewis
    rcases record with ⟨atom, inventory⟩
    exact ⟨atom, source.mem_aromaticCanonicalAtomUniverse atom,
      source.mainGroupLewisAtomElectronicStateRecord?_complete atom inventory lewis⟩

/-- The generated finite record list is contextually well formed. -/
theorem mainGroupLewisAtomElectronicStateRecords_wellFormed
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalAtomElectronicStateRecordsWellFormed
      source.mainGroupLewisAtomElectronicStateRecords := by
  refine ⟨source.mainGroupLewisAtomElectronicStateRecords_keys_nodup, ?_⟩
  intro record present partner directed
  have atomLewis :=
    (source.mem_mainGroupLewisAtomElectronicStateRecords_iff record).mp present
  rcases atomLewis with ⟨firstPartner, firstDirected, firstLewis⟩
  exact (source.mainGroupClosedValenceLewisEndpointInventory_partner_independent
    record.atom firstPartner partner record.inventory firstDirected firstLewis directed).1

/-- Applicability domain: every retained directed endpoint has a closed-valence main-group Lewis
inventory. -/
def EveryIndividualDoubleBondEndpointMainGroupLewisDerivable
    (source : AuthoritativeChemicalInput) : Prop :=
  ∀ endpoint partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      ∃ inventory,
        source.MainGroupClosedValenceLewisEndpointInventory endpoint partner inventory

/-- The applicability domain fails exactly at a concrete directed endpoint carrying one of the
proved Lewis-refusal witnesses. -/
theorem not_everyIndividualDoubleBondEndpointMainGroupLewisDerivable_iff
    (source : AuthoritativeChemicalInput) :
    ¬ source.EveryIndividualDoubleBondEndpointMainGroupLewisDerivable ↔
      ∃ endpoint partner,
        source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
          source.MainGroupClosedValenceLewisEndpointRefusal endpoint partner := by
  classical
  unfold EveryIndividualDoubleBondEndpointMainGroupLewisDerivable
  constructor
  · intro notEvery
    push_neg at notEvery
    obtain ⟨endpoint, partner, directed, noInventory⟩ := notEvery
    refine ⟨endpoint, partner, directed, ?_⟩
    rw [← source.mainGroupClosedValenceLewisEndpointInventory?_eq_none_iff_refusal]
    exact (source.mainGroupClosedValenceLewisEndpointInventory?_eq_none_iff
      endpoint partner).mpr (by
        rintro ⟨inventory, lewis⟩
        exact noInventory inventory lewis)
  · rintro ⟨endpoint, partner, directed, refusal⟩ every
    obtain ⟨inventory, lewis⟩ := every endpoint partner directed
    have present := (source.mainGroupClosedValenceLewisEndpointInventory?_eq_some_iff
      endpoint partner inventory).mpr lewis
    have absent := (source.mainGroupClosedValenceLewisEndpointInventory?_eq_none_iff_refusal
      endpoint partner).mpr refusal
    rw [absent] at present
    contradiction

/-- Molecule input populated automatically from the Lewis-derived atom records. -/
noncomputable def withMainGroupLewisAtomElectronicStates
    (source : AuthoritativeChemicalInput) :
    AuthoritativeChemicalInputWithAtomElectronicStates where
  source := source
  atomElectronicStates := source.mainGroupLewisAtomElectronicStateRecords

/-- The generated input covers every retained endpoint on the explicit applicability domain. -/
theorem withMainGroupLewisAtomElectronicStates_covers
    (source : AuthoritativeChemicalInput)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisDerivable) :
    source.withMainGroupLewisAtomElectronicStates.CoversCanonicalIndividualDoubleBondEndpoints := by
  intro endpoint partner directed
  obtain ⟨inventory, endpointLewis⟩ := derivable endpoint partner directed
  have atomLewis : source.MainGroupClosedValenceLewisAtomInventory endpoint inventory :=
    ⟨partner, directed, endpointLewis⟩
  refine ⟨inventory, ?_⟩
  unfold AuthoritativeChemicalInputWithAtomElectronicStates.inventoryAt?
  apply (source.aromaticCanonicalAtomElectronicStateLookup?_eq_some_iff
    source.mainGroupLewisAtomElectronicStateRecords
    source.mainGroupLewisAtomElectronicStateRecords_keys_nodup endpoint inventory).mpr
  let record : source.AromaticCanonicalAtomElectronicStateRecord :=
    { atom := endpoint, inventory := inventory }
  exact ⟨record,
    (source.mem_mainGroupLewisAtomElectronicStateRecords_iff record).mpr atomLewis,
    rfl, rfl⟩

/-- Structural source validity and Lewis derivability construct the certified finite atom-state
input with no supplied inventory counts. -/
noncomputable def certifiedWithMainGroupLewisAtomElectronicStates
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisDerivable) :
    CertifiedAuthoritativeChemicalInputWithAtomElectronicStates where
  input := source.withMainGroupLewisAtomElectronicStates
  structurallyWellFormed := ⟨sourceWellFormed,
    source.mainGroupLewisAtomElectronicStateRecords_wellFormed⟩
  coversCanonicalIndividualDoubleBondEndpoints :=
    source.withMainGroupLewisAtomElectronicStates_covers derivable

/-- The Lewis-derived analyzer is the complete exact inventory-aware family analyzer. -/
noncomputable def analyzeOrdinaryDoubleBondsWithMainGroupLewisInventories
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisDerivable)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  (source.certifiedWithMainGroupLewisAtomElectronicStates sourceWellFormed derivable).analyzeOrdinaryDoubleBonds
    carrierFuel viewAt

theorem mem_analyzeOrdinaryDoubleBondsWithMainGroupLewisInventories_iff_canonical
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisDerivable)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ source.analyzeOrdinaryDoubleBondsWithMainGroupLewisInventories
        sourceWellFormed derivable carrierFuel viewAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (source.certifiedWithMainGroupLewisAtomElectronicStates
            sourceWellFormed derivable).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) assignment := by
  exact (source.certifiedWithMainGroupLewisAtomElectronicStates
    sourceWellFormed derivable).mem_analyzeOrdinaryDoubleBonds_iff_canonical
      carrierFuel viewAt assignment

theorem analyzeOrdinaryDoubleBondsWithMainGroupLewisInventories_nodup
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisDerivable)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    (source.analyzeOrdinaryDoubleBondsWithMainGroupLewisInventories
      sourceWellFormed derivable carrierFuel viewAt).Nodup := by
  exact (source.certifiedWithMainGroupLewisAtomElectronicStates
    sourceWellFormed derivable).analyzeOrdinaryDoubleBonds_nodup carrierFuel viewAt

/-- Every retained bond in the Lewis-derived family is uniquely emitted or receives the complete
base/virtual-reference refusal classification. -/
theorem every_mainGroupLewisIndividualDoubleBond_exact_success_or_refusal
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisDerivable)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel
          (source.certifiedWithMainGroupLewisAtomElectronicStates
            sourceWellFormed derivable).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈ source.analyzeOrdinaryDoubleBondsWithMainGroupLewisInventories
            sourceWellFormed derivable carrierFuel viewAt ∧ assignment.bond = bond) ∨
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel
          (source.certifiedWithMainGroupLewisAtomElectronicStates
            sourceWellFormed derivable).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel
          (source.certifiedWithMainGroupLewisAtomElectronicStates
            sourceWellFormed derivable).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) = none) := by
  exact (source.certifiedWithMainGroupLewisAtomElectronicStates
    sourceWellFormed derivable).every_individualDoubleBond_exact_success_or_refusal
      carrierFuel viewAt

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
