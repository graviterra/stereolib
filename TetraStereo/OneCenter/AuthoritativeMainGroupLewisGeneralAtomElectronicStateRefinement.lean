import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralEndpointInventory
import TetraStereo.OneCenter.AuthoritativeMainGroupLewisAtomElectronicStateRefinement

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Molecule-wide refinement of unique general Lewis inventories

This module lifts the vacancy-inclusive endpoint classifier to one finite record per atom.  Only a
mathematically unique solution becomes a record.  Impossibility and the exact two-H versus
lone-pair-plus-vacancy collision remain explicit refusals, after which the existing complete
ordinary-double-bond analyzer either emits its independently justified descriptor or refuses the
unsupported vacant/radical completion.
-/

def MainGroupLewisGeneralAtomInventory
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  ∃ partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint atom partner ∧
      source.MainGroupLewisGeneralEndpointInventory atom partner inventory

theorem mainGroupLewisGeneralAtomInventory_iff_endpoint
    (source : AuthoritativeChemicalInput)
    (atom partner : source.AromaticCanonicalAtom)
    (directed : source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint atom partner)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    source.MainGroupLewisGeneralAtomInventory atom inventory ↔
      source.MainGroupLewisGeneralEndpointInventory atom partner inventory := by
  constructor
  · rintro ⟨firstPartner, firstDirected, firstLewis⟩
    exact source.mainGroupLewisGeneralEndpointInventory_partner_independent
      atom firstPartner partner inventory firstDirected firstLewis directed
  · intro lewis
    exact ⟨partner, directed, lewis⟩

def UniquelyDeterminedMainGroupLewisGeneralAtomInventory
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  source.MainGroupLewisGeneralAtomInventory atom inventory ∧
    ∀ other, source.MainGroupLewisGeneralAtomInventory atom other → other = inventory

noncomputable def mainGroupLewisGeneralAtomSolutions
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    List AromaticCanonicalRule3EndpointElectronicInventory := by
  classical
  exact ((mainGroupLewisGeneralEndpointInventoryCandidates
    (source.molecule.atoms.get atom).unpairedElectrons).filter fun inventory =>
      decide (source.MainGroupLewisGeneralAtomInventory atom inventory)).dedup

@[simp] theorem mem_mainGroupLewisGeneralAtomSolutions_iff
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    inventory ∈ source.mainGroupLewisGeneralAtomSolutions atom ↔
      source.MainGroupLewisGeneralAtomInventory atom inventory := by
  classical
  unfold mainGroupLewisGeneralAtomSolutions
  rw [List.mem_dedup, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro atomLewis
    rcases atomLewis with ⟨partner, directed, endpointLewis⟩
    exact ⟨source.mem_mainGroupLewisGeneralEndpointInventoryCandidates_of_lewis
      atom partner inventory endpointLewis, ⟨partner, directed, endpointLewis⟩⟩

theorem mainGroupLewisGeneralAtomSolutions_nodup
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    (source.mainGroupLewisGeneralAtomSolutions atom).Nodup := by
  classical
  exact List.nodup_dedup _

noncomputable def mainGroupLewisUniqueGeneralAtomInventory?
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    Option AromaticCanonicalRule3EndpointElectronicInventory :=
  match source.mainGroupLewisGeneralAtomSolutions atom with
  | [inventory] => some inventory
  | _ => none

@[simp] theorem mainGroupLewisUniqueGeneralAtomInventory?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    source.mainGroupLewisUniqueGeneralAtomInventory? atom = some inventory ↔
      source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory atom inventory := by
  classical
  constructor
  · intro computed
    unfold mainGroupLewisUniqueGeneralAtomInventory? at computed
    cases solutionsObserved : source.mainGroupLewisGeneralAtomSolutions atom with
    | nil => simp [solutionsObserved] at computed
    | cons first rest =>
        cases rest with
        | nil =>
            simp [solutionsObserved] at computed
            subst first
            constructor
            · exact (source.mem_mainGroupLewisGeneralAtomSolutions_iff atom inventory).mp
                (by simp [solutionsObserved])
            · intro other otherLewis
              have present :=
                (source.mem_mainGroupLewisGeneralAtomSolutions_iff atom other).mpr otherLewis
              simpa [solutionsObserved] using present
        | cons second tail => simp [solutionsObserved] at computed
  · rintro ⟨lewis, unique⟩
    have inventoryPresent :=
      (source.mem_mainGroupLewisGeneralAtomSolutions_iff atom inventory).mpr lewis
    cases solutionsObserved : source.mainGroupLewisGeneralAtomSolutions atom with
    | nil => simp [solutionsObserved] at inventoryPresent
    | cons first rest =>
        have firstLewis :=
          (source.mem_mainGroupLewisGeneralAtomSolutions_iff atom first).mp
            (by simp [solutionsObserved])
        have firstIdentity := unique first firstLewis
        subst first
        cases rest with
        | nil => simp [mainGroupLewisUniqueGeneralAtomInventory?, solutionsObserved]
        | cons second tail =>
            have secondLewis :=
              (source.mem_mainGroupLewisGeneralAtomSolutions_iff atom second).mp
                (by simp [solutionsObserved])
            have secondIdentity := unique second secondLewis
            subst second
            have nodup := source.mainGroupLewisGeneralAtomSolutions_nodup atom
            rw [solutionsObserved] at nodup
            simp at nodup

def MainGroupLewisGeneralAtomRefusal
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) : Prop :=
  (¬ ∃ inventory, source.MainGroupLewisGeneralAtomInventory atom inventory) ∨
  (∃ left right,
    source.MainGroupLewisGeneralAtomInventory atom left ∧
      source.MainGroupLewisGeneralAtomInventory atom right ∧ left ≠ right)

theorem mainGroupLewisUniqueGeneralAtomInventory?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    source.mainGroupLewisUniqueGeneralAtomInventory? atom = none ↔
      source.MainGroupLewisGeneralAtomRefusal atom := by
  classical
  constructor
  · intro absent
    by_cases existsSolution : ∃ inventory,
        source.MainGroupLewisGeneralAtomInventory atom inventory
    · rcases existsSolution with ⟨inventory, lewis⟩
      right
      by_contra noAmbiguity
      push_neg at noAmbiguity
      have unique : ∀ other, source.MainGroupLewisGeneralAtomInventory atom other →
          other = inventory := by
        intro other otherLewis
        by_contra different
        exact different (noAmbiguity inventory other lewis otherLewis).symm
      have present :=
        (source.mainGroupLewisUniqueGeneralAtomInventory?_eq_some_iff atom inventory).mpr
          ⟨lewis, unique⟩
      rw [absent] at present
      contradiction
    · exact Or.inl existsSolution
  · intro refusal
    cases observed : source.mainGroupLewisUniqueGeneralAtomInventory? atom with
    | none => rfl
    | some inventory =>
        obtain ⟨lewis, unique⟩ :=
          (source.mainGroupLewisUniqueGeneralAtomInventory?_eq_some_iff atom inventory).mp observed
        rcases refusal with impossible | ambiguous
        · exact False.elim (impossible ⟨inventory, lewis⟩)
        · rcases ambiguous with ⟨left, right, leftLewis, rightLewis, different⟩
          exact False.elim (different ((unique left leftLewis).trans
            (unique right rightLewis).symm))

noncomputable def mainGroupLewisUniqueGeneralAtomElectronicStateRecord?
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalAtomElectronicStateRecord :=
  (source.mainGroupLewisUniqueGeneralAtomInventory? atom).map fun inventory =>
    { atom := atom, inventory := inventory }

theorem mainGroupLewisUniqueGeneralAtomElectronicStateRecord?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom)
    (record : source.AromaticCanonicalAtomElectronicStateRecord) :
    source.mainGroupLewisUniqueGeneralAtomElectronicStateRecord? atom = some record ↔
      record.atom = atom ∧
        source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory atom record.inventory := by
  rcases record with ⟨recordAtom, recordInventory⟩
  unfold mainGroupLewisUniqueGeneralAtomElectronicStateRecord?
  cases observed : source.mainGroupLewisUniqueGeneralAtomInventory? atom with
  | none =>
      simp only [Option.map_none, reduceCtorEq, false_iff]
      rintro ⟨_atomIdentity, recordUnique⟩
      have present :=
        (source.mainGroupLewisUniqueGeneralAtomInventory?_eq_some_iff
          atom recordInventory).mpr recordUnique
      rw [observed] at present
      contradiction
  | some inventory =>
      have unique :=
        (source.mainGroupLewisUniqueGeneralAtomInventory?_eq_some_iff atom inventory).mp observed
      constructor
      · intro computed
        have recordIdentity :
            ({ atom := atom, inventory := inventory } :
              source.AromaticCanonicalAtomElectronicStateRecord) =
                { atom := recordAtom, inventory := recordInventory } :=
          Option.some.inj (by simpa [observed] using computed)
        cases recordIdentity
        exact ⟨rfl, unique⟩
      · rintro ⟨atomIdentity, recordUnique⟩
        have inventoryIdentity := recordUnique.2 inventory unique.1
        simpa [observed, inventoryIdentity] using atomIdentity.symm

noncomputable def mainGroupLewisUniqueGeneralAtomElectronicStateRecords
    (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalAtomElectronicStateRecord :=
  source.aromaticCanonicalAtomUniverse.filterMap
    source.mainGroupLewisUniqueGeneralAtomElectronicStateRecord?

private noncomputable def mainGroupLewisUniqueGeneralAtomKey?
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) : Option ℕ :=
  (source.mainGroupLewisUniqueGeneralAtomInventory? atom).map fun _ => atom.val

private theorem map_mainGroupLewisUniqueGeneralRecords_key
    (source : AuthoritativeChemicalInput)
    (atoms : List source.AromaticCanonicalAtom) :
    (atoms.filterMap source.mainGroupLewisUniqueGeneralAtomElectronicStateRecord?).map
        AromaticCanonicalAtomElectronicStateRecord.key =
      atoms.filterMap source.mainGroupLewisUniqueGeneralAtomKey? := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      cases observed : source.mainGroupLewisUniqueGeneralAtomInventory? atom <;>
        simp [mainGroupLewisUniqueGeneralAtomElectronicStateRecord?,
          mainGroupLewisUniqueGeneralAtomKey?, observed, inductionHypothesis,
          AromaticCanonicalAtomElectronicStateRecord.key]

theorem mainGroupLewisUniqueGeneralAtomElectronicStateRecords_keys_nodup
    (source : AuthoritativeChemicalInput) :
    ((source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords).map
      AromaticCanonicalAtomElectronicStateRecord.key).Nodup := by
  classical
  rw [mainGroupLewisUniqueGeneralAtomElectronicStateRecords,
    source.map_mainGroupLewisUniqueGeneralRecords_key source.aromaticCanonicalAtomUniverse]
  apply List.Nodup.filterMap
  · intro left right key leftComputed rightComputed
    unfold mainGroupLewisUniqueGeneralAtomKey? at leftComputed rightComputed
    cases leftObserved : source.mainGroupLewisUniqueGeneralAtomInventory? left <;>
      simp [leftObserved] at leftComputed
    cases rightObserved : source.mainGroupLewisUniqueGeneralAtomInventory? right <;>
      simp [rightObserved] at rightComputed
    apply Fin.ext
    omega
  · exact source.aromaticCanonicalAtomUniverse_nodup

theorem mem_mainGroupLewisUniqueGeneralAtomElectronicStateRecords_iff
    (source : AuthoritativeChemicalInput)
    (record : source.AromaticCanonicalAtomElectronicStateRecord) :
    record ∈ source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords ↔
      source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory
        record.atom record.inventory := by
  classical
  rw [mainGroupLewisUniqueGeneralAtomElectronicStateRecords, List.mem_filterMap]
  constructor
  · rintro ⟨atom, _present, computed⟩
    obtain ⟨atomIdentity, unique⟩ :=
      (source.mainGroupLewisUniqueGeneralAtomElectronicStateRecord?_eq_some_iff
        atom record).mp computed
    simpa [atomIdentity] using unique
  · intro unique
    rcases record with ⟨atom, inventory⟩
    refine ⟨atom, source.mem_aromaticCanonicalAtomUniverse atom, ?_⟩
    apply (source.mainGroupLewisUniqueGeneralAtomElectronicStateRecord?_eq_some_iff
      atom { atom := atom, inventory := inventory }).mpr
    exact ⟨rfl, unique⟩

theorem mainGroupLewisUniqueGeneralAtomElectronicStateRecords_wellFormed
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalAtomElectronicStateRecordsWellFormed
      source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords := by
  refine ⟨source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords_keys_nodup, ?_⟩
  intro record present partner directed
  have unique :=
    (source.mem_mainGroupLewisUniqueGeneralAtomElectronicStateRecords_iff record).mp present
  rcases unique.1 with ⟨firstPartner, firstDirected, firstLewis⟩
  exact (source.mainGroupLewisGeneralEndpointInventory_partner_independent
    record.atom firstPartner partner record.inventory firstDirected firstLewis directed).1

def EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable
    (source : AuthoritativeChemicalInput) : Prop :=
  ∀ endpoint partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      ∃ inventory,
        source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory ∧
          ∀ other,
            source.MainGroupLewisGeneralEndpointInventory endpoint partner other →
              other = inventory

theorem not_everyIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable_iff
    (source : AuthoritativeChemicalInput) :
    ¬ source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable ↔
      ∃ endpoint partner,
        source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
          source.MainGroupLewisGeneralEndpointRefusal endpoint partner := by
  classical
  unfold EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable
  constructor
  · intro notEvery
    push_neg at notEvery
    rcases notEvery with ⟨endpoint, partner, directed, noUnique⟩
    refine ⟨endpoint, partner, directed, ?_⟩
    rw [← source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_refusal]
    cases observed : source.mainGroupLewisUniqueGeneralEndpointInventory? endpoint partner with
    | none => rfl
    | some inventory =>
        have unique :=
          (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_some_iff
            endpoint partner inventory).mp observed
        rcases noUnique inventory unique.1 with ⟨other, otherLewis, different⟩
        exact False.elim (different (unique.2 other otherLewis))
  · rintro ⟨endpoint, partner, directed, refusal⟩ every
    rcases every endpoint partner directed with ⟨inventory, lewis, unique⟩
    have present :=
      (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_some_iff
        endpoint partner inventory).mpr ⟨lewis, unique⟩
    have absent :=
      (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_refusal
        endpoint partner).mpr refusal
    rw [absent] at present
    contradiction

theorem everyIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable_iff_no_refused_endpoint
    (source : AuthoritativeChemicalInput) :
    source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable ↔
      ¬ ∃ endpoint partner,
        source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
          source.MainGroupLewisGeneralEndpointRefusal endpoint partner := by
  constructor
  · intro every refused
    exact (source.not_everyIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable_iff.mpr
      refused) every
  · intro noRefusal
    by_contra notEvery
    exact noRefusal
      (source.not_everyIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable_iff.mp
        notEvery)

theorem not_everyIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable_iff_exact_failure
    (source : AuthoritativeChemicalInput) :
    ¬ source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable ↔
      ∃ endpoint partner,
        source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
          ((¬ ∃ inventory,
              source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory) ∨
            (source.MainGroupLewisGeneralEndpointInventory endpoint partner
                mainGroupLewisHydrogenPairInventory ∧
              source.MainGroupLewisGeneralEndpointInventory endpoint partner
                mainGroupLewisLonePairVacancyInventory)) := by
  rw [source.not_everyIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable_iff]
  constructor
  · rintro ⟨endpoint, partner, directed, refusal⟩
    refine ⟨endpoint, partner, directed, ?_⟩
    apply (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_noSolution_or_exactCollision
      endpoint partner).mp
    exact (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_refusal
      endpoint partner).mpr refusal
  · rintro ⟨endpoint, partner, directed, failure⟩
    refine ⟨endpoint, partner, directed, ?_⟩
    apply (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_refusal
      endpoint partner).mp
    exact (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_noSolution_or_exactCollision
      endpoint partner).mpr failure

noncomputable def withMainGroupLewisUniqueGeneralAtomElectronicStates
    (source : AuthoritativeChemicalInput) :
    AuthoritativeChemicalInputWithAtomElectronicStates where
  source := source
  atomElectronicStates := source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords

theorem withMainGroupLewisUniqueGeneralAtomElectronicStates_covers
    (source : AuthoritativeChemicalInput)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable) :
    source.withMainGroupLewisUniqueGeneralAtomElectronicStates.CoversCanonicalIndividualDoubleBondEndpoints := by
  intro endpoint partner directed
  rcases derivable endpoint partner directed with ⟨inventory, endpointLewis, endpointUnique⟩
  have atomLewis : source.MainGroupLewisGeneralAtomInventory endpoint inventory :=
    ⟨partner, directed, endpointLewis⟩
  have atomUnique : ∀ other, source.MainGroupLewisGeneralAtomInventory endpoint other →
      other = inventory := by
    intro other otherAtomLewis
    have otherEndpointLewis :=
      (source.mainGroupLewisGeneralAtomInventory_iff_endpoint
        endpoint partner directed other).mp otherAtomLewis
    exact endpointUnique other otherEndpointLewis
  refine ⟨inventory, ?_⟩
  unfold AuthoritativeChemicalInputWithAtomElectronicStates.inventoryAt?
  apply (source.aromaticCanonicalAtomElectronicStateLookup?_eq_some_iff
    source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords
    source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords_keys_nodup
    endpoint inventory).mpr
  let record : source.AromaticCanonicalAtomElectronicStateRecord :=
    { atom := endpoint, inventory := inventory }
  exact ⟨record,
    (source.mem_mainGroupLewisUniqueGeneralAtomElectronicStateRecords_iff record).mpr
      ⟨atomLewis, atomUnique⟩,
    rfl, rfl⟩

noncomputable def certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable) :
    CertifiedAuthoritativeChemicalInputWithAtomElectronicStates where
  input := source.withMainGroupLewisUniqueGeneralAtomElectronicStates
  structurallyWellFormed := ⟨sourceWellFormed,
    source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords_wellFormed⟩
  coversCanonicalIndividualDoubleBondEndpoints :=
    source.withMainGroupLewisUniqueGeneralAtomElectronicStates_covers derivable

noncomputable def analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  (source.certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
    sourceWellFormed derivable).analyzeOrdinaryDoubleBonds carrierFuel viewAt

theorem mem_analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories_iff_canonical
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ source.analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories
        sourceWellFormed derivable carrierFuel viewAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (source.certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
            sourceWellFormed derivable).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) assignment := by
  exact (source.certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
    sourceWellFormed derivable).mem_analyzeOrdinaryDoubleBonds_iff_canonical
      carrierFuel viewAt assignment

theorem analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories_nodup
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    (source.analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories
      sourceWellFormed derivable carrierFuel viewAt).Nodup := by
  exact (source.certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
    sourceWellFormed derivable).analyzeOrdinaryDoubleBonds_nodup carrierFuel viewAt

theorem every_mainGroupLewisUniqueGeneralIndividualDoubleBond_exact_success_or_refusal
    (source : AuthoritativeChemicalInput)
    (sourceWellFormed : source.StructurallyWellFormed)
    (derivable : source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel
          (source.certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
            sourceWellFormed derivable).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈
            source.analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories
              sourceWellFormed derivable carrierFuel viewAt ∧ assignment.bond = bond) ∨
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel
          (source.certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
            sourceWellFormed derivable).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel
          (source.certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
            sourceWellFormed derivable).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) = none) := by
  exact (source.certifiedWithMainGroupLewisUniqueGeneralAtomElectronicStates
    sourceWellFormed derivable).every_individualDoubleBond_exact_success_or_refusal
      carrierFuel viewAt

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
