import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralSourceCertification

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Hybrid generalized-Lewis inference and authoritative atom evidence

Connectivity and the independent main-group electron ledger determine every endpoint inventory
except the proved two-H versus lone-pair-plus-vacancy collision.  This module combines automatic
unique inference with a finite list of independently supplied atom states.  Supplied states are
not trusted by declaration: keys must be unique and every supplied inventory must satisfy the same
generalized atom relation.  The resulting one-record-per-atom source is certified exactly when
each retained endpoint is resolved by one of those two routes.
-/

def MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalAtomElectronicStateRecord) : Prop :=
  (records.map AromaticCanonicalAtomElectronicStateRecord.key).Nodup ∧
    ∀ record, record ∈ records →
      source.MainGroupLewisGeneralAtomInventory record.atom record.inventory

theorem mainGroupLewisGeneralSuppliedAtomElectronicStateLookup?_general
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalAtomElectronicStateRecord)
    (wellFormed :
      source.MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed records)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (lookedUp : source.aromaticCanonicalAtomElectronicStateLookup? records atom = some inventory) :
    source.MainGroupLewisGeneralAtomInventory atom inventory := by
  rcases (source.aromaticCanonicalAtomElectronicStateLookup?_eq_some_iff
    records wellFormed.1 atom inventory).mp lookedUp with
    ⟨record, present, atomIdentity, inventoryIdentity⟩
  simpa [atomIdentity, inventoryIdentity] using wellFormed.2 record present

theorem mainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed_generic
    (source : AuthoritativeChemicalInput)
    (records : List source.AromaticCanonicalAtomElectronicStateRecord)
    (wellFormed :
      source.MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed records) :
    source.AromaticCanonicalAtomElectronicStateRecordsWellFormed records := by
  refine ⟨wellFormed.1, ?_⟩
  intro record present partner directed
  exact ((source.mainGroupLewisGeneralAtomInventory_iff_endpoint
    record.atom partner directed record.inventory).mp
      (wellFormed.2 record present)).1

def MainGroupLewisGeneralHybridAtomInventory
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  source.aromaticCanonicalAtomElectronicStateLookup? supplied atom = some inventory ∨
    (source.aromaticCanonicalAtomElectronicStateLookup? supplied atom = none ∧
      source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory atom inventory)

noncomputable def mainGroupLewisGeneralHybridAtomInventory?
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (atom : source.AromaticCanonicalAtom) :
    Option AromaticCanonicalRule3EndpointElectronicInventory :=
  match source.aromaticCanonicalAtomElectronicStateLookup? supplied atom with
  | some inventory => some inventory
  | none => source.mainGroupLewisUniqueGeneralAtomInventory? atom

@[simp] theorem mainGroupLewisGeneralHybridAtomInventory?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (atom : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    source.mainGroupLewisGeneralHybridAtomInventory? supplied atom = some inventory ↔
      source.MainGroupLewisGeneralHybridAtomInventory supplied atom inventory := by
  unfold mainGroupLewisGeneralHybridAtomInventory?
    MainGroupLewisGeneralHybridAtomInventory
  cases observed : source.aromaticCanonicalAtomElectronicStateLookup? supplied atom with
  | none =>
      simp [source.mainGroupLewisUniqueGeneralAtomInventory?_eq_some_iff atom inventory]
  | some actual => simp

noncomputable def mainGroupLewisGeneralHybridAtomElectronicStateRecord?
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (atom : source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalAtomElectronicStateRecord :=
  (source.mainGroupLewisGeneralHybridAtomInventory? supplied atom).map fun inventory =>
    { atom := atom, inventory := inventory }

theorem mainGroupLewisGeneralHybridAtomElectronicStateRecord?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (atom : source.AromaticCanonicalAtom)
    (record : source.AromaticCanonicalAtomElectronicStateRecord) :
    source.mainGroupLewisGeneralHybridAtomElectronicStateRecord? supplied atom = some record ↔
      record.atom = atom ∧
        source.MainGroupLewisGeneralHybridAtomInventory supplied atom record.inventory := by
  rcases record with ⟨recordAtom, recordInventory⟩
  unfold mainGroupLewisGeneralHybridAtomElectronicStateRecord?
  cases observed : source.mainGroupLewisGeneralHybridAtomInventory? supplied atom with
  | none =>
      simp only [Option.map_none, reduceCtorEq, false_iff]
      rintro ⟨_atomIdentity, hybrid⟩
      have present :=
        (source.mainGroupLewisGeneralHybridAtomInventory?_eq_some_iff
          supplied atom recordInventory).mpr hybrid
      rw [observed] at present
      contradiction
  | some inventory =>
      have hybrid :=
        (source.mainGroupLewisGeneralHybridAtomInventory?_eq_some_iff
          supplied atom inventory).mp observed
      constructor
      · intro computed
        have recordIdentity :
            ({ atom := atom, inventory := inventory } :
              source.AromaticCanonicalAtomElectronicStateRecord) =
                { atom := recordAtom, inventory := recordInventory } :=
          Option.some.inj (by simpa [observed] using computed)
        cases recordIdentity
        exact ⟨rfl, hybrid⟩
      · rintro ⟨atomIdentity, recordHybrid⟩
        have inventoryIdentity : inventory = recordInventory := by
          rcases hybrid with suppliedActual | ⟨suppliedAbsent, inferredActual⟩
          · rcases recordHybrid with suppliedRecord | ⟨recordAbsent, _inferredRecord⟩
            · rw [suppliedActual] at suppliedRecord
              exact Option.some.inj suppliedRecord
            · rw [suppliedActual] at recordAbsent
              contradiction
          · rcases recordHybrid with suppliedRecord | ⟨_recordAbsent, inferredRecord⟩
            · rw [suppliedAbsent] at suppliedRecord
              contradiction
            · exact inferredRecord.2 inventory inferredActual.1
        simpa [observed, inventoryIdentity] using atomIdentity.symm

noncomputable def mainGroupLewisGeneralHybridAtomElectronicStateRecords
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) :
    List source.AromaticCanonicalAtomElectronicStateRecord :=
  source.aromaticCanonicalAtomUniverse.filterMap
    (source.mainGroupLewisGeneralHybridAtomElectronicStateRecord? supplied)

private noncomputable def mainGroupLewisGeneralHybridAtomKey?
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (atom : source.AromaticCanonicalAtom) : Option ℕ :=
  (source.mainGroupLewisGeneralHybridAtomInventory? supplied atom).map fun _ => atom.val

private theorem map_mainGroupLewisGeneralHybridRecords_key
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (atoms : List source.AromaticCanonicalAtom) :
    (atoms.filterMap
        (source.mainGroupLewisGeneralHybridAtomElectronicStateRecord? supplied)).map
        AromaticCanonicalAtomElectronicStateRecord.key =
      atoms.filterMap (source.mainGroupLewisGeneralHybridAtomKey? supplied) := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      cases observed : source.mainGroupLewisGeneralHybridAtomInventory? supplied atom <;>
        simp [mainGroupLewisGeneralHybridAtomElectronicStateRecord?,
          mainGroupLewisGeneralHybridAtomKey?, observed, inductionHypothesis,
          AromaticCanonicalAtomElectronicStateRecord.key]

theorem mainGroupLewisGeneralHybridAtomElectronicStateRecords_keys_nodup
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) :
    ((source.mainGroupLewisGeneralHybridAtomElectronicStateRecords supplied).map
      AromaticCanonicalAtomElectronicStateRecord.key).Nodup := by
  classical
  rw [mainGroupLewisGeneralHybridAtomElectronicStateRecords,
    source.map_mainGroupLewisGeneralHybridRecords_key supplied
      source.aromaticCanonicalAtomUniverse]
  apply List.Nodup.filterMap
  · intro left right key leftComputed rightComputed
    unfold mainGroupLewisGeneralHybridAtomKey? at leftComputed rightComputed
    cases leftObserved : source.mainGroupLewisGeneralHybridAtomInventory? supplied left <;>
      simp [leftObserved] at leftComputed
    cases rightObserved : source.mainGroupLewisGeneralHybridAtomInventory? supplied right <;>
      simp [rightObserved] at rightComputed
    apply Fin.ext
    omega
  · exact source.aromaticCanonicalAtomUniverse_nodup

theorem mem_mainGroupLewisGeneralHybridAtomElectronicStateRecords_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (record : source.AromaticCanonicalAtomElectronicStateRecord) :
    record ∈ source.mainGroupLewisGeneralHybridAtomElectronicStateRecords supplied ↔
      source.MainGroupLewisGeneralHybridAtomInventory
        supplied record.atom record.inventory := by
  classical
  rw [mainGroupLewisGeneralHybridAtomElectronicStateRecords, List.mem_filterMap]
  constructor
  · rintro ⟨atom, _present, computed⟩
    obtain ⟨atomIdentity, hybrid⟩ :=
      (source.mainGroupLewisGeneralHybridAtomElectronicStateRecord?_eq_some_iff
        supplied atom record).mp computed
    simpa [atomIdentity] using hybrid
  · intro hybrid
    rcases record with ⟨atom, inventory⟩
    refine ⟨atom, source.mem_aromaticCanonicalAtomUniverse atom, ?_⟩
    exact (source.mainGroupLewisGeneralHybridAtomElectronicStateRecord?_eq_some_iff
      supplied atom { atom := atom, inventory := inventory }).mpr ⟨rfl, hybrid⟩

theorem mainGroupLewisGeneralHybridAtomElectronicStateRecords_wellFormed
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (suppliedWellFormed :
      source.MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed supplied) :
    source.AromaticCanonicalAtomElectronicStateRecordsWellFormed
      (source.mainGroupLewisGeneralHybridAtomElectronicStateRecords supplied) := by
  refine ⟨source.mainGroupLewisGeneralHybridAtomElectronicStateRecords_keys_nodup supplied, ?_⟩
  intro record present partner directed
  have hybrid :=
    (source.mem_mainGroupLewisGeneralHybridAtomElectronicStateRecords_iff
      supplied record).mp present
  have atomLewis : source.MainGroupLewisGeneralAtomInventory record.atom record.inventory := by
    rcases hybrid with suppliedRecord | ⟨_suppliedAbsent, inferred⟩
    · exact source.mainGroupLewisGeneralSuppliedAtomElectronicStateLookup?_general
        supplied suppliedWellFormed record.atom record.inventory suppliedRecord
    · exact inferred.1
  exact ((source.mainGroupLewisGeneralAtomInventory_iff_endpoint
    record.atom partner directed record.inventory).mp atomLewis).1

def EveryIndividualDoubleBondEndpointMainGroupLewisGeneralHybridResolved
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) : Prop :=
  ∀ endpoint partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      ∃ inventory,
        source.MainGroupLewisGeneralHybridAtomInventory supplied endpoint inventory

noncomputable def withMainGroupLewisGeneralHybridAtomElectronicStates
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) :
    AuthoritativeChemicalInputWithAtomElectronicStates where
  source := source
  atomElectronicStates := source.mainGroupLewisGeneralHybridAtomElectronicStateRecords supplied

theorem withMainGroupLewisGeneralHybridAtomElectronicStates_covers_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) :
    (source.withMainGroupLewisGeneralHybridAtomElectronicStates supplied).CoversCanonicalIndividualDoubleBondEndpoints ↔
      source.EveryIndividualDoubleBondEndpointMainGroupLewisGeneralHybridResolved supplied := by
  classical
  constructor
  · intro covers endpoint partner directed
    rcases covers endpoint partner directed with ⟨inventory, lookedUp⟩
    change source.aromaticCanonicalAtomElectronicStateLookup?
        (source.mainGroupLewisGeneralHybridAtomElectronicStateRecords supplied)
        endpoint = some inventory at lookedUp
    rcases (source.aromaticCanonicalAtomElectronicStateLookup?_eq_some_iff
      (source.mainGroupLewisGeneralHybridAtomElectronicStateRecords supplied)
      (source.mainGroupLewisGeneralHybridAtomElectronicStateRecords_keys_nodup supplied)
      endpoint inventory).mp lookedUp with
      ⟨record, present, atomIdentity, inventoryIdentity⟩
    have hybrid :=
      (source.mem_mainGroupLewisGeneralHybridAtomElectronicStateRecords_iff
        supplied record).mp present
    exact ⟨inventory, by simpa [atomIdentity, inventoryIdentity] using hybrid⟩
  · intro resolved endpoint partner directed
    rcases resolved endpoint partner directed with ⟨inventory, hybrid⟩
    refine ⟨inventory, ?_⟩
    change source.aromaticCanonicalAtomElectronicStateLookup?
        (source.mainGroupLewisGeneralHybridAtomElectronicStateRecords supplied)
        endpoint = some inventory
    apply (source.aromaticCanonicalAtomElectronicStateLookup?_eq_some_iff
      (source.mainGroupLewisGeneralHybridAtomElectronicStateRecords supplied)
      (source.mainGroupLewisGeneralHybridAtomElectronicStateRecords_keys_nodup supplied)
      endpoint inventory).mpr
    let record : source.AromaticCanonicalAtomElectronicStateRecord :=
      { atom := endpoint, inventory := inventory }
    exact ⟨record,
      (source.mem_mainGroupLewisGeneralHybridAtomElectronicStateRecords_iff
        supplied record).mpr hybrid, rfl, rfl⟩

def MainGroupLewisGeneralHybridCertificationReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) : Prop :=
  source.StructurallyWellFormed ∧
    source.MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed supplied ∧
      source.EveryIndividualDoubleBondEndpointMainGroupLewisGeneralHybridResolved supplied

def MainGroupLewisGeneralHybridCertificationRefusal
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) : Prop :=
  ¬ source.StructurallyWellFormed ∨
    ¬ (supplied.map AromaticCanonicalAtomElectronicStateRecord.key).Nodup ∨
    (∃ record ∈ supplied,
      ¬ source.MainGroupLewisGeneralAtomInventory record.atom record.inventory) ∨
    (∃ endpoint partner,
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
        source.aromaticCanonicalAtomElectronicStateLookup? supplied endpoint = none ∧
          ¬ ∃ inventory,
            source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory endpoint inventory)

theorem not_mainGroupLewisGeneralHybridCertificationReady_iff_refusal
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) :
    ¬ source.MainGroupLewisGeneralHybridCertificationReady supplied ↔
      source.MainGroupLewisGeneralHybridCertificationRefusal supplied := by
  classical
  unfold MainGroupLewisGeneralHybridCertificationReady
    MainGroupLewisGeneralHybridCertificationRefusal
    MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed
    EveryIndividualDoubleBondEndpointMainGroupLewisGeneralHybridResolved
    MainGroupLewisGeneralHybridAtomInventory
  constructor
  · intro notReady
    by_cases sourceWellFormed : source.StructurallyWellFormed
    · by_cases uniqueKeys :
        (supplied.map AromaticCanonicalAtomElectronicStateRecord.key).Nodup
      · by_cases suppliedGeneral : ∀ record, record ∈ supplied →
          source.MainGroupLewisGeneralAtomInventory record.atom record.inventory
        · right; right; right
          have unresolved : ¬ ∀ endpoint partner,
              source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
                ∃ inventory,
                  source.aromaticCanonicalAtomElectronicStateLookup? supplied endpoint = some inventory ∨
                    (source.aromaticCanonicalAtomElectronicStateLookup? supplied endpoint = none ∧
                      source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory endpoint inventory) := by
            intro resolved
            exact notReady ⟨sourceWellFormed, ⟨uniqueKeys, suppliedGeneral⟩, resolved⟩
          push_neg at unresolved
          rcases unresolved with ⟨endpoint, partner, directed, noResolution⟩
          refine ⟨endpoint, partner, directed, ?_⟩
          cases observed : source.aromaticCanonicalAtomElectronicStateLookup? supplied endpoint with
          | some inventory => exact False.elim ((noResolution inventory).1 observed)
          | none =>
              refine ⟨rfl, ?_⟩
              rintro ⟨inventory, unique⟩
              exact (noResolution inventory).2 observed unique
        · right; right; left
          push_neg at suppliedGeneral
          exact suppliedGeneral
      · right; left
        exact uniqueKeys
    · exact Or.inl sourceWellFormed
  · rintro (sourceInvalid | duplicateKeys | invalidRecord | unresolved)
      ⟨sourceWellFormed, ⟨uniqueKeys, suppliedGeneral⟩, resolved⟩
    · exact sourceInvalid sourceWellFormed
    · exact duplicateKeys uniqueKeys
    · rcases invalidRecord with ⟨record, present, invalid⟩
      exact invalid (suppliedGeneral record present)
    · rcases unresolved with ⟨endpoint, partner, directed, absent, noUnique⟩
      rcases resolved endpoint partner directed with
        ⟨inventory, suppliedRecord | ⟨_absentAgain, unique⟩⟩
      · rw [absent] at suppliedRecord
        contradiction
      · exact noUnique ⟨inventory, unique⟩

noncomputable def certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied) :
    CertifiedAuthoritativeChemicalInputWithAtomElectronicStates where
  input := source.withMainGroupLewisGeneralHybridAtomElectronicStates supplied
  structurallyWellFormed := ⟨ready.1,
    source.mainGroupLewisGeneralHybridAtomElectronicStateRecords_wellFormed
      supplied ready.2.1⟩
  coversCanonicalIndividualDoubleBondEndpoints :=
    (source.withMainGroupLewisGeneralHybridAtomElectronicStates_covers_iff supplied).mpr
      ready.2.2

noncomputable def certifyMainGroupLewisGeneralHybridAtomElectronicStates?
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) :
    Option CertifiedAuthoritativeChemicalInputWithAtomElectronicStates := by
  classical
  exact if ready : source.MainGroupLewisGeneralHybridCertificationReady supplied then
    some (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady supplied ready)
  else none

@[simp] theorem certifyMainGroupLewisGeneralHybridAtomElectronicStates?_isSome_iff_ready
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) :
    (source.certifyMainGroupLewisGeneralHybridAtomElectronicStates? supplied).isSome ↔
      source.MainGroupLewisGeneralHybridCertificationReady supplied := by
  classical
  simp [certifyMainGroupLewisGeneralHybridAtomElectronicStates?]

@[simp] theorem certifyMainGroupLewisGeneralHybridAtomElectronicStates?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord) :
    source.certifyMainGroupLewisGeneralHybridAtomElectronicStates? supplied = none ↔
      source.MainGroupLewisGeneralHybridCertificationRefusal supplied := by
  classical
  rw [← source.not_mainGroupLewisGeneralHybridCertificationReady_iff_refusal]
  simp [certifyMainGroupLewisGeneralHybridAtomElectronicStates?]

theorem suppliedAtomElectronicState_eq_inferred_of_unique
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (suppliedWellFormed :
      source.MainGroupLewisGeneralSuppliedAtomElectronicStateRecordsWellFormed supplied)
    (atom : source.AromaticCanonicalAtom)
    (suppliedInventory inferredInventory :
      AromaticCanonicalRule3EndpointElectronicInventory)
    (lookedUp : source.aromaticCanonicalAtomElectronicStateLookup? supplied atom =
      some suppliedInventory)
    (inferred : source.UniquelyDeterminedMainGroupLewisGeneralAtomInventory
      atom inferredInventory) :
    suppliedInventory = inferredInventory := by
  exact inferred.2 suppliedInventory
    (source.mainGroupLewisGeneralSuppliedAtomElectronicStateLookup?_general
      supplied suppliedWellFormed atom suppliedInventory lookedUp)

theorem exactCollision_requires_suppliedAtomElectronicState_of_hybridReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (endpoint partner : source.AromaticCanonicalAtom)
    (directed :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner)
    (hydrogenPair : source.MainGroupLewisGeneralEndpointInventory endpoint partner
      mainGroupLewisHydrogenPairInventory)
    (lonePairVacancy : source.MainGroupLewisGeneralEndpointInventory endpoint partner
      mainGroupLewisLonePairVacancyInventory) :
    ∃ inventory,
      source.aromaticCanonicalAtomElectronicStateLookup? supplied endpoint = some inventory := by
  rcases ready.2.2 endpoint partner directed with
    ⟨inventory, suppliedRecord | ⟨_suppliedAbsent, inferred⟩⟩
  · exact ⟨inventory, suppliedRecord⟩
  · have hydrogenAtom : source.MainGroupLewisGeneralAtomInventory endpoint
        mainGroupLewisHydrogenPairInventory :=
      (source.mainGroupLewisGeneralAtomInventory_iff_endpoint
        endpoint partner directed mainGroupLewisHydrogenPairInventory).mpr hydrogenPair
    have vacancyAtom : source.MainGroupLewisGeneralAtomInventory endpoint
        mainGroupLewisLonePairVacancyInventory :=
      (source.mainGroupLewisGeneralAtomInventory_iff_endpoint
        endpoint partner directed mainGroupLewisLonePairVacancyInventory).mpr lonePairVacancy
    have hydrogenIdentity := inferred.2 mainGroupLewisHydrogenPairInventory hydrogenAtom
    have vacancyIdentity := inferred.2 mainGroupLewisLonePairVacancyInventory vacancyAtom
    exact False.elim ((show mainGroupLewisHydrogenPairInventory ≠
      mainGroupLewisLonePairVacancyInventory by decide)
        (hydrogenIdentity.trans vacancyIdentity.symm))

theorem exactCollision_suppliedAtomElectronicState_has_exact_shape_of_hybridReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (endpoint partner : source.AromaticCanonicalAtom)
    (directed :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner)
    (hydrogenPair : source.MainGroupLewisGeneralEndpointInventory endpoint partner
      mainGroupLewisHydrogenPairInventory)
    (lonePairVacancy : source.MainGroupLewisGeneralEndpointInventory endpoint partner
      mainGroupLewisLonePairVacancyInventory) :
    ∃ inventory,
      source.aromaticCanonicalAtomElectronicStateLookup? supplied endpoint = some inventory ∧
        (inventory = mainGroupLewisHydrogenPairInventory ∨
          inventory = mainGroupLewisLonePairVacancyInventory) := by
  rcases source.exactCollision_requires_suppliedAtomElectronicState_of_hybridReady
    supplied ready endpoint partner directed hydrogenPair lonePairVacancy with
    ⟨inventory, lookedUp⟩
  have atomLewis : source.MainGroupLewisGeneralAtomInventory endpoint inventory :=
    source.mainGroupLewisGeneralSuppliedAtomElectronicStateLookup?_general
      supplied ready.2.1 endpoint inventory lookedUp
  have endpointLewis :
      source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory :=
    (source.mainGroupLewisGeneralAtomInventory_iff_endpoint
      endpoint partner directed inventory).mp atomLewis
  by_cases hydrogenIdentity : inventory = mainGroupLewisHydrogenPairInventory
  · exact ⟨inventory, lookedUp, Or.inl hydrogenIdentity⟩
  · have shapes := source.mainGroupLewisGeneralEndpoint_distinct_solutions_exact_shapes
      endpoint partner inventory mainGroupLewisHydrogenPairInventory
      endpointLewis hydrogenPair hydrogenIdentity
    rcases shapes with inventoryHydrogen | inventoryVacancy
    · exact ⟨inventory, lookedUp, Or.inl inventoryHydrogen.1⟩
    · exact ⟨inventory, lookedUp, Or.inr inventoryVacancy.2⟩

noncomputable def analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    Option (List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) := by
  classical
  exact if ready : source.MainGroupLewisGeneralHybridCertificationReady supplied then
    some ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      supplied ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt)
  else none

@[simp] theorem analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    source.analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?
        supplied carrierFuel viewAt = none ↔
      source.MainGroupLewisGeneralHybridCertificationRefusal supplied := by
  classical
  rw [← source.not_mainGroupLewisGeneralHybridCertificationReady_iff_refusal]
  simp [analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?]

theorem analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    source.analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?
        supplied carrierFuel viewAt =
      some ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
        supplied ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt) := by
  classical
  simp [analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?, ready]

theorem analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?_some_nodup
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignments : List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (computed : source.analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence?
      supplied carrierFuel viewAt = some assignments) : assignments.Nodup := by
  classical
  unfold analyzeOrdinaryDoubleBondsWithMainGroupLewisGeneralHybridEvidence? at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst assignments
    exact (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      supplied ready).analyzeOrdinaryDoubleBonds_nodup carrierFuel viewAt
  next notReady => contradiction

theorem mem_certifiedMainGroupLewisGeneralHybridAnalyzeOrdinaryDoubleBonds_iff_canonical
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈
        (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
          supplied ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            supplied ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) assignment := by
  exact (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
    supplied ready).mem_analyzeOrdinaryDoubleBonds_iff_canonical carrierFuel viewAt assignment

theorem every_certifiedMainGroupLewisGeneralHybridIndividualDoubleBond_exact_success_or_refusal
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel
          (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            supplied ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈
            (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
              supplied ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt ∧
            assignment.bond = bond) ∨
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel
          (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            supplied ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel
          (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            supplied ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) = none) := by
  exact (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
    supplied ready).every_individualDoubleBond_exact_success_or_refusal carrierFuel viewAt

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
