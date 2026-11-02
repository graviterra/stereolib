import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralAtomElectronicStateRefinement
import TetraStereo.OneCenter.AuthoritativeChemicalInputAtomElectronicStateValidation

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Total source certification for generalized main-group Lewis inventories

The generalized Lewis atom compiler previously accepted a proof that every retained directed
ordinary-double-bond endpoint has one unique solution.  This module removes that opaque caller
boundary.  It proves that the generated finite atom records pass the existing exact validator if
and only if the source is structurally well formed and every endpoint is uniquely derivable.  A
failed certification is reduced to malformed source structure, no Lewis solution at a concrete
endpoint, or the sole proved two-H versus lone-pair-plus-vacancy collision.
-/

def MainGroupLewisGeneralSourceCertificationReady
    (source : AuthoritativeChemicalInput) : Prop :=
  source.StructurallyWellFormed ∧
    source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable

def MainGroupLewisGeneralSourceCertificationRefusal
    (source : AuthoritativeChemicalInput) : Prop :=
  ¬ source.StructurallyWellFormed ∨
    ∃ endpoint partner,
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
        ((¬ ∃ inventory,
            source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory) ∨
          (source.MainGroupLewisGeneralEndpointInventory endpoint partner
              mainGroupLewisHydrogenPairInventory ∧
            source.MainGroupLewisGeneralEndpointInventory endpoint partner
              mainGroupLewisLonePairVacancyInventory))

theorem not_mainGroupLewisGeneralSourceCertificationReady_iff_refusal
    (source : AuthoritativeChemicalInput) :
    ¬ source.MainGroupLewisGeneralSourceCertificationReady ↔
      source.MainGroupLewisGeneralSourceCertificationRefusal := by
  classical
  unfold MainGroupLewisGeneralSourceCertificationReady
    MainGroupLewisGeneralSourceCertificationRefusal
  constructor
  · intro notReady
    by_cases sourceWellFormed : source.StructurallyWellFormed
    · right
      apply source.not_everyIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable_iff_exact_failure.mp
      intro every
      exact notReady ⟨sourceWellFormed, every⟩
    · exact Or.inl sourceWellFormed
  · rintro (sourceInvalid | endpointFailure) ⟨sourceWellFormed, every⟩
    · exact sourceInvalid sourceWellFormed
    · exact
        (source.not_everyIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable_iff_exact_failure.mpr
          endpointFailure) every

theorem withMainGroupLewisUniqueGeneralAtomElectronicStates_covers_iff
    (source : AuthoritativeChemicalInput) :
    source.withMainGroupLewisUniqueGeneralAtomElectronicStates.CoversCanonicalIndividualDoubleBondEndpoints ↔
      source.EveryIndividualDoubleBondEndpointMainGroupLewisUniquelyDerivable := by
  classical
  constructor
  · intro covers endpoint partner directed
    rcases covers endpoint partner directed with ⟨inventory, lookedUp⟩
    change source.aromaticCanonicalAtomElectronicStateLookup?
        source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords endpoint = some inventory
      at lookedUp
    rcases (source.aromaticCanonicalAtomElectronicStateLookup?_eq_some_iff
      source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords
      source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords_keys_nodup
      endpoint inventory).mp lookedUp with
      ⟨record, present, atomIdentity, inventoryIdentity⟩
    have atomUnique :=
      (source.mem_mainGroupLewisUniqueGeneralAtomElectronicStateRecords_iff record).mp present
    have endpointLewis :
        source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory := by
      rw [← atomIdentity, ← inventoryIdentity]
      exact (source.mainGroupLewisGeneralAtomInventory_iff_endpoint
        record.atom partner (by simpa [atomIdentity] using directed) record.inventory).mp atomUnique.1
    refine ⟨inventory, endpointLewis, ?_⟩
    intro other otherEndpointLewis
    have otherAtomLewis : source.MainGroupLewisGeneralAtomInventory endpoint other :=
      (source.mainGroupLewisGeneralAtomInventory_iff_endpoint
        endpoint partner directed other).mpr otherEndpointLewis
    have otherIdentity : other = record.inventory :=
      atomUnique.2 other (by simpa [atomIdentity] using otherAtomLewis)
    exact otherIdentity.trans inventoryIdentity
  · exact source.withMainGroupLewisUniqueGeneralAtomElectronicStates_covers

theorem withMainGroupLewisUniqueGeneralAtomElectronicStates_certificationReady_iff
    (source : AuthoritativeChemicalInput) :
    source.withMainGroupLewisUniqueGeneralAtomElectronicStates.CertificationReady ↔
      source.MainGroupLewisGeneralSourceCertificationReady := by
  unfold AuthoritativeChemicalInputWithAtomElectronicStates.CertificationReady
    MainGroupLewisGeneralSourceCertificationReady
    AuthoritativeChemicalInputWithAtomElectronicStates.StructurallyWellFormed
  constructor
  · rintro ⟨⟨sourceWellFormed, _recordsWellFormed⟩, covered⟩
    exact ⟨sourceWellFormed,
      source.withMainGroupLewisUniqueGeneralAtomElectronicStates_covers_iff.mp covered⟩
  · rintro ⟨sourceWellFormed, derivable⟩
    exact ⟨⟨sourceWellFormed,
      source.mainGroupLewisUniqueGeneralAtomElectronicStateRecords_wellFormed⟩,
      source.withMainGroupLewisUniqueGeneralAtomElectronicStates_covers_iff.mpr derivable⟩

noncomputable def certifyMainGroupLewisUniqueGeneralAtomElectronicStates?
    (source : AuthoritativeChemicalInput) :
    Option CertifiedAuthoritativeChemicalInputWithAtomElectronicStates :=
  source.withMainGroupLewisUniqueGeneralAtomElectronicStates.certify?

@[simp] theorem certifyMainGroupLewisUniqueGeneralAtomElectronicStates?_isSome_iff_ready
    (source : AuthoritativeChemicalInput) :
    source.certifyMainGroupLewisUniqueGeneralAtomElectronicStates?.isSome ↔
      source.MainGroupLewisGeneralSourceCertificationReady := by
  unfold certifyMainGroupLewisUniqueGeneralAtomElectronicStates?
  rw [AuthoritativeChemicalInputWithAtomElectronicStates.certify?_isSome_iff_ready,
    source.withMainGroupLewisUniqueGeneralAtomElectronicStates_certificationReady_iff]

@[simp] theorem certifyMainGroupLewisUniqueGeneralAtomElectronicStates?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput) :
    source.certifyMainGroupLewisUniqueGeneralAtomElectronicStates? = none ↔
      source.MainGroupLewisGeneralSourceCertificationRefusal := by
  unfold certifyMainGroupLewisUniqueGeneralAtomElectronicStates?
  rw [AuthoritativeChemicalInputWithAtomElectronicStates.certify?_eq_none_iff_refusal,
    ← AuthoritativeChemicalInputWithAtomElectronicStates.not_certificationReady_iff_refusal,
    source.withMainGroupLewisUniqueGeneralAtomElectronicStates_certificationReady_iff,
    source.not_mainGroupLewisGeneralSourceCertificationReady_iff_refusal]

noncomputable def certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady
    (source : AuthoritativeChemicalInput)
    (ready : source.MainGroupLewisGeneralSourceCertificationReady) :
    CertifiedAuthoritativeChemicalInputWithAtomElectronicStates :=
  source.withMainGroupLewisUniqueGeneralAtomElectronicStates.certifiedOf
    (source.withMainGroupLewisUniqueGeneralAtomElectronicStates_certificationReady_iff.mpr ready)

noncomputable def analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?
    (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    Option (List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :=
  source.withMainGroupLewisUniqueGeneralAtomElectronicStates.analyzeOrdinaryDoubleBonds?
    carrierFuel viewAt

@[simp] theorem analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    source.analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?
        carrierFuel viewAt = none ↔
      source.MainGroupLewisGeneralSourceCertificationRefusal := by
  unfold analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?
  rw [AuthoritativeChemicalInputWithAtomElectronicStates.analyzeOrdinaryDoubleBonds?_eq_none_iff_refusal,
    ← AuthoritativeChemicalInputWithAtomElectronicStates.not_certificationReady_iff_refusal,
    source.withMainGroupLewisUniqueGeneralAtomElectronicStates_certificationReady_iff,
    source.not_mainGroupLewisGeneralSourceCertificationReady_iff_refusal]

theorem analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?_eq_some_of_ready
    (source : AuthoritativeChemicalInput)
    (ready : source.MainGroupLewisGeneralSourceCertificationReady)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    source.analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?
        carrierFuel viewAt =
      some ((source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).analyzeOrdinaryDoubleBonds
        carrierFuel viewAt) := by
  unfold analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?
    certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady
  exact source.withMainGroupLewisUniqueGeneralAtomElectronicStates.analyzeOrdinaryDoubleBonds?_eq_some_of_ready
    (source.withMainGroupLewisUniqueGeneralAtomElectronicStates_certificationReady_iff.mpr ready)
    carrierFuel viewAt

theorem analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?_some_nodup
    (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignments : List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (computed : source.analyzeOrdinaryDoubleBondsWithMainGroupLewisUniqueGeneralInventories?
      carrierFuel viewAt = some assignments) :
    assignments.Nodup := by
  exact source.withMainGroupLewisUniqueGeneralAtomElectronicStates.analyzeOrdinaryDoubleBonds?_some_nodup
    carrierFuel viewAt assignments computed

theorem mem_certifiedMainGroupLewisUniqueGeneralAnalyzeOrdinaryDoubleBonds_iff_canonical
    (source : AuthoritativeChemicalInput)
    (ready : source.MainGroupLewisGeneralSourceCertificationReady)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈
        (source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).analyzeOrdinaryDoubleBonds
          carrierFuel viewAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) assignment := by
  exact (source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).mem_analyzeOrdinaryDoubleBonds_iff_canonical
    carrierFuel viewAt assignment

theorem every_certifiedMainGroupLewisUniqueGeneralIndividualDoubleBond_exact_success_or_refusal
    (source : AuthoritativeChemicalInput)
    (ready : source.MainGroupLewisGeneralSourceCertificationReady)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel
          (source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈
            (source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).analyzeOrdinaryDoubleBonds
              carrierFuel viewAt ∧ assignment.bond = bond) ∨
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel
          (source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel
          (source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).inventorySource
          bond (viewAt bond.left) (viewAt bond.right) = none) := by
  exact (source.certifiedMainGroupLewisUniqueGeneralAtomElectronicStatesOfReady ready).every_individualDoubleBond_exact_success_or_refusal
    carrierFuel viewAt

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
