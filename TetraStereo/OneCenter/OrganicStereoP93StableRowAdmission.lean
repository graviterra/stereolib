import TetraStereo.OneCenter.IUPACRemaining71P93ClosedProductionFamilies
import TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress
import TetraStereo.OneCenter.OrganicStereoNoncarbonTetrahedralIngress
import TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress
import TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress
import TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Stable row-source admission for the 46 closed P-93 production rows

The closed production family `Remaining71P93ClosedProductionRow` has 56 rows.  Five rows are the
general-handling rows of P-93.1 and five are the molecule-specific fullerene rows whose references
are relational/handedness/type-4/superimposed carriers.  This module supports the remaining 46 rows
into the seven pre-existing stable source-observation carriers:

* `SourceAcyclicObservation`
* `SourceNoncarbonObservation`
* `SourceCyclicObservation`
* `SourceFusedVonBaeyerObservation`
* `SourceCyclophaneAuthorityObservation`
* `SourceSpiroAuthorityObservation`
* `P93CoupledRingChainAuthorityObservation`

Each row is mapped to the constructor of the carrier whose payload is exactly the row's own
`(row.reference policies).Observation` record type.  Two acyclic rows (`acyclicCenters` and
`ordinaryDoubleBonds`) have a bare `P93AcyclicAuthorityAssignment` observation and no matching
constructor in `SourceAcyclicObservation`; they are carried directly as that actual record rather
than being forced through an invented placement constructor.  The fullerene
`generalMethodology` row is likewise carried directly as its actual singleton observation, and the
single coupled-ring-chain row is carried directly as its actual carrier structure.

This is an admission seam only.  It does not prove that any source satisfies a row, does not
kernel-check the 46/10 split as a coverage claim, and does not add inverse, normalization, or
boundedness hypotheses.  The row tag is retained in `RowEntry`, because several rows share one
payload carrier type and an untagged payload cannot recover the row.
-/

namespace TetraStereo.OneCenter

open IUPACNormativeProvision
open OrganicStereoP93AcyclicIngress
open OrganicStereoNoncarbonTetrahedralIngress
open OrganicStereoMonocyclicRingAssemblyIngress
open OrganicStereoFusedVonBaeyerIngress
open OrganicStereoCyclophaneAuthorityIngress
open OrganicStereoSpiroAuthorityIngress

namespace OrganicStereoP93StableRowAdmission

/-! ## The executable 46/10 split -/

/-- Executable admission predicate.  `true` exactly for the 46 stable actual rows: all noncarbon,
monocyclic, von Baeyer, ring-assembly, acyclic, spiro (including the nontetrahedral row), fused /
cyclophane, and coupled-ring-chain rows, plus `fullerene.generalMethodology`. -/
def stableSupported : Remaining71P93ClosedProductionRow → Bool
  | .fullerene .generalMethodology => true
  | .fullerene .inherentParentChirality => false
  | .fullerene .inherentSubstitutionChirality => false
  | .fullerene .noninherentSubstitutionChirality => false
  | .fullerene .chiralSubstituents => false
  | .fullerene .superimposedStereogenicElements => false
  | .noncarbon _ => true
  | .general _ => false
  | .monocyclic _ => true
  | .vonBaeyer _ => true
  | .ringAssembly _ => true
  | .acyclic _ => true
  | .spiro _ => true
  | .spiroNontetrahedral => true
  | .fusedCyclophane _ => true
  | .coupledRingChain _ => true

/-- The supported sublist of the existing concrete 56-row list. -/
def stableRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93ClosedProductionRow.all.filter stableSupported

/-- The excluded sublist: the five general rows and the five molecule-specific fullerene rows. -/
def excludedRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93ClosedProductionRow.all.filter (fun row => !stableSupported row)

@[simp] theorem stableRows_length : stableRows.length = 46 := by
  decide

@[simp] theorem excludedRows_length : excludedRows.length = 10 := by
  decide

theorem stableRows_nodup : stableRows.Nodup := by
  decide

theorem excludedRows_nodup : excludedRows.Nodup := by
  decide

/-- The executable split is exhaustive up to order over the existing 56-row list: the supported and
excluded sublists together are a permutation of `all`.  (Concatenation groups the two sublists, so
the statement is a permutation rather than an equality.)  This is a concrete list identity, not a
native coverage proof: no source is asserted to inhabit any row. -/
theorem stableRows_append_excludedRows_perm :
    (stableRows ++ excludedRows).Perm Remaining71P93ClosedProductionRow.all := by
  decide

/-- Executable disjointness of the two filtered sublists. -/
theorem stableRows_disjoint_excludedRows :
    stableRows.filter (fun row => decide (row ∈ excludedRows)) = [] := by
  decide

/-- Exact excluded case contract, in the order of `Remaining71P93ClosedProductionRow.all`. -/
theorem excludedRows_exact :
    excludedRows =
      [ .fullerene .inherentParentChirality
      , .fullerene .inherentSubstitutionChirality
      , .fullerene .noninherentSubstitutionChirality
      , .fullerene .chiralSubstituents
      , .fullerene .superimposedStereogenicElements
      , .general .absoluteConfiguration
      , .general .relativeConfiguration
      , .general .mixedAbsoluteRelativeConfiguration
      , .general .racemates
      , .general .ambo
      ] := by
  decide

/-- A concrete excluded row cannot carry the admission certificate. -/
theorem false_of_stableSupported_eq_false
    (row : Remaining71P93ClosedProductionRow)
    (hfalse : stableSupported row = false)
    (supported : stableSupported row = true) : False := by
  rw [hfalse] at supported
  cases supported

/-! ## Row-indexed destination payloads

The payload family is indexed by the exact row.  Its value is always an actual existing carrier (or
the row's actual observation record when the carrier has no matching constructor).  Excluded rows
have `PUnit` payloads; `toFamily` cannot construct one (its `supported` certificate is
contradictory), so the seam cannot fabricate a destination for them. -/

def FamilyPayload (policies : Remaining71ReviewedPolicies) :
    Remaining71P93ClosedProductionRow → Type
  | .fullerene .generalMethodology => P93FullereneMethodologyAuthorityObservation
  | .fullerene .inherentParentChirality => PUnit
  | .fullerene .inherentSubstitutionChirality => PUnit
  | .fullerene .noninherentSubstitutionChirality => PUnit
  | .fullerene .chiralSubstituents => PUnit
  | .fullerene .superimposedStereogenicElements => PUnit
  | .noncarbon _ => SourceNoncarbonObservation policies.p93Noncarbon
  | .general _ => PUnit
  | .monocyclic _ =>
      SourceCyclicObservation policies.p93Cyclic.monocyclic policies.p93Cyclic.ringAssembly
  | .vonBaeyer _ =>
      SourceFusedVonBaeyerObservation policies.p93Cyclic.fused policies.p93Cyclic.vonBaeyer
  | .ringAssembly _ =>
      SourceCyclicObservation policies.p93Cyclic.monocyclic policies.p93Cyclic.ringAssembly
  | .acyclic .acyclicCenters => P93AcyclicAuthorityAssignment policies.p93Acyclic
  | .acyclic .ordinaryDoubleBonds => P93AcyclicAuthorityAssignment policies.p93Acyclic
  | .acyclic _ => SourceAcyclicObservation policies.p93Acyclic
  | .spiro _ => SourceSpiroAuthorityObservation policies.p93Cyclic.spiro
  | .spiroNontetrahedral => SourceSpiroAuthorityObservation policies.p93Cyclic.spiro
  | .fusedCyclophane .fusedBridgedCIP =>
      SourceFusedVonBaeyerObservation policies.p93Cyclic.fused policies.p93Cyclic.vonBaeyer
  | .fusedCyclophane .cisoidTransoid =>
      SourceFusedVonBaeyerObservation policies.p93Cyclic.fused policies.p93Cyclic.vonBaeyer
  | .fusedCyclophane .cyclophanePlanes =>
      SourceCyclophaneAuthorityObservation policies.p93Cyclic.cyclophane
  | .fusedCyclophane .cyclophaneCenters =>
      SourceCyclophaneAuthorityObservation policies.p93Cyclic.cyclophane
  | .fusedCyclophane .cyclophaneDoubleBonds =>
      SourceCyclophaneAuthorityObservation policies.p93Cyclic.cyclophane
  | .coupledRingChain _ =>
      P93CoupledRingChainAuthorityObservation policies.p93Cyclic.coupledRingChain

/-! ## Forward admission: row observation to actual destination carrier -/

def toFamily (policies : Remaining71ReviewedPolicies) :
    (row : Remaining71P93ClosedProductionRow) → stableSupported row = true →
      (row.reference policies).Observation → FamilyPayload policies row
  | .fullerene .generalMethodology, _, observation => observation
  | .fullerene .inherentParentChirality, supported, _ =>
      False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | .fullerene .inherentSubstitutionChirality, supported, _ =>
      False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | .fullerene .noninherentSubstitutionChirality, supported, _ =>
      False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | .fullerene .chiralSubstituents, supported, _ =>
      False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | .fullerene .superimposedStereogenicElements, supported, _ =>
      False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | .noncarbon .otherElementTetrahedra, _, observation => .tetrahedral observation
  | .noncarbon .otherElementGeneralMethodology, _, observation => .citation observation
  | .noncarbon .azaniumPhosphanium, _, observation => .onic observation
  | .noncarbon .aminePhosphaneOxides, _, observation => .oxide observation
  | .noncarbon .phosphatesPhosphonates, _, observation => .phosphorusOxo observation
  | .noncarbon .sulfatesSulfonates, _, observation => .chalcogenOxo observation
  | .noncarbon .group14Noncarbon, _, observation => .group14 observation
  | .general _, supported, _ =>
      False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | .monocyclic .cyclicConfigurations, _, observation => .monocyclicGeneral observation
  | .monocyclic .monocyclicAbsoluteCenters, _, observation => .monocyclicCenter observation
  | .monocyclic .monocyclicAchiralCenters, _, observation => .monocyclicCenter observation
  | .monocyclic .monocyclicCisTrans, _, observation => .monocyclicCisTrans observation
  | .monocyclic .monocyclicRCT, _, observation => .monocyclicRCT observation
  | .monocyclic .unsaturatedMonocycles, _, observation => .monocyclicUnsaturation observation
  | .monocyclic .cyclicDoubleBonds, _, observation => .monocyclicDoubleBond observation
  | .monocyclic .exocyclicDoubleBondEZ, _, observation => .monocyclicExocyclic observation
  | .monocyclic .exocyclicDoubleBondOther, _, observation => .monocyclicExocyclic observation
  | .vonBaeyer .vonBaeyerCIPCenters, _, observation => .vonBaeyerCenter observation
  | .vonBaeyer .vonBaeyerEndoExoSynAnti, _, observation =>
      .vonBaeyerBridgeOrientation observation
  | .vonBaeyer .vonBaeyerCisTrans, _, observation => .vonBaeyerBridgeheadRelative observation
  | .vonBaeyer .vonBaeyerDoubleBonds, _, observation => .vonBaeyerUnsaturation observation
  | .ringAssembly .axes, _, observation => .ringAssemblyAxes observation
  | .ringAssembly .centers, _, observation => .ringAssemblyCenters observation
  | .ringAssembly .doubleBonds, _, observation => .ringAssemblyDoubleBonds observation
  | .acyclic .acyclicCenters, _, observation => observation
  | .acyclic .singleAcyclicCenter, _, observation => .singleCenter observation
  | .acyclic .multipleDescriptorsOneCenter, _, observation =>
      .multipleCenterDescriptors observation
  | .acyclic .prefixComponentCenters, _, observation => .prefixComponent observation
  | .acyclic .ordinaryDoubleBonds, _, observation => observation
  | .acyclic .doubleBondEZCisTrans, _, observation => .doubleBond observation
  | .acyclic .multipleDoubleBonds, _, observation => .multipleDoubleBond observation
  | .acyclic .heteroatomDoubleBonds, _, observation => .heteroDoubleBond observation
  | .acyclic .evenCumulenes, _, observation => .evenCumulene observation
  | .acyclic .oddCumulenes, _, observation => .oddCumulene observation
  | .acyclic .multipleAcyclicStereogenicUnits, _, observation => .multipleUnits observation
  | .spiro .spiroXabcd, _, observation => .xabcd observation
  | .spiro .spiroXabab, _, observation => .xabab observation
  | .spiro .spiroDoubleBonds, _, observation => .doubleBond observation
  | .spiro .spiroAxialChirality, _, observation => .axial observation
  | .spiroNontetrahedral, _, observation => .polyhedral observation
  | .fusedCyclophane .fusedBridgedCIP, _, observation => .fusedCIP observation
  | .fusedCyclophane .cisoidTransoid, _, observation => .fusedRelation observation
  | .fusedCyclophane .cyclophanePlanes, _, observation => .plane observation
  | .fusedCyclophane .cyclophaneCenters, _, observation => .center observation
  | .fusedCyclophane .cyclophaneDoubleBonds, _, observation => .doubleBond observation
  | .coupledRingChain .configurations, _, observation => observation

/-! ## Backward decoding: actual destination carrier to row observation -/

/-- Partial decode.  `none` means the payload belongs to a different constructor of the shared
carrier, so it is not the observation of this row.  The row is an explicit input: a bare payload
does not carry the row tag. -/
def readBack (policies : Remaining71ReviewedPolicies) :
    (row : Remaining71P93ClosedProductionRow) →
      FamilyPayload policies row → Option ((row.reference policies).Observation)
  | .fullerene .generalMethodology, payload => some payload
  | .fullerene .inherentParentChirality, _ => none
  | .fullerene .inherentSubstitutionChirality, _ => none
  | .fullerene .noninherentSubstitutionChirality, _ => none
  | .fullerene .chiralSubstituents, _ => none
  | .fullerene .superimposedStereogenicElements, _ => none
  | .noncarbon .otherElementTetrahedra, payload =>
      match payload with
      | .tetrahedral observation => some observation
      | _ => none
  | .noncarbon .otherElementGeneralMethodology, payload =>
      match payload with
      | .citation observation => some observation
      | _ => none
  | .noncarbon .azaniumPhosphanium, payload =>
      match payload with
      | .onic observation => some observation
      | _ => none
  | .noncarbon .aminePhosphaneOxides, payload =>
      match payload with
      | .oxide observation => some observation
      | _ => none
  | .noncarbon .phosphatesPhosphonates, payload =>
      match payload with
      | .phosphorusOxo observation => some observation
      | _ => none
  | .noncarbon .sulfatesSulfonates, payload =>
      match payload with
      | .chalcogenOxo observation => some observation
      | _ => none
  | .noncarbon .group14Noncarbon, payload =>
      match payload with
      | .group14 observation => some observation
      | _ => none
  | .general _, _ => none
  | .monocyclic .cyclicConfigurations, payload =>
      match payload with
      | .monocyclicGeneral observation => some observation
      | _ => none
  | .monocyclic .monocyclicAbsoluteCenters, payload =>
      match payload with
      | .monocyclicCenter observation => some observation
      | _ => none
  | .monocyclic .monocyclicAchiralCenters, payload =>
      match payload with
      | .monocyclicCenter observation => some observation
      | _ => none
  | .monocyclic .monocyclicCisTrans, payload =>
      match payload with
      | .monocyclicCisTrans observation => some observation
      | _ => none
  | .monocyclic .monocyclicRCT, payload =>
      match payload with
      | .monocyclicRCT observation => some observation
      | _ => none
  | .monocyclic .unsaturatedMonocycles, payload =>
      match payload with
      | .monocyclicUnsaturation observation => some observation
      | _ => none
  | .monocyclic .cyclicDoubleBonds, payload =>
      match payload with
      | .monocyclicDoubleBond observation => some observation
      | _ => none
  | .monocyclic .exocyclicDoubleBondEZ, payload =>
      match payload with
      | .monocyclicExocyclic observation => some observation
      | _ => none
  | .monocyclic .exocyclicDoubleBondOther, payload =>
      match payload with
      | .monocyclicExocyclic observation => some observation
      | _ => none
  | .vonBaeyer .vonBaeyerCIPCenters, payload =>
      match payload with
      | .vonBaeyerCenter observation => some observation
      | _ => none
  | .vonBaeyer .vonBaeyerEndoExoSynAnti, payload =>
      match payload with
      | .vonBaeyerBridgeOrientation observation => some observation
      | _ => none
  | .vonBaeyer .vonBaeyerCisTrans, payload =>
      match payload with
      | .vonBaeyerBridgeheadRelative observation => some observation
      | _ => none
  | .vonBaeyer .vonBaeyerDoubleBonds, payload =>
      match payload with
      | .vonBaeyerUnsaturation observation => some observation
      | _ => none
  | .ringAssembly .axes, payload =>
      match payload with
      | .ringAssemblyAxes observation => some observation
      | _ => none
  | .ringAssembly .centers, payload =>
      match payload with
      | .ringAssemblyCenters observation => some observation
      | _ => none
  | .ringAssembly .doubleBonds, payload =>
      match payload with
      | .ringAssemblyDoubleBonds observation => some observation
      | _ => none
  | .acyclic .acyclicCenters, payload => some payload
  | .acyclic .singleAcyclicCenter, payload =>
      match payload with
      | .singleCenter observation => some observation
      | _ => none
  | .acyclic .multipleDescriptorsOneCenter, payload =>
      match payload with
      | .multipleCenterDescriptors observation => some observation
      | _ => none
  | .acyclic .prefixComponentCenters, payload =>
      match payload with
      | .prefixComponent observation => some observation
      | _ => none
  | .acyclic .ordinaryDoubleBonds, payload => some payload
  | .acyclic .doubleBondEZCisTrans, payload =>
      match payload with
      | .doubleBond observation => some observation
      | _ => none
  | .acyclic .multipleDoubleBonds, payload =>
      match payload with
      | .multipleDoubleBond observation => some observation
      | _ => none
  | .acyclic .heteroatomDoubleBonds, payload =>
      match payload with
      | .heteroDoubleBond observation => some observation
      | _ => none
  | .acyclic .evenCumulenes, payload =>
      match payload with
      | .evenCumulene observation => some observation
      | _ => none
  | .acyclic .oddCumulenes, payload =>
      match payload with
      | .oddCumulene observation => some observation
      | _ => none
  | .acyclic .multipleAcyclicStereogenicUnits, payload =>
      match payload with
      | .multipleUnits observation => some observation
      | _ => none
  | .spiro .spiroXabcd, payload =>
      match payload with
      | .xabcd observation => some observation
      | _ => none
  | .spiro .spiroXabab, payload =>
      match payload with
      | .xabab observation => some observation
      | _ => none
  | .spiro .spiroDoubleBonds, payload =>
      match payload with
      | .doubleBond observation => some observation
      | _ => none
  | .spiro .spiroAxialChirality, payload =>
      match payload with
      | .axial observation => some observation
      | _ => none
  | .spiroNontetrahedral, payload =>
      match payload with
      | .polyhedral observation => some observation
      | _ => none
  | .fusedCyclophane .fusedBridgedCIP, payload =>
      match payload with
      | .fusedCIP observation => some observation
      | _ => none
  | .fusedCyclophane .cisoidTransoid, payload =>
      match payload with
      | .fusedRelation observation => some observation
      | _ => none
  | .fusedCyclophane .cyclophanePlanes, payload =>
      match payload with
      | .plane observation => some observation
      | _ => none
  | .fusedCyclophane .cyclophaneCenters, payload =>
      match payload with
      | .center observation => some observation
      | _ => none
  | .fusedCyclophane .cyclophaneDoubleBonds, payload =>
      match payload with
      | .doubleBond observation => some observation
      | _ => none
  | .coupledRingChain .configurations, payload => some payload

/-! ## Actual destination validity dispatch

Every branch is the pre-existing `ValidFor` of the actual destination carrier at the same source
and policy (or, for the two bare acyclic rows and the direct singleton rows, the pre-existing
`ValidFor` of the actual record).  No inverse, normalization, or boundedness hypothesis is added. -/

def destinationValidFor (policies : Remaining71ReviewedPolicies) :
    (row : Remaining71P93ClosedProductionRow) →
      AuthoritativeChemicalInput → FamilyPayload policies row → Prop
  | .fullerene .generalMethodology, source, observation =>
      P93FullereneMethodologyAuthorityObservation.ValidFor policies.p93Cyclic.fullerene
        source observation
  | .fullerene .inherentParentChirality, _, _ => False
  | .fullerene .inherentSubstitutionChirality, _, _ => False
  | .fullerene .noninherentSubstitutionChirality, _, _ => False
  | .fullerene .chiralSubstituents, _, _ => False
  | .fullerene .superimposedStereogenicElements, _, _ => False
  | .noncarbon _, source, payload =>
      SourceNoncarbonObservation.ValidFor policies.p93Noncarbon source payload
  | .general _, _, _ => False
  | .monocyclic _, source, payload =>
      SourceCyclicObservation.ValidFor source payload
  | .vonBaeyer _, source, payload =>
      SourceFusedVonBaeyerObservation.ValidFor source payload
  | .ringAssembly _, source, payload =>
      SourceCyclicObservation.ValidFor source payload
  | .acyclic .acyclicCenters, source, payload =>
      P93AcyclicAuthorityAssignment.ValidFor policies.p93Acyclic source payload
  | .acyclic .ordinaryDoubleBonds, source, payload =>
      P93AcyclicAuthorityAssignment.ValidFor policies.p93Acyclic source payload
  | .acyclic .singleAcyclicCenter, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .acyclic .multipleDescriptorsOneCenter, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .acyclic .prefixComponentCenters, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .acyclic .doubleBondEZCisTrans, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .acyclic .multipleDoubleBonds, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .acyclic .heteroatomDoubleBonds, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .acyclic .evenCumulenes, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .acyclic .oddCumulenes, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .acyclic .multipleAcyclicStereogenicUnits, source, payload =>
      SourceAcyclicObservation.ValidFor source payload
  | .spiro _, source, payload =>
      SourceSpiroAuthorityObservation.ValidFor source payload
  | .spiroNontetrahedral, source, payload =>
      SourceSpiroAuthorityObservation.ValidFor source payload
  | .fusedCyclophane .fusedBridgedCIP, source, payload =>
      SourceFusedVonBaeyerObservation.ValidFor source payload
  | .fusedCyclophane .cisoidTransoid, source, payload =>
      SourceFusedVonBaeyerObservation.ValidFor source payload
  | .fusedCyclophane .cyclophanePlanes, source, payload =>
      SourceCyclophaneAuthorityObservation.ValidFor source payload
  | .fusedCyclophane .cyclophaneCenters, source, payload =>
      SourceCyclophaneAuthorityObservation.ValidFor source payload
  | .fusedCyclophane .cyclophaneDoubleBonds, source, payload =>
      SourceCyclophaneAuthorityObservation.ValidFor source payload
  | .coupledRingChain _, source, payload =>
      P93CoupledRingChainAuthorityObservation.ValidFor
        policies.p93Cyclic.coupledRingChain source payload

/-! ## Round trip for all 46 supported rows -/

theorem readBack_toFamily (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation) :
    readBack policies row (toFamily policies row supported observation) = some observation := by
  cases row with
  | fullerene child =>
      cases child with
      | generalMethodology => rfl
      | inherentParentChirality =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
      | inherentSubstitutionChirality =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
      | noninherentSubstitutionChirality =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
      | chiralSubstituents =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
      | superimposedStereogenicElements =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | noncarbon child =>
      cases child <;> rfl
  | general child =>
      exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | monocyclic child =>
      cases child <;> rfl
  | vonBaeyer child =>
      cases child <;> rfl
  | ringAssembly child =>
      cases child <;> rfl
  | acyclic child =>
      cases child <;> rfl
  | spiro child =>
      cases child <;> rfl
  | spiroNontetrahedral => rfl
  | fusedCyclophane child =>
      cases child <;> rfl
  | coupledRingChain child =>
      cases child
      rfl

/-! ## Judged row observations satisfy the actual destination validity -/

theorem destinationValidFor_of_judged (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policies).Observation)
    (judged : (row.reference policies).Judges source observation) :
    destinationValidFor policies row source
      (toFamily policies row supported observation) := by
  cases row with
  | fullerene child =>
      cases child with
      | generalMethodology => exact judged
      | inherentParentChirality =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
      | inherentSubstitutionChirality =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
      | noninherentSubstitutionChirality =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
      | chiralSubstituents =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
      | superimposedStereogenicElements =>
          exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | noncarbon child =>
      cases child with
      | otherElementTetrahedra => exact judged
      | otherElementGeneralMethodology => exact judged
      | azaniumPhosphanium => exact judged
      | aminePhosphaneOxides => exact judged.1
      | phosphatesPhosphonates => exact judged.1
      | sulfatesSulfonates => exact judged.1
      | group14Noncarbon => exact judged.1
  | general child =>
      exact False.elim (false_of_stableSupported_eq_false _ rfl supported)
  | monocyclic child =>
      cases child with
      | cyclicConfigurations => exact judged
      | monocyclicAbsoluteCenters => exact judged.1
      | monocyclicAchiralCenters => exact judged.1
      | monocyclicCisTrans => exact judged
      | monocyclicRCT => exact judged
      | unsaturatedMonocycles => exact judged.1
      | cyclicDoubleBonds => exact judged
      | exocyclicDoubleBondEZ => exact judged.1
      | exocyclicDoubleBondOther => exact judged.1
  | vonBaeyer child =>
      cases child with
      | vonBaeyerCIPCenters => exact judged.1
      | vonBaeyerEndoExoSynAnti => exact judged
      | vonBaeyerCisTrans => exact judged
      | vonBaeyerDoubleBonds => exact judged
  | ringAssembly child =>
      cases child <;> exact judged
  | acyclic child =>
      cases child with
      | acyclicCenters => exact judged.1
      | singleAcyclicCenter => exact judged
      | multipleDescriptorsOneCenter => exact judged
      | prefixComponentCenters => exact judged.1
      | ordinaryDoubleBonds => exact judged.1
      | doubleBondEZCisTrans => exact judged
      | multipleDoubleBonds => exact judged
      | heteroatomDoubleBonds => exact judged.1
      | evenCumulenes => exact judged
      | oddCumulenes => exact judged
      | multipleAcyclicStereogenicUnits => exact judged
  | spiro child =>
      cases child <;> exact judged
  | spiroNontetrahedral => exact judged
  | fusedCyclophane child =>
      cases child <;> exact judged
  | coupledRingChain child =>
      cases child
      exact judged

/-! ## Row identity in the indexed output metadata

`RowEntry` stores the row tag next to its payload and its certificate.  The payload type alone is
not injective: several different rows share one carrier, so an untagged payload cannot recover the
row.  The tag must be retained by downstream union/composition code. -/

structure RowEntry (policies : Remaining71ReviewedPolicies) where
  row : Remaining71P93ClosedProductionRow
  supported : stableSupported row = true
  payload : FamilyPayload policies row

def packRow (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation) : RowEntry policies where
  row := row
  supported := supported
  payload := toFamily policies row supported observation

@[simp] theorem packRow_row (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation) :
    (packRow policies row supported observation).row = row := rfl

@[simp] theorem packRow_supported (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation) :
    (packRow policies row supported observation).supported = supported := rfl

@[simp] theorem packRow_payload (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation) :
    (packRow policies row supported observation).payload =
      toFamily policies row supported observation := rfl

theorem packRow_destinationValidFor (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policies).Observation)
    (judged : (row.reference policies).Judges source observation) :
    destinationValidFor policies row source
      (packRow policies row supported observation).payload :=
  destinationValidFor_of_judged policies row supported source observation judged

/-- The two monocyclic center rows share the `monocyclicCenter` payload carrier type. -/
theorem monocyclicCenter_payload_shared (policies : Remaining71ReviewedPolicies) :
    FamilyPayload policies (.monocyclic .monocyclicAbsoluteCenters) =
      FamilyPayload policies (.monocyclic .monocyclicAchiralCenters) := rfl

/-- The two exocyclic double-bond rows share the `monocyclicExocyclic` payload carrier type. -/
theorem monocyclicExocyclic_payload_shared (policies : Remaining71ReviewedPolicies) :
    FamilyPayload policies (.monocyclic .exocyclicDoubleBondEZ) =
      FamilyPayload policies (.monocyclic .exocyclicDoubleBondOther) := rfl

/-- The two bare acyclic rows share exactly the same payload record type (with no carrier tag at
all). -/
theorem acyclicAssignment_payload_shared (policies : Remaining71ReviewedPolicies) :
    FamilyPayload policies (.acyclic .acyclicCenters) =
      FamilyPayload policies (.acyclic .ordinaryDoubleBonds) := rfl

end OrganicStereoP93StableRowAdmission

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.stableRows_length
assert_kernel_only TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.excludedRows_length
assert_kernel_only TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.excludedRows_exact
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.stableRows_append_excludedRows_perm
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.stableRows_disjoint_excludedRows
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.readBack_toFamily
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.destinationValidFor_of_judged
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.packRow_destinationValidFor
