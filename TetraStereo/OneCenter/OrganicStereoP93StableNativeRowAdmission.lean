import TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission
import TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes
import TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoCertifiedSourceCoreCompletion
import TetraStereo.KernelOnly

set_option autoImplicit false












































namespace TetraStereo.OneCenter

open IUPACNormativeProvision
open OrganicStereoP93AcyclicIngress
open OrganicStereoNoncarbonTetrahedralIngress
open OrganicStereoMonocyclicRingAssemblyIngress
open OrganicStereoFusedVonBaeyerIngress
open OrganicStereoCyclophaneAuthorityIngress
open OrganicStereoSpiroAuthorityIngress
open OrganicStereoCoupledRingChainNativeAxes
open OrganicStereoFullereneAuthorityIngress

namespace OrganicStereoP93StableRowAdmission

/-! ## Native payload types, indexed by the exact row -/

/-- The native payload of a closed production row.  Every supported branch is one of the
pre-existing per-family native codecs; excluded rows have `PUnit` payloads, mirroring
`FamilyPayload`.  Nothing here stores a source record, an original observation, or an
`AuthoritativeChemicalInput`. -/
def NativePayload (policies : Remaining71ReviewedPolicies) (V : Type) :
    Remaining71P93ClosedProductionRow → Type
  | .fullerene .generalMethodology => NativeFullereneMethodologyAuthorityObservation
  | .fullerene .inherentParentChirality => PUnit
  | .fullerene .inherentSubstitutionChirality => PUnit
  | .fullerene .noninherentSubstitutionChirality => PUnit
  | .fullerene .chiralSubstituents => PUnit
  | .fullerene .superimposedStereogenicElements => PUnit
  | .noncarbon _ => NativeNoncarbonObservation V policies.p93Noncarbon.Descriptor
  | .general _ => PUnit
  | .monocyclic _ =>
      CyclicObservation V policies.p93Cyclic.monocyclic policies.p93Cyclic.ringAssembly
  | .vonBaeyer _ =>
      SuppliedFusedVonBaeyerObservation V policies.p93Cyclic.fused policies.p93Cyclic.vonBaeyer
  | .ringAssembly _ =>
      CyclicObservation V policies.p93Cyclic.monocyclic policies.p93Cyclic.ringAssembly
  | .acyclic .acyclicCenters => SuppliedAcyclicAssignment V policies.p93Acyclic.Component
  | .acyclic .ordinaryDoubleBonds => SuppliedAcyclicAssignment V policies.p93Acyclic.Component
  | .acyclic _ => AcyclicObservation V policies.p93Acyclic
  | .spiro _ => NativeSpiroAuthorityObservation policies.p93Cyclic.spiro V
  | .spiroNontetrahedral => NativeSpiroAuthorityObservation policies.p93Cyclic.spiro V
  | .fusedCyclophane .fusedBridgedCIP =>
      SuppliedFusedVonBaeyerObservation V policies.p93Cyclic.fused policies.p93Cyclic.vonBaeyer
  | .fusedCyclophane .cisoidTransoid =>
      SuppliedFusedVonBaeyerObservation V policies.p93Cyclic.fused policies.p93Cyclic.vonBaeyer
  | .fusedCyclophane .cyclophanePlanes =>
      NativeCyclophaneAuthorityObservation V policies.p93Cyclic.cyclophane
  | .fusedCyclophane .cyclophaneCenters =>
      NativeCyclophaneAuthorityObservation V policies.p93Cyclic.cyclophane
  | .fusedCyclophane .cyclophaneDoubleBonds =>
      NativeCyclophaneAuthorityObservation V policies.p93Cyclic.cyclophane
  | .coupledRingChain _ =>
      SuppliedNativeCoupledRingChainObservation V policies.p93Cyclic.coupledRingChain

/-! ## Bounds derived from validity and the exact source binding

The two helper facts below are the only places where a bound is transported from the source's own
atom count to `Fintype.card V`; both use the binding's exact graph equality
(`PhysicalFrameSourceBinding.atomCount_eq`), never an assumed cardinality agreement. -/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The physical unit of a valid acyclic assignment is bounded by `Fintype.card V`. -/
theorem assignmentUnitBoundedIn_of_validFor_binding
    (policy : P93AcyclicAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (valid : P93AcyclicAuthorityAssignment.ValidFor policy binding.source assignment) :
    OrganicStereoP93AcyclicIngress.UnitBoundedIn (Fintype.card V) assignment.unit := by
  have bounded := OrganicStereoP93AcyclicIngress.assignmentUnitBoundedIn_of_validFor
    binding.source assignment valid binding.spatial_wellFormed
  rwa [binding.atomCount_eq] at bounded

/-- Source-side exact recovery of a combined cyclic observation, with both the bound and the
normalization fixed point derived from the record's own `ValidFor` and the exact source binding.
This is the normalized specialization of the family inverse; it is not a new inverse. -/
theorem unrelabelCyclicObservation_relabelCyclicObservation_binding
    (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (observation : SourceCyclicObservation policies.p93Cyclic.monocyclic
      policies.p93Cyclic.ringAssembly)
    (valid : SourceCyclicObservation.ValidFor binding.source observation) :
    OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation binding.enumeration
      (OrganicStereoMonocyclicRingAssemblyIngress.relabelCyclicObservation binding.enumeration
        observation
        (SourceCyclicObservation.boundedIn_of_validFor_binding binding structurallyWellFormed
          observation valid)) = observation :=
  OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation_relabelCyclicObservation
    binding.enumeration observation _
    (SourceCyclicObservation.normalizationFixed_of_validFor binding.source observation valid)

/-- Source-side exact recovery of a coupled ring/chain observation, with the bound and the
normalization fixed point derived from its own `ValidFor`. -/
theorem unrelabelNativeObservation_relabelNativeObservation_binding
    (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : P93CoupledRingChainAuthorityObservation
      policies.p93Cyclic.coupledRingChain)
    (valid : P93CoupledRingChainAuthorityObservation.ValidFor
      policies.p93Cyclic.coupledRingChain binding.source observation) :
    OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation binding.enumeration
      (OrganicStereoCoupledRingChainNativeAxes.relabelNativeObservation binding.enumeration
        observation
        (NativeObservationBoundedIn.of_validFor_binding binding observation valid)) =
      observation :=
  OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation_relabelNativeObservation
    binding.enumeration observation _
    (OrganicStereoCoupledRingChainNativeAxes.nativeObservationNormalizationFixed_of_validFor
      binding.source observation valid)

/-! ## Forward encoding: family payload to native payload -/

/-- Encode one row-indexed family payload into its native payload.  Every boundedness and
normalization premise is derived from `valid : destinationValidFor ... payload`; the caller never
supplies a bound.  Excluded rows cannot be encoded from a genuine validity proof: their
`destinationValidFor` is `False`. -/
def encodePayload (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed) :
    (row : Remaining71P93ClosedProductionRow) →
      (payload : FamilyPayload policies row) →
      destinationValidFor policies row binding.source payload →
      NativePayload policies V row
  | .fullerene .generalMethodology, _, _ => .fourWayDecisionRule
  | .fullerene .inherentParentChirality, _, valid => False.elim valid
  | .fullerene .inherentSubstitutionChirality, _, valid => False.elim valid
  | .fullerene .noninherentSubstitutionChirality, _, valid => False.elim valid
  | .fullerene .chiralSubstituents, _, valid => False.elim valid
  | .fullerene .superimposedStereogenicElements, _, valid => False.elim valid
  | .noncarbon _, payload, valid =>
      OrganicStereoNoncarbonTetrahedralIngress.toNativeObservation binding.enumeration
        policies.p93Noncarbon payload
        (SourceNoncarbonObservation.boundedIn_of_validFor_binding binding payload valid)
  | .general _, _, valid => False.elim valid
  | .monocyclic _, payload, valid =>
      OrganicStereoMonocyclicRingAssemblyIngress.relabelCyclicObservation binding.enumeration
        payload
        (SourceCyclicObservation.boundedIn_of_validFor_binding binding structurallyWellFormed
          payload valid)
  | .vonBaeyer _, payload, valid =>
      OrganicStereoFusedVonBaeyerIngress.relabelObservation binding.enumeration payload
        (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding binding payload valid)
  | .ringAssembly _, payload, valid =>
      OrganicStereoMonocyclicRingAssemblyIngress.relabelCyclicObservation binding.enumeration
        payload
        (SourceCyclicObservation.boundedIn_of_validFor_binding binding structurallyWellFormed
          payload valid)
  | .acyclic .acyclicCenters, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment binding.enumeration payload
        (assignmentUnitBoundedIn_of_validFor_binding policies.p93Acyclic binding payload valid)
  | .acyclic .ordinaryDoubleBonds, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment binding.enumeration payload
        (assignmentUnitBoundedIn_of_validFor_binding policies.p93Acyclic binding payload valid)
  | .acyclic .singleAcyclicCenter, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .multipleDescriptorsOneCenter, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .prefixComponentCenters, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .doubleBondEZCisTrans, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .multipleDoubleBonds, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .heteroatomDoubleBonds, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .evenCumulenes, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .oddCumulenes, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .multipleAcyclicStereogenicUnits, payload, valid =>
      OrganicStereoP93AcyclicIngress.relabelObservation binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .spiro _, payload, valid =>
      OrganicStereoSpiroAuthorityIngress.relabelObservation binding.enumeration payload
        (SourceSpiroAuthorityObservation.boundedIn_of_validFor
          policies.p93Cyclic.spiro binding payload valid)
  | .spiroNontetrahedral, payload, valid =>
      OrganicStereoSpiroAuthorityIngress.relabelObservation binding.enumeration payload
        (SourceSpiroAuthorityObservation.boundedIn_of_validFor
          policies.p93Cyclic.spiro binding payload valid)
  | .fusedCyclophane .fusedBridgedCIP, payload, valid =>
      OrganicStereoFusedVonBaeyerIngress.relabelObservation binding.enumeration payload
        (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding binding payload valid)
  | .fusedCyclophane .cisoidTransoid, payload, valid =>
      OrganicStereoFusedVonBaeyerIngress.relabelObservation binding.enumeration payload
        (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding binding payload valid)
  | .fusedCyclophane .cyclophanePlanes, payload, valid =>
      OrganicStereoCyclophaneAuthorityIngress.relabelObservation binding.enumeration payload
        (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding binding payload valid)
  | .fusedCyclophane .cyclophaneCenters, payload, valid =>
      OrganicStereoCyclophaneAuthorityIngress.relabelObservation binding.enumeration payload
        (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding binding payload valid)
  | .fusedCyclophane .cyclophaneDoubleBonds, payload, valid =>
      OrganicStereoCyclophaneAuthorityIngress.relabelObservation binding.enumeration payload
        (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding binding payload valid)
  | .coupledRingChain _, payload, valid =>
      OrganicStereoCoupledRingChainNativeAxes.relabelNativeObservation binding.enumeration payload
        (NativeObservationBoundedIn.of_validFor_binding binding payload valid)

/-! ## Backward decoding: native payload to family payload -/

/-- Decode one native payload into the row-indexed family payload.  The row is an explicit input;
the native payload type alone is not injective. -/
def decodePayload (policies : Remaining71ReviewedPolicies)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (row : Remaining71P93ClosedProductionRow) →
      NativePayload policies V row → FamilyPayload policies row
  | .fullerene .generalMethodology, _ =>
      P93FullereneMethodologyAuthorityObservation.fourWayDecisionRule
  | .fullerene .inherentParentChirality, _ => PUnit.unit
  | .fullerene .inherentSubstitutionChirality, _ => PUnit.unit
  | .fullerene .noninherentSubstitutionChirality, _ => PUnit.unit
  | .fullerene .chiralSubstituents, _ => PUnit.unit
  | .fullerene .superimposedStereogenicElements, _ => PUnit.unit
  | .noncarbon _, native =>
      OrganicStereoNoncarbonTetrahedralIngress.ofNativeObservation enumeration
        policies.p93Noncarbon native
  | .general _, _ => PUnit.unit
  | .monocyclic _, native =>
      OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation
        enumeration native
  | .vonBaeyer _, native =>
      OrganicStereoFusedVonBaeyerIngress.unrelabelObservation enumeration native
  | .ringAssembly _, native =>
      OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation
        enumeration native
  | .acyclic .acyclicCenters, native =>
      OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment enumeration native
  | .acyclic .ordinaryDoubleBonds, native =>
      OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment enumeration native
  | .acyclic .singleAcyclicCenter, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .acyclic .multipleDescriptorsOneCenter, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .acyclic .prefixComponentCenters, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .acyclic .doubleBondEZCisTrans, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .acyclic .multipleDoubleBonds, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .acyclic .heteroatomDoubleBonds, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .acyclic .evenCumulenes, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .acyclic .oddCumulenes, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .acyclic .multipleAcyclicStereogenicUnits, native =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration native
  | .spiro _, native =>
      OrganicStereoSpiroAuthorityIngress.decodeObservation enumeration native
  | .spiroNontetrahedral, native =>
      OrganicStereoSpiroAuthorityIngress.decodeObservation enumeration native
  | .fusedCyclophane .fusedBridgedCIP, native =>
      OrganicStereoFusedVonBaeyerIngress.unrelabelObservation enumeration native
  | .fusedCyclophane .cisoidTransoid, native =>
      OrganicStereoFusedVonBaeyerIngress.unrelabelObservation enumeration native
  | .fusedCyclophane .cyclophanePlanes, native =>
      OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation enumeration native
  | .fusedCyclophane .cyclophaneCenters, native =>
      OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation enumeration native
  | .fusedCyclophane .cyclophaneDoubleBonds, native =>
      OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation enumeration native
  | .coupledRingChain _, native =>
      OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation
        enumeration native

/-! ## The methodology row agrees with the actual fullerene codec

The fullerene ingress codec takes a `FullereneAuthorityCommonSource`, but on the methodology row it
ignores that source: the observation is the nullary four-way decision rule.  These two lemmas show
that the local branches are exactly that codec's encode/decode, so the methodology row is not a
private surrogate. -/

theorem encodePayload_methodology_eq
    (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (common : FullereneAuthorityCommonSource V)
    (payload : P93FullereneMethodologyAuthorityObservation)
    (valid : destinationValidFor policies (.fullerene .generalMethodology) binding.source
      payload) :
    encodePayload policies binding structurallyWellFormed (.fullerene .generalMethodology)
        payload valid =
      common.encodeMethodologyObservation payload := by
  cases payload
  rfl

theorem decodePayload_methodology_eq
    (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (common : FullereneAuthorityCommonSource V)
    (native : NativeFullereneMethodologyAuthorityObservation) :
    decodePayload policies binding.enumeration (.fullerene .generalMethodology) native =
      common.decodeMethodologyObservation native := by
  cases native
  rfl

/-! ## Exact decode ∘ encode on the family payload -/

/-- **Exact family-payload recovery.**  Decoding the native encoding of any valid family payload
returns that same payload.  Every branch is the pre-existing family inverse; the cyclic and
coupled branches use the normalized specialization whose premises are derived from `valid`. -/
theorem decodePayload_encodePayload (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed) :
    (row : Remaining71P93ClosedProductionRow) →
      (payload : FamilyPayload policies row) →
      (valid : destinationValidFor policies row binding.source payload) →
      decodePayload policies binding.enumeration row
        (encodePayload policies binding structurallyWellFormed row payload valid) = payload
  | .fullerene .generalMethodology, payload, _ => by
      cases payload
      rfl
  | .fullerene .inherentParentChirality, _, valid => False.elim valid
  | .fullerene .inherentSubstitutionChirality, _, valid => False.elim valid
  | .fullerene .noninherentSubstitutionChirality, _, valid => False.elim valid
  | .fullerene .chiralSubstituents, _, valid => False.elim valid
  | .fullerene .superimposedStereogenicElements, _, valid => False.elim valid
  | .noncarbon _, payload, valid =>
      OrganicStereoNoncarbonTetrahedralIngress.ofNativeObservation_toNativeObservation
        binding.enumeration policies.p93Noncarbon payload
        (SourceNoncarbonObservation.boundedIn_of_validFor_binding binding payload valid)
  | .general _, _, valid => False.elim valid
  | .monocyclic _, payload, valid =>
      unrelabelCyclicObservation_relabelCyclicObservation_binding policies binding
        structurallyWellFormed payload valid
  | .vonBaeyer _, payload, valid =>
      OrganicStereoFusedVonBaeyerIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding binding payload valid)
  | .ringAssembly _, payload, valid =>
      unrelabelCyclicObservation_relabelCyclicObservation_binding policies binding
        structurallyWellFormed payload valid
  | .acyclic .acyclicCenters, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment_relabelAcyclicAssignment
        binding.enumeration payload
        (assignmentUnitBoundedIn_of_validFor_binding policies.p93Acyclic binding payload valid)
  | .acyclic .ordinaryDoubleBonds, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment_relabelAcyclicAssignment
        binding.enumeration payload
        (assignmentUnitBoundedIn_of_validFor_binding policies.p93Acyclic binding payload valid)
  | .acyclic .singleAcyclicCenter, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .multipleDescriptorsOneCenter, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .prefixComponentCenters, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .doubleBondEZCisTrans, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .multipleDoubleBonds, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .heteroatomDoubleBonds, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .evenCumulenes, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .oddCumulenes, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .acyclic .multipleAcyclicStereogenicUnits, payload, valid =>
      OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceAcyclicObservation.boundedIn_of_validFor_binding binding payload valid)
  | .spiro _, payload, valid =>
      OrganicStereoSpiroAuthorityIngress.decodeObservation_relabelObservation
        binding.enumeration payload
        (SourceSpiroAuthorityObservation.boundedIn_of_validFor
          policies.p93Cyclic.spiro binding payload valid)
  | .spiroNontetrahedral, payload, valid =>
      OrganicStereoSpiroAuthorityIngress.decodeObservation_relabelObservation
        binding.enumeration payload
        (SourceSpiroAuthorityObservation.boundedIn_of_validFor
          policies.p93Cyclic.spiro binding payload valid)
  | .fusedCyclophane .fusedBridgedCIP, payload, valid =>
      OrganicStereoFusedVonBaeyerIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding binding payload valid)
  | .fusedCyclophane .cisoidTransoid, payload, valid =>
      OrganicStereoFusedVonBaeyerIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding binding payload valid)
  | .fusedCyclophane .cyclophanePlanes, payload, valid =>
      OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding binding payload valid)
  | .fusedCyclophane .cyclophaneCenters, payload, valid =>
      OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding binding payload valid)
  | .fusedCyclophane .cyclophaneDoubleBonds, payload, valid =>
      OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation_relabelObservation
        binding.enumeration payload
        (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding binding payload valid)
  | .coupledRingChain _, payload, valid =>
      unrelabelNativeObservation_relabelNativeObservation_binding policies binding
        payload valid

/-! ## Row-observation native endpoint -/

/-- Encode the row's own source observation into the native payload. -/
def encodeNative (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    NativePayload policies V row :=
  encodePayload policies binding structurallyWellFormed row
    (toFamily policies row supported observation) valid

/-- Encode a row observation whose validity is supplied by the row's own `Judges`; the
`destinationValidFor` premise is derived, not assumed. -/
def encodeJudged (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (judged : (row.reference policies).Judges binding.source observation) :
    NativePayload policies V row :=
  encodeNative policies binding structurallyWellFormed row supported observation
    (destinationValidFor_of_judged policies row supported binding.source observation judged)

/-- Decode a native payload back to the row's own observation.  `none` means the native payload
belongs to a different constructor of the shared carrier, so it is not this row's observation. -/
def decodeNative (policies : Remaining71ReviewedPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (row : Remaining71P93ClosedProductionRow)
    (native : NativePayload policies V row) :
    Option ((row.reference policies).Observation) :=
  readBack policies row (decodePayload policies enumeration row native)

/-- **Read-back is `some` of the original.**  For every stable row, decoding the native encoding of
a valid row observation returns exactly that observation: same constructor, same fields. -/
theorem decodeNative_encodeNative (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    decodeNative policies binding.enumeration row
        (encodeNative policies binding structurallyWellFormed row supported observation valid) =
      some observation := by
  show readBack policies row
      (decodePayload policies binding.enumeration row
        (encodePayload policies binding structurallyWellFormed row
          (toFamily policies row supported observation) valid)) = some observation
  rw [decodePayload_encodePayload policies binding structurallyWellFormed row
    (toFamily policies row supported observation) valid]
  exact readBack_toFamily policies row supported observation

/-- **Read-back is `some` of the original**, with validity derived from the row's own `Judges`. -/
theorem decodeNative_encodeJudged (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (judged : (row.reference policies).Judges binding.source observation) :
    decodeNative policies binding.enumeration row
        (encodeJudged policies binding structurallyWellFormed row supported observation judged) =
      some observation :=
  decodeNative_encodeNative policies binding structurallyWellFormed row supported observation
    (destinationValidFor_of_judged policies row supported binding.source observation judged)

/-- **Validity of the decoded payload.**  The family payload recovered from a native payload that
was itself encoded from a valid payload is valid at the exact same source and policy.  This is
validity transport along the record equality, not an invariance-under-renumbering claim. -/
theorem destinationValidFor_decodePayload_encodePayload
    (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (payload : FamilyPayload policies row)
    (valid : destinationValidFor policies row binding.source payload) :
    destinationValidFor policies row binding.source
      (decodePayload policies binding.enumeration row
        (encodePayload policies binding structurallyWellFormed row payload valid)) := by
  rw [decodePayload_encodePayload policies binding structurallyWellFormed row payload valid]
  exact valid

/-- **Validity of the decoded observation.**  If the native endpoint returns `some observation'`,
then that observation satisfies the actual row destination validity at the same source; it is
exactly the original observation. -/
theorem destinationValidFor_of_decodeNative_encodeNative
    (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation))
    (observation' : (row.reference policies).Observation)
    (decoded : decodeNative policies binding.enumeration row
        (encodeNative policies binding structurallyWellFormed row supported observation valid) =
      some observation') :
    destinationValidFor policies row binding.source
      (toFamily policies row supported observation') := by
  have equal : observation = observation' :=
    Option.some.inj (by
      rw [← decoded]
      exact (decodeNative_encodeNative policies binding structurallyWellFormed row supported
        observation valid).symm)
  subst equal
  exact valid

/-! ## The native satellite and exact source recovery -/

/-- A one-row native satellite: the shared finite graph/spatial/diagram channels (the binding's
`shared` source, with observations excluded) plus the row tag and its native payload. -/
structure NativeRowSatellite (policies : Remaining71ReviewedPolicies) (V : Type)
    [DecidableEq V] [Fintype V] where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  row : Remaining71P93ClosedProductionRow
  supported : stableSupported row = true
  payload : NativePayload policies V row

namespace NativeRowSatellite

/-- The satellite's shared finite source, with the row payload intentionally excluded. -/
def toFiniteSource {policies : Remaining71ReviewedPolicies}
    (satellite : NativeRowSatellite policies V) : OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end NativeRowSatellite

/-- A recovered source record: the exact authoritative input, the row tag, its certificate, and
the decoded observation. -/
structure RecoveredNativeRow (policies : Remaining71ReviewedPolicies) where
  source : AuthoritativeChemicalInput
  row : Remaining71P93ClosedProductionRow
  supported : stableSupported row = true
  observation : Option ((row.reference policies).Observation)

/-- Adapt a row observation into the native satellite: the shared finite source is retained
verbatim, and the payload is the native encoding. -/
def adaptNativeRow (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    NativeRowSatellite policies V where
  graph := binding.shared.graph
  spatial? := binding.shared.spatial?
  diagram? := binding.shared.diagram?
  row := row
  supported := supported
  payload := encodeNative policies binding structurallyWellFormed row supported observation valid

/-- The adapted satellite's graph channel is exactly the binding's shared graph. -/
@[simp] theorem adaptNativeRow_graph (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    (adaptNativeRow policies binding structurallyWellFormed row supported observation valid).graph =
      binding.shared.graph := rfl

/-- The adapted satellite's spatial channel is exactly the binding's shared spatial channel,
including absence. -/
@[simp] theorem adaptNativeRow_spatial? (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    (adaptNativeRow policies binding structurallyWellFormed row supported observation valid).spatial? =
      binding.shared.spatial? := rfl

/-- The adapted satellite's diagram channel is exactly the binding's shared diagram channel,
including absence. -/
@[simp] theorem adaptNativeRow_diagram? (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    (adaptNativeRow policies binding structurallyWellFormed row supported observation valid).diagram? =
      binding.shared.diagram? := rfl

/-- Decode a native satellite into the recovered source record.  The decoder's only
representation input is the fixed atom enumeration: it does **not** take the original
`PhysicalFrameSourceBinding` or the certified source.  The source is rebuilt from the satellite's
own primitive graph/spatial/diagram channels, and the observation from the native payload. -/
def decodeNativeRow (policies : Remaining71ReviewedPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : NativeRowSatellite policies V) :
    RecoveredNativeRow policies where
  source := (NativeRowSatellite.toFiniteSource satellite).encode enumeration
  row := satellite.row
  supported := satellite.supported
  observation := decodeNative policies enumeration satellite.row satellite.payload

/-- **Decoded source equality.**  The source recovered from the adapted native satellite is
exactly the authoritative input bound by the source binding. -/
theorem decodeNativeRow_source_adaptNativeRow (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    (decodeNativeRow policies binding.enumeration
      (adaptNativeRow policies binding structurallyWellFormed row supported observation valid)).source =
      binding.source := by
  show binding.shared.encode binding.enumeration = binding.source
  exact binding.encode_shared

/-- The recovered row tag is the original row tag. -/
@[simp] theorem decodeNativeRow_row_adaptNativeRow (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    (decodeNativeRow policies binding.enumeration
      (adaptNativeRow policies binding structurallyWellFormed row supported observation valid)).row =
      row := rfl

/-- The recovered admission certificate is the original certificate. -/
theorem decodeNativeRow_supported_adaptNativeRow (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    (decodeNativeRow policies binding.enumeration
      (adaptNativeRow policies binding structurallyWellFormed row supported observation valid)).supported =
      supported := rfl

/-- **Decoded observation equality.**  The observation recovered from the adapted native satellite
is `some` of the exact original row observation. -/
theorem decodeNativeRow_observation_adaptNativeRow (policies : Remaining71ReviewedPolicies)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row binding.source
      (toFamily policies row supported observation)) :
    (decodeNativeRow policies binding.enumeration
      (adaptNativeRow policies binding structurallyWellFormed row supported observation valid)).observation =
      some observation := by
  show decodeNative policies binding.enumeration row
      (encodeNative policies binding structurallyWellFormed row supported observation valid) =
    some observation
  exact decodeNative_encodeNative policies binding structurallyWellFormed row supported
    observation valid

/-! ## Certified-source instantiation

`PhysicalFrameSourceBinding.ofCertified` is the concrete binding of a certified authoritative input
to its exact finite ingress source.  Its own equality supplies the decoded-source endpoint, and
`certified.structurallyWellFormed.1` is the structural premise needed by the cyclic rows.  Nothing
about a future constructed-core equality is assumed here. -/

/-- The concrete binding of a certified input. -/
abbrev certifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding
      (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

/-- Adapt a certified input and a judged row observation into the native satellite, at the
identity enumeration of `ofCertified`. -/
def adaptCertifiedNativeRow (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    NativeRowSatellite policies (Fin certified.input.molecule.atomCount) :=
  adaptNativeRow policies (certifiedBinding certified)
    certified.structurallyWellFormed.1 row supported observation valid

/-- The certified satellite's graph channel is exactly the graph of the actual decoded core
`certified.decode`, not a freshly invented source. -/
@[simp] theorem adaptCertifiedNativeRow_graph
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (adaptCertifiedNativeRow policies certified row supported observation valid).graph =
      (certified.decode).graph := rfl

/-- The certified satellite's spatial channel is exactly the decoded core's spatial channel,
including absence. -/
@[simp] theorem adaptCertifiedNativeRow_spatial?
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (adaptCertifiedNativeRow policies certified row supported observation valid).spatial? =
      (certified.decode).spatial? := rfl

/-- The certified satellite's diagram channel is exactly the decoded core's diagram channel,
including absence. -/
@[simp] theorem adaptCertifiedNativeRow_diagram?
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (adaptCertifiedNativeRow policies certified row supported observation valid).diagram? =
      (certified.decode).diagram? := rfl

/-- **Decoded source equality at the certified endpoint**: the recovered source is exactly the
certified input, via the actual ingress round trip of `certified.decode`. -/
theorem decodeNativeRow_source_adaptCertifiedNativeRow
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (decodeNativeRow policies (certifiedBinding certified).enumeration
      (adaptCertifiedNativeRow policies certified row supported observation valid)).source =
      certified.input := by
  show (certified.decode).encode (certifiedBinding certified).enumeration = certified.input
  exact CertifiedAuthoritativeChemicalInput.encode_decode certified

/-! ### Ties to the constructed independent core

The sourcecore module's `constructedCore` is the current joint molecular core.  Its finite source
is definitionally `certified.decode`, so the satellite's three primitive channels are exactly the
constructed core's finite-source channels.  These equalities are the integration surface: no
caller-supplied agreement between an original source and the decoded core is used. -/

/-- The certified satellite's graph channel equals the constructed core's finite-source graph. -/
theorem adaptCertifiedNativeRow_graph_constructedCore
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (adaptCertifiedNativeRow policies certified row supported observation valid).graph =
      (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
        (OrganicStereoCertifiedSourceCoreCompletion.constructedCore certified)).graph := by
  rw [adaptCertifiedNativeRow_graph,
    OrganicStereoCertifiedSourceCoreCompletion.coreFiniteSource_constructedCore_graph]

/-- The certified satellite's spatial channel equals the constructed core's finite-source
spatial channel, including absence. -/
theorem adaptCertifiedNativeRow_spatial?_constructedCore
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (adaptCertifiedNativeRow policies certified row supported observation valid).spatial? =
      (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
        (OrganicStereoCertifiedSourceCoreCompletion.constructedCore certified)).spatial? := by
  rw [adaptCertifiedNativeRow_spatial?,
    OrganicStereoCertifiedSourceCoreCompletion.coreFiniteSource_constructedCore_spatial?]

/-- The certified satellite's diagram channel equals the constructed core's finite-source
drawing channel, including absence. -/
theorem adaptCertifiedNativeRow_diagram?_constructedCore
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (adaptCertifiedNativeRow policies certified row supported observation valid).diagram? =
      (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
        (OrganicStereoCertifiedSourceCoreCompletion.constructedCore certified)).diagram? := by
  rw [adaptCertifiedNativeRow_diagram?,
    OrganicStereoCertifiedSourceCoreCompletion.coreFiniteSource_constructedCore_diagram?]

/-- **Decoded source through the constructed core.**  The source recovered by `decodeNativeRow`
from the certified native satellite is exactly `recoveredSource` of the constructed core at its
own constructed enumeration.  This is the native-output-only source endpoint: the decoder used
only the satellite and the fixed enumeration, never the original binding or certified source. -/
theorem decodeNativeRow_source_adaptCertifiedNativeRow_eq_constructedRecoveredSource
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (decodeNativeRow policies (certifiedBinding certified).enumeration
      (adaptCertifiedNativeRow policies certified row supported observation valid)).source =
      OrganicStereoCertifiedSourceCoreCompletion.recoveredSource
        (OrganicStereoCertifiedSourceCoreCompletion.constructedCore certified)
        (OrganicStereoCertifiedSourceCoreCompletion.constructedEnumeration certified) := by
  rw [OrganicStereoCertifiedSourceCoreCompletion.recoveredSource_constructedCore]
  exact decodeNativeRow_source_adaptCertifiedNativeRow policies certified row supported
    observation valid

/-- **Observation recovery at the certified endpoint**: the recovered observation is exactly the
original row observation. -/
theorem decodeNativeRow_observation_adaptCertifiedNativeRow
    (policies : Remaining71ReviewedPolicies)
    (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P93ClosedProductionRow)
    (supported : stableSupported row = true)
    (observation : (row.reference policies).Observation)
    (valid : destinationValidFor policies row certified.input
      (toFamily policies row supported observation)) :
    (decodeNativeRow policies (certifiedBinding certified).enumeration
      (adaptCertifiedNativeRow policies certified row supported observation valid)).observation =
      some observation :=
  decodeNativeRow_observation_adaptNativeRow policies (certifiedBinding certified)
    certified.structurallyWellFormed.1 row supported observation valid

end OrganicStereoP93StableRowAdmission

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.decodePayload_encodePayload
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.decodeNative_encodeNative
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.decodeNative_encodeJudged
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.destinationValidFor_decodePayload_encodePayload
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.destinationValidFor_of_decodeNative_encodeNative
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.decodeNativeRow_source_adaptNativeRow
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.decodeNativeRow_observation_adaptNativeRow
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.decodeNativeRow_source_adaptCertifiedNativeRow
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.decodeNativeRow_observation_adaptCertifiedNativeRow
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptNativeRow_graph
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptNativeRow_spatial?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptNativeRow_diagram?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptCertifiedNativeRow_graph
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptCertifiedNativeRow_spatial?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptCertifiedNativeRow_diagram?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptCertifiedNativeRow_graph_constructedCore
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptCertifiedNativeRow_spatial?_constructedCore
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.adaptCertifiedNativeRow_diagram?_constructedCore
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93StableRowAdmission.decodeNativeRow_source_adaptCertifiedNativeRow_eq_constructedRecoveredSource
