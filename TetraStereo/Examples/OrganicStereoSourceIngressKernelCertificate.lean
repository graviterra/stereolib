import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly
import TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily
import TetraStereo.OneCenter.OrganicStereoDonorGroupingIngress
import TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
import TetraStereo.OneCenter.OrganicStereoSuppliedCitationTransport
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Kernel-authority certificate for the accepted source-ingress adapter batch

This module imports the six accepted source adapters **simultaneously**, so the build is also a
namespace-collision check across

* `OrganicStereoMolecularEvidenceAssembly` (independent molecular-evidence ingress),
* `OrganicStereoOrderedObservationFamily` (ordered P-94 conformer/observation families and the
  explicit source coordinate resolver),
* `OrganicStereoDonorGroupingIngress` (source-bound `V`-native donor ledger ingress),
* `OrganicStereoSuppliedCitationIngress` (supplied P-91/P-93 citation source ingress),
* `OrganicStereoSuppliedCitationTransport` (whole-record citation transport and `Fin` codec),
* `OrganicStereoP93PhysicalFrameIngress` (concrete P-93 physical-frame ingress and recovery).

The `assert_kernel_only` commands below check kernel closure of eighteen distinct consequential
endpoints.  The seven typed `example`s use the actual declared functions (no wrapper definitions are
introduced) at fully general types: the molecular-evidence assembly inverse, the supplied-citation
source inverse, the P-94 coordinate resolver under an explicit enumeration, the donor-ledger inverse,
the citation transport whole-set inverse, P-93 coordinate-based frame recovery, and P-93 source
recovery at the binding's own enumeration.

Scope.  These are exact-recovery/representation results about the supplied records.  Nothing here
asserts external chemical authority, citation authorisation, descriptor correctness, donor
support-completeness, chemical admissibility, or general real-world chemical validity; the P-93
examples consume existing coordinate-incidence evidence rather than produce it.
-/

namespace TetraStereo.Examples.OrganicStereoSourceIngressKernelCertificate

/-! ## Molecular-evidence assembly -/

assert_kernel_only TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode_assemble
assert_kernel_only TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble_injective
assert_kernel_only TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode_image_assemble_image

/-! ## Ordered observation families and the P-94 coordinate resolver -/

assert_kernel_only TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.EncodedCoordinateObservation.pointAt_relabel
assert_kernel_only TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.EncodedCoordinateObservation.pointAt_ofSource_encodeIndex
assert_kernel_only TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.EncodedCoordinateObservation.virtualPointAt_ofSource
assert_kernel_only TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.OrderedObservationFamily.toCertifiedFiniteConformerCollection_ofCertifiedFiniteConformerCollection

/-! ## Donor grouping ingress: validity, unordered binary support, ledger inverse -/

assert_kernel_only TetraStereo.OneCenter.DonorGroupingIngress.occurrenceFactsOfIncidence
assert_kernel_only TetraStereo.OneCenter.DonorGroupingIngress.nativeValidityOfLedger
assert_kernel_only TetraStereo.OneCenter.DonorGroupingIngress.decodeLedger_channelOfLedger
assert_kernel_only TetraStereo.OneCenter.DonorGroupingIngress.channelOfLedger_injective

/-! ## Supplied citation ingress and transport -/

assert_kernel_only TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.suppliedSource_adapt
assert_kernel_only TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.unrelabelAssignments_relabelAssignments
assert_kernel_only TetraStereo.OneCenter.OrganicStereoSuppliedCitationTransport.decodeFin_encodeFin
assert_kernel_only TetraStereo.OneCenter.OrganicStereoSuppliedCitationTransport.decodeFin_image_encodeFinSet

/-! ## P-93 physical-frame ingress -/

assert_kernel_only TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.decodePolyhedral_relabelPolyhedral
assert_kernel_only TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.decodeFrame_relabelFrame_of_validFor
assert_kernel_only TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.suppliedSource_adapt

/-! ## Typed general examples using the actual functions -/

open TetraStereo.OneCenter
open TetraStereo.OneCenter.BlueBookP94.CoordinateRing

/-- The independent-evidence assembly is an exact left inverse on every supplied request. -/
example {V : Type} [DecidableEq V] [Fintype V]
    (request : TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.OrganicMolecularEvidence V) :
    TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode
        (TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble request) = request :=
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode_assemble request

/-- The supplied-citation adapter recovers every bounded raw source exactly. -/
example {V : Type} [DecidableEq V] [Fintype V] {n : ℕ}
    {BaseName Numbering Locant Prefix : Type*}
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.RawSuppliedCitationSource
      V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
        n assignment.unit) :
    TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.suppliedSource enumeration
        (TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.adapt graph enumeration raw
          bounded) = raw :=
  TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.suppliedSource_adapt
    graph enumeration raw bounded

/-- The P-94 coordinate resolver is invariant under relabelling with the composed enumeration,
for every encoded coordinate observation and every atom. -/
example {V W : Type} {source : CertifiedAuthoritativeChemicalInput} {Framework : Type*}
    (e : SourceAtomIndex source ≃ V) (r : V ≃ W)
    (observation :
      TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.EncodedCoordinateObservation
        Framework V)
    (atom : V) :
    TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.EncodedCoordinateObservation.pointAt
        (e.trans r)
        (TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.EncodedCoordinateObservation.relabel
          r observation)
        (r atom) =
      TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.EncodedCoordinateObservation.pointAt
        e observation atom :=
  TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily.EncodedCoordinateObservation.pointAt_relabel
    e r observation atom

/-- Every enriched donor ledger is recovered exactly from its native channel plus the proof-only
`NativeChannelValidity` certificate. -/
example {V : Type} [DecidableEq V] [Fintype V]
    {LigandId LigandKind FragmentId FragmentKind : Type*}
    [DecidableEq LigandId] [DecidableEq LigandKind]
    [DecidableEq FragmentId] [DecidableEq FragmentKind]
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : TetraStereo.OneCenter.DonorOccurrenceEncoding.DonorLedger
      (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    TetraStereo.OneCenter.DonorGroupingIngress.decodeLedger graph eV
        (rfl : graph.interactions.length = graph.interactions.length)
        (TetraStereo.OneCenter.DonorGroupingIngress.channelOfLedger graph eV ledger)
        (TetraStereo.OneCenter.DonorGroupingIngress.nativeValidityOfLedger graph eV ledger) =
      ledger :=
  TetraStereo.OneCenter.DonorGroupingIngress.decodeLedger_channelOfLedger graph eV ledger

/-- The citation `Fin` codec recovers the whole image of an arbitrary set of satellites. -/
example {V : Type} [DecidableEq V] [Fintype V] {n : ℕ}
    {BaseName Numbering Locant Prefix : Type*}
    (enumeration : V ≃ Fin n)
    (satellites : Set
      (TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.SuppliedCitationSatellite
        V BaseName Numbering Locant Prefix)) :
    TetraStereo.OneCenter.OrganicStereoSuppliedCitationTransport.decodeFin enumeration ''
        TetraStereo.OneCenter.OrganicStereoSuppliedCitationTransport.encodeFinSet enumeration
          satellites = satellites :=
  TetraStereo.OneCenter.OrganicStereoSuppliedCitationTransport.decodeFin_image_encodeFinSet
    enumeration satellites

/-- P-93 polyhedral frame recovery: with the actual `SpatialPointAt`/`SpatialPointsAt` evidence
for the center and ordered ligands, decoding the relabelled native payload against the shared
coordinate configuration returns the original frame. -/
example {V : Type} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n)
    (frame : P93AuthorityPolyhedralFrame)
    (bounded : TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.PolyhedralFrameBoundedIn
      n frame)
    (centerPointAt : SpatialPointAt frame.spatial frame.record.center frame.centerPoint)
    (positionsAt : SpatialPointsAt frame.spatial frame.record.ligands frame.positionPoints) :
    TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.decodePolyhedral e frame.spatial
        (TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.relabelPolyhedral e frame
          bounded) = frame :=
  TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.decodePolyhedral_relabelPolyhedral
    e frame bounded centerPointAt positionsAt

/-- P-93 source recovery: decoding the adapted satellite at the binding's own enumeration returns
the bound authoritative input and the exact ordered frame list. -/
example {V : Type} [DecidableEq V] [Fintype V]
    (raw : TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.RawPhysicalFrameSource V) :
    TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.suppliedSource
        raw.binding.enumeration
        (TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.adapt raw) =
      { source := raw.binding.source, frames := raw.frames } :=
  TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress.suppliedSource_adapt raw

end TetraStereo.Examples.OrganicStereoSourceIngressKernelCertificate
