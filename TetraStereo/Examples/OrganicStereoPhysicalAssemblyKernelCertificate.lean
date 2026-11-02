
























































import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress
import TetraStereo.OneCenter.OrganicStereoVaryingPhysicalRequestAssembly
import TetraStereo.OneCenter.OrganicStereoMixedOutputPhysicalBinding
import TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
import TetraStereo.OneCenter.OrganicStereoP94AuthorityObservationIngress
import TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress
import TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly
import TetraStereo.OneCenter.OrganicStereoMixedSourceSamples

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace TetraStereo.Examples.OrganicStereoPhysicalAssemblyKernelCertificate

open TetraStereo.OneCenter
open TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly
open TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress
open TetraStereo.OneCenter.OrganicStereoVaryingPhysicalRequestAssembly
open TetraStereo.OneCenter.OrganicStereoMixedOutputPhysicalBinding
open TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
open TetraStereo.OneCenter.OrganicStereoP94AuthorityObservationIngress
open TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress
open TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly

universe u v

/-! ## Kernel-closure checks on the thirty consequential endpoints -/

/-! ### Fixed-base shared physical case ingress -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.EncodedCollection.decode_encode
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.EncodedCollection.set_image_inverse
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.SharedCaseRequest.universal_ordered_recovery
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.PackedIngress.decode_pack
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.PackedIngress.pack_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.PackedIngress.full_request_recovery
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.ringPlaneCaseOfObservation_decode
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.closedRingCaseOfObservation_recovery
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress.PackedResidueMeta.toIngress?_ofIngress

/-! ### Varying-base request assembly -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoVaryingPhysicalRequestAssembly.VaryingRequest.decode_pack
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoVaryingPhysicalRequestAssembly.VaryingRequest.pack_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoVaryingPhysicalRequestAssembly.VaryingRequest.decode_image_pack_image

/-! ### Actual assembled-state context binding -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMixedOutputPhysicalBinding.sharedContext_eq_assembledPhysicalContext
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMixedOutputPhysicalBinding.assembleMixed_observation_source_graph
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMixedOutputPhysicalBinding.assembleMixed_donor_occurrence_facts

/-! ### Canonical finite transport -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport.canonicalDecode_canonicalize
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport.decode_canonicalAssemble
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport.canonicalAssemble_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport.decode_canonicalDecode_image_canonicalAssemble_image

/-! ### Total P-94 authority ingress -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94AuthorityObservationIngress.EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94AuthorityObservationIngress.decodeTotalCertificate_encodeTotalCertificate
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94AuthorityObservationIngress.evidence_correlatedSet_inverse

/-! ### P-93 acyclic record/list/Set codec -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.suppliedSource_adaptCertified

/-! ### Ordered mixed independent-source assembly -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly.decodeMixed_assembleMixed
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly.decodeMixed_image_assembleMixed_image
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly.donorEntryOfLedger_recovered

/-! ### Heterogeneous samples -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMixedSourceSamples.decodeData_encodeData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMixedSourceSamples.UncertainSample.decodeSet_encodeSet

/-! ## Typed composite certificates -/

/-- **Fixed-base shared ingress certificate.**  For a genuine fixed-base request, packing and then
decoding returns the request (including its optional residue ingredient), the assembled state's
own channels are exactly the encoded ordered bundle, and clearing the ingress channels returns the
supplied base.  The two emptiness fields of the request are the real hypotheses; nothing about a
varying base is assumed. -/
theorem sharedIngress_certificate
    {V E B : Type u} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    {Locant : Type v} {base : WholeState V E B}
    (request : SharedCaseRequest Locant base) :
    (SharedCaseRequest.pack request).decode request.empty request.residue_empty = request ∧
      CaseBundle.extractCases request.assemble = (EncodedCollection.encode request.cases).bundle ∧
      SharedCaseRequest.clearIngressChannels request.assemble = base :=
  ⟨PackedIngress.decode_pack request,
    request.universal_ordered_recovery.2.1,
    request.universal_ordered_recovery.2.2⟩

/-- **Varying-base ingress certificate.**  Decoding the packed output of an arbitrary full
request/base pair returns that pair exactly; the packed state is the actual assembled state and
the packed sidecar is the certificate tree of the request's own ordered collection; and packing is
injective on the whole dependent request type, with no fixed base and no emptiness hypothesis
supplied by the caller. -/
theorem varyingIngress_certificate
    {V E B : Type u} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    {Locant : Type v} (r : VaryingRequest V E B Locant) :
    r.encode.decode = r ∧
      r.pack.state = r.request.assemble ∧
      HEq r.pack.sidecar (ChannelSidecar.ofCases r.request.cases) ∧
      Function.Injective (fun request : VaryingRequest V E B Locant => request.pack) :=
  ⟨r.decode_encode, r.pack_state, r.pack_sidecar,
    VaryingRequest.pack_injective⟩

/-- A genuine two-entry mixed request over an independently supplied core: one entry built from an
actual donor ledger through `donorEntryOfLedger`, one entry built from an arbitrary ordered shared
case collection through `sharedCasesEntryOfCases`.  Both entries are indexed by the common
`sharedContext` of the core and its enumeration. -/
def physicalAssemblyExampleRequest
    {V : Type} [DecidableEq V] [Fintype V]
    {LigandId LigandKind FragmentId FragmentKind : Type}
    [DecidableEq LigandId] [DecidableEq LigandKind]
    [DecidableEq FragmentId] [DecidableEq FragmentKind]
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (ledger : TetraStereo.OneCenter.DonorOccurrenceEncoding.DonorLedger
      (core.graph.certifiedEncoding enumeration).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (cases : List (PhysicalCase (sharedContext core enumeration))) :
    @MixedSourceRequest V _ _ LigandId LigandKind FragmentId FragmentKind
      Unit Unit Unit Unit Unit Unit :=
  { core := core
    enumeration := enumeration
    entries :=
      [ donorEntryOfLedger core enumeration ledger
      , sharedCasesEntryOfCases core enumeration cases ] }

/-- **Mixed assembly certificate.**  The actual assembled representation of the two-entry request
decodes back to that request; its assembled core is the actual `assemble` output; its decoded entry
list has exactly the two constructed occurrences; its shared physical context is literally the
physical context of the actual assembled output at the same enumeration; and the first decoded
occurrence is the donor entry built from the supplied ledger.  The display-only `State`,
`Framework`, `BaseName`, `Numbering`, `Locant` and `Prefix` parameters are instantiated at `Unit`;
neither the donor entry nor the shared case entry depends on them. -/
theorem physicalAssemblyExampleRequest_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    {LigandId LigandKind FragmentId FragmentKind : Type}
    [DecidableEq LigandId] [DecidableEq LigandKind]
    [DecidableEq FragmentId] [DecidableEq FragmentKind]
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (ledger : TetraStereo.OneCenter.DonorOccurrenceEncoding.DonorLedger
      (core.graph.certifiedEncoding enumeration).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (cases : List (PhysicalCase (sharedContext core enumeration))) :
    decodeMixed
        (assembleMixed (physicalAssemblyExampleRequest core enumeration ledger cases)) =
      physicalAssemblyExampleRequest core enumeration ledger cases ∧
      (assembleMixed
        (physicalAssemblyExampleRequest core enumeration ledger cases)).assembled =
        assembleEvidence core ∧
      (decodeMixed
        (assembleMixed
          (physicalAssemblyExampleRequest core enumeration ledger cases))).entries.length = 2 ∧
      sharedContext core enumeration =
        representationPhysicalContext (assembleEvidence core) enumeration ∧
      HEq
        ((decodeMixed
          (assembleMixed
            (physicalAssemblyExampleRequest core enumeration ledger cases))).entries[0]?)
        (some
          (show MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
              Unit Unit Unit Unit Unit Unit core enumeration from
            donorEntryOfLedger core enumeration ledger)) := by
  refine ⟨decodeMixed_assembleMixed _,
    rfl,
    ?_,
    ?_,
    ?_⟩
  · rw [decodeMixed_assembleMixed]
    rfl
  · simpa using sharedContext_eq_assembledPhysicalContext core enumeration
  · simpa [physicalAssemblyExampleRequest,
      TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly.donorEntryOfLedger] using
      decodeMixed_getElem?_heq
        (physicalAssemblyExampleRequest core enumeration ledger cases) 0

/-- **Canonical transport certificate.**  Decoding the canonical assembly of an independently
supplied molecular-evidence request through the actual upstream decoder returns that request, and
the canonical record decodes to the actual assembled representation. -/
theorem canonicalRequest_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    decode (canonicalDecode (canonicalAssemble enumeration request)) = request ∧
      canonicalDecode (canonicalAssemble enumeration request) = assemble request :=
  ⟨decode_canonicalAssemble enumeration request,
    canonicalDecode_canonicalAssemble enumeration request⟩

/-- **P-94 authority certificate.**  Encoding a `ValidFor` authority observation and decoding it at
the same enumeration returns the original observation, and the recovered observation satisfies
exactly the same validity predicate at the same source and policy.  No virtual-ledger bound is
required: the total codec retains unresolved references verbatim. -/
theorem p94Authority_certificate
    {source : CertifiedAuthoritativeChemicalInput} {policy : P94AuthorityPolicy}
    {V : Type} (e : SourceAtomIndex source ≃ V)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy source.input) :
    (EncodedP94AuthorityObservation.ofAuthorityValid e observation valid).toAuthority e =
        observation ∧
      (((EncodedP94AuthorityObservation.ofAuthorityValid e observation valid).toAuthority
          e).ValidFor policy source.input ↔
        observation.ValidFor policy source.input) :=
  ⟨EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid e observation valid,
    EncodedP94AuthorityObservation.ofAuthorityValid_validFor_iff e observation valid⟩

/-- **P-93 acyclic source certificate.**  Adapting a raw certified-binding source and decoding it
returns the exact authoritative input and the exact ordered list of acyclic records, and every
recovered record satisfies the same `ValidFor` at the binding's source. -/
theorem p93Acyclic_certificate
    {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93AcyclicAuthorityPolicy}
    (raw : RawAcyclicObservationSource V policy) :
    suppliedSource raw.binding.enumeration (adapt raw) =
        { source := raw.binding.source, observations := raw.observations } ∧
      ∀ observation ∈ raw.observations, observation.ValidFor raw.binding.source := by
  have recovered := suppliedSource_adapt raw
  have listEq :
      (suppliedSource raw.binding.enumeration (adapt raw)).observations =
        raw.observations :=
    congrArg RecoveredAcyclicObservationSource.observations recovered
  refine ⟨recovered, ?_⟩
  intro observation member
  exact suppliedSource_adapt_validFor raw observation (by rw [listEq]; exact member)

/-- **Heterogeneous sample certificate.**  Encoding and decoding a valid sample over the actual
mixed assembly returns the whole sample; the total and every normalized mole fraction are
preserved exactly through the existing `MolarComposition` carrier. -/
theorem mixedSample_certificate
    {I : Type*} [Fintype I]
    {ctx : OrganicStereoMixedSourceSamples.Context I}
    (s : OrganicStereoMixedSourceSamples.HeterogeneousSample ctx) :
    OrganicStereoMixedSourceSamples.decode
        (OrganicStereoMixedSourceSamples.encode s) = s ∧
      OrganicStereoMixedSourceSamples.AssembledSample.total
          (OrganicStereoMixedSourceSamples.encode s) =
        OrganicStereoMixedSourceSamples.HeterogeneousSample.total s ∧
      ∀ i, OrganicStereoMixedSourceSamples.AssembledSample.fraction
          (OrganicStereoMixedSourceSamples.encode s) i =
        OrganicStereoMixedSourceSamples.HeterogeneousSample.fraction s i :=
  ⟨OrganicStereoMixedSourceSamples.decode_encode s,
    OrganicStereoMixedSourceSamples.encode_total s,
    fun i => OrganicStereoMixedSourceSamples.encode_fraction s i⟩

/-- **Mixed assembly on arbitrary correlated sets.**  The actual `assembleMixed` is injective on
whole independent mixed requests (derived from the exact request inverse, not assumed), and
decoding the assembled image of an arbitrary set of requests returns exactly that set. -/
theorem mixedAssemblySet_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    {LigandId LigandKind FragmentId FragmentKind : Type}
    [DecidableEq LigandId] [DecidableEq LigandKind]
    [DecidableEq FragmentId] [DecidableEq FragmentKind]
    {State Framework BaseName Numbering Locant Prefix : Type} :
    Function.Injective
        (fun request : @MixedSourceRequest V _ _ LigandId LigandKind FragmentId FragmentKind
            State Framework BaseName Numbering Locant Prefix =>
          assembleMixed request) ∧
      ∀ requests : Set (@MixedSourceRequest V _ _ LigandId LigandKind FragmentId FragmentKind
          State Framework BaseName Numbering Locant Prefix),
        decodeMixed '' (assembleMixed '' requests) = requests := by
  constructor
  · intro first second equal
    have applied := congrArg decodeMixed equal
    simpa only [decodeMixed_assembleMixed] using applied
  · intro requests
    exact decodeMixed_image_assembleMixed_image requests

/-- **Source-bound residue certificate.**  The attached residue channel has the ledger's residue
count, decoding its annotation recovers exactly the ledger's observable view at the same encoding
equivalence, and rebuilding from the packed proof-only metadata through the total
`PackedResidueMeta` codec returns the original ingress. -/
theorem residueIngress_certificate
    {V E B : Type u} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    {Locant : Type v} {base : WholeState V E B}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (ingress : ResidueIngress Locant base enumeration) :
    ingress.channel.residueCount = ingress.ledger.residueCount ∧
      decodeView? ingress.codec
          (TetraStereo.OneCenter.OrganicStereoIndependentElectronicEncoding.encodedAtomEquiv
            base.graph enumeration)
          ingress.channel.annotation = some (viewOfLedger ingress.ledger) ∧
      PackedResidueMeta.toIngress? (base := base)
          (PackedResidueMeta.some (PackedResidue.ofIngress ingress)) = some ingress :=
  ⟨ingress.channel_residueCount,
    ingress.channel_decodeView,
    PackedResidueMeta.toIngress?_ofIngress ingress⟩

end TetraStereo.Examples.OrganicStereoPhysicalAssemblyKernelCertificate
