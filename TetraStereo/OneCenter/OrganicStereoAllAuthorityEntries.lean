import TetraStereo.OneCenter.OrganicStereoAuthorityMixedSourceAssembly
import TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress
import TetraStereo.OneCenter.OrganicStereoNativeP94SourceContext
import TetraStereo.OneCenter.OrganicStereoNoncarbonTetrahedralIngress
import TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress
import TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress
import TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress
import TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding
import TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress
import TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes
import TetraStereo.OneCenter.IUPACRemaining71P93GeneralReviewedSemantics
import TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The complete closed authority family union

This module is the single concrete closed authority entry codec.  It replaces the three-way
`AuthorityMixedEntry` scope with one ordered heterogeneous list whose tags are exactly the live
families of the actual authority vocabulary:

* the legacy `MixedEntry` five-way union in its raw form; in the native form the four
  non-observation legacy constructors are copied unchanged and the observation constructor is
  rebuilt from a source-free `NativeSourceContext` together with the ordered family at the
  certified source reconstructed from that context (no original certified source and no whole
  original observation are stored),
* the P-94 authority records, at a source context reconstructed from the common core graph plus
  the source's own optional native coordinate/drawing channels and its proof-only structural
  certificate (`OrganicStereoNativeP94SourceContext.NativeSourceContext`); no certified source
  record and no whole original observation is stored,
* the P-93 acyclic records, through the existing source tie,
* the P-93.1 general-configuration five-row family (`absolute`, `relative`,
  `mixedAbsoluteRelative`, `racemate` and `ambo`) as actual `SourceGeneralObservation` values with
  their actual `Judged` certificates at the reconstructed common source; the generic
  `policy.Descriptor` language and all five forms are retained,
* the noncarbon tetrahedral authority (seven source rows),
* the unified monocyclic/ring-assembly channel (the eleven-row `SourceCyclicObservation`, that is
  the eight monocyclic rows plus the three ring-assembly successor rows),
* the fused/von Baeyer authority (six rows),
* the cyclophane authority (three rows),
* the spiro authority (five rows),
* the non-relational fullerene authority (four rows),
* the relational fullerene successor native input channel,
* the tagged relational fullerene variant rows (handed types 1--3, Type-4 and superimposed) beyond
  that base channel, through `OrganicStereoRelationalFullereneVariantIngress`,
* the coupled/ring-chain authority (with all fifteen nested evidence cases), encoded through the
  native-axes successor payload, and
* the coupled/ring-chain native-axes successor, encoded through the same native-axes payload.

## Coverage statement

The closed union has fifteen raw constructor tags over thirteen distinct families of the currently
staged authority vocabulary.  Two tags are dedicated alternate routes rather than additional
families: the coupled/ring-chain family deliberately appears under **two** tags, `.coupled` and
`.coupledNativeAxes` (the raw domain keeps both source shapes and the raw inverse must distinguish
them; the two tags share the one native payload type
`SuppliedNativeCoupledRingChainObservation`), and `.fullereneMethodology` is the molecule-free
route for the fullerene methodology row, which the molecule-carrying `.fullerene` tag still covers
(the methodology row has `MoleculeBoundTo = True` and no molecule in its observation, so it is not
counted as a separate family).  This is therefore *not* a claim of thirteen distinct chemical
families of the English-language literature, and it is not a claim of complete chemical coverage:
it is the explicit covered vocabulary listed above.

The relational variant branch uses the actual tagged union codec for `handed` / `type4` /
`superimposed`; the Type-4 branch acquires neither a numbering record nor a turn, and no variant
tag is collapsed into another.

## The general P-93.1 five-row family

`AllAuthorityPolicies.generalPolicy` is the field whose type
`IUPACNormativeProvision.P93GeneralAuthorityPolicy` comes directly from
`IUPACRemaining71P93GeneralReviewedSemantics`.  The raw `.general` constructor stores an actual
`SourceGeneralObservation policies.generalPolicy` — one of the five reviewed forms `absolute`,
`relative`, `mixedAbsoluteRelative`, `racemate` and `ambo` — together with the actual
`SourceGeneralObservation.Judged` certificate at the reconstructed common source
`recoveredSource core enumeration`.  The descriptor language is the arbitrary `policy.Descriptor`
of the reviewed policy; nothing is hard-coded to the Blue Book descriptor language, and no form is
collapsed into another.

The native `.general` constructor is decomposed and source-free.  It stores the actual
`NativeSourceContext core.graph enumeration` (optional native coordinate and drawing channels, so
absence and presence are both preserved), the actual `NativeGeneralObservation
policies.generalPolicy V` with every physical unit relabelled into `V`, the actual `Judged`
certificate of the decoded observation at the source *reconstructed from that context*, and a
proof-only coherence equality identifying that reconstructed source with the common
`recoveredSource`.  The context and the judgment are therefore always attached to the same
source; the decoder transports the judgment along the coherence equality, and the encoder derives
both the equality and the judgment from `decode_generalContext_source` recovery.  No certified
source, raw observation, `RawMolecule`, or inverse hypothesis is retained.  The representation
bounds needed by `encodeGeneralObservation` are derived from the actual judgment through
`SourceGeneralObservation.boundedIn_of_judged`; nothing is assumed.

## Kernel-authority endpoints

`decodeEntry_encodeEntry` dispatches every one of the fifteen tags explicitly, including the
general branch.  The dedicated endpoints `decodeGeneralEntry_encodeGeneralEntry`,
`decode_generalContext`, `decode_generalContext_source`, `general_extEq` and
`decodeEntry_encodeEntry_general` are guarded by `assert_kernel_only`, alongside the seventeen
pre-existing guards.


**Every union row is one individual observation.**  The one ordered list is therefore a list of
records, not a list of per-family blocks: arbitrary cross-family interleaving, repetition and
cross-family correlation are literal.  There are no separate family marginals.

Every P-93 family is stated at the one reconstructed common source
`recoveredSource core enumeration`, built from the actual core graph, rational-coordinate channel
and drawing channel.  The source well-formedness certificate is supplied once by the request.  All
boundedness premises of the native codecs are derived from the entry's actual `ValidFor` predicate
and that one binding; no inverse, agreement or codec-round-trip premise is assumed.

The module proves the exact entry inverse for every concrete constructor, the exact ordered-list
inverse under dependent core transport, the exact whole-request inverse, injectivity, and the
arbitrary correlated set-image inverse.
-/

namespace TetraStereo.OneCenter

open OrganicStereoMixedSourceAssembly
open OrganicStereoAuthorityMixedSourceAssembly
open OrganicStereoP94AuthorityObservationIngress
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoNativeP94SourceContext
open OrganicStereoP93AcyclicIngress
open OrganicStereoP93GeneralAuthorityIngress
open OrganicStereoOrderedObservationFamily
open DonorGroupingIngress
open OrganicStereoSharedPhysicalCaseIngress

namespace OrganicStereoAllAuthorityEntries

variable {V : Type} [DecidableEq V] [Fintype V]
variable {LigandId LigandKind FragmentId FragmentKind : Type}
variable {State Framework : Type}
variable {BaseName Numbering Locant Prefix : Type}

/-! ## The complete policy record -/

/-- Every live authority policy used by the closed union, in one record. -/
structure AllAuthorityPolicies where
  /-- The P-94 authority policy. -/
  policy94 : P94AuthorityPolicy
  /-- The P-93 acyclic authority policy. -/
  policy93 : P93AcyclicAuthorityPolicy
  /-- The noncarbon tetrahedral authority policy. -/
  noncarbonPolicy : P93NoncarbonTetrahedralAuthorityPolicy
  /-- The monocyclic authority policy. -/
  monocyclicPolicy : P93MonocyclicAuthorityPolicy
  /-- The ring-assembly authority policy. -/
  assemblyPolicy : P93RingAssemblyAuthorityPolicy
  /-- The fused-ring authority policy. -/
  fusedPolicy : P93FusedAuthorityPolicy
  /-- The von Baeyer authority policy. -/
  vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy
  /-- The cyclophane authority policy. -/
  cyclophanePolicy : P93CyclophaneAuthorityPolicy
  /-- The spiro authority policy. -/
  spiroPolicy : P93SpiroAuthorityPolicy
  /-- The general P-93.1 five-row authority policy.  Its descriptor type is the arbitrary
  `policy.Descriptor`; nothing is hard-coded to the Blue Book descriptor language. -/
  generalPolicy : IUPACNormativeProvision.P93GeneralAuthorityPolicy
  /-- The fullerene authority policy. -/
  fullerenePolicy : P93FullereneAuthorityPolicy
  /-- The relational fullerene authority policy. -/
  relationalPolicy : P93RelationalFullereneAuthorityPolicy
  /-- The coupled/ring-chain authority policy. -/
  coupledPolicy : P93CoupledRingChainAuthorityPolicy

variable {policies : AllAuthorityPolicies}
variable {core : OrganicMolecularEvidence V}
variable {enumeration : V ≃ Fin (Fintype.card V)}

/-! ## The one reconstructed common source -/

/-- The authoritative input reconstructed from the actual core graph, rational-coordinate channel
and drawing channel at the common enumeration. -/
abbrev recoveredSource (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : AuthoritativeChemicalInput :=
  recoveredAcyclicSource core enumeration

/-- The one physical-frame binding of the reconstructed source to the common core.  Every equality
is definitional; the only transported datum is the request's structural well-formedness
certificate. -/
def commonBinding (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V where
  source := recoveredSource core enumeration
  shared := coreFiniteSource core
  enumeration := enumeration
  graph_eq := rfl
  spatial_eq := rfl
  diagram_eq := rfl
  spatial_wellFormed := source_well_formed.2.1

/-! ## The source-independent decoded channels

Each decoder is the actual per-observation successor codec of its family.  They are total
functions of the native payload and the reconstructed common context; none of them consults an
original request, an original source record or an original observation. -/

/-- Decode one noncarbon tetrahedral native observation. -/
abbrev decodedNoncarbon (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoNoncarbonTetrahedralIngress.NativeNoncarbonObservation V
      policies.noncarbonPolicy.Descriptor) :
    OrganicStereoNoncarbonTetrahedralIngress.SourceNoncarbonObservation
      policies.noncarbonPolicy :=
  OrganicStereoNoncarbonTetrahedralIngress.ofNativeObservation enumeration
    policies.noncarbonPolicy observation

/-- Decode one unified monocyclic/ring-assembly native observation. -/
abbrev decodedCyclic (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoMonocyclicRingAssemblyIngress.CyclicObservation V
      policies.monocyclicPolicy policies.assemblyPolicy) :
    OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation
      policies.monocyclicPolicy policies.assemblyPolicy :=
  OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation enumeration observation

/-- Decode one fused/von Baeyer native observation. -/
abbrev decodedFused (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoFusedVonBaeyerIngress.SuppliedFusedVonBaeyerObservation V
      policies.fusedPolicy policies.vonBaeyerPolicy) :
    OrganicStereoFusedVonBaeyerIngress.SourceFusedVonBaeyerObservation
      policies.fusedPolicy policies.vonBaeyerPolicy :=
  OrganicStereoFusedVonBaeyerIngress.unrelabelObservation enumeration observation

/-- Decode one cyclophane native observation. -/
abbrev decodedCyclophane (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoCyclophaneAuthorityIngress.NativeCyclophaneAuthorityObservation
      V policies.cyclophanePolicy) :
    OrganicStereoCyclophaneAuthorityIngress.SourceCyclophaneAuthorityObservation
      policies.cyclophanePolicy :=
  OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation enumeration observation

/-- Decode one spiro native observation. -/
abbrev decodedSpiro (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoSpiroAuthorityIngress.NativeSpiroAuthorityObservation
      policies.spiroPolicy V) :
    OrganicStereoSpiroAuthorityIngress.SourceSpiroAuthorityObservation
      policies.spiroPolicy :=
  OrganicStereoSpiroAuthorityIngress.decodeObservation enumeration observation

/-- The source-independent fullerene decode context rebuilt from the common core. -/
def fullereneContext (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext V :=
  OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofEnumeration
    enumeration (coreFiniteSource core).spatial?

/-- Decode one non-relational fullerene native observation. -/
abbrev decodedFullerene (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoFullereneAuthorityIngress.NativeFullereneAuthorityObservationFamily
      V) :
    OrganicStereoFullereneAuthorityIngress.SourceFullereneAuthorityObservation
      policies.fullerenePolicy :=
  (fullereneContext core enumeration).decodeFamily policies.fullerenePolicy observation

/-- Decode one native fullerene methodology observation.  The methodology row carries no
molecule-specific physical payload: the existing decode context sends its unique native record to
the unique source record, and no `RawMolecule` or conversion equality is involved. -/
abbrev decodedFullereneMethodology (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : OrganicStereoFullereneAuthorityIngress.NativeFullereneMethodologyAuthorityObservation) :
    P93FullereneMethodologyAuthorityObservation :=
  (fullereneContext core enumeration).decodeMethodologyObservation observation

open OrganicStereoFullereneAuthorityIngress

/-- Encode one source fullerene methodology observation.  The encoder ignores the common source
(as the upstream methodology codec does) and emits the unique native record. -/
def encodeFullereneMethodology
    (observation : P93FullereneMethodologyAuthorityObservation) :
    NativeFullereneMethodologyAuthorityObservation :=
  .fourWayDecisionRule

/-- Decode one native fullerene methodology observation without any common source. -/
def decodeFullereneMethodology
    (observation : NativeFullereneMethodologyAuthorityObservation) :
    P93FullereneMethodologyAuthorityObservation :=
  .fourWayDecisionRule

/-- Exact molecule-free methodology inverse.  Neither side has a molecule-specific payload. -/
theorem decodeFullereneMethodology_encodeFullereneMethodology
    (observation : P93FullereneMethodologyAuthorityObservation) :
    decodeFullereneMethodology (encodeFullereneMethodology observation) = observation := by
  cases observation
  rfl

/-- The molecule-free methodology codec is the existing upstream codec at the common decode
context: its native side is the unique record and its source side is the unique record. -/
theorem decodeFullereneMethodology_eq (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : NativeFullereneMethodologyAuthorityObservation) :
    decodedFullereneMethodology core enumeration observation =
      decodeFullereneMethodology observation := by
  cases observation
  rfl

/-- The relational successor shared spatial configuration. -/
def relationalSharedSpatial? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Option SpatialConfiguration :=
  OrganicFiniteSource.encodeSpatial? enumeration (coreFiniteSource core).spatial?

/-- Decode one relational fullerene native observation. -/
abbrev decodedRelational (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoRelationalFullereneInputEncoding.NativeRelationalFullereneObservation
      V enumeration policies.relationalPolicy) :
    P93RelationalFullereneAuthorityObservation policies.relationalPolicy :=
  OrganicStereoRelationalFullereneInputEncoding.unrelabelObservation enumeration
    policies.relationalPolicy (relationalSharedSpatial? core enumeration) observation

/-- Decode one tagged relational fullerene variant observation (handed, Type-4 or superimposed).
The spatial channel is the common reconstructed source's channel, and each tag is decoded through
its own concrete codec: `handed` and `superimposed` through the full native base, and `type4`
through the Type-4 codec, which acquires neither a numbering record nor a turn. -/
abbrev decodedRelationalVariant (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoRelationalFullereneVariantIngress.NativeRelationalVariantObservation
      V enumeration policies.relationalPolicy) :
    OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation
      policies.relationalPolicy :=
  OrganicStereoRelationalFullereneVariantIngress.decodeVariant enumeration
    (relationalSharedSpatial? core enumeration) observation

/-- Decode one coupled/ring-chain native observation. -/
abbrev decodedCoupled (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoCoupledRingChainIngress.SuppliedCoupledRingChainObservation
      V policies.coupledPolicy) :
    P93CoupledRingChainAuthorityObservation policies.coupledPolicy :=
  OrganicStereoCoupledRingChainIngress.unrelabelCoupledObservation enumeration observation

/-- Decode one coupled/ring-chain native-axes native observation. -/
abbrev decodedCoupledNativeAxes (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoCoupledRingChainNativeAxes.SuppliedNativeCoupledRingChainObservation
      V policies.coupledPolicy) :
    P93CoupledRingChainAuthorityObservation policies.coupledPolicy :=
  OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation enumeration observation

/-! ## The general P-93.1 five-row channel

The raw side is the actual five-tag `SourceGeneralObservation` with its actual reviewed `Judged`
predicate at the reconstructed common source.  The native side is decomposed: the source-free
`NativeSourceContext` (optional native coordinates and drawing channel), the native five-tag
observation, and the actual `Judged` certificate at the common source.  The representation bounds
are derived, never assumed, from that certificate through
`SourceGeneralObservation.boundedIn_of_judged`. -/

/-- The certified common source of the general branch.  Its input is exactly
`recoveredSource core enumeration`; the certificate is the request's structural certificate. -/
def generalCertifiedSource (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    CertifiedAuthoritativeChemicalInput where
  input := recoveredSource core enumeration
  structurallyWellFormed := source_well_formed

/-- The source-free native context of the general branch: the common source's optional coordinate
and drawing channels, tied to the common graph by the definitional graph equality.  Absence and
presence of both optional channels are preserved exactly. -/
def generalContext (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    NativeSourceContext core.graph enumeration :=
  encodeSourceContext core.graph enumeration
    (generalCertifiedSource core enumeration source_well_formed) rfl

/-- Decode one native five-tag general observation into the actual raw P-93.1 five-tag family. -/
abbrev decodedGeneral (enumeration : V ≃ Fin (Fintype.card V))
    (policies : AllAuthorityPolicies)
    (observation : OrganicStereoP93GeneralAuthorityIngress.NativeGeneralObservation
      policies.generalPolicy V) :
    OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation policies.generalPolicy :=
  OrganicStereoP93GeneralAuthorityIngress.decodeGeneralObservation policies.generalPolicy
    enumeration observation

/-- The explicit representation bounds of a general observation, derived from its actual reviewed
judgment at the reconstructed common source and the request's structural certificate. -/
def generalBounds (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed)
    (observation : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation
      policies.generalPolicy)
    (judged : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.Judged
      policies.generalPolicy (recoveredSource core enumeration) observation) :
    observation.BoundedIn (Fintype.card V) :=
  OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.boundedIn_of_judged
    policies.generalPolicy (generalCertifiedSource core enumeration source_well_formed)
    core.graph enumeration rfl observation judged

/-- Encode one actual raw general observation into the native five-tag observation.  Every unit
bound is derived from the actual judgment; no inverse or agreement premise is assumed. -/
def encodeGeneralEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed)
    (observation : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation
      policies.generalPolicy)
    (judged : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.Judged
      policies.generalPolicy (recoveredSource core enumeration) observation) :
    OrganicStereoP93GeneralAuthorityIngress.NativeGeneralObservation policies.generalPolicy V :=
  OrganicStereoP93GeneralAuthorityIngress.encodeGeneralObservation policies.generalPolicy
    enumeration observation
    (generalBounds core enumeration source_well_formed observation judged)

/-- **Exact general observation inverse.**  Decoding the encoded native five-tag observation
returns the actual raw P-93.1 observation: all five forms, the generic descriptor type, ordered
assignment lists, duplicates, scopes, typography, the exact rational racemate fraction and the
`ambo` composition class are recovered literally. -/
theorem decodeGeneralEntry_encodeGeneralEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed)
    (observation : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation
      policies.generalPolicy)
    (judged : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.Judged
      policies.generalPolicy (recoveredSource core enumeration) observation) :
    decodedGeneral enumeration policies
        (encodeGeneralEntry core enumeration source_well_formed observation judged) =
      observation := by
  unfold decodedGeneral encodeGeneralEntry generalBounds
  exact OrganicStereoP93GeneralAuthorityIngress.decodeGeneralObservation_encodeGeneralObservation
    policies.generalPolicy enumeration observation
    (OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.boundedIn_of_judged
      policies.generalPolicy (generalCertifiedSource core enumeration source_well_formed)
      core.graph enumeration rfl observation judged)

/-- The native general context reconstructs exactly the certified common source, including both
optional channels. -/
theorem decode_generalContext (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    decodeSourceContext core.graph enumeration (generalContext core enumeration source_well_formed) =
      generalCertifiedSource core enumeration source_well_formed :=
  decode_encodeSourceContext core.graph enumeration
    (generalCertifiedSource core enumeration source_well_formed) rfl

/-- The source reconstructed from the native general context is exactly the common reconstructed
source. -/
theorem decode_generalContext_source (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    (decodeSourceContext core.graph enumeration
        (generalContext core enumeration source_well_formed)).input =
      recoveredSource core enumeration := by
  rw [decode_generalContext]
  rfl

/-- Exact preservation of the optional spatial channel: `none` stays `none`, and a present channel
is the same encoded channel. -/
theorem decode_generalContext_spatial? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    (decodeSourceContext core.graph enumeration
        (generalContext core enumeration source_well_formed)).input.spatial? =
      (recoveredSource core enumeration).spatial? := by
  rw [decode_generalContext_source]

/-- Exact preservation of the optional drawing channel, including its ordered bond and parity
lists. -/
theorem decode_generalContext_diagram? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    (decodeSourceContext core.graph enumeration
        (generalContext core enumeration source_well_formed)).input.diagram? =
      (recoveredSource core enumeration).diagram? := by
  rw [decode_generalContext_source]

/-! ## Native legacy entries: the source-free observation channel

`OrderedObservationFamily`'s `source` parameter is phantom: no field of the structure mentions it.
`reseatFamily` therefore moves a family to another certified source without touching any data
field.  The native mirror `NativeLegacyEntry` keeps the four non-observation legacy constructors
verbatim, while the observation constructor stores only the source-free native context and the
family at the certified source *reconstructed* from that context.  In particular the family's own
geometry is independent of the common core geometry; only the graph tie to the common core is
retained, exactly as in the raw legacy entry. -/

/-- Re-index an ordered observation family from one certified source to another.  The source is a
phantom parameter, so every field (scope, count, ordered conformers, scope agreement and optional
payload) is unchanged. -/
def reseatFamily {source target : CertifiedAuthoritativeChemicalInput}
    (family : OrderedObservationFamily source V State Framework) :
    OrderedObservationFamily target V State Framework where
  scope := family.scope
  count := family.count
  conformer := family.conformer
  wellScoped := family.wellScoped
  observation? := family.observation?

/-- Reseating a family to its own source is the identity. -/
@[simp] theorem reseatFamily_self {source : CertifiedAuthoritativeChemicalInput}
    (family : OrderedObservationFamily source V State Framework) :
    reseatFamily (target := source) family = family := rfl

/-- The native mirror of `MixedEntry`.  The observation case stores the source-free native
context and the ordered family at the certified source reconstructed from that context; the other
four constructors are the legacy donor, citation, physical-frame and shared-case payloads
unchanged.  No `CertifiedAuthoritativeChemicalInput` and no `MixedEntry` are retained. -/
inductive NativeLegacyEntry (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Type where
  /-- A source-free native observation context together with the ordered family at the certified
  source reconstructed from it. -/
  | observation (context : NativeSourceContext core.graph enumeration)
      (family : OrderedObservationFamily
        (decodeSourceContext core.graph enumeration context) V State Framework) :
      NativeLegacyEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration
  /-- The legacy native donor channel and its validity against the common graph. -/
  | donor
      (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
        core.graph.interactions.length)
      (validity : NativeChannelValidity core.graph enumeration
        (rfl : core.graph.interactions.length = core.graph.interactions.length) channel) :
      NativeLegacyEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration
  /-- The legacy supplied citation satellite tied to the common graph. -/
  | citation
      (satellite : OrganicStereoSuppliedCitationIngress.SuppliedCitationSatellite V
        BaseName Numbering Locant Prefix)
      (graph_eq : satellite.graph = core.graph) :
      NativeLegacyEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration
  /-- The legacy P-93 physical frame satellite tied to the common graph, coordinates and drawing
  channel. -/
  | physicalFrame
      (satellite : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite V)
      (graph_eq : satellite.graph = core.graph)
      (spatial_eq : satellite.spatial? = core.rationalPositions?)
      (diagram_eq : satellite.diagram? = core.diagram?) :
      NativeLegacyEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration
  /-- The legacy proof-carrying shared physical case collection at the common context. -/
  | sharedCases
      (encoded : EncodedCollection (sharedContext core enumeration)) :
      NativeLegacyEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration

/-- Encode one legacy mixed entry natively.  The observation case factors the certified source
through `encodeSourceContext` and reseats the ordered family to the reconstructed source; the
other four constructors are copied verbatim. -/
def encodeLegacyEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration →
    NativeLegacyEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration
  | .observation source family source_graph_eq =>
      let context := encodeSourceContext core.graph enumeration source source_graph_eq
      .observation context
        (reseatFamily (source := source)
          (target := decodeSourceContext core.graph enumeration context) family)
  | .donor channel validity => .donor channel validity
  | .citation satellite graph_eq => .citation satellite graph_eq
  | .physicalFrame satellite graph_eq spatial_eq diagram_eq =>
      .physicalFrame satellite graph_eq spatial_eq diagram_eq
  | .sharedCases encoded => .sharedCases encoded

/-- Decode one native legacy entry.  The observation case reconstructs the certified source from
the native context and forms the raw legacy observation at that source; the graph tie is the
definitional `decodeSourceContext_molecule` equality.  The other four constructors are copied
verbatim. -/
def decodeLegacyEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    NativeLegacyEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration →
    MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration
  | .observation context family =>
      .observation (decodeSourceContext core.graph enumeration context) family
        (decodeSourceContext_molecule core.graph enumeration context)
  | .donor channel validity => .donor channel validity
  | .citation satellite graph_eq => .citation satellite graph_eq
  | .physicalFrame satellite graph_eq spatial_eq diagram_eq =>
      .physicalFrame satellite graph_eq spatial_eq diagram_eq
  | .sharedCases encoded => .sharedCases encoded

/-- Heterogeneous equality of a reseated family with its original.  The source is a phantom
parameter, so reseating along a source equality transports the family without changing any
field. -/
theorem heq_reseatFamily {source target : CertifiedAuthoritativeChemicalInput}
    (equal : source = target) (family : OrderedObservationFamily source V State Framework) :
    HEq (reseatFamily (target := target) family) family := by
  cases equal
  exact heq_of_eq (reseatFamily_self family)

/-- Extensionality of raw legacy observation entries across a source equality and a
heterogeneous family equality.  The graph ties are proposition-valued and are identified by proof
irrelevance. -/
theorem mixedObservation_extEq
    {firstSource secondSource : CertifiedAuthoritativeChemicalInput}
    {firstFamily : OrderedObservationFamily firstSource V State Framework}
    {secondFamily : OrderedObservationFamily secondSource V State Framework}
    {firstGraph : firstSource.input.molecule = core.graph.encode enumeration}
    {secondGraph : secondSource.input.molecule = core.graph.encode enumeration}
    (source : firstSource = secondSource) (family : HEq firstFamily secondFamily) :
    (MixedEntry.observation firstSource firstFamily firstGraph :
      MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration) =
      (MixedEntry.observation secondSource secondFamily secondGraph :
        MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix core enumeration) := by
  cases source
  cases eq_of_heq family
  rfl

/-- **Exact legacy entry inverse.**  Encoding a legacy mixed entry into its source-free native
form and decoding it returns the original entry.  The observation case uses the exact source
reconstruction `decode_encodeSourceContext`; the remaining payload fields are the identity and the
proposition-valued fields are identified by proof irrelevance. -/
theorem decodeLegacyEntry_encodeLegacyEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration) :
    decodeLegacyEntry core enumeration (encodeLegacyEntry core enumeration entry) = entry := by
  cases entry with
  | observation source family source_graph_eq =>
      simp only [encodeLegacyEntry, decodeLegacyEntry]
      refine mixedObservation_extEq
        (decode_encodeSourceContext core.graph enumeration source source_graph_eq) ?_
      exact heq_reseatFamily
        (decode_encodeSourceContext core.graph enumeration source source_graph_eq).symm family
  | donor channel validity => rfl
  | citation satellite graph_eq => rfl
  | physicalFrame satellite graph_eq spatial_eq diagram_eq => rfl
  | sharedCases encoded => rfl

/-! ## The raw entry union -/

/-- One raw entry of the closed authority union.  Every constructor retains exactly one actual
observation, its actual policy, and its actual admission certificate — `ValidFor` for the
geometric families and the reviewed `Judged` predicate for the general P-93.1 family.  All P-93
families are stated at the one reconstructed common source. -/
inductive RawEntry (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type)
    (policies : AllAuthorityPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Type where
  /-- An accepted legacy mixed entry, unchanged. -/
  | legacy (entry : MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix core enumeration) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One P-94 authority observation, its actual certified source, the genuine source-to-common
  graph equality, and its actual authority `ValidFor` predicate. -/
  | p94 (source : CertifiedAuthoritativeChemicalInput)
      (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
      (observation : P94AuthorityObservation policies.policy94)
      (valid : observation.ValidFor policies.policy94 source.input) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One P-93 acyclic observation with its genuine source tie. -/
  | acyclic (tie : AcyclicSourceTie V enumeration)
      (graph_eq : tie.shared.graph = core.graph)
      (spatial_eq : tie.shared.spatial? = core.rationalPositions?)
      (diagram_eq : tie.shared.diagram? = core.diagram?)
      (observation : SourceAcyclicObservation policies.policy93)
      (valid : observation.ValidFor tie.source) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One P-93.1 general-configuration authority observation: one of the five reviewed forms
  (`absolute`, `relative`, `mixedAbsoluteRelative`, `racemate`, `ambo`) at the generic
  `policy.Descriptor`, with its actual reviewed `Judged` certificate at the reconstructed common
  source. -/
  | general
      (observation : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation
        policies.generalPolicy)
      (judged : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.Judged
        policies.generalPolicy (recoveredSource core enumeration) observation) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One noncarbon tetrahedral authority observation. -/
  | noncarbon
      (observation : OrganicStereoNoncarbonTetrahedralIngress.SourceNoncarbonObservation
        policies.noncarbonPolicy)
      (valid : observation.ValidFor policies.noncarbonPolicy
        (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One unified monocyclic/ring-assembly observation. -/
  | cyclic
      (observation : OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation
        policies.monocyclicPolicy policies.assemblyPolicy)
      (valid : observation.ValidFor (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One fused/von Baeyer authority observation. -/
  | fused
      (observation : OrganicStereoFusedVonBaeyerIngress.SourceFusedVonBaeyerObservation
        policies.fusedPolicy policies.vonBaeyerPolicy)
      (valid : observation.ValidFor (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One cyclophane authority observation. -/
  | cyclophane
      (observation : OrganicStereoCyclophaneAuthorityIngress.SourceCyclophaneAuthorityObservation
        policies.cyclophanePolicy)
      (valid : observation.ValidFor (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One spiro authority observation. -/
  | spiro
      (observation : OrganicStereoSpiroAuthorityIngress.SourceSpiroAuthorityObservation
        policies.spiroPolicy)
      (valid : observation.ValidFor (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One non-relational fullerene authority observation, with the raw molecule syntax needed to
  form the existing common source and its observation-specific conversion premise. -/
  | fullerene (molecule : RawMolecule)
      (conversion_eq : molecule.toSemanticMolecule? =
        some (recoveredSource core enumeration).molecule)
      (observation : OrganicStereoFullereneAuthorityIngress.SourceFullereneAuthorityObservation
        policies.fullerenePolicy)
      (valid : observation.ValidFor (recoveredSource core enumeration))
      (moleculeBound : observation.MoleculeBoundTo (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One molecule-free fullerene methodology observation.  The methodology row has no
  molecule-specific physical payload (`MoleculeBoundTo` is `True` and the native record is
  molecule-free), so this dedicated route stores the actual observation and its actual validity
  without inventing an unrelated `RawMolecule` or conversion equality.  The old `fullerene` tag
  remains available for the molecule-carrying rows. -/
  | fullereneMethodology (observation : P93FullereneMethodologyAuthorityObservation)
      (valid : observation.ValidFor policies.fullerenePolicy
        (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One relational fullerene successor native input observation. -/
  | relationalFullerene
      (observation : P93RelationalFullereneAuthorityObservation policies.relationalPolicy)
      (valid : observation.ValidFor policies.relationalPolicy
        (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One tagged relational fullerene variant observation (handed, Type-4 or superimposed)
  beyond the existing base channel, with its actual source validity. -/
  | relationalVariants
      (observation : OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation
        policies.relationalPolicy)
      (valid : observation.ValidFor (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One coupled/ring-chain authority observation, with all fifteen nested evidence cases
  retained inside the carrier. -/
  | coupled
      (observation : P93CoupledRingChainAuthorityObservation policies.coupledPolicy)
      (valid : observation.ValidFor policies.coupledPolicy
        (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One coupled/ring-chain native-axes successor observation. -/
  | coupledNativeAxes
      (observation : P93CoupledRingChainAuthorityObservation policies.coupledPolicy)
      (valid : observation.ValidFor policies.coupledPolicy
        (recoveredSource core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration

/-! ## The native entry union -/

/-- One concrete native entry of the closed authority union.  Every constructor stores exactly one
native observation plus its proof-only decoded-side admission certificate (`ValidFor`, or the
reviewed `Judged` predicate for the general P-93.1 family), exactly as the accepted lower modules
do.  Decoding is therefore total and never consults the original request.

The P-94 payload is the actual `NativeAuthorityObservation`: a source-free
`NativeSourceContext` (optional native coordinates and drawing annotation), the full encoded
authority payload reindexed onto the *reconstructed* certified source, and the decoded validity
proof.  No original certified source and no whole original observation is retained.  The legacy
observation payload is likewise the source-free `NativeSourceContext` plus the family at the
reconstructed source (`NativeLegacyEntry`).  Both coupled tags carry the native-axes successor
payload; neither keeps a whole normalization result or a whole spatial configuration. -/
inductive NativeEntry (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type)
    (policies : AllAuthorityPolicies)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Type where
  | legacy (entry : NativeLegacyEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix core enumeration) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | p94 (observation : NativeAuthorityObservation core.graph enumeration policies.policy94) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | acyclic (observation : AcyclicObservation V policies.policy93)
      (source_well_formed : (recoveredSource core enumeration).SpatialIndicesWellFormed)
      (valid : (unrelabelObservation enumeration observation).ValidFor
        (decodedAcyclicTie core enumeration source_well_formed).source) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  /-- One P-93.1 general-configuration observation.  The payload is source-free: the actual native
  context (optional coordinate and drawing channels), the actual native five-tag observation with
  every physical unit relabelled into `V`, and the actual `Judged` certificate at the source
  reconstructed from that context.  The source-coherence equality ties that reconstructed source
  to the common `recoveredSource`, so the context and the judgment are never detached; the decoder
  transports the judgment along it. -/
  | general
      (context : NativeSourceContext core.graph enumeration)
      (observation : OrganicStereoP93GeneralAuthorityIngress.NativeGeneralObservation
        policies.generalPolicy V)
      (judged : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.Judged
        policies.generalPolicy
        (decodeSourceContext core.graph enumeration context).input
        (decodedGeneral enumeration policies observation))
      (source_eq : (decodeSourceContext core.graph enumeration context).input =
        recoveredSource core enumeration) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | noncarbon
      (observation : OrganicStereoNoncarbonTetrahedralIngress.NativeNoncarbonObservation V
        policies.noncarbonPolicy.Descriptor)
      (valid : (decodedNoncarbon enumeration policies observation).ValidFor
        policies.noncarbonPolicy (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | cyclic
      (observation : OrganicStereoMonocyclicRingAssemblyIngress.CyclicObservation V
        policies.monocyclicPolicy policies.assemblyPolicy)
      (valid : (decodedCyclic enumeration policies observation).ValidFor
        (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | fused
      (observation : OrganicStereoFusedVonBaeyerIngress.SuppliedFusedVonBaeyerObservation V
        policies.fusedPolicy policies.vonBaeyerPolicy)
      (valid : (decodedFused enumeration policies observation).ValidFor
        (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | cyclophane
      (observation : OrganicStereoCyclophaneAuthorityIngress.NativeCyclophaneAuthorityObservation
        V policies.cyclophanePolicy)
      (valid : (decodedCyclophane enumeration policies observation).ValidFor
        (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | spiro
      (observation : OrganicStereoSpiroAuthorityIngress.NativeSpiroAuthorityObservation
        policies.spiroPolicy V)
      (valid : (decodedSpiro enumeration policies observation).ValidFor
        (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | fullerene (molecule : RawMolecule)
      (conversion_eq : molecule.toSemanticMolecule? =
        some (recoveredSource core enumeration).molecule)
      (observation : OrganicStereoFullereneAuthorityIngress.NativeFullereneAuthorityObservationFamily
        V)
      (valid : (decodedFullerene core enumeration policies observation).ValidFor
        (recoveredSource core enumeration))
      (moleculeBound : (decodedFullerene core enumeration policies observation).MoleculeBoundTo
        (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | fullereneMethodology
      (observation : OrganicStereoFullereneAuthorityIngress.NativeFullereneMethodologyAuthorityObservation)
      (valid : (decodedFullereneMethodology core enumeration observation).ValidFor
        policies.fullerenePolicy (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | relationalFullerene
      (observation : OrganicStereoRelationalFullereneInputEncoding.NativeRelationalFullereneObservation
        V enumeration policies.relationalPolicy)
      (valid : (decodedRelational core enumeration policies observation).ValidFor
        policies.relationalPolicy (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | relationalVariants
      (observation : OrganicStereoRelationalFullereneVariantIngress.NativeRelationalVariantObservation
        V enumeration policies.relationalPolicy)
      (valid : (decodedRelationalVariant core enumeration policies observation).ValidFor
        (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | coupled
      (observation : OrganicStereoCoupledRingChainNativeAxes.SuppliedNativeCoupledRingChainObservation
        V policies.coupledPolicy)
      (valid : (decodedCoupledNativeAxes enumeration policies observation).ValidFor
        policies.coupledPolicy (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration
  | coupledNativeAxes
      (observation : OrganicStereoCoupledRingChainNativeAxes.SuppliedNativeCoupledRingChainObservation
        V policies.coupledPolicy)
      (valid : (decodedCoupledNativeAxes enumeration policies observation).ValidFor
        policies.coupledPolicy (recoveredSource core enumeration)) :
      NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration

/-! ## The concrete encoder -/

/-- Encode one raw entry.  Every boundedness and normalization premise is derived from the entry's
own `ValidFor` predicate and the one common binding; no inverse or agreement premise is assumed.

The P-94 branch is the actual `encodeNativeAuthorityObservation`, which stores only the
source-free native context and the full encoded payload reindexed onto the reconstructed source.
The P-93 families use their actual per-observation relabelling codecs.  The fullerene branch keeps
the raw molecule syntax and its observation-specific conversion equalities; the remaining P-93
payloads never store a source record. -/
def encodeEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies core enumeration →
    NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies core enumeration
  | .legacy entry => .legacy (encodeLegacyEntry core enumeration entry)
  | .p94 source source_graph_eq observation valid =>
      .p94
        (encodeNativeAuthorityObservation core.graph enumeration source source_graph_eq
          (EncodedP94AuthorityObservation.ofAuthorityValid
            (nativeSourceAtomResolver core.graph enumeration source source_graph_eq)
            observation valid)
          (by
            simpa only [EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid] using valid))
  | .acyclic tie graph_eq spatial_eq diagram_eq observation valid =>
      let bound :=
        SourceAcyclicObservation.boundedIn_of_validFor_binding tie.toBinding observation valid
      let sourceWellFormed
          : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed := by
        rw [recoveredAcyclicSource_eq_tie core enumeration tie graph_eq spatial_eq diagram_eq]
        exact tie.spatial_wellFormed
      .acyclic
        (relabelObservation enumeration observation bound)
        sourceWellFormed
        (by
          have hSource
              : (decodedAcyclicTie core enumeration sourceWellFormed).source = tie.source :=
            recoveredAcyclicSource_eq_tie core enumeration tie graph_eq spatial_eq diagram_eq
          rw [hSource]
          exact validFor_of_relabelObservation enumeration tie.source observation bound valid)
  | .general observation judged =>
      .general
        (generalContext core enumeration source_well_formed)
        (encodeGeneralEntry core enumeration source_well_formed observation judged)
        (by
          rw [decode_generalContext_source core enumeration source_well_formed]
          rw [decodeGeneralEntry_encodeGeneralEntry core enumeration source_well_formed
            observation judged]
          exact judged)
        (decode_generalContext_source core enumeration source_well_formed)
  | .noncarbon observation valid =>
      let bound :=
        OrganicStereoNoncarbonTetrahedralIngress.SourceNoncarbonObservation.boundedIn_of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      .noncarbon
        (OrganicStereoNoncarbonTetrahedralIngress.toNativeObservation enumeration
          policies.noncarbonPolicy observation bound)
        (by
          rw [decodedNoncarbon,
            OrganicStereoNoncarbonTetrahedralIngress.ofNativeObservation_toNativeObservation
              enumeration policies.noncarbonPolicy observation bound]
          exact valid)
  | .cyclic observation valid =>
      let bound :=
        OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation.boundedIn_of_validFor_binding
          (commonBinding core enumeration source_well_formed) source_well_formed.1 observation valid
      let normalizationFixed :=
        OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation.normalizationFixed_of_validFor
          (recoveredSource core enumeration) observation valid
      .cyclic
        (OrganicStereoMonocyclicRingAssemblyIngress.relabelCyclicObservation enumeration observation
          bound)
        (by
          rw [decodedCyclic,
            OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation_relabelCyclicObservation
              enumeration observation bound normalizationFixed]
          exact valid)
  | .fused observation valid =>
      let bound :=
        OrganicStereoFusedVonBaeyerIngress.SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      .fused
        (OrganicStereoFusedVonBaeyerIngress.relabelObservation enumeration observation bound)
        (by
          rw [decodedFused,
            OrganicStereoFusedVonBaeyerIngress.unrelabelObservation_relabelObservation
              enumeration observation bound]
          exact valid)
  | .cyclophane observation valid =>
      let bound :=
        OrganicStereoCyclophaneAuthorityIngress.SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      .cyclophane
        (OrganicStereoCyclophaneAuthorityIngress.relabelObservation enumeration observation bound)
        (by
          rw [decodedCyclophane,
            OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation_relabelObservation
              enumeration observation bound]
          exact valid)
  | .spiro observation valid =>
      let bound :=
        OrganicStereoSpiroAuthorityIngress.SourceSpiroAuthorityObservation.boundedIn_of_validFor
          policies.spiroPolicy (commonBinding core enumeration source_well_formed) observation valid
      .spiro
        (OrganicStereoSpiroAuthorityIngress.relabelObservation enumeration observation bound)
        (by
          rw [decodedSpiro,
            OrganicStereoSpiroAuthorityIngress.decodeObservation_relabelObservation
              enumeration observation bound]
          exact valid)
  | .fullerene molecule conversion_eq observation valid moleculeBound =>
      let commonSource :
          OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource V :=
        { binding := commonBinding core enumeration source_well_formed
          molecule := molecule
          conversion_eq := conversion_eq }
      let hContext : fullereneContext core enumeration =
          OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofSource
            commonSource := rfl
      let hDecode :
          (fullereneContext core enumeration).decodeFamily policies.fullerenePolicy
            (commonSource.encodeFamily policies.fullerenePolicy observation) = observation := by
        have hSource :=
          OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.decodeFamily_ofSource
            commonSource policies.fullerenePolicy
            (commonSource.encodeFamily policies.fullerenePolicy observation)
        rw [hContext, hSource]
        exact commonSource.decodeFamily_encodeFamily_of_validFor policies.fullerenePolicy
          observation valid
      .fullerene molecule conversion_eq
        (commonSource.encodeFamily policies.fullerenePolicy observation)
        (by
          rw [decodedFullerene, hDecode]
          exact valid)
        (by
          rw [decodedFullerene, hDecode]
          exact moleculeBound)
  | .fullereneMethodology observation valid =>
      .fullereneMethodology (encodeFullereneMethodology observation)
        (by
          cases observation
          exact valid)
  | .relationalFullerene observation valid =>
      let bound :=
        OrganicStereoRelationalFullereneIngress.relationalObservationBoundedIn_of_validFor
          (OrganicStereoRelationalFullereneIngress.relationalObservationAtomCount_eq
            (commonBinding core enumeration source_well_formed) observation valid)
          valid
      .relationalFullerene
        (OrganicStereoRelationalFullereneInputEncoding.relabelObservation enumeration
          policies.relationalPolicy observation bound)
        (by
          rw [decodedRelational,
            OrganicStereoRelationalFullereneInputEncoding.unrelabelObservation_relabelObservation
              enumeration policies.relationalPolicy observation bound
              (relationalSharedSpatial? core enumeration) valid.structureAgreement.2.1.symm]
          exact valid)
  | .relationalVariants observation valid =>
      let bound :=
        OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation.boundedIn_of_validFor
          (commonBinding core enumeration source_well_formed) observation valid
      .relationalVariants
        (OrganicStereoRelationalFullereneVariantIngress.encodeVariant enumeration observation bound)
        (by
          rw [decodedRelationalVariant,
            OrganicStereoRelationalFullereneVariantIngress.decodeVariant_encodeVariant
              enumeration observation bound (relationalSharedSpatial? core enumeration)
              (OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
                (commonBinding core enumeration source_well_formed) observation valid)]
          exact valid)
  | .coupled observation valid =>
      let bound :=
        OrganicStereoCoupledRingChainNativeAxes.NativeObservationBoundedIn.of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      let normalizationFixed :=
        OrganicStereoCoupledRingChainNativeAxes.nativeObservationNormalizationFixed_of_validFor
          (recoveredSource core enumeration) observation valid
      .coupled
        (OrganicStereoCoupledRingChainNativeAxes.relabelNativeObservation enumeration observation
          bound)
        (by
          rw [decodedCoupledNativeAxes,
            OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation_relabelNativeObservation
              enumeration observation bound normalizationFixed]
          exact valid)
  | .coupledNativeAxes observation valid =>
      let bound :=
        OrganicStereoCoupledRingChainNativeAxes.NativeObservationBoundedIn.of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      let normalizationFixed :=
        OrganicStereoCoupledRingChainNativeAxes.nativeObservationNormalizationFixed_of_validFor
          (recoveredSource core enumeration) observation valid
      .coupledNativeAxes
        (OrganicStereoCoupledRingChainNativeAxes.relabelNativeObservation enumeration observation
          bound)
        (by
          rw [decodedCoupledNativeAxes,
            OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation_relabelNativeObservation
              enumeration observation bound normalizationFixed]
          exact valid)

/-! ## The concrete decoder -/

/-- Decode one native entry.  Every decoder uses only the reconstructed common source and the
stored native payload; no original request, source record or observation is consulted.

The P-94 branch is the actual `decodeNativeAuthorityObservation`: it reconstructs the certified
source from the source-free native context and decodes the full authority payload against that
reconstruction. -/
def decodeEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies core enumeration →
    RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies core enumeration
  | .legacy entry => .legacy (decodeLegacyEntry core enumeration entry)
  | .p94 observation =>
      let recovered :=
        OrganicStereoNativeP94SourceContext.decodeNativeAuthorityObservation
          core.graph enumeration observation
      .p94 recovered.source rfl recovered.observation recovered.valid
  | .acyclic observation source_well_formed valid =>
      .acyclic (decodedAcyclicTie core enumeration source_well_formed)
        rfl rfl rfl
        (unrelabelObservation enumeration observation)
        valid
  | .general _context observation judged source_eq =>
      .general (decodedGeneral enumeration policies observation) (source_eq ▸ judged)
  | .noncarbon observation valid =>
      .noncarbon (decodedNoncarbon enumeration policies observation) valid
  | .cyclic observation valid =>
      .cyclic (decodedCyclic enumeration policies observation) valid
  | .fused observation valid =>
      .fused (decodedFused enumeration policies observation) valid
  | .cyclophane observation valid =>
      .cyclophane (decodedCyclophane enumeration policies observation) valid
  | .spiro observation valid =>
      .spiro (decodedSpiro enumeration policies observation) valid
  | .fullerene molecule conversion_eq observation valid moleculeBound =>
      .fullerene molecule conversion_eq
        (decodedFullerene core enumeration policies observation) valid moleculeBound
  | .fullereneMethodology observation valid =>
      .fullereneMethodology (decodedFullereneMethodology core enumeration observation) valid
  | .relationalFullerene observation valid =>
      .relationalFullerene (decodedRelational core enumeration policies observation) valid
  | .relationalVariants observation valid =>
      .relationalVariants (decodedRelationalVariant core enumeration policies observation) valid
  | .coupled observation valid =>
      .coupled (decodedCoupledNativeAxes enumeration policies observation) valid
  | .coupledNativeAxes observation valid =>
      .coupledNativeAxes (decodedCoupledNativeAxes enumeration policies observation) valid

/-! ## Entry extensionality

Each lemma identifies two raw entries differing only in the payload and in proposition-valued
certificates.  They are the constructor-level steps of the exact entry inverse. -/

theorem p94_extEq
    {firstSource secondSource : CertifiedAuthoritativeChemicalInput}
    {firstGraph : firstSource.input.molecule = core.graph.encode enumeration}
    {secondGraph : secondSource.input.molecule = core.graph.encode enumeration}
    {firstObservation secondObservation : P94AuthorityObservation policies.policy94}
    {firstValid : firstObservation.ValidFor policies.policy94 firstSource.input}
    {secondValid : secondObservation.ValidFor policies.policy94 secondSource.input}
    (source : firstSource = secondSource) (observation : firstObservation = secondObservation) :
    (RawEntry.p94 firstSource firstGraph firstObservation firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.p94 secondSource secondGraph secondObservation secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases source
  cases observation
  rfl

theorem acyclic_extEq {firstTie secondTie : AcyclicSourceTie V enumeration}
    {firstGraph : firstTie.shared.graph = core.graph}
    {firstSpatial : firstTie.shared.spatial? = core.rationalPositions?}
    {firstDiagram : firstTie.shared.diagram? = core.diagram?}
    {secondGraph : secondTie.shared.graph = core.graph}
    {secondSpatial : secondTie.shared.spatial? = core.rationalPositions?}
    {secondDiagram : secondTie.shared.diagram? = core.diagram?}
    {firstObservation secondObservation : SourceAcyclicObservation policies.policy93}
    {firstValid : firstObservation.ValidFor firstTie.source}
    {secondValid : secondObservation.ValidFor secondTie.source}
    (tie : firstTie = secondTie) (observation : firstObservation = secondObservation) :
    (RawEntry.acyclic firstTie firstGraph firstSpatial firstDiagram
        firstObservation firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.acyclic secondTie secondGraph secondSpatial secondDiagram
        secondObservation secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases tie
  cases observation
  rfl

theorem noncarbon_extEq
    {first second : OrganicStereoNoncarbonTetrahedralIngress.SourceNoncarbonObservation
      policies.noncarbonPolicy}
    {firstValid : first.ValidFor policies.noncarbonPolicy (recoveredSource core enumeration)}
    {secondValid : second.ValidFor policies.noncarbonPolicy (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.noncarbon first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.noncarbon second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

theorem cyclic_extEq
    {first second : OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation
      policies.monocyclicPolicy policies.assemblyPolicy}
    {firstValid : first.ValidFor (recoveredSource core enumeration)}
    {secondValid : second.ValidFor (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.cyclic first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.cyclic second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

theorem fused_extEq
    {first second : OrganicStereoFusedVonBaeyerIngress.SourceFusedVonBaeyerObservation
      policies.fusedPolicy policies.vonBaeyerPolicy}
    {firstValid : first.ValidFor (recoveredSource core enumeration)}
    {secondValid : second.ValidFor (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.fused first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.fused second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

theorem cyclophane_extEq
    {first second : OrganicStereoCyclophaneAuthorityIngress.SourceCyclophaneAuthorityObservation
      policies.cyclophanePolicy}
    {firstValid : first.ValidFor (recoveredSource core enumeration)}
    {secondValid : second.ValidFor (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.cyclophane first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.cyclophane second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

theorem spiro_extEq
    {first second : OrganicStereoSpiroAuthorityIngress.SourceSpiroAuthorityObservation
      policies.spiroPolicy}
    {firstValid : first.ValidFor (recoveredSource core enumeration)}
    {secondValid : second.ValidFor (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.spiro first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.spiro second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

theorem fullerene_extEq
    {firstMolecule secondMolecule : RawMolecule}
    {firstConversion : firstMolecule.toSemanticMolecule? =
      some (recoveredSource core enumeration).molecule}
    {secondConversion : secondMolecule.toSemanticMolecule? =
      some (recoveredSource core enumeration).molecule}
    {first second : OrganicStereoFullereneAuthorityIngress.SourceFullereneAuthorityObservation
      policies.fullerenePolicy}
    {firstValid : first.ValidFor (recoveredSource core enumeration)}
    {secondValid : second.ValidFor (recoveredSource core enumeration)}
    {firstBound : first.MoleculeBoundTo (recoveredSource core enumeration)}
    {secondBound : second.MoleculeBoundTo (recoveredSource core enumeration)}
    (molecule : firstMolecule = secondMolecule) (observation : first = second) :
    (RawEntry.fullerene firstMolecule firstConversion first firstValid firstBound :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.fullerene secondMolecule secondConversion second secondValid secondBound :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases molecule
  cases observation
  rfl

theorem relationalFullerene_extEq
    {first second : P93RelationalFullereneAuthorityObservation policies.relationalPolicy}
    {firstValid : first.ValidFor policies.relationalPolicy
      (recoveredSource core enumeration)}
    {secondValid : second.ValidFor policies.relationalPolicy
      (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.relationalFullerene first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.relationalFullerene second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

theorem relationalVariants_extEq
    {first second :
      OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation
        policies.relationalPolicy}
    {firstValid : first.ValidFor (recoveredSource core enumeration)}
    {secondValid : second.ValidFor (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.relationalVariants first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.relationalVariants second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

theorem coupled_extEq
    {first second : P93CoupledRingChainAuthorityObservation policies.coupledPolicy}
    {firstValid : first.ValidFor policies.coupledPolicy (recoveredSource core enumeration)}
    {secondValid : second.ValidFor policies.coupledPolicy (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.coupled first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.coupled second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

theorem coupledNativeAxes_extEq
    {first second : P93CoupledRingChainAuthorityObservation policies.coupledPolicy}
    {firstValid : first.ValidFor policies.coupledPolicy (recoveredSource core enumeration)}
    {secondValid : second.ValidFor policies.coupledPolicy (recoveredSource core enumeration)}
    (observation : first = second) :
    (RawEntry.coupledNativeAxes first firstValid :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.coupledNativeAxes second secondValid :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

/-- Constructor extensionality for the general branch: two general entries with the same actual
five-tag observation are equal, the proposition-valued judgment certificates being identified by
proof irrelevance. -/
theorem general_extEq
    {first second :
      OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation policies.generalPolicy}
    {firstJudged : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.Judged
      policies.generalPolicy (recoveredSource core enumeration) first}
    {secondJudged : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.Judged
      policies.generalPolicy (recoveredSource core enumeration) second}
    (observation : first = second) :
    (RawEntry.general first firstJudged :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (RawEntry.general second secondJudged :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) := by
  cases observation
  rfl

/-! ## The exact entry inverse -/

/-- **Exact entry inverse.**  Every concrete family constructor is dispatched explicitly.  There is
no per-family inverse field, no hypothesis and no catch-all: the legacy payload, the P-94
reconstructed context and full payload, the P-93 tie, and every single-observation family payload
are recovered literally, with the same order and multiplicity position in the enclosing list. -/
theorem decodeEntry_encodeEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed)
    (entry : RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies core enumeration) :
    decodeEntry core enumeration (encodeEntry core enumeration source_well_formed entry) =
      entry := by
  cases entry with
  | legacy entry =>
      simp only [encodeEntry, decodeEntry]
      rw [decodeLegacyEntry_encodeLegacyEntry core enumeration entry]
  | p94 source source_graph_eq observation valid =>
      simp only [encodeEntry, decodeEntry]
      have hvalid :
          (EncodedP94AuthorityObservation.toAuthority
            (nativeSourceAtomResolver core.graph enumeration source source_graph_eq)
            (EncodedP94AuthorityObservation.ofAuthorityValid
              (nativeSourceAtomResolver core.graph enumeration source source_graph_eq)
              observation valid)).ValidFor policies.policy94 source.input := by
        simpa only [EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid] using valid
      refine p94_extEq
        (OrganicStereoNativeP94SourceContext.decodeNativeAuthorityObservation_encodeNativeAuthorityObservation
          core.graph enumeration source source_graph_eq
          (EncodedP94AuthorityObservation.ofAuthorityValid
            (nativeSourceAtomResolver core.graph enumeration source source_graph_eq)
            observation valid) hvalid).1 ?_
      exact (OrganicStereoNativeP94SourceContext.decodeNativeAuthorityObservation_encodeNativeAuthorityObservation
        core.graph enumeration source source_graph_eq
        (EncodedP94AuthorityObservation.ofAuthorityValid
          (nativeSourceAtomResolver core.graph enumeration source source_graph_eq)
          observation valid) hvalid).2.trans
        (EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid
          (nativeSourceAtomResolver core.graph enumeration source source_graph_eq)
          observation valid)
  | acyclic tie graph_eq spatial_eq diagram_eq observation valid =>
      simp only [encodeEntry, decodeEntry]
      let sourceWellFormed
          : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed := by
        rw [recoveredAcyclicSource_eq_tie core enumeration tie graph_eq spatial_eq diagram_eq]
        exact tie.spatial_wellFormed
      refine acyclic_extEq
        (decodedAcyclicTie_eq_tie core enumeration sourceWellFormed tie graph_eq spatial_eq
          diagram_eq) ?_
      exact unrelabelObservation_relabelObservation enumeration observation
        (SourceAcyclicObservation.boundedIn_of_validFor_binding tie.toBinding observation valid)
  | general observation judged =>
      simp only [encodeEntry, decodeEntry]
      exact general_extEq
        (decodeGeneralEntry_encodeGeneralEntry core enumeration source_well_formed
          observation judged)
  | noncarbon observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoNoncarbonTetrahedralIngress.SourceNoncarbonObservation.boundedIn_of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      exact noncarbon_extEq
        (OrganicStereoNoncarbonTetrahedralIngress.ofNativeObservation_toNativeObservation
          enumeration policies.noncarbonPolicy observation bound)
  | cyclic observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation.boundedIn_of_validFor_binding
          (commonBinding core enumeration source_well_formed) source_well_formed.1 observation valid
      let normalizationFixed :=
        OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation.normalizationFixed_of_validFor
          (recoveredSource core enumeration) observation valid
      exact cyclic_extEq
        (OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation_relabelCyclicObservation
          enumeration observation bound normalizationFixed)
  | fused observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoFusedVonBaeyerIngress.SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      exact fused_extEq
        (OrganicStereoFusedVonBaeyerIngress.unrelabelObservation_relabelObservation
          enumeration observation bound)
  | cyclophane observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoCyclophaneAuthorityIngress.SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      exact cyclophane_extEq
        (OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation_relabelObservation
          enumeration observation bound)
  | spiro observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoSpiroAuthorityIngress.SourceSpiroAuthorityObservation.boundedIn_of_validFor
          policies.spiroPolicy (commonBinding core enumeration source_well_formed) observation valid
      exact spiro_extEq
        (OrganicStereoSpiroAuthorityIngress.decodeObservation_relabelObservation
          enumeration observation bound)
  | fullerene molecule conversion_eq observation valid moleculeBound =>
      simp only [encodeEntry, decodeEntry]
      let commonSource :
          OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource V :=
        { binding := commonBinding core enumeration source_well_formed
          molecule := molecule
          conversion_eq := conversion_eq }
      let hContext : fullereneContext core enumeration =
          OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofSource
            commonSource := rfl
      let hDecode :
          (fullereneContext core enumeration).decodeFamily policies.fullerenePolicy
            (commonSource.encodeFamily policies.fullerenePolicy observation) = observation := by
        have hSource :=
          OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.decodeFamily_ofSource
            commonSource policies.fullerenePolicy
            (commonSource.encodeFamily policies.fullerenePolicy observation)
        rw [hContext, hSource]
        exact commonSource.decodeFamily_encodeFamily_of_validFor policies.fullerenePolicy
          observation valid
      exact fullerene_extEq rfl hDecode
  | fullereneMethodology observation valid =>
      simp only [encodeEntry, decodeEntry]
  | relationalFullerene observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoRelationalFullereneIngress.relationalObservationBoundedIn_of_validFor
          (OrganicStereoRelationalFullereneIngress.relationalObservationAtomCount_eq
            (commonBinding core enumeration source_well_formed) observation valid)
          valid
      exact relationalFullerene_extEq
        (OrganicStereoRelationalFullereneInputEncoding.unrelabelObservation_relabelObservation
          enumeration policies.relationalPolicy observation bound
          (relationalSharedSpatial? core enumeration) valid.structureAgreement.2.1.symm)
  | relationalVariants observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation.boundedIn_of_validFor
          (commonBinding core enumeration source_well_formed) observation valid
      exact relationalVariants_extEq
        (OrganicStereoRelationalFullereneVariantIngress.decodeVariant_encodeVariant
          enumeration observation bound (relationalSharedSpatial? core enumeration)
          (OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
            (commonBinding core enumeration source_well_formed) observation valid))
  | coupled observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoCoupledRingChainNativeAxes.NativeObservationBoundedIn.of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      let normalizationFixed :=
        OrganicStereoCoupledRingChainNativeAxes.nativeObservationNormalizationFixed_of_validFor
          (recoveredSource core enumeration) observation valid
      exact coupled_extEq
        (OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation_relabelNativeObservation
          enumeration observation bound normalizationFixed)
  | coupledNativeAxes observation valid =>
      simp only [encodeEntry, decodeEntry]
      let bound :=
        OrganicStereoCoupledRingChainNativeAxes.NativeObservationBoundedIn.of_validFor_binding
          (commonBinding core enumeration source_well_formed) observation valid
      let normalizationFixed :=
        OrganicStereoCoupledRingChainNativeAxes.nativeObservationNormalizationFixed_of_validFor
          (recoveredSource core enumeration) observation valid
      exact coupledNativeAxes_extEq
        (OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation_relabelNativeObservation
          enumeration observation bound normalizationFixed)

/-- Alias with the endpoint name used by the downstream whole assembly. -/
theorem decode_encodeEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed)
    (entry : RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies core enumeration) :
    decodeEntry core enumeration (encodeEntry core enumeration source_well_formed entry) =
      entry :=
  decodeEntry_encodeEntry core enumeration source_well_formed entry

/-- **Decisive general-branch endpoint.**  Encoding one raw P-93.1 general entry and decoding it
returns exactly the same five-tag observation and its actual judgment certificate.  All five
reviewed forms, the generic descriptor type and the ordered assignment data are recovered
literally; no source record and no inverse premise is involved. -/
theorem decodeEntry_encodeEntry_general (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed)
    (observation : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation
      policies.generalPolicy)
    (judged : OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.Judged
      policies.generalPolicy (recoveredSource core enumeration) observation) :
    (decodeEntry core enumeration
        (encodeEntry core enumeration source_well_formed
          (.general observation judged :
            RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
              BaseName Numbering Locant Prefix policies core enumeration)) :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration) =
      (.general observation judged :
        RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policies core enumeration) :=
  decodeEntry_encodeEntry core enumeration source_well_formed
    (.general observation judged :
      RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policies core enumeration)

/-! ## The whole closed-union request and representation -/

/-- The whole closed-union request: one independently supplied core, the complete policy record,
the one explicit enumeration, the one source well-formedness certificate, and the one ordered
heterogeneous entry list of individual observations. -/
structure AllAuthorityRequest (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type) where
  /-- The complete policy record. -/
  policies : AllAuthorityPolicies
  /-- The independently supplied molecular core. -/
  core : OrganicMolecularEvidence V
  /-- The one explicit atom enumeration. -/
  enumeration : V ≃ Fin (Fintype.card V)
  /-- The structural certificate of the reconstructed common source. -/
  source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed
  /-- The one ordered heterogeneous entry list. -/
  entries : List (RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix policies core enumeration)

/-- The assembled representation: the accepted molecular representation, the policy record, the
enumeration, the source certificate of the decoded core, and the one ordered native entry list. -/
structure AllAuthorityRepresentation (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type) where
  /-- The accepted assembled whole state. -/
  assembled : OrganicMolecularRepresentation V
  /-- The complete policy record. -/
  policies : AllAuthorityPolicies
  /-- The one explicit atom enumeration. -/
  enumeration : V ≃ Fin (Fintype.card V)
  /-- The structural certificate of the source reconstructed from the decoded core. -/
  source_well_formed :
    (recoveredSource (decodeEvidence assembled) enumeration).StructurallyWellFormed
  /-- The one ordered heterogeneous native entry list. -/
  entries : List (NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix policies (decodeEvidence assembled) enumeration)

/-- Extensionality of closed-union requests.  The proposition-valued source certificate is
identified by proof irrelevance once the core and enumeration agree. -/
theorem AllAuthorityRequest.extEq
    {first second : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix}
    (policies_eq : first.policies = second.policies)
    (core_eq : first.core = second.core)
    (enumeration_eq : first.enumeration = second.enumeration)
    (entries : HEq first.entries second.entries) : first = second := by
  obtain ⟨firstPolicies, firstCore, firstEnumeration, firstWellFormed, firstEntries⟩ := first
  obtain ⟨secondPolicies, secondCore, secondEnumeration, secondWellFormed,
    secondEntries⟩ := second
  dsimp only at policies_eq core_eq enumeration_eq entries
  cases policies_eq
  cases core_eq
  cases enumeration_eq
  have entriesEq : firstEntries = secondEntries := eq_of_heq entries
  cases entriesEq
  rfl

/-- Assemble the closed union.  The core goes through the accepted mixed assembly; the single
ordered entry list is transported along the proved core inverse and each individual observation is
encoded by its concrete family codec. -/
def assembleAll
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    AllAuthorityRepresentation (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix where
  assembled := assembleCore request.core request.enumeration
  policies := request.policies
  enumeration := request.enumeration
  source_well_formed :=
    (decodeCore_eq_assembleCore request.core request.enumeration).symm ▸
      request.source_well_formed
  entries :=
    (decodeCore_eq_assembleCore request.core request.enumeration).symm ▸
      request.entries.map (encodeEntry request.core request.enumeration
        request.source_well_formed)

/-- Decode the closed union.  The core is read from the accepted assembly and every entry through
its concrete decoder.  The accepted evidence decoder is proof-relevant, so this whole-request
decoder is `noncomputable`; every family entry decoder itself is executable. -/
noncomputable def decodeAll
    (representation : AllAuthorityRepresentation (V := V) LigandId LigandKind FragmentId
      FragmentKind State Framework BaseName Numbering Locant Prefix) :
    AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix where
  policies := representation.policies
  core := decodeEvidence representation.assembled
  enumeration := representation.enumeration
  source_well_formed := representation.source_well_formed
  entries := representation.entries.map
    (decodeEntry (decodeEvidence representation.assembled) representation.enumeration)

/-! ## Dependent ordered-list transport -/

/-- Mapping the ordered entry list along a core equality and then decoding it returns the original
list heterogeneously.  The encoder depends on the request's source certificate, so this variant
carries that certificate explicitly. -/
theorem map_decodeEntry_encodeEntry_eqRec
    {first second : OrganicMolecularEvidence V}
    (equal : first = second)
    (source_well_formed : (recoveredSource second enumeration).StructurallyWellFormed)
    (entries : List (RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies second enumeration)) :
    HEq (((equal.symm ▸ entries.map
        (encodeEntry second enumeration source_well_formed)).map
      (decodeEntry first enumeration))) entries := by
  cases equal
  apply heq_of_eq
  rw [List.map_map]
  induction entries with
  | nil => rfl
  | cons head tail tailInvariant =>
      rw [List.map_cons]
      exact (List.cons.injEq _ _ _ _).mpr
        ⟨decodeEntry_encodeEntry first enumeration source_well_formed head, tailInvariant⟩

/-! ## Exact whole-request inverse, injectivity and set-image recovery -/

/-- **Exact whole-request inverse.**  Decoding the assembled representation returns the whole
request literally: the complete policy record, the independent core, the explicit enumeration, the
source certificate, and the one ordered heterogeneous entry list with every family payload,
interleaving, repetition and cross-family correlation retained. -/
theorem decodeAll_assembleAll
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    decodeAll (assembleAll request) = request := by
  apply AllAuthorityRequest.extEq
    (first := decodeAll (assembleAll request)) (second := request)
  · rfl
  · exact decodeCore_eq_assembleCore request.core request.enumeration
  · rfl
  · exact map_decodeEntry_encodeEntry_eqRec
      (equal := decodeCore_eq_assembleCore request.core request.enumeration)
      (source_well_formed := request.source_well_formed)
      (entries := request.entries)

/-- The assembly is injective: equal assembled representations have equal requests. -/
theorem assembleAll_injective :
    ∀ first second : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
        State Framework BaseName Numbering Locant Prefix,
      assembleAll first = assembleAll second → first = second := by
  intro first second equal
  have applied := congrArg decodeAll equal
  rwa [decodeAll_assembleAll first, decodeAll_assembleAll second] at applied

/-- **Arbitrary correlated set-image recovery.**  For every set of closed-union requests, the
requests whose assembled representation decodes into that set are exactly the original set. -/
theorem decodeAll_image_assembleAll_image
    (requests : Set (AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix)) :
    decodeAll '' (assembleAll '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨representation, ⟨original, member, rfl⟩, decoded⟩
    rw [← decoded, decodeAll_assembleAll]
    exact member
  · intro member
    exact ⟨assembleAll request, ⟨request, member, rfl⟩, decodeAll_assembleAll request⟩

/-! ## Explicit endpoints for the downstream whole assembly -/

/-- The assembled representation's entry list is the literal transport of the encoded ordered
list. -/
theorem assembleAll_entries
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleAll request).entries =
      (decodeCore_eq_assembleCore request.core request.enumeration).symm ▸
        request.entries.map (encodeEntry request.core request.enumeration
          request.source_well_formed) := rfl

/-- The decoded ordered entry list is the original ordered entry list, transported along the
proved core inverse.  The list type is indexed by the core, so the endpoint is a heterogeneous
equality; it is exactly the dependent transport used by the whole-request inverse.  Order,
multiplicity, interleaving and cross-family correlation are preserved. -/
theorem decodeAll_entries_assembleAll
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    HEq (decodeAll (assembleAll request)).entries request.entries :=
  map_decodeEntry_encodeEntry_eqRec
    (equal := decodeCore_eq_assembleCore request.core request.enumeration)
    (source_well_formed := request.source_well_formed)
    (entries := request.entries)

/-- The decoded ordered entry list, read back at the supplied core, is the supplied list.  This is
the transported (homogeneous) form of `decodeAll_entries_assembleAll`; the transport is along the
actual core inverse `decodeEvidence (assembleCore c e) = c`. -/
theorem decodeAll_entries_assembleAll_eq
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeCore_eq_assembleCore request.core request.enumeration) ▸
        (decodeAll (assembleAll request)).entries =
      request.entries :=
  eq_of_heq (eqRec_heq_iff.mpr (decodeAll_entries_assembleAll request))

/-- The decoded core is the supplied core. -/
theorem decodeAll_core_assembleAll
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeAll (assembleAll request)).core = request.core := by
  rw [decodeAll_assembleAll]

/-- The represented policy record is the supplied policy record. -/
theorem decodeAll_policies_assembleAll
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeAll (assembleAll request)).policies = request.policies := by
  rw [decodeAll_assembleAll]

/-- The reconstructed source graph is the core graph encoded at the common enumeration. -/
theorem assembleAll_source_molecule
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (recoveredSource (decodeEvidence (assembleAll request).assembled)
        request.enumeration).molecule =
      request.core.graph.encode request.enumeration := by
  rw [show decodeEvidence (assembleAll request).assembled = request.core from
    decodeCore_eq_assembleCore request.core request.enumeration]
  rfl

/-- The reconstructed source spatial channel is exactly the core's rational-coordinate channel
materialised at the common enumeration. -/
theorem assembleAll_source_spatial
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (recoveredSource (decodeEvidence (assembleAll request).assembled)
        request.enumeration).spatial? =
      OrganicFiniteSource.encodeSpatial? request.enumeration request.core.rationalPositions? := by
  rw [show decodeEvidence (assembleAll request).assembled = request.core from
    decodeCore_eq_assembleCore request.core request.enumeration]
  rfl

/-- The reconstructed source drawing channel is exactly the core's drawing channel encoded at the
common enumeration. -/
theorem assembleAll_source_diagram
    (request : AllAuthorityRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (recoveredSource (decodeEvidence (assembleAll request).assembled)
        request.enumeration).diagram? =
      request.core.diagram?.map
        (OrganicDiagramSource.encodeDiagram request.enumeration) := by
  rw [show decodeEvidence (assembleAll request).assembled = request.core from
    decodeCore_eq_assembleCore request.core request.enumeration]
  rfl

/-! ## The source bindings exposed to the downstream whole assembly

The downstream consumer can transport the ordered list to the decoded core because every family
row is stated at the same reconstructed source.  The three projection equalities below are the
exact bindings it needs; none of them is assumed by a codec. -/

/-- The common binding's graph equality, read as the source/molecule tie. -/
theorem commonBinding_graph_eq
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    (commonBinding core enumeration source_well_formed).shared.graph.encode enumeration =
      (recoveredSource core enumeration).molecule :=
  (commonBinding core enumeration source_well_formed).graph_eq

/-- The common binding's spatial equality: the reconstructed source's spatial channel is the core's
rational-coordinate channel materialised at the common enumeration. -/
theorem commonBinding_spatial_eq
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    (recoveredSource core enumeration).spatial? =
      OrganicFiniteSource.encodeSpatial? enumeration core.rationalPositions? :=
  ((commonBinding core enumeration source_well_formed).spatial_eq).symm

/-- The common binding's drawing equality. -/
theorem commonBinding_diagram_eq
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredSource core enumeration).StructurallyWellFormed) :
    (recoveredSource core enumeration).diagram? =
      core.diagram?.map (OrganicDiagramSource.encodeDiagram enumeration) :=
  ((commonBinding core enumeration source_well_formed).diagram_eq).symm

end OrganicStereoAllAuthorityEntries

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeLegacyEntry_encodeLegacyEntry
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeFullereneMethodology_encodeFullereneMethodology
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeFullereneMethodology_eq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeEntry_encodeEntry
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decode_encodeEntry
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.map_decodeEntry_encodeEntry_eqRec
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeAll_assembleAll
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.assembleAll_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeAll_image_assembleAll_image
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeAll_entries_assembleAll
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeAll_entries_assembleAll_eq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeAll_core_assembleAll
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeAll_policies_assembleAll
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.assembleAll_source_molecule
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.assembleAll_source_spatial
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.assembleAll_source_diagram
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.commonBinding_graph_eq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeGeneralEntry_encodeGeneralEntry
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.general_extEq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decode_generalContext
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decode_generalContext_source
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries.decodeEntry_encodeEntry_general
