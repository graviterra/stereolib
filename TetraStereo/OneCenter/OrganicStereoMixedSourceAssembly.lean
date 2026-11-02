

































































import TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly
import TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily
import TetraStereo.OneCenter.OrganicStereoDonorGroupingIngress
import TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress
import TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress
import TetraStereo.OneCenter.OrganicStereoJointCoreEncoding

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter
namespace OrganicStereoMixedSourceAssembly

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoElectronicDescriptionIngress
open OrganicStereoOrderedObservationFamily
open DonorGroupingIngress
open DonorOccurrenceEncoding
open OrganicStereoSharedPhysicalCaseIngress
open BlueBookP94.CoordinateTorsion

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]
variable {LigandId LigandKind FragmentId FragmentKind : Type}
variable [DecidableEq LigandId] [DecidableEq LigandKind]
variable [DecidableEq FragmentId] [DecidableEq FragmentKind]
variable {State Framework : Type}
variable {BaseName Numbering Locant Prefix : Type}

/-! ## Unambiguous access to the native molecular assembly

`OrganicStereoSharedPhysicalCaseIngress` imports `OrganicStereoSimultaneousCaseAssembly`, which has
a parent-namespace `assemble` for whole case requests.  The molecular assembly lives in its own
dedicated namespace now, so every use below goes through these two small definitions rather than an
ambiguous unqualified name. -/

/-- The actual upstream molecular-evidence assembly. -/
def assembleEvidence (request : OrganicMolecularEvidence V) : OrganicMolecularRepresentation V :=
  OrganicStereoMolecularEvidenceAssembly.assemble request

/-- The actual upstream molecular-evidence decoding. -/
def decodeEvidence (representation : OrganicMolecularRepresentation V) : OrganicMolecularEvidence V :=
  OrganicStereoMolecularEvidenceAssembly.decode representation

/-- The actual upstream exact inverse of molecular assembly. -/
theorem decodeEvidence_assembleEvidence (request : OrganicMolecularEvidence V) :
    decodeEvidence (assembleEvidence request) = request :=
  OrganicStereoMolecularEvidenceAssembly.decode_assemble request











/-- The actual electronic channel attached to the common core.  It is the existing ingress
channel built from the core's supplied site source and complete slot assignment, or `none` when the
core has no inventory.  Nothing is derived from geometry and no slot is invented. -/
def electronicChannelOption (core : OrganicMolecularEvidence V) :
    Option (ElectronicChannel V) :=
  match h : core.electronic? with
  | none => none
  | some evidence =>
      some (ingressChannel
        (evidence.toSiteSource core.graph
          (fun owner => core.electronic_unpaired evidence h owner))
        evidence.assignment)

/-- The attached inventory is tied to the graph exactly as the independent evidence was: the
channel's own counts give the same unpaired-electron agreement. -/
theorem electronicChannelOption_unpaired (core : OrganicMolecularEvidence V) :
    ∀ channel, electronicChannelOption core = some channel → ∀ owner,
      (channel.counts.counts owner).unpairedElectronPositions =
        (core.graph.atomData owner).unpairedElectrons := by
  intro channel present owner
  unfold electronicChannelOption at present
  split at present
  · cases present
  · rename_i evidence h
    have channelEq :
        ingressChannel
          (evidence.toSiteSource core.graph
            (fun owner => core.electronic_unpaired evidence h owner))
          evidence.assignment = channel := Option.some_inj.mp present
    subst channel
    simp [ingressChannel_counts, IndependentElectronicEvidence.toSiteSource]
    exact core.electronic_unpaired evidence h owner

/-- The existing `baseState` of the independent core. -/
def coreBaseState (request : OrganicMolecularEvidence V) : WholeState V (Fin 0) (Fin 0) :=
  OrganicStereoMolecularEvidenceAssembly.baseState request

/-- The common base state: the existing `baseState` of the core, with the core's actual electronic
inventory attached.  Its graph is the core graph definitionally and its conformation is the core
conformation definitionally. -/
def commonBaseState (core : OrganicMolecularEvidence V) :
    WholeState V (Fin 0) (Fin 0) :=
  { coreBaseState core with
    electronic? := electronicChannelOption core
    electronic_unpaired := electronicChannelOption_unpaired core }

/-- The one common physical context of the mixed request.  It is literally
`SharedPhysicalContext.ofState (commonBaseState core) enumeration`, so the shared physical case
ingress and the mixed assembly use the same context constructor as the upstream ingress. -/
def sharedContext (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : SharedPhysicalContext V :=
  SharedPhysicalContext.ofState (commonBaseState core) enumeration

@[simp] theorem sharedContext_graph (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (sharedContext core enumeration).graph = core.graph := rfl

@[simp] theorem sharedContext_electronic? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (sharedContext core enumeration).electronic? = electronicChannelOption core := rfl

@[simp] theorem sharedContext_conformation (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (sharedContext core enumeration).conformation = core.conformation := rfl

@[simp] theorem sharedContext_enumeration (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (sharedContext core enumeration).enumeration = enumeration := rfl

/-! ## The one ordered heterogeneous entry list -/

/-- One independently supplied native source entry, over the common core and enumeration.

The list of these entries is the single ordered mixed collection: it retains the cross-family
order, every duplicate occurrence, and the exact payload of each family.  Every graph/geometry tie
is stated as an equality or as the actual upstream validity predicate; no entry stores a
pre-assembled state or the mixed request itself. -/
inductive MixedEntry {V : Type} [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Type where
  /-- An actual supplied ordered conformer/observation family.  The certified source is retained
  as the family's genuine index and is tied to the common encoded graph by equality.  The family's
  optional payload is stored literally, including present-empty versus absent channels and the
  source-indexed spatial list inside coordinate observations. -/
  | observation (source : CertifiedAuthoritativeChemicalInput)
      (family : OrderedObservationFamily source V State Framework)
      (source_graph_eq : source.input.molecule = core.graph.encode enumeration) :
      MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration
  /-- A `V`-native donor channel together with its proof-only validity against the common graph.
  The interaction count is the common graph's interaction count and every occurrence is checked
  against the actual interaction at its own occurrence index. -/
  | donor
      (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
        core.graph.interactions.length)
      (validity : NativeChannelValidity core.graph enumeration
        (rfl : core.graph.interactions.length = core.graph.interactions.length) channel) :
      MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration
  /-- A supplied citation satellite tied to the common graph.  The annotated name, ordered located
  assignments and optional external unit identity are typed metadata, not atom indices. -/
  | citation
      (satellite : OrganicStereoSuppliedCitationIngress.SuppliedCitationSatellite V
        BaseName Numbering Locant Prefix)
      (graph_eq : satellite.graph = core.graph) :
      MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration
  /-- A supplied P-93 physical frame satellite with exact ties of its shared graph, coordinate
  channel and drawing channel to the common core.  Polyhedral coordinate fields are reconstructed
  from the shared coordinates and the ordered ligands, not stored as metadata here. -/
  | physicalFrame
      (satellite : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite V)
      (graph_eq : satellite.graph = core.graph)
      (spatial_eq : satellite.spatial? = core.rationalPositions?)
      (diagram_eq : satellite.diagram? = core.diagram?) :
      MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration
  /-- The proof-carrying shared physical case collection, indexed by the common
  `SharedPhysicalContext.ofState` context.  Certificate data (including the optional coplanarity
  presence) is retained exactly. -/
  | sharedCases
      (encoded : EncodedCollection (sharedContext core enumeration)) :
      MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix core enumeration

namespace MixedEntry

variable {core : OrganicMolecularEvidence V}
variable {enumeration : V ≃ Fin (Fintype.card V)}

/-- The external tag of an entry.  It records the cross-family order without changing the payload. -/
inductive Tag where
  | observation
  | donor
  | citation
  | physicalFrame
  | sharedCases
  deriving DecidableEq, Repr

/-- The tag of one mixed entry. -/
def tag : MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix core enumeration → Tag
  | .observation _ _ _ => .observation
  | .donor _ _ => .donor
  | .citation _ _ => .citation
  | .physicalFrame _ _ _ _ => .physicalFrame
  | .sharedCases _ => .sharedCases

/-- The actual common-source binding predicate of one entry.  Each clause is the exact upstream
tie carried by the entry: a source graph equality, an actual `NativeChannelValidity`, or a satellite
graph/geometry equality.  Shared case entries are already indexed by the common `ofState` context,
so no weaker metadata claim is introduced for them. -/
def Bound : MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix core enumeration → Prop
  | .observation source _ source_graph_eq => source.input.molecule = core.graph.encode enumeration
  | .donor channel _ => NativeChannelValidity core.graph enumeration
      (rfl : core.graph.interactions.length = core.graph.interactions.length) channel
  | .citation satellite _ => satellite.graph = core.graph
  | .physicalFrame satellite _ _ _ =>
      satellite.graph = core.graph ∧
      satellite.spatial? = core.rationalPositions? ∧
      satellite.diagram? = core.diagram?
  | .sharedCases _ => True

/-- Every entry carries its actual common-source binding proof. -/
theorem bound (entry : MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix core enumeration) : entry.Bound := by
  cases entry with
  | observation source family sourceGraphEq => exact sourceGraphEq
  | donor channel validity => exact validity
  | citation satellite graphEq => exact graphEq
  | physicalFrame satellite graphEq spatialEq diagramEq => exact ⟨graphEq, spatialEq, diagramEq⟩
  | sharedCases encoded => trivial

/-- The donor channel of a donor entry, when present. -/
def donorChannel? : MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix core enumeration →
    Option (VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      core.graph.interactions.length)
  | .donor channel _ => some channel
  | _ => none

/-- The citation satellite of a citation entry, when present. -/
def citationSatellite? : MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix core enumeration →
    Option (OrganicStereoSuppliedCitationIngress.SuppliedCitationSatellite V
      BaseName Numbering Locant Prefix)
  | .citation satellite _ => some satellite
  | _ => none

/-- The physical frame satellite of a physical frame entry, when present. -/
def physicalFrameSatellite? : MixedEntry LigandId LigandKind FragmentId FragmentKind
    State Framework BaseName Numbering Locant Prefix core enumeration →
    Option (OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite V)
  | .physicalFrame satellite _ _ _ => some satellite
  | _ => none

/-- The shared case encoding of a shared case entry, when present. -/
def sharedCasesEncoded? : MixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix core enumeration →
    Option (EncodedCollection (sharedContext core enumeration))
  | .sharedCases encoded => some encoded
  | _ => none

end MixedEntry

/-! ## Resolving source-indexed observation coordinates through the common enumeration

An observation family retains the *source-indexed* coordinate lists exactly as supplied.  Its
source is tied to the common encoded graph by `source_graph_eq`, and the common request supplies
one atom enumeration.  These two facts induce the genuine equivalence
`SourceAtomIndex source ≃ V`; coordinates are then interpreted through that equivalence and never
through an unrelated enumeration.  Conformers are independent physical data and are not required to
coincide with the core geometry. -/

/-- The atom-count identification induced by the observation's exact source/graph tie. -/
theorem observationSourceAtomCount_eq (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (sourceGraphEq : source.input.molecule = core.graph.encode enumeration) :
    source.input.molecule.atomCount =
      (core.graph.certifiedEncoding enumeration).input.molecule.atomCount := by
  rw [sourceGraphEq]
  rfl

/-- The genuine equivalence between the observation's source atom indices and the common atom
labels: the upstream certified-encoding equivalence composed with the exact source/graph
identification.  This is derived, not chosen independently. -/
def observationSourceAtomEquiv (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (sourceGraphEq : source.input.molecule = core.graph.encode enumeration) :
    V ≃ SourceAtomIndex source :=
  (JointCoreEncoding.sourceAtomEquiv core.graph enumeration).trans
    (finCongr (observationSourceAtomCount_eq core enumeration source sourceGraphEq).symm)

/-- The resolver used for source-indexed observation payloads. -/
def observationSourceAtomResolver (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (sourceGraphEq : source.input.molecule = core.graph.encode enumeration) :
    SourceAtomIndex source ≃ V :=
  (observationSourceAtomEquiv core enumeration source sourceGraphEq).symm

@[simp] theorem observationSourceAtomEquiv_apply (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (sourceGraphEq : source.input.molecule = core.graph.encode enumeration) (atom : V) :
    observationSourceAtomEquiv core enumeration source sourceGraphEq atom =
      finCongr (observationSourceAtomCount_eq core enumeration source sourceGraphEq).symm
        (JointCoreEncoding.sourceAtomEquiv core.graph enumeration atom) := rfl

/-- Exact coordinate evaluation at an encoded atom through the derived resolver.  The result is the
source-indexed positional lookup at the resolver's inverse; a missing source position yields `none`
and no coordinate is fabricated. -/
def coordinatePointAt {source : CertifiedAuthoritativeChemicalInput}
    (resolver : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V) (atom : V) :
    Option CartesianPoint3 :=
  EncodedCoordinateObservation.pointAt resolver observation atom

/-- Exact source-indexed coordinate evaluation: evaluating at the resolver image of a source atom
returns the supplied source point at that atom.  This is the pointwise bridge that keeps the
source-indexed spatial list under its own source indexing. -/
@[simp] theorem coordinatePointAt_source {source : CertifiedAuthoritativeChemicalInput}
    (resolver : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V)
    (atom : SourceAtomIndex source) :
    coordinatePointAt resolver observation (resolver atom) =
      observation.spatial.positions[atom.val]? := by
  simp [coordinatePointAt, EncodedCoordinateObservation.pointAt]

/-- Exact virtual-point evaluation through the retained encoded ledger. -/
def coordinateVirtualPointAt (observation : EncodedCoordinateObservation Framework V)
    (participant : EncodedVirtualTorsionParticipant V) : Option CartesianPoint3 :=
  EncodedCoordinateObservation.virtualPointAt observation participant

/-- Exact source-level virtual-point evaluation: encoding the source participant through the
derived resolver and looking it up in the retained ledger returns that ledger's point.  Present
versus absent status is preserved because the lookup is `Option`-valued. -/
@[simp] theorem coordinateVirtualPointAt_source
    {source : CertifiedAuthoritativeChemicalInput}
    (resolver : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V)
    (participant : VirtualTorsionParticipant)
    (bound : VirtualParticipantBounded participant source.input.molecule.atomCount) :
    coordinateVirtualPointAt observation
        (encodeVirtualParticipant resolver participant bound) =
      EncodedVirtualTorsionPoint.lookup observation.virtualPoints
        (encodeVirtualParticipant resolver participant bound) := rfl

/-- The coordinate channel exposed by a family, retaining both presence layers: `none` means the
observation payload is absent, `some none` means a supplied payload whose coordinate channel is
absent, and `some (some data)` is a supplied coordinate channel. -/
def observationCoordinateInOut?
    {source : CertifiedAuthoritativeChemicalInput}
    (family : OrderedObservationFamily source V State Framework) :
    Option (Option (CoordinateInOutData Framework V)) :=
  family.observation?.map (fun payload => payload.coordinateInOut?)

@[simp] theorem observationCoordinateInOut?_eq
    {source : CertifiedAuthoritativeChemicalInput}
    (family : OrderedObservationFamily source V State Framework) :
    observationCoordinateInOut? family =
      family.observation?.map (fun payload => payload.coordinateInOut?) := rfl

/-- Payload presence is preserved exactly by the exposed coordinate channel. -/
theorem observationCoordinateInOut?_isSome_iff
    {source : CertifiedAuthoritativeChemicalInput}
    (family : OrderedObservationFamily source V State Framework) :
    (observationCoordinateInOut? family).isSome = family.observation?.isSome := by
  rw [observationCoordinateInOut?_eq]
  cases family.observation? <;> rfl

/-! ## The mixed request and its representation -/

/-- The whole mixed request: one independently supplied core, one explicit enumeration, and one
ordered heterogeneous list of native source entries over that core. -/
structure MixedSourceRequest (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type) where
  /-- The independently supplied common molecular evidence; it is not a pre-assembled state. -/
  core : OrganicMolecularEvidence V
  /-- The one explicit atom enumeration used for every encoded/source interface. -/
  enumeration : V ≃ Fin (Fintype.card V)
  /-- The one ordered mixed entry list. -/
  entries : List (MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
    State Framework BaseName Numbering Locant Prefix core enumeration)

/-- The assembled mixed representation: the actual `assemble` output for the core, the explicit
enumeration used by every encoded interface, and the one ordered entry list re-indexed at the
decoded core.  No copy of the request itself, and no pre-assembled core, is stored; the enumeration
is retained as the explicit external indexing choice. -/
structure MixedSourceRepresentation (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type) where
  /-- The actual upstream molecular-evidence assembly of the core. -/
  assembled : OrganicMolecularRepresentation V
  /-- The one explicit atom enumeration used by every encoded/source interface. -/
  enumeration : V ≃ Fin (Fintype.card V)
  /-- The one ordered mixed entry list over the decoded core. -/
  entries : List (MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
    State Framework BaseName Numbering Locant Prefix (decodeEvidence assembled) enumeration)

/-- Entry transport along an equality of cores.  This is the only place where the dependent entry
type is transported; it is an ordinary `Eq.rec` and carries every payload field, including all
proof fields. -/
theorem eqRec_entries_heq {core decoded : OrganicMolecularEvidence V}
    (h : decoded = core)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entries : List (MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix core enumeration)) :
    HEq (h.symm ▸ entries) entries := by
  cases h
  rfl

/-- Assemble the mixed request.  The core is assembled by the actual upstream `assemble`; the
entry list is transported along the proved upstream inverse `decode (assemble core) = core`. -/
def assembleMixed (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind
    State Framework BaseName Numbering Locant Prefix) :
    MixedSourceRepresentation V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix where
  assembled := assembleEvidence request.core
  enumeration := request.enumeration
  entries := (decodeEvidence_assembleEvidence request.core).symm ▸ request.entries

/-- Decode the mixed representation.  The core is read back from the actual assembled
representation; the entries are read from the one ordered list at the retained enumeration. -/
def decodeMixed
    (representation : MixedSourceRepresentation V LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix where
  core := decodeEvidence representation.assembled
  enumeration := representation.enumeration
  entries := representation.entries

/-- The assembled component is exactly the actual upstream assembly. -/
@[simp] theorem assembleMixed_assembled
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) :
    (assembleMixed request).assembled = assembleEvidence request.core := rfl

/-- Extensionality of mixed requests.  The entry fields are compared heterogeneously because they
are indexed by the (equal) core and enumeration. -/
theorem MixedSourceRequest.extEq
    {first second : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix}
    (core : first.core = second.core)
    (enumeration : first.enumeration = second.enumeration)
    (entries : HEq first.entries second.entries) :
    first = second := by
  obtain ⟨firstCore, firstEnumeration, firstEntries⟩ := first
  obtain ⟨secondCore, secondEnumeration, secondEntries⟩ := second
  cases core
  cases enumeration
  have entriesEq : firstEntries = secondEntries := eq_of_heq entries
  rw [entriesEq]

/-! ## Exact inverse of the mixed assembly -/

/-- Decoding the mixed assembly returns the whole mixed request literally: the independent core,
the explicit enumeration, and the one ordered entry list including every payload field. -/
theorem decodeMixed_assembleMixed
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) :
    decodeMixed (assembleMixed request) = request := by
  apply MixedSourceRequest.extEq
  · exact decodeEvidence_assembleEvidence request.core
  · rfl
  · exact eqRec_entries_heq (decodeEvidence_assembleEvidence request.core)
      request.enumeration request.entries

/-- The decoded core is exactly the independently supplied core. -/
@[simp] theorem decodeMixed_core
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) :
    (decodeMixed (assembleMixed request)).core = request.core :=
  decodeEvidence_assembleEvidence request.core

/-- The decoded enumeration is exactly the supplied enumeration. -/
@[simp] theorem decodeMixed_enumeration
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) :
    (decodeMixed (assembleMixed request)).enumeration = request.enumeration := rfl

/-- The decoded common graph is exactly the independently supplied graph. -/
@[simp] theorem decodeMixed_core_graph
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) :
    (decodeMixed (assembleMixed request)).core.graph = request.core.graph :=
  congrArg (fun evidence => evidence.graph) (decodeEvidence_assembleEvidence request.core)

/-- Exact whole-list preservation of the mixed entries, heterogeneously at the decoded and the
supplied core: order and multiplicity are retained literally. -/
theorem decodeMixed_entries_heq
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) :
    HEq (decodeMixed (assembleMixed request)).entries request.entries :=
  eqRec_entries_heq (decodeEvidence_assembleEvidence request.core)
    request.enumeration request.entries

/-- Heterogeneous indexing of a list transported along an equality of its type index. -/
theorem eqRec_list_getElem?_heq {P : OrganicMolecularEvidence V → Type}
    {core decoded : OrganicMolecularEvidence V} (h : decoded = core)
    (entries : List (P core)) (index : Nat) :
    HEq ((h.symm ▸ entries)[index]?) (entries[index]?) := by
  cases h
  rfl

/-- Length preservation of a list transported along an equality of its type index. -/
theorem eqRec_list_length {P : OrganicMolecularEvidence V → Type}
    {core decoded : OrganicMolecularEvidence V} (h : decoded = core)
    (entries : List (P core)) :
    (h.symm ▸ entries).length = entries.length := by
  cases h
  rfl

/-- Per-occurrence exact preservation: at every position the decoded entry is the supplied entry,
with all payload fields and all validity proofs.  This is the occurrence-level form that detects
duplicate ordering and cross-family coexistence.  The entry index type is indexed by the decoded
core and the fixed common enumeration, so the transport is along the actual core equality. -/
theorem decodeMixed_getElem?_heq
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) (index : Nat) :
    HEq ((decodeMixed (assembleMixed request)).entries[index]?)
        (request.entries[index]?) :=
  eqRec_list_getElem?_heq
    (P := fun core => MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix core request.enumeration)
    (decodeEvidence_assembleEvidence request.core) request.entries index

/-- The number of mixed occurrences is preserved exactly. -/
theorem decodeMixed_entries_length
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) :
    (decodeMixed (assembleMixed request)).entries.length = request.entries.length :=
  eqRec_list_length
    (P := fun core => MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix core request.enumeration)
    (decodeEvidence_assembleEvidence request.core) request.entries

/-- Every decoded entry is bound to the decoded common core by its actual source/geometry tie.
This is the mixed-assembly common-source validity recovery statement: an observation entry exposes
its source graph equality, a donor entry exposes its actual `NativeChannelValidity`, and the
citation and P-93 entries expose their graph (and, for P-93, geometry) equalities. -/
theorem decodeMixed_entries_bound
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) :
    ∀ entry ∈ (decodeMixed (assembleMixed request)).entries, MixedEntry.Bound entry :=
  fun entry _ => MixedEntry.bound entry

/-! ### Occurrence-level validity projections

These theorems expose the stored actual validity at the decoded common graph.  The donor case is
the substantive one: every occurrence of the decoded channel is checked against the actual
interaction at its own occurrence index in the decoded common graph. -/

/-- The actual donor validity recovered at the decoded common graph. -/
theorem decodeMixed_donor_occurrence_facts
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) {index : Nat}
    {channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      (decodeEvidence (assembleEvidence request.core)).graph.interactions.length}
    {validity : NativeChannelValidity (decodeEvidence (assembleEvidence request.core)).graph
      request.enumeration
      (rfl : (decodeEvidence (assembleEvidence request.core)).graph.interactions.length =
        (decodeEvidence (assembleEvidence request.core)).graph.interactions.length) channel}
    (found : (decodeMixed (assembleMixed request)).entries[index]? =
      some (MixedEntry.donor channel validity)) :
    ∀ occurrence, occurrence ∈ channel.occurrences →
      NativeOccurrenceFacts (decodeEvidence (assembleEvidence request.core)).graph
        request.enumeration
        (rfl : (decodeEvidence (assembleEvidence request.core)).graph.interactions.length =
          (decodeEvidence (assembleEvidence request.core)).graph.interactions.length) occurrence :=
  fun occurrence member => validity.facts occurrence member

/-- The source graph tie recovered for an observation occurrence. -/
theorem decodeMixed_observation_source_graph
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) {index : Nat}
    {source : CertifiedAuthoritativeChemicalInput}
    {family : OrderedObservationFamily source V State Framework}
    {sourceGraphEq : source.input.molecule =
      (decodeEvidence (assembleEvidence request.core)).graph.encode request.enumeration}
    (found : (decodeMixed (assembleMixed request)).entries[index]? =
      some (MixedEntry.observation source family sourceGraphEq)) :
    source.input.molecule =
      (decodeEvidence (assembleEvidence request.core)).graph.encode request.enumeration :=
  sourceGraphEq

/-- The graph tie recovered for a citation occurrence. -/
theorem decodeMixed_citation_graph
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) {index : Nat}
    {satellite : OrganicStereoSuppliedCitationIngress.SuppliedCitationSatellite V
      BaseName Numbering Locant Prefix}
    {graphEq : satellite.graph = (decodeEvidence (assembleEvidence request.core)).graph}
    (found : (decodeMixed (assembleMixed request)).entries[index]? =
      some (MixedEntry.citation satellite graphEq)) :
    satellite.graph = (decodeEvidence (assembleEvidence request.core)).graph :=
  graphEq

/-- The exact graph, coordinate and drawing ties recovered for a P-93 frame occurrence. -/
theorem decodeMixed_physicalFrame_ties
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix) {index : Nat}
    {satellite : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite V}
    {graphEq : satellite.graph = (decodeEvidence (assembleEvidence request.core)).graph}
    {spatialEq : satellite.spatial? =
      (decodeEvidence (assembleEvidence request.core)).rationalPositions?}
    {diagramEq : satellite.diagram? = (decodeEvidence (assembleEvidence request.core)).diagram?}
    (found : (decodeMixed (assembleMixed request)).entries[index]? =
      some (MixedEntry.physicalFrame satellite graphEq spatialEq diagramEq)) :
    satellite.graph = (decodeEvidence (assembleEvidence request.core)).graph ∧
      satellite.spatial? = (decodeEvidence (assembleEvidence request.core)).rationalPositions? ∧
      satellite.diagram? = (decodeEvidence (assembleEvidence request.core)).diagram? :=
  ⟨graphEq, spatialEq, diagramEq⟩

/-! ## Concrete payload adapters and their exact recovery -/

/-- One observation entry from an actually supplied certified source and ordered family. -/
def observationEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (family : OrderedObservationFamily source V State Framework)
    (sourceGraphEq : source.input.molecule = core.graph.encode enumeration) :
    MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration :=
  .observation source family sourceGraphEq

/-- One donor entry from the actual enriched ledger over the common certified encoding.  The
channel is the upstream `channelOfLedger` and the validity is the upstream
`nativeValidityOfLedger`; no validity is assumed. -/
def donorEntryOfLedger (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (core.graph.certifiedEncoding enumeration).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration :=
  .donor (channelOfLedger core.graph enumeration ledger)
    (nativeValidityOfLedger core.graph enumeration ledger)

/-- Exact ledger recovery through the donor entry adapter: the decoded ledger is the supplied
one, including every incidence, occurrence index and metadata field. -/
@[simp] theorem donorEntryOfLedger_recovered (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (core.graph.certifiedEncoding enumeration).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    decodeLedger core.graph enumeration
      (rfl : core.graph.interactions.length = core.graph.interactions.length)
      (channelOfLedger core.graph enumeration ledger)
      (nativeValidityOfLedger core.graph enumeration ledger) = ledger :=
  decodeLedger_channelOfLedger core.graph enumeration ledger

/-- One citation entry from the raw supplied source, through the concrete upstream `adapt`. -/
def citationEntryOfRaw (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (raw : OrganicStereoSuppliedCitationIngress.RawSuppliedCitationSource V
      BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
        (Fintype.card V) assignment.unit) :
    MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration :=
  .citation (OrganicStereoSuppliedCitationIngress.adapt core.graph enumeration raw bounded) rfl

/-- Exact raw-source recovery for the citation adapter: annotated name, ordered located
assignments and optional external unit identity are all returned literally. -/
@[simp] theorem citationEntryOfRaw_recovered (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (raw : OrganicStereoSuppliedCitationIngress.RawSuppliedCitationSource V
      BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
        (Fintype.card V) assignment.unit) :
    OrganicStereoSuppliedCitationIngress.suppliedSource enumeration
      (OrganicStereoSuppliedCitationIngress.adapt core.graph enumeration raw bounded) = raw :=
  OrganicStereoSuppliedCitationIngress.suppliedSource_adapt core.graph enumeration raw bounded

/-- One P-93 physical frame entry from a concrete satellite and its exact ties to the common core.
The satellite is produced upstream by `PhysicalFrameSatellite.adapt`; its polyhedral payload does
not store coordinates. -/
def physicalFrameEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite V)
    (graphEq : satellite.graph = core.graph)
    (spatialEq : satellite.spatial? = core.rationalPositions?)
    (diagramEq : satellite.diagram? = core.diagram?) :
    MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration :=
  .physicalFrame satellite graphEq spatialEq diagramEq

/-- One P-93 physical frame entry constructed from a raw physical-frame source through the actual
upstream `adapt`.  The raw source uses the *same* enumeration as the mixed request and its shared
finite source is tied to the common core graph, shared coordinates and drawing channel by actual
equalities.  The constructed entry stores the adapted satellite; the raw request itself is not
stored. -/
def physicalFrameEntryOfRaw (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (raw : OrganicStereoP93PhysicalFrameIngress.RawPhysicalFrameSource V)
    (enumeration_eq : raw.binding.enumeration = enumeration)
    (graph_eq : raw.binding.shared.graph = core.graph)
    (spatial_eq : raw.binding.shared.spatial? = core.rationalPositions?)
    (diagram_eq : raw.binding.shared.diagram? = core.diagram?) :
    MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration :=
  .physicalFrame (OrganicStereoP93PhysicalFrameIngress.adapt raw)
    (by
      rw [OrganicStereoP93PhysicalFrameIngress.adapt_graph]
      exact graph_eq)
    (by
      rw [OrganicStereoP93PhysicalFrameIngress.adapt_spatial?]
      exact spatial_eq)
    (by
      rw [OrganicStereoP93PhysicalFrameIngress.adapt_diagram?]
      exact diagram_eq)

/-- Extracting the satellite stored by `physicalFrameEntryOfRaw` returns exactly the adapted
satellite, not a reconstruction from metadata. -/
@[simp] theorem physicalFrameEntryOfRaw_satellite (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (raw : OrganicStereoP93PhysicalFrameIngress.RawPhysicalFrameSource V)
    (enumeration_eq : raw.binding.enumeration = enumeration)
    (graph_eq : raw.binding.shared.graph = core.graph)
    (spatial_eq : raw.binding.shared.spatial? = core.rationalPositions?)
    (diagram_eq : raw.binding.shared.diagram? = core.diagram?) :
    (physicalFrameEntryOfRaw (LigandId := LigandId) (LigandKind := LigandKind)
      (FragmentId := FragmentId) (FragmentKind := FragmentKind) (State := State)
      (Framework := Framework) (BaseName := BaseName) (Numbering := Numbering)
      (Locant := Locant) (Prefix := Prefix)
      core enumeration raw enumeration_eq graph_eq spatial_eq
      diagram_eq).physicalFrameSatellite? =
      some (OrganicStereoP93PhysicalFrameIngress.adapt raw) := rfl

/-- **Native P-93 ingress connection.**  The entry built from the raw source, extracted and then
decoded at the *common* enumeration, recovers the exact authoritative input and the exact ordered
carrier frame list.  The enumeration equality is the actual supplied tie; only the external
enumeration label is rewritten, never the physical payload. -/
theorem physicalFrameEntryOfRaw_recovered (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (raw : OrganicStereoP93PhysicalFrameIngress.RawPhysicalFrameSource V)
    (enumeration_eq : raw.binding.enumeration = enumeration)
    (graph_eq : raw.binding.shared.graph = core.graph)
    (spatial_eq : raw.binding.shared.spatial? = core.rationalPositions?)
    (diagram_eq : raw.binding.shared.diagram? = core.diagram?) :
    (physicalFrameEntryOfRaw (LigandId := LigandId) (LigandKind := LigandKind)
      (FragmentId := FragmentId) (FragmentKind := FragmentKind) (State := State)
      (Framework := Framework) (BaseName := BaseName) (Numbering := Numbering)
      (Locant := Locant) (Prefix := Prefix)
      core enumeration raw enumeration_eq graph_eq spatial_eq
      diagram_eq).physicalFrameSatellite?.map
        (OrganicStereoP93PhysicalFrameIngress.suppliedSource enumeration) =
      some ({ source := raw.binding.source, frames := raw.frames } :
        OrganicStereoP93PhysicalFrameIngress.RecoveredPhysicalFrameSource) := by
  rw [physicalFrameEntryOfRaw_satellite]
  change some
      (OrganicStereoP93PhysicalFrameIngress.suppliedSource enumeration
        (OrganicStereoP93PhysicalFrameIngress.adapt raw)) =
    some ({ source := raw.binding.source, frames := raw.frames } :
      OrganicStereoP93PhysicalFrameIngress.RecoveredPhysicalFrameSource)
  rw [← enumeration_eq]
  exact congrArg some (OrganicStereoP93PhysicalFrameIngress.suppliedSource_adapt raw)

/-- Exact recovery of a P-93 raw source: the authoritative input and the ordered source frame
list are returned literally. -/
@[simp] theorem physicalFrame_suppliedSource_adapt
    (raw : OrganicStereoP93PhysicalFrameIngress.RawPhysicalFrameSource V) :
    OrganicStereoP93PhysicalFrameIngress.suppliedSource raw.binding.enumeration
      (OrganicStereoP93PhysicalFrameIngress.adapt raw) =
      { source := raw.binding.source, frames := raw.frames } :=
  OrganicStereoP93PhysicalFrameIngress.suppliedSource_adapt raw

/-- The exact decoded source preserves the supplied `ValidFor` predicate by equality: every carrier
frame is valid for the source recovered from the adapted satellite, because the recovered source is
literally the binding's source. -/
theorem physicalFrame_recovered_valid
    (raw : OrganicStereoP93PhysicalFrameIngress.RawPhysicalFrameSource V)
    {frame : OrganicStereoP93PhysicalFrameIngress.SourcePhysicalFrame}
    (member : frame ∈ raw.frames) :
    frame.ValidFor
      (OrganicStereoP93PhysicalFrameIngress.suppliedSource raw.binding.enumeration
        (OrganicStereoP93PhysicalFrameIngress.adapt raw)).source := by
  rw [OrganicStereoP93PhysicalFrameIngress.suppliedSource_adapt]
  exact raw.valid frame member

/-- One shared physical case entry from an arbitrary ordered collection of cases indexed by the
common `ofState` context. -/
def sharedCasesEntryOfCases (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (cases : List (PhysicalCase (sharedContext core enumeration))) :
    MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix core enumeration :=
  .sharedCases (EncodedCollection.encode cases)

/-- Exact ordered case collection recovery, including duplicates, certificate data and the
present-empty coplanarity option. -/
@[simp] theorem sharedCasesEntryOfCases_recovered (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (cases : List (PhysicalCase (sharedContext core enumeration))) :
    (EncodedCollection.encode cases).decode = cases :=
  EncodedCollection.decode_encode cases

/-- The shared case channels attached to the common base state are exactly the encoded collection's
bundle.  The attachment uses the actual `assembleCases`/`attachCases` API with the case context
literally equal to `SharedPhysicalContext.ofState (commonBaseState core) enumeration`. -/
theorem sharedCases_attach_extract (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (cases : List (PhysicalCase (sharedContext core enumeration))) :
    CaseBundle.extractCases
        (assembleCases (commonBaseState core) cases) =
      (EncodedCollection.encode cases).bundle :=
  (EncodedCollection.encode_bundle_attachCases (commonBaseState core) cases).symm

/-- The arbitrary correlated-set recovery of the shared case ingress itself: the collections whose
encoding lies in the image of a set are exactly that set.  This is the set-level form that keeps
every coexistence and correlation pattern of the shared cases. -/
theorem sharedCases_encode_set_image (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (collections : Set (List (PhysicalCase (sharedContext core enumeration)))) :
    EncodedCollection.encode ⁻¹' (EncodedCollection.encode '' collections) = collections :=
  EncodedCollection.set_image_inverse collections

/-! ## Arbitrary correlated sets of whole mixed requests -/

/-- **Set-image recovery.**  For every set of mixed requests, the requests whose assembled mixed
representation decodes into that set are exactly the original set.  Nothing about the correlation
between the core, the entry order and the individual payloads is lost. -/
theorem decodeMixed_image_assembleMixed_image
    (requests : Set (MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix)) :
    decodeMixed '' (assembleMixed '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨representation, ⟨original, member, rfl⟩, decoded⟩
    rw [← decoded, decodeMixed_assembleMixed]
    exact member
  · intro member
    exact ⟨assembleMixed request, ⟨request, member, rfl⟩, decodeMixed_assembleMixed request⟩







/-- Ordered observation families: the cardinality-based `Fin` encoding and its exact inverse. -/
@[simp] theorem observationFamily_fin_transport
    {source : CertifiedAuthoritativeChemicalInput}
    (enumeration : V ≃ Fin (Fintype.card V))
    (family : OrderedObservationFamily source V State Framework) :
    OrderedObservationFamily.relabel enumeration.symm
        (OrderedObservationFamily.finEncodeCard enumeration family) = family :=
  OrderedObservationFamily.finEncodeCard_symm enumeration family

/-- Donor channels: relabelling along the canonical `Fin` enumeration and back returns the
channel exactly, including every occurrence, index and metadata field. -/
@[simp] theorem donorChannel_fin_transport
    (enumeration : V ≃ Fin (Fintype.card V)) {n : Nat}
    (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind n) :
    relabelChannel enumeration.symm (relabelChannel enumeration channel) = channel :=
  relabelChannel_symm enumeration channel

/-- Actual donor validity is independent of the enumeration codec.  It is *not* claimed invariant
under an arbitrary atom permutation: validity is stated against the actual common graph and its
interaction participants. -/
theorem nativeChannelValidity_enumeration_irrel
    {graph : FiniteAtomInteractionHypergraph V} {n : Nat}
    {countEq : n = graph.interactions.length}
    {channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind n}
    (first second : V ≃ Fin (Fintype.card V))
    (validity : NativeChannelValidity graph first countEq channel) :
    NativeChannelValidity graph second countEq channel := by
  refine ⟨fun occurrence member => ?_⟩
  have facts := validity.facts occurrence member
  exact ⟨facts.kind_coordinate, facts.participants_length, facts.support,
    facts.donor_ne_centre⟩

/-- Citation sources: re-index the satellite from one explicit enumeration to another by recovering
the exact raw source with the first codec and re-adapting it with the second. -/
def citationReindex
    (first second : V ≃ Fin (Fintype.card V))
    (satellite : OrganicStereoSuppliedCitationIngress.SuppliedCitationSatellite V
      BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈
        (OrganicStereoSuppliedCitationIngress.suppliedSource first satellite).assignments,
      OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
        (Fintype.card V) assignment.unit) :
    OrganicStereoSuppliedCitationIngress.SuppliedCitationSatellite V
      BaseName Numbering Locant Prefix :=
  OrganicStereoSuppliedCitationIngress.adapt satellite.graph second
    (OrganicStereoSuppliedCitationIngress.suppliedSource first satellite) bounded

/-- The citation re-indexing recovers exactly the raw source decoded through the first
enumeration: the annotated name, ordered assignments and external identity are unchanged. -/
@[simp] theorem citationReindex_recovered
    (first second : V ≃ Fin (Fintype.card V))
    (satellite : OrganicStereoSuppliedCitationIngress.SuppliedCitationSatellite V
      BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈
        (OrganicStereoSuppliedCitationIngress.suppliedSource first satellite).assignments,
      OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
        (Fintype.card V) assignment.unit) :
    OrganicStereoSuppliedCitationIngress.suppliedSource second
        (citationReindex first second satellite bounded) =
      OrganicStereoSuppliedCitationIngress.suppliedSource first satellite :=
  OrganicStereoSuppliedCitationIngress.suppliedSource_adapt satellite.graph second
    (OrganicStereoSuppliedCitationIngress.suppliedSource first satellite) bounded

/-- P-93 payloads: the native payload is recovered exactly from its decoded source frame and the
shared coordinate configuration.  For a polyhedral payload this is the true reconstruction of
`spatial`, `centerPoint` and `positionPoints` from the shared coordinates and the ordered ligands,
not a metadata copy. -/
@[simp] theorem physicalFrame_payload_transport
    {n : Nat} (enumeration : V ≃ Fin n) (spatial : SpatialConfiguration)
    (frame : OrganicStereoP93PhysicalFrameIngress.PhysicalFrame V) :
    OrganicStereoP93PhysicalFrameIngress.relabelFrame enumeration
        (OrganicStereoP93PhysicalFrameIngress.decodeFrame enumeration spatial frame)
        (OrganicStereoP93PhysicalFrameIngress.decodeFrame_bounded enumeration spatial frame) =
      frame :=
  OrganicStereoP93PhysicalFrameIngress.relabelFrame_decodeFrame enumeration spatial frame

end

end OrganicStereoMixedSourceAssembly
end TetraStereo.OneCenter
