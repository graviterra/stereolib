import TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly
import TetraStereo.OneCenter.OrganicStereoP94AuthorityObservationIngress
import TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false















































namespace TetraStereo.OneCenter
namespace OrganicStereoAuthorityMixedSourceAssembly

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMixedSourceAssembly
open OrganicStereoP94AuthorityObservationIngress
open OrganicStereoP93AcyclicIngress
open BlueBookP93.Acyclic

universe u

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]
variable {LigandId LigandKind FragmentId FragmentKind : Type}
variable [DecidableEq LigandId] [DecidableEq LigandKind]
variable [DecidableEq FragmentId] [DecidableEq FragmentKind]
variable {State Framework : Type}
variable {BaseName Numbering Locant Prefix : Type}
variable {policy94 : P94AuthorityPolicy}
variable {policy93 : P93AcyclicAuthorityPolicy}
variable {enumeration : V ≃ Fin (Fintype.card V)}
variable {core : OrganicMolecularEvidence V}

/-! ## The accepted core assembly

The core is assembled by the accepted mixed assembly with an empty entry list.  Its inverse is the
accepted molecular-evidence inverse, unfolded through the actual `decodeMixed_assembleMixed`
theorem.  This keeps the authority module on the accepted path rather than introducing a second
core assembler. -/

/-- The actual accepted molecular assembly of the common core. -/
def assembleCore (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : OrganicMolecularRepresentation V :=
  (assembleMixed
    ({ core := core, enumeration := enumeration, entries := [] } :
      MixedSourceRequest V PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit)).assembled

/-- The recovered core is exactly the supplied core, obtained from the actual
`decodeMixed_assembleMixed` inverse. -/
theorem decodeCore_eq_assembleCore (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    decodeEvidence (assembleCore core enumeration) = core := by
  unfold assembleCore
  exact congrArg (fun request => request.core)
    (decodeMixed_assembleMixed
      ({ core := core, enumeration := enumeration, entries := [] } :
        MixedSourceRequest V PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit))

/-! ## The common finite source recovered from the core

The P-93 binding ties a shared finite source to the authoritative input.  When decoding a P-93
entry from the assembled core, the recovered source is rebuilt from the core's graph, rational
coordinates and drawing channel under the common enumeration.  The two supporting equalities say
that, when the shared source is the core's finite source, the recovered input is the source and
the finite source is the shared source. -/

/-- The finite source carried by the common core: its graph, optional exact rational coordinates
and optional drawing channel.  No external data is added. -/
def coreFiniteSource (core : OrganicMolecularEvidence V) : OrganicFiniteSource V where
  graph := core.graph
  spatial? := core.rationalPositions?
  diagram? := core.diagram?

/-- The authoritative input encoded from the core's finite source at the common enumeration. -/
def recoveredAcyclicSource (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : AuthoritativeChemicalInput :=
  (coreFiniteSource core).encode enumeration

/-- A P-93 source tie at the common enumeration: the genuine source, the shared finite source,
and the actual graph/coordinate/drawing equalities to the common core.  The well-formedness of the
source's spatial channel is retained because it is not derivable from acyclic `ValidFor`. -/
structure AcyclicSourceTie (V : Type) [DecidableEq V] [Fintype V]
    (enumeration : V ≃ Fin (Fintype.card V)) where
  source : AuthoritativeChemicalInput
  shared : OrganicFiniteSource V
  graph_eq : shared.graph.encode enumeration = source.molecule
  spatial_eq : OrganicFiniteSource.encodeSpatial? enumeration shared.spatial? = source.spatial?
  diagram_eq : shared.diagram?.map (OrganicDiagramSource.encodeDiagram enumeration) =
    source.diagram?
  spatial_wellFormed : source.SpatialIndicesWellFormed

namespace AcyclicSourceTie

variable {V : Type} [DecidableEq V] [Fintype V] {enumeration : V ≃ Fin (Fintype.card V)}

/-- The existing molecule-codec binding represented by the tie. -/
def toBinding (tie : AcyclicSourceTie V enumeration) : AcyclicSourceBinding V where
  source := tie.source
  shared := tie.shared
  enumeration := enumeration
  graph_eq := tie.graph_eq
  spatial_eq := tie.spatial_eq
  diagram_eq := tie.diagram_eq
  spatial_wellFormed := tie.spatial_wellFormed

/-- Extensionality of source ties.  The remaining fields are proposition-valued and are identified
by proof irrelevance. -/
theorem extEq {first second : AcyclicSourceTie V enumeration}
    (source : first.source = second.source)
    (shared : first.shared = second.shared) : first = second := by
  obtain ⟨firstSource, firstShared, firstGraph, firstSpatial, firstDiagram,
    firstWellFormed⟩ := first
  obtain ⟨secondSource, secondShared, secondGraph, secondSpatial, secondDiagram,
    secondWellFormed⟩ := second
  dsimp only at source shared
  cases source
  cases shared
  rfl

end AcyclicSourceTie

/-- The recovered input is the tie's source whenever the tie's shared channels equal the core's
channels.  All three comparisons are actual equalities, not cardinalities. -/
theorem recoveredAcyclicSource_eq_tie (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (tie : AcyclicSourceTie V enumeration)
    (graph_eq : tie.shared.graph = core.graph)
    (spatial_eq : tie.shared.spatial? = core.rationalPositions?)
    (diagram_eq : tie.shared.diagram? = core.diagram?) :
    recoveredAcyclicSource core enumeration = tie.source := by
  apply authoritativeInput_ext
  · change core.graph.encode enumeration = tie.source.molecule
    rw [← graph_eq]
    exact tie.graph_eq
  · change OrganicFiniteSource.encodeSpatial? enumeration core.rationalPositions? =
      tie.source.spatial?
    rw [← spatial_eq]
    exact tie.spatial_eq
  · change core.diagram?.map (OrganicDiagramSource.encodeDiagram enumeration) =
      tie.source.diagram?
    rw [← diagram_eq]
    exact tie.diagram_eq

/-- The core's finite source is the tie's shared source whenever the shared channels equal the
core's channels. -/
theorem coreFiniteSource_eq_tie_shared (core : OrganicMolecularEvidence V)
    (tie : AcyclicSourceTie V enumeration)
    (graph_eq : tie.shared.graph = core.graph)
    (spatial_eq : tie.shared.spatial? = core.rationalPositions?)
    (diagram_eq : tie.shared.diagram? = core.diagram?) :
    coreFiniteSource core = tie.shared := by
  change (⟨core.graph, core.rationalPositions?, core.diagram?⟩ : OrganicFiniteSource V) =
    tie.shared
  rw [show tie.shared =
    ⟨tie.shared.graph, tie.shared.spatial?, tie.shared.diagram?⟩ from rfl]
  rw [graph_eq, spatial_eq, diagram_eq]

/-- The source tie recovered from the core and a proof that the recovered source's spatial channel
is well formed.  The ties are the definitional equalities of the core encoder. -/
def decodedAcyclicTie (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed) :
    AcyclicSourceTie V enumeration where
  source := recoveredAcyclicSource core enumeration
  shared := coreFiniteSource core
  graph_eq := rfl
  spatial_eq := rfl
  diagram_eq := rfl
  spatial_wellFormed := source_well_formed

/-- The reconstructed tie is the supplied tie whenever the supplied shared channels equal the
core's channels.  This is the tie-level step of the P-93 entry inverse. -/
theorem decodedAcyclicTie_eq_tie (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (source_well_formed : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed)
    (tie : AcyclicSourceTie V enumeration)
    (graph_eq : tie.shared.graph = core.graph)
    (spatial_eq : tie.shared.spatial? = core.rationalPositions?)
    (diagram_eq : tie.shared.diagram? = core.diagram?) :
    decodedAcyclicTie core enumeration source_well_formed = tie :=
  AcyclicSourceTie.extEq
    (recoveredAcyclicSource_eq_tie core enumeration tie graph_eq spatial_eq diagram_eq)
    (coreFiniteSource_eq_tie_shared core tie graph_eq spatial_eq diagram_eq)

/-! ## The one ordered tagged extension entry list -/

/-- One raw entry over the common core and enumeration: the accepted legacy mixed entry, a raw
P-94 authority observation, or a raw P-93 acyclic observation.  The constructors are tags in a
single list; there is no separate collection per family, so interleaving and multiplicity are
literal. -/
inductive AuthorityMixedEntry {V : Type} [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type)
    (policy94 : P94AuthorityPolicy) (policy93 : P93AcyclicAuthorityPolicy)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Type where
  /-- An accepted legacy mixed entry, unchanged. -/
  | legacy (entry : MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix core enumeration) :
      AuthorityMixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policy94 policy93 core enumeration
  /-- A raw P-94 authority observation, its certified source, the genuine source-to-common-graph
  equality, and its actual authority `ValidFor` predicate. -/
  | observationP94 (source : CertifiedAuthoritativeChemicalInput)
      (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
      (observation : P94AuthorityObservation policy94)
      (valid : observation.ValidFor policy94 source.input) :
      AuthorityMixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policy94 policy93 core enumeration
  /-- A raw P-93 acyclic observation, its genuine source tie at the common enumeration, the three
  actual equalities to the common core, and its actual `ValidFor` predicate. -/
  | acyclicP93 (tie : AcyclicSourceTie V enumeration)
      (graph_eq : tie.shared.graph = core.graph)
      (spatial_eq : tie.shared.spatial? = core.rationalPositions?)
      (diagram_eq : tie.shared.diagram? = core.diagram?)
      (observation : SourceAcyclicObservation policy93)
      (valid : observation.ValidFor tie.source) :
      AuthorityMixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policy94 policy93 core enumeration

/-- One concrete encoded entry over the common core and enumeration.  The P-94 record is the exact
output of `EncodedP94AuthorityObservation.ofAuthorityValid`; the P-93 record is the exact output of
`relabelObservation` together with the recovered source well-formedness.  The validity proofs are
stated at the decoded records, so decoding never needs to consult the original request. -/
inductive EncodedAuthorityMixedEntry {V : Type} [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type)
    (policy94 : P94AuthorityPolicy) (policy93 : P93AcyclicAuthorityPolicy)
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Type where
  | legacy (entry : MixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix core enumeration) :
      EncodedAuthorityMixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policy94 policy93 core enumeration
  | observationP94 (source : CertifiedAuthoritativeChemicalInput)
      (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
      (encoded : EncodedP94AuthorityObservation policy94 source V)
      (valid : (encoded.toAuthority
        (observationSourceAtomResolver core enumeration source source_graph_eq)).ValidFor
          policy94 source.input) :
      EncodedAuthorityMixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policy94 policy93 core enumeration
  | acyclicP93 (observation : AcyclicObservation V policy93)
      (source_well_formed : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed)
      (valid : (unrelabelObservation enumeration observation).ValidFor
        (decodedAcyclicTie core enumeration source_well_formed).source) :
      EncodedAuthorityMixedEntry LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policy94 policy93 core enumeration

/-! ## Concrete decoders and encoders -/

/-- Decode a raw P-94 record through the genuine source-atom resolver derived from the exact
source/graph equality.  No atom-count-only identification is used. -/
def decodedP94Authority (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {source : CertifiedAuthoritativeChemicalInput}
    (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
    (encoded : EncodedP94AuthorityObservation policy94 source V) :
    P94AuthorityObservation policy94 :=
  encoded.toAuthority (observationSourceAtomResolver core enumeration source source_graph_eq)

@[simp] theorem decodedP94Authority_molecule (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {source : CertifiedAuthoritativeChemicalInput}
    (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
    (encoded : EncodedP94AuthorityObservation policy94 source V) :
    (decodedP94Authority core enumeration source_graph_eq encoded).molecule = encoded.molecule :=
  rfl

@[simp] theorem decodedP94Authority_claim (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {source : CertifiedAuthoritativeChemicalInput}
    (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
    (encoded : EncodedP94AuthorityObservation policy94 source V) :
    (decodedP94Authority core enumeration source_graph_eq encoded).claim = encoded.claim :=
  rfl

/-- The optional ordered coordinate certificate survives decoding with exactly the same presence. -/
theorem decodedP94Authority_certificate_isSome (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {source : CertifiedAuthoritativeChemicalInput}
    (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
    (encoded : EncodedP94AuthorityObservation policy94 source V) :
    (decodedP94Authority core enumeration source_graph_eq encoded).inOutCertificate?.isSome =
      encoded.inOutCertificate?.isSome := by
  simp [decodedP94Authority]

/-- The decoded raw molecule is semantically the source molecule.  This is the stored conversion
equality of the encoded record, read back at the decoded molecule. -/
theorem decodedP94Authority_converted (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {source : CertifiedAuthoritativeChemicalInput}
    (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
    (encoded : EncodedP94AuthorityObservation policy94 source V) :
    (decodedP94Authority core enumeration source_graph_eq encoded).molecule.toSemanticMolecule? =
      some source.input.molecule := by
  simpa [decodedP94Authority] using encoded.converted

/-- Encode one raw entry.  The P-94 branch is the actual `ofAuthorityValid`; the P-93 branch is the
actual `relabelObservation`, with the physical-unit bound derived from the actual `ValidFor` and
the genuine source binding. -/
def encodeAuthorityEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration
  | .legacy entry => .legacy entry
  | .observationP94 source source_graph_eq observation valid =>
      .observationP94 source source_graph_eq
        (EncodedP94AuthorityObservation.ofAuthorityValid
          (observationSourceAtomResolver core enumeration source source_graph_eq)
          observation valid)
        (by
          simpa only [EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid] using valid)
  | .acyclicP93 tie graph_eq spatial_eq diagram_eq observation valid =>
      let bound :=
        SourceAcyclicObservation.boundedIn_of_validFor_binding tie.toBinding observation valid
      let sourceWellFormed
          : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed := by
        rw [recoveredAcyclicSource_eq_tie core enumeration tie graph_eq spatial_eq diagram_eq]
        exact tie.spatial_wellFormed
      .acyclicP93
        (relabelObservation enumeration observation bound)
        sourceWellFormed
        (by
          have hSource
              : (decodedAcyclicTie core enumeration sourceWellFormed).source = tie.source :=
            recoveredAcyclicSource_eq_tie core enumeration tie graph_eq spatial_eq diagram_eq
          rw [hSource]
          exact validFor_of_relabelObservation enumeration tie.source observation bound valid)

/-- Decode one concrete encoded entry.  P-94 uses the actual `toAuthority` through the derived
source-atom resolver; P-93 uses the actual `unrelabelObservation` and reconstructs the source tie
from the core and the stored well-formedness proof. -/
def decodeAuthorityEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration
  | .legacy entry => .legacy entry
  | .observationP94 source source_graph_eq encoded valid =>
      .observationP94 source source_graph_eq
        (encoded.toAuthority
          (observationSourceAtomResolver core enumeration source source_graph_eq))
        valid
  | .acyclicP93 observation source_well_formed valid =>
      .acyclicP93 (decodedAcyclicTie core enumeration source_well_formed)
        rfl rfl rfl
        (unrelabelObservation enumeration observation)
        valid

/-! ### Entry extensionality and the exact entry inverse -/

/-- Extensionality of a raw P-94 entry across its decoded observation.  The validity proof is
proposition-valued and is transported by the equality. -/
theorem observationP94_extEq {source : CertifiedAuthoritativeChemicalInput}
    {source_graph_eq : source.input.molecule = core.graph.encode enumeration}
    {first second : P94AuthorityObservation policy94}
    {firstValid : first.ValidFor policy94 source.input}
    {secondValid : second.ValidFor policy94 source.input}
    (observation : first = second) :
    (AuthorityMixedEntry.observationP94 source source_graph_eq first firstValid :
      AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policy94 policy93 core enumeration) =
      (AuthorityMixedEntry.observationP94 source source_graph_eq second secondValid :
        AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policy94 policy93 core enumeration) := by
  cases observation
  rfl

/-- Extensionality of a raw P-93 entry across its source tie and decoded observation.  All
remaining fields are proposition-valued and are identified by proof irrelevance. -/
theorem acyclicP93_extEq {firstTie secondTie : AcyclicSourceTie V enumeration}
    {firstGraph : firstTie.shared.graph = core.graph}
    {firstSpatial : firstTie.shared.spatial? = core.rationalPositions?}
    {firstDiagram : firstTie.shared.diagram? = core.diagram?}
    {secondGraph : secondTie.shared.graph = core.graph}
    {secondSpatial : secondTie.shared.spatial? = core.rationalPositions?}
    {secondDiagram : secondTie.shared.diagram? = core.diagram?}
    {firstObservation secondObservation : SourceAcyclicObservation policy93}
    {firstValid : firstObservation.ValidFor firstTie.source}
    {secondValid : secondObservation.ValidFor secondTie.source}
    (tie : firstTie = secondTie) (observation : firstObservation = secondObservation) :
    (AuthorityMixedEntry.acyclicP93 firstTie firstGraph firstSpatial firstDiagram
        firstObservation firstValid :
      AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
        BaseName Numbering Locant Prefix policy94 policy93 core enumeration) =
      (AuthorityMixedEntry.acyclicP93 secondTie secondGraph secondSpatial secondDiagram
        secondObservation secondValid :
        AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
          BaseName Numbering Locant Prefix policy94 policy93 core enumeration) := by
  cases tie
  cases observation
  rfl

/-- Extensionality of an encoded P-94 entry across its encoded observation.  The decoded validity
proof is transported by the equality. -/
theorem encodedObservationP94_extEq {source : CertifiedAuthoritativeChemicalInput}
    {source_graph_eq : source.input.molecule = core.graph.encode enumeration}
    {first second : EncodedP94AuthorityObservation policy94 source V}
    {firstValid : (first.toAuthority
      (observationSourceAtomResolver core enumeration source source_graph_eq)).ValidFor
        policy94 source.input}
    {secondValid : (second.toAuthority
      (observationSourceAtomResolver core enumeration source source_graph_eq)).ValidFor
        policy94 source.input}
    (encoded : first = second) :
    (EncodedAuthorityMixedEntry.observationP94 source source_graph_eq first firstValid :
      EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
        Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) =
      (EncodedAuthorityMixedEntry.observationP94 source source_graph_eq second secondValid :
        EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
          Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) := by
  cases encoded
  rfl

/-- Extensionality of an encoded P-93 entry across its native observation. -/
theorem encodedAcyclicP93_extEq
    {firstObservation secondObservation : AcyclicObservation V policy93}
    {firstWellFormed : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed}
    {secondWellFormed : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed}
    {firstValid : (unrelabelObservation enumeration firstObservation).ValidFor
      (decodedAcyclicTie core enumeration firstWellFormed).source}
    {secondValid : (unrelabelObservation enumeration secondObservation).ValidFor
      (decodedAcyclicTie core enumeration secondWellFormed).source}
    (observation : firstObservation = secondObservation) :
    (EncodedAuthorityMixedEntry.acyclicP93 firstObservation firstWellFormed firstValid :
      EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
        Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) =
      (EncodedAuthorityMixedEntry.acyclicP93 secondObservation secondWellFormed secondValid :
        EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
          Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) := by
  cases observation
  rfl

/-- **Exact entry inverse.**  Every raw entry is recovered literally after encoding and decoding:
the legacy payload, the P-94 source/equality/claim/certificate, and the P-93 source tie and
observation. -/
theorem decodeAuthorityEntry_encodeAuthorityEntry (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    decodeAuthorityEntry core enumeration (encodeAuthorityEntry core enumeration entry) = entry := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq observation valid =>
      simp only [encodeAuthorityEntry, decodeAuthorityEntry]
      exact observationP94_extEq
        (EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid
          (observationSourceAtomResolver core enumeration source source_graph_eq)
          observation valid)
  | acyclicP93 tie graph_eq spatial_eq diagram_eq observation valid =>
      simp only [encodeAuthorityEntry, decodeAuthorityEntry]
      let sourceWellFormed
          : (recoveredAcyclicSource core enumeration).SpatialIndicesWellFormed := by
        rw [recoveredAcyclicSource_eq_tie core enumeration tie graph_eq spatial_eq diagram_eq]
        exact tie.spatial_wellFormed
      exact acyclicP93_extEq
        (decodedAcyclicTie_eq_tie core enumeration sourceWellFormed tie graph_eq spatial_eq
          diagram_eq)
        (unrelabelObservation_relabelObservation enumeration observation
          (SourceAcyclicObservation.boundedIn_of_validFor_binding tie.toBinding observation valid))

/-! ## Assignment flattening and explicit projection data -/

/-- The assignments of a source acyclic observation, flattened in the observation's own order.  The
eleven constructors are handled explicitly; no shape is rejected. -/
def acyclicAssignments (observation : SourceAcyclicObservation policy93) :
    List (P93AcyclicAuthorityAssignment policy93) :=
  match observation with
  | .singleCenter record => [record.assignment]
  | .multipleCenterDescriptors record => record.assignments
  | .prefixComponent record => [record.assignment]
  | .doubleBond record => [record.assignment]
  | .heteroDoubleBond record => [record.assignment]
  | .multipleDoubleBond record => record.assignments
  | .evenCumulene record => [record.assignment]
  | .oddCumulene record => [record.assignment]
  | .placedAssignment record => [record.assignment]
  | .multipleUnits record => record.assignments.map (fun placed => placed.assignment)
  | .bareAssignment assignment => [assignment]

/-- The optional citation tokens of a source observation in assignment order. -/
def acyclicCitationTokens (observation : SourceAcyclicObservation policy93) :
    List (Option P93AuthorityCitationToken) :=
  (acyclicAssignments observation).map (fun assignment => assignment.citation?)

/-- The parent-name components of a source observation in assignment order. -/
def acyclicComponents (observation : SourceAcyclicObservation policy93) :
    List policy93.Component :=
  (acyclicAssignments observation).map (fun assignment => assignment.component)

/-- The independently judged unit kinds of a source observation in assignment order. -/
def acyclicKinds (observation : SourceAcyclicObservation policy93) : List UnitKind :=
  (acyclicAssignments observation).map (fun assignment => assignment.kind)

/-- The assignments of a native supplied observation. -/
def nativeAssignments (observation : AcyclicObservation V policy93) :
    List (SuppliedAcyclicAssignment V policy93.Component) :=
  match observation with
  | .singleCenter record => [record.assignment]
  | .multipleCenterDescriptors record => record.assignments
  | .prefixComponent record => [record.assignment]
  | .doubleBond record => [record.assignment]
  | .heteroDoubleBond record => [record.assignment]
  | .multipleDoubleBond record => record.assignments
  | .evenCumulene record => [record.assignment]
  | .oddCumulene record => [record.assignment]
  | .placedAssignment record => [record.assignment]
  | .multipleUnits record => record.assignments.map (fun placed => placed.assignment)
  | .bareAssignment assignment => [assignment]

/-- The optional citation tokens of a native observation in assignment order. -/
def nativeCitationTokens (observation : AcyclicObservation V policy93) :
    List (Option P93AuthorityCitationToken) :=
  (nativeAssignments observation).map (fun assignment => assignment.citation?)

/-- The parent-name components of a native observation in assignment order. -/
def nativeComponents (observation : AcyclicObservation V policy93) : List policy93.Component :=
  (nativeAssignments observation).map (fun assignment => assignment.component)

/-- The independently judged unit kinds of a native observation in assignment order. -/
def nativeKinds (observation : AcyclicObservation V policy93) : List UnitKind :=
  (nativeAssignments observation).map (fun assignment => assignment.kind)

/-- Decoding a relabelled source observation preserves the optional citation list exactly. -/
theorem acyclicCitationTokens_unrelabelObservation (e : V ≃ Fin (Fintype.card V))
    (observation : AcyclicObservation V policy93) :
    acyclicCitationTokens (unrelabelObservation e observation) =
      nativeCitationTokens observation := by
  cases observation <;>
    simp [acyclicCitationTokens, nativeCitationTokens, acyclicAssignments, nativeAssignments,
      unrelabelObservation, unrelabelAcyclicAssignments, unrelabelPlacedAssignments,
      List.map_map]

/-- Decoding a relabelled source observation preserves the parent-name component list exactly. -/
theorem acyclicComponents_unrelabelObservation (e : V ≃ Fin (Fintype.card V))
    (observation : AcyclicObservation V policy93) :
    acyclicComponents (unrelabelObservation e observation) = nativeComponents observation := by
  cases observation <;>
    simp [acyclicComponents, nativeComponents, acyclicAssignments, nativeAssignments,
      unrelabelObservation, unrelabelAcyclicAssignments, unrelabelPlacedAssignments,
      List.map_map]

/-- Decoding a relabelled source observation preserves the independently judged unit kind list
exactly. -/
theorem acyclicKinds_unrelabelObservation (e : V ≃ Fin (Fintype.card V))
    (observation : AcyclicObservation V policy93) :
    acyclicKinds (unrelabelObservation e observation) = nativeKinds observation := by
  cases observation <;>
    simp [acyclicKinds, nativeKinds, acyclicAssignments, nativeAssignments, unrelabelObservation,
      unrelabelAcyclicAssignments, unrelabelPlacedAssignments, List.map_map]

/-! ## Explicit entry projections -/

namespace AuthorityMixedEntry

/-- The raw P-94 authority observation of an entry, when present. -/
def p94Observation? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (P94AuthorityObservation policy94)
  | .observationP94 _ _ observation _ => some observation
  | _ => none

/-- The P-94 claim of an entry, when present. -/
def p94Claim? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option P94AuthorityClaim
  | .observationP94 _ _ observation _ => some observation.claim
  | _ => none

/-- The presence of the optional ordered coordinate certificate of an entry, when present. -/
def p94CertificatePresent? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration → Option Bool
  | .observationP94 _ _ observation _ => some observation.inOutCertificate?.isSome
  | _ => none

/-- The raw molecule of an entry, when present. -/
def p94Molecule? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration → Option RawMolecule
  | .observationP94 _ _ observation _ => some observation.molecule
  | _ => none

/-- The certified source's semantic molecule of an entry, when present. -/
def p94SourceMolecule? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration → Option SemanticMolecule
  | .observationP94 source _ _ _ => some source.input.molecule
  | _ => none

/-- The raw P-93 acyclic observation of an entry, when present. -/
def acyclicObservation? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (SourceAcyclicObservation policy93)
  | .acyclicP93 _ _ _ _ observation _ => some observation
  | _ => none

/-- The source tie of a P-93 entry, when present. -/
def acyclicTie? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (AcyclicSourceTie V enumeration)
  | .acyclicP93 tie _ _ _ _ _ => some tie
  | _ => none

/-- The source of a P-93 entry, when present. -/
def acyclicSource? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option AuthoritativeChemicalInput
  | .acyclicP93 tie _ _ _ _ _ => some tie.source
  | _ => none

/-- The optional citation tokens of a P-93 entry, one per assignment in order, when present.
`none` is retained as `none`; no token is invented. -/
def acyclicCitationTokens? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (List (Option P93AuthorityCitationToken))
  | .acyclicP93 _ _ _ _ observation _ => some (acyclicCitationTokens observation)
  | _ => none

/-- The parent-name components of a P-93 entry, one per assignment in order, when present. -/
def acyclicComponents? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (List policy93.Component)
  | .acyclicP93 _ _ _ _ observation _ => some (acyclicComponents observation)
  | _ => none

/-- The independently judged unit kinds of a P-93 entry, one per assignment in order, when
present. -/
def acyclicKinds? :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration → Option (List UnitKind)
  | .acyclicP93 _ _ _ _ observation _ => some (acyclicKinds observation)
  | _ => none

end AuthorityMixedEntry

namespace EncodedAuthorityMixedEntry

/-- The claim of an encoded P-94 entry, when present. -/
def p94Claim? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option P94AuthorityClaim
  | .observationP94 _ _ encoded _ => some encoded.claim
  | _ => none

/-- The certificate presence of an encoded P-94 entry, when present. -/
def p94CertificatePresent? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration → Option Bool
  | .observationP94 _ _ encoded _ => some encoded.inOutCertificate?.isSome
  | _ => none

/-- The raw molecule of an encoded P-94 entry, when present. -/
def p94Molecule? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option RawMolecule
  | .observationP94 _ _ encoded _ => some encoded.molecule
  | _ => none

/-- The certified source's semantic molecule of an encoded P-94 entry, when present. -/
def p94SourceMolecule? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option SemanticMolecule
  | .observationP94 source _ _ _ => some source.input.molecule
  | _ => none

/-- The native acyclic observation of an encoded P-93 entry, when present. -/
def acyclicObservation? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (AcyclicObservation V policy93)
  | .acyclicP93 observation _ _ => some observation
  | _ => none

/-- The source recovered from an encoded P-93 entry, when present. -/
def acyclicSource? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option AuthoritativeChemicalInput
  | .acyclicP93 _ _ _ => some (recoveredAcyclicSource core enumeration)
  | _ => none

/-- The optional citation tokens of an encoded P-93 entry in assignment order, when present. -/
def acyclicCitationTokens? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (List (Option P93AuthorityCitationToken))
  | .acyclicP93 observation _ _ => some (nativeCitationTokens observation)
  | _ => none

/-- The parent-name components of an encoded P-93 entry in assignment order, when present. -/
def acyclicComponents? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (List policy93.Component)
  | .acyclicP93 observation _ _ => some (nativeComponents observation)
  | _ => none

/-- The independently judged unit kinds of an encoded P-93 entry in assignment order, when
present. -/
def acyclicKinds? :
    EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration →
      Option (List UnitKind)
  | .acyclicP93 observation _ _ => some (nativeKinds observation)
  | _ => none

end EncodedAuthorityMixedEntry

/-! ### Projection recovery theorems -/

theorem decodeAuthorityEntry_p94Claim? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    (decodeAuthorityEntry core enumeration entry).p94Claim? = entry.p94Claim? := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq encoded valid => rfl
  | acyclicP93 observation wellFormed valid => rfl

theorem decodeAuthorityEntry_p94CertificatePresent? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    (decodeAuthorityEntry core enumeration entry).p94CertificatePresent? =
      entry.p94CertificatePresent? := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq encoded valid =>
      show some (decodedP94Authority core enumeration source_graph_eq encoded).inOutCertificate?.isSome =
        some encoded.inOutCertificate?.isSome
      exact congrArg some
        (decodedP94Authority_certificate_isSome core enumeration source_graph_eq encoded)
  | acyclicP93 observation wellFormed valid => rfl

theorem decodeAuthorityEntry_p94Molecule? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    (decodeAuthorityEntry core enumeration entry).p94Molecule? = entry.p94Molecule? := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq encoded valid => rfl
  | acyclicP93 observation wellFormed valid => rfl

theorem decodeAuthorityEntry_p94SourceMolecule? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    (decodeAuthorityEntry core enumeration entry).p94SourceMolecule? =
      entry.p94SourceMolecule? := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq encoded valid => rfl
  | acyclicP93 observation wellFormed valid => rfl

theorem decodeAuthorityEntry_acyclicCitationTokens? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    (decodeAuthorityEntry core enumeration entry).acyclicCitationTokens? =
      entry.acyclicCitationTokens? := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq encoded valid => rfl
  | acyclicP93 observation wellFormed valid =>
      simp [decodeAuthorityEntry, AuthorityMixedEntry.acyclicCitationTokens?,
        EncodedAuthorityMixedEntry.acyclicCitationTokens?,
        acyclicCitationTokens_unrelabelObservation]

theorem decodeAuthorityEntry_acyclicComponents? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    (decodeAuthorityEntry core enumeration entry).acyclicComponents? =
      entry.acyclicComponents? := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq encoded valid => rfl
  | acyclicP93 observation wellFormed valid =>
      simp [decodeAuthorityEntry, AuthorityMixedEntry.acyclicComponents?,
        EncodedAuthorityMixedEntry.acyclicComponents?,
        acyclicComponents_unrelabelObservation]

theorem decodeAuthorityEntry_acyclicKinds? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    (decodeAuthorityEntry core enumeration entry).acyclicKinds? = entry.acyclicKinds? := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq encoded valid => rfl
  | acyclicP93 observation wellFormed valid =>
      simp [decodeAuthorityEntry, AuthorityMixedEntry.acyclicKinds?,
        EncodedAuthorityMixedEntry.acyclicKinds?, acyclicKinds_unrelabelObservation]

theorem decodeAuthorityEntry_acyclicSource? (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration) :
    (decodeAuthorityEntry core enumeration entry).acyclicSource? = entry.acyclicSource? := by
  cases entry with
  | legacy entry => rfl
  | observationP94 source source_graph_eq encoded valid => rfl
  | acyclicP93 observation wellFormed valid => rfl

/-! ## The whole authority mixed request and representation -/

/-- The whole authority mixed request: one independently supplied core, the fixed P-94 and P-93
policies, the one explicit enumeration, and the one ordered tagged entry list. -/
structure AuthorityMixedSourceRequest (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type) where
  policy94 : P94AuthorityPolicy
  policy93 : P93AcyclicAuthorityPolicy
  core : OrganicMolecularEvidence V
  enumeration : V ≃ Fin (Fintype.card V)
  entries : List (AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
    State Framework BaseName Numbering Locant Prefix policy94 policy93 core enumeration)

/-- The assembled authority representation: the actual accepted molecular representation, the
fixed policies, the explicit enumeration, and the one ordered list of concrete encoded entries
over the recovered core. -/
structure AuthorityMixedSourceRepresentation (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type) where
  assembled : OrganicMolecularRepresentation V
  policy94 : P94AuthorityPolicy
  policy93 : P93AcyclicAuthorityPolicy
  enumeration : V ≃ Fin (Fintype.card V)
  entries : List (EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
    State Framework BaseName Numbering Locant Prefix policy94 policy93 (decodeEvidence assembled)
    enumeration)

/-- Extensionality of authority mixed requests. -/
theorem AuthorityMixedSourceRequest.extEq
    {first second : AuthorityMixedSourceRequest (V := V) LigandId LigandKind FragmentId
      FragmentKind State Framework BaseName Numbering Locant Prefix}
    (policy94_eq : first.policy94 = second.policy94)
    (policy93_eq : first.policy93 = second.policy93)
    (core_eq : first.core = second.core)
    (enumeration_eq : first.enumeration = second.enumeration)
    (entries : HEq first.entries second.entries) : first = second := by
  obtain ⟨firstPolicy94, firstPolicy93, firstCore, firstEnumeration, firstEntries⟩ := first
  obtain ⟨secondPolicy94, secondPolicy93, secondCore, secondEnumeration, secondEntries⟩ := second
  dsimp only at policy94_eq policy93_eq core_eq enumeration_eq entries
  cases policy94_eq
  cases policy93_eq
  cases core_eq
  cases enumeration_eq
  have entriesEq : firstEntries = secondEntries := eq_of_heq entries
  cases entriesEq
  rfl

/-- Assemble the authority mixed request.  The core goes through the accepted mixed assembly;
the entry list is transported along the proved core inverse and each entry is encoded by the
concrete codecs above. -/
def assembleAuthorityMixed
    (request : AuthorityMixedSourceRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    AuthorityMixedSourceRepresentation (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix where
  assembled := assembleCore request.core request.enumeration
  policy94 := request.policy94
  policy93 := request.policy93
  enumeration := request.enumeration
  entries :=
    (decodeCore_eq_assembleCore request.core request.enumeration).symm ▸
      request.entries.map (encodeAuthorityEntry request.core request.enumeration)

/-- Decode the authority mixed representation: the core from the actual assembled molecular
representation, and every entry through its concrete decoder. -/
def decodeAuthorityMixed
    (representation : AuthorityMixedSourceRepresentation (V := V) LigandId LigandKind FragmentId
      FragmentKind State Framework BaseName Numbering Locant Prefix) :
    AuthorityMixedSourceRequest (V := V) LigandId LigandKind FragmentId FragmentKind State
      Framework BaseName Numbering Locant Prefix where
  policy94 := representation.policy94
  policy93 := representation.policy93
  core := decodeEvidence representation.assembled
  enumeration := representation.enumeration
  entries := representation.entries.map
    (decodeAuthorityEntry (decodeEvidence representation.assembled) representation.enumeration)

/-! ## The generic dependent-map transport -/

/-- Mapping an entry list along a type-index equality and then decoding it returns the original
list heterogeneously.  This is the list-level dependent transport used by the whole-request
inverse; it is proved by list induction and the exact entry inverse. -/
theorem map_decode_eqRec {I : Type u} {P Q : I → Type}
    (encode : ∀ index, P index → Q index)
    (decode : ∀ index, Q index → P index)
    (leftInverse : ∀ index (entry : P index), decode index (encode index entry) = entry)
    {first second : I} (equal : first = second) (entries : List (P second)) :
    HEq ((equal.symm ▸ entries.map (encode second)).map (decode first)) entries := by
  cases equal
  apply heq_of_eq
  rw [List.map_map]
  induction entries with
  | nil => rfl
  | cons head tail tailInvariant =>
      rw [List.map_cons]
      exact (List.cons.injEq _ _ _ _).mpr ⟨leftInverse _ head, tailInvariant⟩

/-! ## Exact whole-request inverse, injectivity and set-image recovery -/

/-- **Exact whole-request inverse.**  Decoding the assembled authority representation returns the
whole request literally: both policies, the independent core, the explicit enumeration, and one
ordered tagged entry list with every P-94 claim/certificate and every P-93 citation/component/kind
retained in order and with multiplicity. -/
theorem decodeAuthorityMixed_assembleAuthorityMixed
    (request : AuthorityMixedSourceRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    decodeAuthorityMixed (assembleAuthorityMixed request) = request := by
  apply AuthorityMixedSourceRequest.extEq
  · rfl
  · rfl
  · exact decodeCore_eq_assembleCore request.core request.enumeration
  · rfl
  · exact map_decode_eqRec
      (I := OrganicMolecularEvidence V)
      (P := fun core => AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind
        State Framework BaseName Numbering Locant Prefix request.policy94 request.policy93 core
        request.enumeration)
      (Q := fun core => EncodedAuthorityMixedEntry (V := V) LigandId LigandKind FragmentId
        FragmentKind State Framework BaseName Numbering Locant Prefix request.policy94
        request.policy93 core request.enumeration)
      (encode := fun core entry => encodeAuthorityEntry core request.enumeration entry)
      (decode := fun core entry => decodeAuthorityEntry core request.enumeration entry)
      (leftInverse := fun core entry =>
        decodeAuthorityEntry_encodeAuthorityEntry core request.enumeration entry)
      (decodeCore_eq_assembleCore request.core request.enumeration)
      request.entries

/-- The assembly is injective: equal assembled representations have equal requests. -/
theorem assembleAuthorityMixed_injective :
    ∀ first second : AuthorityMixedSourceRequest (V := V) LigandId LigandKind FragmentId
        FragmentKind State Framework BaseName Numbering Locant Prefix,
      assembleAuthorityMixed first = assembleAuthorityMixed second → first = second := by
  intro first second equal
  have applied := congrArg decodeAuthorityMixed equal
  rwa [decodeAuthorityMixed_assembleAuthorityMixed first,
    decodeAuthorityMixed_assembleAuthorityMixed second] at applied

/-- **Arbitrary correlated set-image recovery.**  For every set of authority mixed requests, the
requests whose assembled representation decodes into that set are exactly the original set.  This
retains the correlation between the core, the policies, the enumeration, the interleaving of the
three entry families, and every duplicate occurrence. -/
theorem decodeAuthorityMixed_image_assembleAuthorityMixed_image
    (requests : Set (AuthorityMixedSourceRequest (V := V) LigandId LigandKind FragmentId
      FragmentKind State Framework BaseName Numbering Locant Prefix)) :
    decodeAuthorityMixed '' (assembleAuthorityMixed '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨representation, ⟨original, member, rfl⟩, decoded⟩
    rw [← decoded, decodeAuthorityMixed_assembleAuthorityMixed]
    exact member
  · intro member
    exact ⟨assembleAuthorityMixed request, ⟨request, member, rfl⟩,
      decodeAuthorityMixed_assembleAuthorityMixed request⟩

/-! ## Adapters from the existing raw source shapes -/

/-- Build a raw P-94 entry from a valid authority observation.  The source-to-common-graph
equality is genuine data supplied by the caller. -/
def p94EntryOfValid
    {core : OrganicMolecularEvidence V} {enumeration : V ≃ Fin (Fintype.card V)}
    (source : CertifiedAuthoritativeChemicalInput)
    (source_graph_eq : source.input.molecule = core.graph.encode enumeration)
    (observation : P94AuthorityObservation policy94)
    (valid : observation.ValidFor policy94 source.input) :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration :=
  .observationP94 source source_graph_eq observation valid

/-- Build a raw P-93 entry from an existing `PhysicalFrameSourceBinding` whose own enumeration is
propositionally the common enumeration.  The graph, spatial and diagram equalities are transported
along that enumeration equality, so the entry is stated at the common enumeration with genuine
equalities to the common core. -/
def acyclicEntryOfBinding
    {core : OrganicMolecularEvidence V} {enumeration : V ≃ Fin (Fintype.card V)}
    (binding : AcyclicSourceBinding V)
    (enumeration_eq : binding.enumeration = enumeration)
    (graph_eq : binding.shared.graph = core.graph)
    (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
    (diagram_eq : binding.shared.diagram? = core.diagram?)
    (observation : SourceAcyclicObservation policy93)
    (valid : observation.ValidFor binding.source) :
    AuthorityMixedEntry (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policy94 policy93 core enumeration :=
  .acyclicP93
    { source := binding.source
      shared := binding.shared
      graph_eq := by rw [← enumeration_eq]; exact binding.graph_eq
      spatial_eq := by rw [← enumeration_eq]; exact binding.spatial_eq
      diagram_eq := by rw [← enumeration_eq]; exact binding.diagram_eq
      spatial_wellFormed := binding.spatial_wellFormed }
    graph_eq spatial_eq diagram_eq observation valid

end

end OrganicStereoAuthorityMixedSourceAssembly
end TetraStereo.OneCenter
