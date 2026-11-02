/-
# Actual assembled-state binding of the mixed shared physical context

`OrganicStereoMixedSourceAssembly.sharedContext` is the single context indexing the
proof-carrying shared physical case entries of a mixed source request.  By construction it is
`SharedPhysicalContext.ofState (commonBaseState core) enumeration`, where `commonBaseState core`
is the core's base state with the core's electronic inventory attached.  The accepted projection
module `OrganicStereoMolecularAssemblyProjections` proves that the *actual* output
`OrganicStereoMolecularEvidenceAssembly.assemble core` stores the request's concrete electronic
ingress channel, graph and conformation.  What was still missing is the direct equality between
the context used by the case certificates and the context of the **actual** assembled state, at
the representation's own effective edge/band `Fintype` instances.

This module supplies that equality.  It contains no new molecule carrier and no carrier
reconstruction: every statement is a projection or a rewriting of the accepted upstream
equalities.

* `representationPhysicalContext` reads `SharedPhysicalContext.ofState` of a representation's
  actual `state` at its packed `fintypeEdgeIndex`/`fintypeBandIndex` instances.
* `sharedPhysicalContext_extEq` is a small extensionality lemma; the proposition-valued
  `electronic_unpaired` field is identified by proof irrelevance.
* The four `representationPhysicalContext_*` projection lemmas read the context's graph,
  inventory, conformation and enumeration at the actual assembled representation.
* `electronicChannelOption_eq_requestElectronicChannel?` identifies the context's concrete
  electronic channel with the projection module's concrete request channel, by unfolding the two
  `match` definitions; no agreement is assumed.
* `sharedContext_eq_assembledPhysicalContext` is the main result: the shared context of the mixed
  request is exactly the physical context of the actual assembled output.
* `assembleMixed_observation_source_graph`, `assembleMixed_donor_occurrence_facts` and
  `assembleMixed_physicalFrame_ties` rewrite the accepted entry-level source/geometry equalities
  so that they hold at the actual output fields (`stateGraph`, `stateRationalPositions?`,
  `stateDiagram?`) rather than only at the decoded core.
-/

import TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly
import TetraStereo.OneCenter.OrganicStereoMolecularAssemblyProjections
import TetraStereo.OneCenter.OrganicStereoDonorGroupingIngress
import TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter
namespace OrganicStereoMixedOutputPhysicalBinding

open OrganicStereoMixedSourceAssembly
open OrganicStereoMolecularAssemblyProjections
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoSharedPhysicalCaseIngress
open OrganicStereoOrderedObservationFamily
open DonorGroupingIngress

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The physical context of an actual assembled representation -/

/-- The shared physical context of an actual assembled representation, read at the
representation's own packed effective edge/band `Fintype` instances.  The body is literally
`SharedPhysicalContext.ofState representation.state enumeration` at those instances; it is a view
of the actual state's graph, inventory and conformation, not a second carrier. -/
def representationPhysicalContext (representation : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) : SharedPhysicalContext V :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  SharedPhysicalContext.ofState representation.state enumeration

/-- The graph of the actual assembled-state context is the representation's assembled graph. -/
@[simp] theorem representationPhysicalContext_graph
    (representation : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (representationPhysicalContext representation enumeration).graph =
      representation.stateGraph := rfl

/-- The electronic inventory of the actual assembled-state context is exactly the channel stored in
the representation's state. -/
@[simp] theorem representationPhysicalContext_electronic?
    (representation : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (representationPhysicalContext representation enumeration).electronic? =
      stateElectronicChannel? representation := rfl

/-- The conformation of the actual assembled-state context is the representation's assembled
conformation. -/
@[simp] theorem representationPhysicalContext_conformation
    (representation : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (representationPhysicalContext representation enumeration).conformation =
      representation.stateConformation := rfl

/-- The enumeration of the actual assembled-state context is the explicit enumeration. -/
@[simp] theorem representationPhysicalContext_enumeration
    (representation : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (representationPhysicalContext representation enumeration).enumeration = enumeration := rfl

/-- Extensionality for `SharedPhysicalContext`.  The `electronic_unpaired` field is
proposition-valued and is identified by proof irrelevance once the data fields agree.  This is the
same pattern as `WholeState.extEq`, specialised to the four-context data fields. -/
theorem sharedPhysicalContext_extEq {first second : SharedPhysicalContext V}
    (graph : first.graph = second.graph)
    (electronic : first.electronic? = second.electronic?)
    (conformation : first.conformation = second.conformation)
    (enumeration : first.enumeration = second.enumeration) :
    first = second := by
  obtain ⟨graph₁, electronic₁, unpaired₁, conformation₁, enumeration₁⟩ := first
  obtain ⟨graph₂, electronic₂, unpaired₂, conformation₂, enumeration₂⟩ := second
  dsimp only at graph electronic conformation enumeration
  cases graph
  cases electronic
  cases conformation
  cases enumeration
  have unpaired : unpaired₁ = unpaired₂ := by
    funext channel present owner
    exact Subsingleton.elim _ _
  cases unpaired
  rfl

/-! ## The two concrete electronic channels agree -/

/-- The context's concrete electronic channel and the projection module's concrete request
channel are the same definition: both match on `core.electronic?` and build the ingress channel
from the request's own graph, unpaired-electron tie and complete assignment.  No agreement between
the assembled state and the request is assumed. -/
theorem electronicChannelOption_eq_requestElectronicChannel?
    (core : OrganicMolecularEvidence V) :
    electronicChannelOption core = requestElectronicChannel? core := by
  unfold electronicChannelOption
  split
  · rename_i h
    exact (OrganicStereoMolecularAssemblyProjections.requestElectronicChannel?_none
      core h).symm
  · rename_i evidence h
    refine (congrArg some ?_).trans
      (OrganicStereoMolecularAssemblyProjections.requestElectronicChannel?_some
        core evidence h).symm
    unfold OrganicStereoMolecularAssemblyProjections.requestElectronicChannel
    rfl

/-! ## Main result: the mixed context is the actual assembled-state context -/

/-- **Main result.**  The shared physical context indexing the mixed source entries is exactly the
physical context of the actual `OrganicStereoMolecularEvidenceAssembly.assemble core` output, read
at the representation's effective edge/band `Fintype` instances.  The graph, inventory and
conformation are identified by the accepted assembly projections; the enumeration is literal.
This is a direct binding to the assembled state, not merely to the decoded core. -/
theorem sharedContext_eq_assembledPhysicalContext
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    sharedContext core enumeration =
      representationPhysicalContext
        (OrganicStereoMolecularEvidenceAssembly.assemble core) enumeration := by
  apply sharedPhysicalContext_extEq
  · rw [representationPhysicalContext_graph,
      sharedContext_graph, assemble_stateGraph]
  · rw [representationPhysicalContext_electronic?, sharedContext_electronic?,
      assemble_stateElectronicChannel?,
      electronicChannelOption_eq_requestElectronicChannel?]
  · rw [representationPhysicalContext_conformation, sharedContext_conformation,
      assemble_stateConformation]
  · rw [representationPhysicalContext_enumeration, sharedContext_enumeration]

/-! ## Decoded-core projections at the actual state fields -/

/-- The graph decoded from an assembled representation is the representation's actual assembled
graph.  This is the definitional projection used to move the entry-level ties from the decoded core
to the actual output. -/
@[simp] theorem decodeEvidence_graph (representation : OrganicMolecularRepresentation V) :
    (decodeEvidence representation).graph = representation.stateGraph := rfl

/-- The exact rational provenance decoded from an assembled representation is the
representation's actual assembled provenance channel. -/
@[simp] theorem decodeEvidence_rationalPositions?
    (representation : OrganicMolecularRepresentation V) :
    (decodeEvidence representation).rationalPositions? =
      representation.stateRationalPositions? := rfl

/-- The optional drawing source decoded from an assembled representation is the representation's
actual assembled drawing channel. -/
@[simp] theorem decodeEvidence_diagram? (representation : OrganicMolecularRepresentation V) :
    (decodeEvidence representation).diagram? = representation.stateDiagram? := rfl

/-! ## Occurrence facts at a different but equal graph -/

/-- Transport native occurrence facts along an equality of interaction graphs.  The interaction
count proof is propositional; every choice of count proof for the target graph yields the same
facts.  This is a general transport lemma, not a new validity claim. -/
theorem nativeOccurrenceFacts_castGraph
    {LigandId LigandKind FragmentId FragmentKind : Type}
    {graph graph' : FiniteAtomInteractionHypergraph V}
    {eV : V ≃ Fin (Fintype.card V)} {n : Nat}
    {count_eq : n = graph.interactions.length}
    {occurrence : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n}
    (graph_eq : graph = graph')
    (facts : NativeOccurrenceFacts graph eV count_eq occurrence) :
    ∀ count_eq' : n = graph'.interactions.length,
      NativeOccurrenceFacts graph' eV count_eq' occurrence := by
  cases graph_eq
  intro count_eq'
  cases Subsingleton.elim count_eq' count_eq
  exact facts

/-! ## Entry-level corollaries at the actual output fields -/

variable {LigandId LigandKind FragmentId FragmentKind : Type}
variable [DecidableEq LigandId] [DecidableEq LigandKind]
variable [DecidableEq FragmentId] [DecidableEq FragmentKind]
variable {State Framework : Type}
variable {BaseName Numbering Locant Prefix : Type}

/-- An observation entry's source graph tie, recovered from the actual mixed output's entry list,
holds at the **actual assembled graph** as well as at the decoded core.  Obtained by rewriting the
accepted `decodeMixed_observation_source_graph` equality with the decoded-core graph projection and
the assembly graph projection; no output agreement is assumed. -/
theorem assembleMixed_observation_source_graph
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix)
    {index : Nat} {source : CertifiedAuthoritativeChemicalInput}
    {family : OrderedObservationFamily source V State Framework}
    {sourceGraphEq : source.input.molecule =
      (decodeEvidence (assembleEvidence request.core)).graph.encode request.enumeration}
    (found : (assembleMixed request).entries[index]? =
      some (MixedEntry.observation source family sourceGraphEq)) :
    source.input.molecule =
      (assembleMixed request).assembled.stateGraph.encode request.enumeration := by
  have source' := decodeMixed_observation_source_graph request found
  rw [assembleMixed_assembled, source', decodeEvidence_graph]

/-- A donor entry's stored validity yields, at every occurrence, the actual interaction facts of
the **actual assembled graph**: the interaction kind is `coordinate`, the participant list has
length two, its support is exactly the donor/centre pair, and the donor differs from the centre.
The facts are transported from the decoded core by the accepted occurrence-facts theorem and the
decoded-core graph projection; the interaction-count proof is derived, not assumed. -/
theorem assembleMixed_donor_occurrence_facts
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix)
    {index : Nat}
    {channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      (decodeEvidence (assembleEvidence request.core)).graph.interactions.length}
    {validity : NativeChannelValidity (decodeEvidence (assembleEvidence request.core)).graph
      request.enumeration
      (rfl : (decodeEvidence (assembleEvidence request.core)).graph.interactions.length =
        (decodeEvidence (assembleEvidence request.core)).graph.interactions.length) channel}
    (found : (assembleMixed request).entries[index]? =
      some (MixedEntry.donor channel validity)) :
    ∀ occurrence : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind
        (decodeEvidence (assembleEvidence request.core)).graph.interactions.length,
      occurrence ∈ channel.occurrences →
      NativeOccurrenceFacts (assembleMixed request).assembled.stateGraph request.enumeration
        (by
          rw [assembleMixed_assembled]
          exact congrArg
            (fun graph : FiniteAtomInteractionHypergraph V => graph.interactions.length)
            (decodeEvidence_graph (assembleEvidence request.core)))
        occurrence := by
  intro occurrence member
  exact nativeOccurrenceFacts_castGraph
    (decodeEvidence_graph (assembleEvidence request.core))
    (decodeMixed_donor_occurrence_facts request found occurrence member)
    (by
      exact congrArg
        (fun graph : FiniteAtomInteractionHypergraph V => graph.interactions.length)
        (decodeEvidence_graph (assembleEvidence request.core)))

/-- A P-93 physical-frame entry's exact graph, shared-coordinate and drawing ties, recovered from
the actual mixed output's entry list, hold at the **actual assembled output fields**
(`stateGraph`, `stateRationalPositions?`, `stateDiagram?`).  Obtained by rewriting the accepted
`decodeMixed_physicalFrame_ties` conjunction with the decoded-core projections and the assembly
projection; no output agreement is assumed. -/
theorem assembleMixed_physicalFrame_ties
    (request : MixedSourceRequest V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix)
    {index : Nat}
    {satellite : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite V}
    {graphEq : satellite.graph =
      (decodeEvidence (assembleEvidence request.core)).graph}
    {spatialEq : satellite.spatial? =
      (decodeEvidence (assembleEvidence request.core)).rationalPositions?}
    {diagramEq : satellite.diagram? =
      (decodeEvidence (assembleEvidence request.core)).diagram?}
    (found : (assembleMixed request).entries[index]? =
      some (MixedEntry.physicalFrame satellite graphEq spatialEq diagramEq)) :
    satellite.graph = (assembleMixed request).assembled.stateGraph ∧
      satellite.spatial? =
        (assembleMixed request).assembled.stateRationalPositions? ∧
      satellite.diagram? = (assembleMixed request).assembled.stateDiagram? := by
  obtain ⟨graph', spatial', diagram'⟩ := decodeMixed_physicalFrame_ties request found
  refine ⟨?_, ?_, ?_⟩
  · rw [assembleMixed_assembled]
    exact graph'.trans (decodeEvidence_graph (assembleEvidence request.core))
  · rw [assembleMixed_assembled]
    exact spatial'.trans (decodeEvidence_rationalPositions? (assembleEvidence request.core))
  · rw [assembleMixed_assembled]
    exact diagram'.trans (decodeEvidence_diagram? (assembleEvidence request.core))

end OrganicStereoMixedOutputPhysicalBinding
end TetraStereo.OneCenter
