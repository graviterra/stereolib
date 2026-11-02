import TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

namespace OrganicStereoMolecularAssemblyProjections

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoElectronicSites
open OrganicStereoIndependentElectronicEncoding
open OrganicStereoElectronicDescriptionIngress
open OrganicStereoElectronicStateAttachment
open OrganicStereoBandStateAttachment

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]







































/-! ## The concrete expected electronic channel -/

/-- The concrete electronic channel ingressed from one supplied inventory.  Its counts are the
supplied independent counts and its evidence at every owner/kind is the canonical `List.ofFn`
enumeration of the supplied complete assignment over the actual `Fin` slots.  The source's only
graph tie is the request's own `electronic_unpaired` proof, so nothing is assumed beyond the
request. -/
def requestElectronicChannel (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) : ElectronicChannel V :=
  ingressChannel
    (evidence.toSiteSource request.graph
      (fun owner => request.electronic_unpaired evidence h owner))
    evidence.assignment

/-- The expected optional electronic channel determined by the request.  Genuine absence stays
`none`; a present inventory is the concrete `requestElectronicChannel`. -/
def requestElectronicChannel? (request : OrganicMolecularEvidence V) :
    Option (ElectronicChannel V) :=
  match h : request.electronic? with
  | none => none
  | some evidence => some (requestElectronicChannel request evidence h)

/-- The expected channel option is absent exactly when the request supplies no inventory. -/
@[simp] theorem requestElectronicChannel?_none (request : OrganicMolecularEvidence V)
    (h : request.electronic? = none) :
    requestElectronicChannel? request = none := by
  unfold requestElectronicChannel?
  split
  · rfl
  · rename_i evidence he
    rw [h] at he
    cases he

/-- The expected channel option is the concrete ingress channel when an inventory is supplied. -/
@[simp] theorem requestElectronicChannel?_some (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) :
    requestElectronicChannel? request = some (requestElectronicChannel request evidence h) := by
  unfold requestElectronicChannel?
  split
  · rename_i he
    rw [h] at he
    cases he
  · rename_i other he
    rw [h] at he
    cases he
    congr 1

/-! ## Exact contents of the concrete expected channel -/

/-- The expected channel's counts are exactly the supplied counts. -/
@[simp] theorem requestElectronicChannel_counts (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) :
    (requestElectronicChannel request evidence h).counts = evidence.siteCounts := rfl

/-- The expected channel's per-owner/per-kind evidence list is exactly the canonical slot
enumeration of the supplied assignment.  Slot order and multiplicity are literal. -/
theorem requestElectronicChannel_evidence (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) (owner : V) (kind : SiteKind) :
    (requestElectronicChannel request evidence h).evidence owner kind =
      List.ofFn (fun slot : Fin ((evidence.siteCounts.counts owner).count kind) =>
        evidence.assignment.valueAt ⟨owner, kind, slot⟩) := rfl

/-- The complete assignment read back from the expected channel at every counted
owner/kind/slot identity is exactly the supplied assignment.  No slot is invented or dropped. -/
theorem requestElectronicChannel_toSiteAssignment (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) :
    (requestElectronicChannel request evidence h).toSiteAssignment =
      evidence.assignment := by
  unfold requestElectronicChannel
  apply IndependentSiteAssignment.ext
  intro identity
  exact ingressEvidence_get _ _ identity.owner identity.kind identity.slot _

/-- Pointwise slot form of complete-assignment preservation: at every supplied identity the
stored evidence is exactly the supplied evidence. -/
theorem requestElectronicChannel_valueAt (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence)
    (owner : V) (kind : SiteKind)
    (slot : Fin ((evidence.siteCounts.counts owner).count kind)) :
    (requestElectronicChannel request evidence h).toSiteAssignment.valueAt
        ⟨owner, kind, slot⟩ =
      evidence.assignment.valueAt ⟨owner, kind, slot⟩ := by
  rw [requestElectronicChannel_toSiteAssignment]

/-! ## Accessing the actual assembled state's channel -/

/-- The optional electronic channel actually stored in a representation's assembled whole state,
read while supplying the representation's own effective edge and band `Fintype` instances
explicitly.  This is a projection of the actual output, not a reconstruction. -/
def stateElectronicChannel? (representation : OrganicMolecularRepresentation V) :
    Option (ElectronicChannel V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.electronic?

/-- The electronic channel of the base state is absent, hence the optional electronic ingress
operation stores exactly the request's expected channel (and leaves absence absent). -/
theorem attachElectronicOption_electronic? {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) (hstate : state.electronic? = none) :
    (attachElectronicOption request state graph_eq).electronic? =
      requestElectronicChannel? request := by
  cases h : request.electronic? with
  | none =>
      rw [requestElectronicChannel?_none request h]
      unfold attachElectronicOption
      split
      · exact hstate
      · rename_i evidence he
        rw [h] at he
        cases he
  | some evidence =>
      rw [requestElectronicChannel?_some request evidence h]
      unfold attachElectronicOption
      split
      · rename_i he
        rw [h] at he
        cases he
      · rename_i other he
        rw [h] at he
        cases he
        rw [attachElectronic_electronic?]
        congr 1

/-! ## Main result: the actual output stores the request's concrete ingress channel -/

/-- **Main result.**  The electronic channel actually stored in the assembled output is exactly
the concrete ingress channel built from the independently supplied request inventory.  The four
assembly branches (no paths/no bands, paths only, bands only, both) all reduce to the same
electronic ingress operation followed by path/band replacements that copy `electronic?`
literally, so the equality holds for every presence combination with no assumed context
agreement. -/
theorem assemble_stateElectronicChannel? (request : OrganicMolecularEvidence V) :
    stateElectronicChannel? (assemble request) = requestElectronicChannel? request := by
  unfold assemble
  split <;> split <;>
    simp_all [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, baseState, stateElectronicChannel?,
      attachElectronicOption_electronic?, baseState_electronic?,
      attachIndependentBands_electronic,
      attachIndependentBondPathData_electronic?]

/-- In the present case the actual output's channel option is exactly the concrete channel built
from the supplied evidence. -/
theorem assemble_stateElectronicChannel?_eq_some (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) :
    stateElectronicChannel? (assemble request) =
      some (requestElectronicChannel request evidence h) := by
  rw [assemble_stateElectronicChannel?, requestElectronicChannel?_some request evidence h]

/-- In the absent case the actual output stores no electronic channel. -/
theorem assemble_stateElectronicChannel?_eq_none (request : OrganicMolecularEvidence V)
    (h : request.electronic? = none) :
    stateElectronicChannel? (assemble request) = none := by
  rw [assemble_stateElectronicChannel?, requestElectronicChannel?_none request h]

/-- The counts of the concrete channel recoverable from the actual output are exactly the
supplied independent counts. -/
theorem assemble_stateElectronicChannel?_counts (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) :
    (requestElectronicChannel request evidence h).counts = evidence.siteCounts :=
  requestElectronicChannel_counts request evidence h

/-- The complete assignment recoverable from the actual output's channel is exactly the supplied
assignment, including every owner, kind and slot identity. -/
theorem assemble_stateElectronicChannel?_toSiteAssignment
    (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) :
    (requestElectronicChannel request evidence h).toSiteAssignment =
      evidence.assignment :=
  requestElectronicChannel_toSiteAssignment request evidence h

/-- Every supplied owner/kind/slot identity reads back the supplied evidence from the actual
output's channel. -/
theorem assemble_stateElectronicChannel?_valueAt
    (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence)
    (owner : V) (kind : SiteKind)
    (slot : Fin ((evidence.siteCounts.counts owner).count kind)) :
    (requestElectronicChannel request evidence h).toSiteAssignment.valueAt
        ⟨owner, kind, slot⟩ =
      evidence.assignment.valueAt ⟨owner, kind, slot⟩ :=
  requestElectronicChannel_valueAt request evidence h owner kind slot

/-- Bundled complete-inventory statement for the present case: the actual output's channel is the
concrete ingress channel, with the supplied counts and the supplied complete assignment. -/
theorem assemble_stateElectronicChannel?_complete (request : OrganicMolecularEvidence V)
    (evidence : IndependentElectronicEvidence V)
    (h : request.electronic? = some evidence) :
    stateElectronicChannel? (assemble request) =
        some (requestElectronicChannel request evidence h) ∧
      (requestElectronicChannel request evidence h).counts = evidence.siteCounts ∧
      (requestElectronicChannel request evidence h).toSiteAssignment =
        evidence.assignment :=
  ⟨assemble_stateElectronicChannel?_eq_some request evidence h,
    requestElectronicChannel_counts request evidence h,
    requestElectronicChannel_toSiteAssignment request evidence h⟩

/-- Heterogeneous assignment preservation for an arbitrary channel found in the actual output.
The equivalence is deliberately heterogeneous because the channel's counts type is only
propositionally (indeed definitionally) the supplied counts; consumers that substitute the
equality from `assemble_stateElectronicChannel?_eq_some` obtain the non-heterogeneous form. -/
theorem assemble_stateElectronicChannel?_toSiteAssignment_heq
    (request : OrganicMolecularEvidence V) {channel : ElectronicChannel V}
    (found : stateElectronicChannel? (assemble request) = some channel) :
    ∃ evidence : IndependentElectronicEvidence V,
      request.electronic? = some evidence ∧
        HEq channel.toSiteAssignment evidence.assignment := by
  cases h : request.electronic? with
  | none =>
      rw [assemble_stateElectronicChannel?_eq_none request h] at found
      cases found
  | some evidence =>
      rw [assemble_stateElectronicChannel?_eq_some request evidence h] at found
      cases found
      exact ⟨evidence, rfl, heq_of_eq (requestElectronicChannel_toSiteAssignment
        request evidence h)⟩

/-! ## Graph and conformation projections -/

/-- The assembled graph is the independently supplied request graph, in every presence
combination. -/
theorem assemble_stateGraph (request : OrganicMolecularEvidence V) :
    (assemble request).stateGraph = request.graph := by
  cases hb : request.bands? with
  | none => exact assemble_graph_of_no_bands request hb
  | some bands =>
      exact (assemble_graph_of_bands request bands hb).trans
        (request.bands_graph_eq bands hb)

/-- The assembled real conformation is the independently supplied request conformation, in every
presence combination. -/
theorem assemble_stateConformation (request : OrganicMolecularEvidence V) :
    (assemble request).stateConformation = request.conformation := by
  cases hb : request.bands? with
  | none => exact assemble_conformation_of_no_bands request hb
  | some bands =>
      exact (assemble_conformation_of_bands request bands hb).trans
        (request.bands_conformation_eq bands hb)

/-- The exact rational provenance channel is copied literally. -/
theorem assemble_stateRationalPositions? (request : OrganicMolecularEvidence V) :
    (assemble request).stateRationalPositions? = request.rationalPositions? :=
  (assemble_annotation_projections request).1

/-- The optional drawing source is copied literally. -/
theorem assemble_stateDiagram? (request : OrganicMolecularEvidence V) :
    (assemble request).stateDiagram? = request.diagram? :=
  (assemble_annotation_projections request).2.2.1

/-- The optional sparse drawing positions are copied literally. -/
theorem assemble_stateDiagramPartial? (request : OrganicMolecularEvidence V) :
    (assemble request).stateDiagramPartial? = request.diagramPartial? :=
  (assemble_annotation_projections request).2.2.2.1

/-- The raw drawing incidence ledger is copied literally. -/
theorem assemble_stateDiagramIncidence (request : OrganicMolecularEvidence V) :
    (assemble request).stateDiagramIncidence = request.diagramIncidence :=
  (assemble_annotation_projections request).2.2.2.2.1

/-! ## The compact physical-context view -/

/-- A compact physical-context view of an assembled output (or of a request): the actual graph,
the shared real conformation, exact rational provenance, the drawing channels and the electronic
inventory.  This is a view over existing projections; it deliberately does not duplicate the
whole `WholeState` carrier or any path/band family. -/
structure PhysicalContext (V : Type) [DecidableEq V] [Fintype V] where
  /-- The actual interaction graph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- The actual shared real conformation. -/
  conformation : MolecularConformation V
  /-- Exact rational coordinates, when supplied. -/
  rationalPositions? : Option (V → CartesianPoint3)
  /-- The optional drawing source. -/
  diagram? : Option (OrganicDiagramSource V)
  /-- The optional sparse drawing positions. -/
  diagramPartial? : Option (SourcePartialPositions V)
  /-- The raw drawing incidence ledger. -/
  diagramIncidence : List DiagramIncidenceRow
  /-- The electronic inventory actually stored, as a concrete channel option. -/
  electronic? : Option (ElectronicChannel V)

/-- The physical-context view of an assembled representation.  Every field is read from the
actual state at the representation's own effective edge/band index types. -/
def representationContext (representation : OrganicMolecularRepresentation V) :
    PhysicalContext V where
  graph := representation.stateGraph
  conformation := representation.stateConformation
  rationalPositions? := representation.stateRationalPositions?
  diagram? := representation.stateDiagram?
  diagramPartial? := representation.stateDiagramPartial?
  diagramIncidence := representation.stateDiagramIncidence
  electronic? := stateElectronicChannel? representation

/-- The independently supplied physical-context view of a request.  Its electronic field is the
concrete ingress channel built from the request's own inventory, not a decoded summary. -/
def requestContext (request : OrganicMolecularEvidence V) : PhysicalContext V where
  graph := request.graph
  conformation := request.conformation
  rationalPositions? := request.rationalPositions?
  diagram? := request.diagram?
  diagramPartial? := request.diagramPartial?
  diagramIncidence := request.diagramIncidence
  electronic? := requestElectronicChannel? request

/-- **Bundled context equality.**  The physical context of the actual assembled output is exactly
the independently supplied request context: the same graph, the same real conformation, the same
exact rational provenance, the same drawing channels, and the same concrete electronic ingress
channel.  No context agreement is assumed. -/
theorem assemble_context (request : OrganicMolecularEvidence V) :
    representationContext (assemble request) = requestContext request := by
  unfold representationContext requestContext
  rw [assemble_stateGraph request, assemble_stateConformation request,
    assemble_stateRationalPositions? request, assemble_stateDiagram? request,
    assemble_stateDiagramPartial? request, assemble_stateDiagramIncidence request,
    assemble_stateElectronicChannel? request]

end

end OrganicStereoMolecularAssemblyProjections

end TetraStereo.OneCenter
