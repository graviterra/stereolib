/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly
import TetraStereo.OneCenter.OrganicStereoPartialCoordinateStateCompletion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Compatibility coverage of the joint authority–cell representation

This module closes the partial-coordinate compatible-state idea of
`OrganicStereoPartialCoordinateStateCompletion` at the level of the *actual* joint
authority–cell record of `OrganicStereoJointAuthorityCellAssembly`.

## The domain is defined over every actual `JointRequest`

`jointCompatibleRequests graph K policySelection? cells?` is a filter (preimage) over **all**
actual `JointRequest V ...` values.  It imposes only

* the core graph is the independently supplied `graph`;
* the shared core conformation belongs to the supplied conformation set `K`;
* the policy record satisfies the **optional** supplied policy-selection constraint
  (`PolicySelectionCompatible`, which constrains only `JointRequest.policies` — it is *not*
  a constraint on independent authority observations or ordered row evidence);
* the cell list satisfies the **optional** supplied cell-set constraint.

Every other channel — the atom enumeration, the structural certificate, the complete
ordered `RawEntry` row list, the optional rational-coordinate/path/band/drawing channels,
the role/fragment/convention/cage/frame metadata, and the cell compatibility ties — is
unconstrained.  In particular the domain is **not** the image of any default completion:
no fixed completion is chosen before the domain is defined.

The supplied policy-selection and cell constraints are genuine extra constraints on top of the
graph/coordinate domain.  When `cells? = some S` with `[] ∉ S`, or `policySelection? = some p`
with a different policy record, the domain is strictly smaller than the unrestricted one
(`jointCompatibleRequests_some_cells_strict`, `jointCompatibleRequests_some_policySelection_strict`).
The ordered row list is not inspected by the base domain
(`mem_jointCompatibleRequests_withEntries_iff`), so supplied rows are an additional
constraint when a caller adds one; they are never silently fixed here.

## Witnesses versus domain restriction

`witnessJointRequest` and `witnessJointRequestWithEntries` construct actual `JointRequest`
values with every optional channel absent and either an empty or a supplied ordered row
list.  These constructions are used **only** to prove nonemptiness of the projection and of
the domain.  They are not a definition of the domain, and no theorem here claims that an
"absence mask" can be recovered from this single completion.  In particular the projection
theorem is proved in full generality only when the optional constraints actually accept the
constructed witness; for a supplied cell set that excludes `[]` the projection is not
asserted to be all of `K`.

## Representation

The actual upstream codecs are reused without replacement:

* `assembleJoint` / `decodeJoint`, with `decodeJoint_assembleJoint` the exact left inverse;
* `decodeJoint_image_assembleJoint_image`, the generic exact set inverse;
* `decodeSpatial` / `decodeSpatialCell` / `decodedCore`, for the native cell and core
  projections.

`nativeJointCompatible` states compatibility directly on the native fields
(`relabelGraph` of the canonical output graph, `MolecularConformation.reindex` of the
canonical output conformation, the policy record, and the decoded cell list), and
`decodeJoint_mem_jointCompatibleRequests_iff` proves it is exactly the preimage of the
source domain under `decodeJoint`.

The main image theorem
`assembleJoint_image_jointCompatibleRequests` identifies the image of the compatible
requests with the *canonical* native representations (`assembleJoint (decodeJoint r) = r`)
that are natively compatible.  No surjectivity of `assembleJoint` is asserted, because an
arbitrary native representation need not be in the image of the upstream assembly.

## Correlated two-atom coordinates

The concrete two-atom example instantiates the domain at the existing nondegenerate
correlation relation `TetraStereo.OneCenter.correlationRelation` (the second atom is the
first shifted by a fixed nonzero displacement).  This is a genuinely correlated relation:
both marginals are all of real three-space and the relation is a proper subset of their
product.  The joint domain's coordinate projection is exactly that relation, a concrete
member realizes the correlation, and the uncorrelated zero conformation is excluded.

## Scope boundary on authority observations and rows

Supplied authority *observations* and ordered *row evidence* are not modelled as constraints
here.  The only authority-side datum constrained is the stored policy record
`JointRequest.policies` (a policy selection); `PolicySelectionCompatible` is explicitly not
authority-evidence compatibility.  The ordered row list is proved unconstrained by the base
domain (`mem_jointCompatibleRequests_withEntries_iff`), so row content remains unconstrained
in this module.  The substantive independent constraints studied here are the shared core
graph, the shared conformation set (including sparse partial coordinates), and the supplied
cell set, with the exact necessary cell projection in
`cellsProjection_jointCompatibleRequests_subset`.

Nothing here claims chemical realizability, an executable CIP solver, injectivity of
continuous cells, or complete chemical coverage by definition.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoJointCompatibleStateCoverage

open OrganicStereoJointAuthorityCellAssembly
open OrganicStereoSpatialSupportMolecularAssembly
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoAllAuthorityEntries
open OrganicStereoAuthorityMixedSourceAssembly
open TetraStereo.OneCenter.PartialCoordinateExample

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The packaged auxiliary parameter types -/

/-- The ten auxiliary source types of `JointRequest`/`JointRepresentation`, packaged so
that the definitions below take one parameter instead of ten.  This is a binder
convenience only: every use is the dependency's **actual** `JointRequest` and
`JointRepresentation` at these types. -/
structure JointTypes where
  /-- The ligand identifier type. -/
  ligandId : Type
  /-- The ligand kind type. -/
  ligandKind : Type
  /-- The fragment identifier type. -/
  fragmentId : Type
  /-- The fragment kind type. -/
  fragmentKind : Type
  /-- The state type. -/
  state : Type
  /-- The framework type. -/
  framework : Type
  /-- The base-name type. -/
  baseName : Type
  /-- The numbering type. -/
  numbering : Type
  /-- The locant type. -/
  locant : Type
  /-- The prefix type. -/
  prefixType : Type

variable {P : JointTypes}

/-- The actual upstream joint request at the packaged parameter types. -/
abbrev JRequest (V : Type) [DecidableEq V] [Fintype V] (P : JointTypes) : Type _ :=
  JointRequest V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state P.framework
    P.baseName P.numbering P.locant P.prefixType

/-- The actual upstream joint representation at the packaged parameter types. -/
abbrev JRepresentation (V : Type) [DecidableEq V] [Fintype V] (P : JointTypes) : Type _ :=
  JointRepresentation V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
    P.framework P.baseName P.numbering P.locant P.prefixType

/-! ## The empty optional-channel witness

The constructions in this section are existence witnesses only.  They are never used to
define the compatible-state domain. -/

/-- An `OrganicMolecularEvidence` at the supplied graph and conformation with every
optional channel genuinely absent (`none` or the empty list).  All proposition-valued
compatibility fields are vacuous at those defaults. -/
def emptyCore (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) : OrganicMolecularEvidence V where
  graph := graph
  conformation := conformation
  rationalPositions_valid := by
    intro positions present
    cases present
  electronic_unpaired := by
    intro evidence present
    cases present
  paths_graph_eq := by
    intro family present
    cases present
  paths_conformation_eq := by
    intro family present
    cases present
  bands_graph_eq := by
    intro bands present
    cases present
  bands_conformation_eq := by
    intro bands present
    cases present
  role_valid := by
    intro annotation member
    cases member
  diagram_valid := by
    intro row member
    cases member

@[simp] theorem emptyCore_graph (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).graph = graph := rfl

@[simp] theorem emptyCore_conformation (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).conformation = conformation := rfl

@[simp] theorem emptyCore_rationalPositions? (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).rationalPositions? = none := rfl

@[simp] theorem emptyCore_electronic? (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).electronic? = none := rfl

@[simp] theorem emptyCore_paths? (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).paths? = none := rfl

@[simp] theorem emptyCore_bands? (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).bands? = none := rfl

@[simp] theorem emptyCore_roles (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).roles = [] := rfl

@[simp] theorem emptyCore_diagram? (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).diagram? = none := rfl

@[simp] theorem emptyCore_diagramPartial? (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (emptyCore graph conformation).diagramPartial? = none := rfl

/-- An `OrganicSpatialMolecularEvidence` with the supplied core and an empty cell family.
All four cell-compatibility fields are vacuous over the empty list. -/
def emptySpatial (core : OrganicMolecularEvidence V) : OrganicSpatialMolecularEvidence V where
  core := core
  cells := []
  occurrence_bound := by
    intro cell member
    cases member
  anchors_mem := by
    intro cell member
    cases member
  anchor_value := by
    intro cell member
    cases member
  role_reference := by
    intro cell member
    cases member

@[simp] theorem emptySpatial_core (core : OrganicMolecularEvidence V) :
    (emptySpatial core).core = core := rfl

@[simp] theorem emptySpatial_cells (core : OrganicMolecularEvidence V) :
    (emptySpatial core).cells = [] := rfl

/-! ## The empty-source structural certificate

With every optional source channel absent, the reconstructed source is the graph encoding
at the enumeration, so its structural well-formedness is the upstream graph-encoding
theorem.  The spatial and diagram index conditions are vacuous at `none`. -/

/-- The reconstructed source of the empty core is structurally well formed. -/
theorem emptyCore_recoveredSource_structurallyWellFormed
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (recoveredSource (emptyCore graph conformation) enumeration).StructurallyWellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [recoveredSource, recoveredAcyclicSource, coreFiniteSource, emptyCore,
      OrganicFiniteSource.encode] using graph.encode_structurallyWellFormed enumeration
  · simp [recoveredSource, recoveredAcyclicSource, coreFiniteSource, emptyCore,
      OrganicFiniteSource.encode, AuthoritativeChemicalInput.SpatialIndicesWellFormed]
  · simp [recoveredSource, recoveredAcyclicSource, coreFiniteSource, emptyCore,
      OrganicFiniteSource.encode, AuthoritativeChemicalInput.DiagramIndicesWellFormed]

/-! ## Witness joint requests -/

/-- An actual `JointRequest` at the supplied policy record, enumeration, graph and
conformation, with every optional core channel absent, no spatial cells, and a supplied
ordered row list.  Used only as an existence witness. -/
def witnessJointRequestWithEntries (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType policies
      (emptyCore graph conformation) enumeration)) : JRequest V P where
  policies := policies
  spatial := emptySpatial (emptyCore graph conformation)
  enumeration := enumeration
  source_well_formed :=
    emptyCore_recoveredSource_structurallyWellFormed graph conformation enumeration
  entries := entries

/-- The witness request with an empty ordered row list. -/
abbrev witnessJointRequest (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) : JRequest V P :=
  witnessJointRequestWithEntries policies enumeration graph conformation []

@[simp] theorem witnessJointRequestWithEntries_policies (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType policies
      (emptyCore graph conformation) enumeration)) :
    (witnessJointRequestWithEntries policies enumeration graph conformation entries).policies =
      policies := rfl

@[simp] theorem witnessJointRequestWithEntries_enumeration (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType policies
      (emptyCore graph conformation) enumeration)) :
    (witnessJointRequestWithEntries policies enumeration graph conformation entries).enumeration =
      enumeration := rfl

@[simp] theorem witnessJointRequestWithEntries_entries (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType policies
      (emptyCore graph conformation) enumeration)) :
    (witnessJointRequestWithEntries policies enumeration graph conformation entries).entries =
      entries := rfl

@[simp] theorem witnessJointRequest_policies (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).policies =
      policies := rfl

@[simp] theorem witnessJointRequest_enumeration (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).enumeration =
      enumeration := rfl

@[simp] theorem witnessJointRequest_entries (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).entries = [] := rfl

@[simp] theorem witnessJointRequest_spatial (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).spatial =
      emptySpatial (emptyCore graph conformation) := rfl

@[simp] theorem witnessJointRequest_graph (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).spatial.core.graph =
      graph := rfl

@[simp] theorem witnessJointRequest_conformation (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).spatial.core.conformation =
      conformation := rfl

@[simp] theorem witnessJointRequest_cells (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).spatial.cells = [] := rfl

@[simp] theorem witnessJointRequest_rationalPositions? (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).spatial.core.rationalPositions? =
      none := rfl

@[simp] theorem witnessJointRequest_paths? (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).spatial.core.paths? =
      none := rfl

@[simp] theorem witnessJointRequest_bands? (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).spatial.core.bands? =
      none := rfl

@[simp] theorem witnessJointRequest_diagram? (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) :
    (witnessJointRequest (P := P) policies enumeration graph conformation).spatial.core.diagram? =
      none := rfl

/-! ## Optional supplied policy selection and cell-set constraints -/

/-- The optional supplied policy-selection constraint.  When `policySelection? = none` it is
vacuous; when `policySelection? = some p` it forces the policy record to be exactly `p`.

This constrains **only** the stored `JointRequest.policies` record.  It does *not* constrain
any independent authority observation, ordered authority row, or authority evidence channel,
and no result below should be read as authority-evidence compatibility.  The ordered row list
is separately shown to be unconstrained by the base domain
(`mem_jointCompatibleRequests_withEntries_iff`). -/
def PolicySelectionCompatible (policySelection? : Option AllAuthorityPolicies)
    (policies : AllAuthorityPolicies) : Prop :=
  ∀ supplied, policySelection? = some supplied → policies = supplied

/-- The optional supplied-cell-set constraint.  When `cells? = none` it is vacuous; when
`cells? = some S` it forces the cell list to belong to `S`. -/
def CellsCompatible (cells? : Option (Set (List (SpatialMolecularCell V))))
    (cells : List (SpatialMolecularCell V)) : Prop :=
  ∀ supplied, cells? = some supplied → cells ∈ supplied

@[simp] theorem policySelectionCompatible_none (policies : AllAuthorityPolicies) :
    PolicySelectionCompatible none policies := by
  intro supplied absent
  cases absent

@[simp] theorem policySelectionCompatible_some_iff (supplied policies : AllAuthorityPolicies) :
    PolicySelectionCompatible (some supplied) policies ↔ policies = supplied := by
  constructor
  · intro compatible
    exact compatible supplied rfl
  · intro equal other present
    cases present
    exact equal

@[simp] theorem cellsCompatible_none (cells : List (SpatialMolecularCell V)) :
    CellsCompatible (V := V) none cells := by
  intro supplied absent
  cases absent

@[simp] theorem cellsCompatible_some_iff (supplied : Set (List (SpatialMolecularCell V)))
    (cells : List (SpatialMolecularCell V)) :
    CellsCompatible (V := V) (some supplied) cells ↔ cells ∈ supplied := by
  constructor
  · intro compatible
    exact compatible supplied rfl
  · intro member other present
    cases present
    exact member

/-! ## The compatible-state domain over every actual joint request -/

/-- **The domain.**  All actual joint requests whose core graph is `graph`, whose core
conformation lies in `K`, whose policy record satisfies the optional policy-selection
constraint and whose cell list satisfies the optional cell-set constraint.

No other channel is constrained: the enumeration, the structural certificate, the ordered
row list, every optional core channel, every metadata channel and all cell compatibility
ties remain free.  In particular this set is not the image of a fixed default completion. -/
def jointCompatibleRequests (graph : FiniteAtomInteractionHypergraph V)
    (K : Set (MolecularConformation V))
    (policySelection? : Option AllAuthorityPolicies)
    (cells? : Option (Set (List (SpatialMolecularCell V)))) :
    Set (JRequest V P) :=
  fun request =>
    request.spatial.core.graph = graph ∧
      request.spatial.core.conformation ∈ K ∧
      PolicySelectionCompatible policySelection? request.policies ∧
      CellsCompatible cells? request.spatial.cells

/-- Exact membership in the domain.  The statement mentions only the graph, the shared
conformation and the two optional constraints. -/
@[simp] theorem mem_jointCompatibleRequests_iff
    {graph : FiniteAtomInteractionHypergraph V} {K : Set (MolecularConformation V)}
    {policySelection? : Option AllAuthorityPolicies}
    {cells? : Option (Set (List (SpatialMolecularCell V)))} {request : JRequest V P} :
    request ∈ jointCompatibleRequests (P := P) graph K policySelection? cells? ↔
      request.spatial.core.graph = graph ∧
        request.spatial.core.conformation ∈ K ∧
        PolicySelectionCompatible policySelection? request.policies ∧
        CellsCompatible cells? request.spatial.cells :=
  Iff.rfl

/-- Exact membership with both optional constraints supplied. -/
theorem mem_jointCompatibleRequests_some_both_iff
    {graph : FiniteAtomInteractionHypergraph V} {K : Set (MolecularConformation V)}
    {policies : AllAuthorityPolicies}
    {S : Set (List (SpatialMolecularCell V))} {request : JRequest V P} :
    request ∈ jointCompatibleRequests (P := P) graph K (some policies) (some S) ↔
      request.spatial.core.graph = graph ∧ request.spatial.core.conformation ∈ K ∧
        request.policies = policies ∧ request.spatial.cells ∈ S := by
  rw [mem_jointCompatibleRequests_iff]
  simp [policySelectionCompatible_some_iff, cellsCompatible_some_iff]

/-- Any request that actually satisfies the graph, coordinate, policy-selection and cell
conditions belongs to the domain. -/
theorem jointCompatibleRequests_coverage {graph : FiniteAtomInteractionHypergraph V}
    {K : Set (MolecularConformation V)} {policySelection? : Option AllAuthorityPolicies}
    {cells? : Option (Set (List (SpatialMolecularCell V)))} (request : JRequest V P)
    (graph_eq : request.spatial.core.graph = graph)
    (conformation_mem : request.spatial.core.conformation ∈ K)
    (authority : PolicySelectionCompatible policySelection? request.policies)
    (cells : CellsCompatible cells? request.spatial.cells) :
    request ∈ jointCompatibleRequests (P := P) graph K policySelection? cells? :=
  ⟨graph_eq, conformation_mem, authority, cells⟩

/-- Two requests that agree on the core graph, the shared conformation, the policy record
and the cell list are either both compatible or both incompatible, regardless of every
other channel. -/
theorem jointCompatibleRequests_other_channels_irrelevant
    {graph : FiniteAtomInteractionHypergraph V} {K : Set (MolecularConformation V)}
    {policySelection? : Option AllAuthorityPolicies}
    {cells? : Option (Set (List (SpatialMolecularCell V)))}
    {request other : JRequest V P}
    (member : request ∈ jointCompatibleRequests graph K policySelection? cells?)
    (sameGraph : other.spatial.core.graph = graph)
    (sameConformation : other.spatial.core.conformation = request.spatial.core.conformation)
    (samePolicies : other.policies = request.policies)
    (sameCells : other.spatial.cells = request.spatial.cells) :
    other ∈ jointCompatibleRequests graph K policySelection? cells? := by
  rw [mem_jointCompatibleRequests_iff] at member ⊢
  exact ⟨sameGraph, sameConformation.symm ▸ member.2.1,
    samePolicies.symm ▸ member.2.2.1, sameCells.symm ▸ member.2.2.2⟩

/-! ## The constructed empty witness belongs to the domain -/

/-- The witness request lies in the domain whenever its conformation lies in `K`; with
both optional constraints unrestricted. -/
theorem witnessJointRequest_mem (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    {graph : FiniteAtomInteractionHypergraph V}
    {K : Set (MolecularConformation V)}
    {conformation : MolecularConformation V} (member : conformation ∈ K) :
    witnessJointRequest (P := P) policies enumeration graph conformation ∈
      jointCompatibleRequests (P := P) graph K none none :=
  ⟨rfl, member, policySelectionCompatible_none policies, cellsCompatible_none _⟩

/-- The with-entries witness also lies in the unrestricted-constraint domain. -/
theorem witnessJointRequestWithEntries_mem (policies : AllAuthorityPolicies)
    (enumeration : V ≃ Fin (Fintype.card V))
    {graph : FiniteAtomInteractionHypergraph V}
    {K : Set (MolecularConformation V)}
    {conformation : MolecularConformation V} (member : conformation ∈ K)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType policies
      (emptyCore graph conformation) enumeration)) :
    witnessJointRequestWithEntries (P := P) policies enumeration graph conformation entries ∈
      jointCompatibleRequests (P := P) graph K none none :=
  ⟨rfl, member, policySelectionCompatible_none policies, cellsCompatible_none _⟩

/-! ## Conformation projection and nonemptiness -/

/-- The shared-conformation projection of a set of joint requests. -/
def jointConformationProjection (requests : Set (JRequest V P)) :
    Set (MolecularConformation V) :=
  { conformation | ∃ request ∈ requests, request.spatial.core.conformation = conformation }

@[simp] theorem mem_jointConformationProjection_iff {requests : Set (JRequest V P)}
    {conformation : MolecularConformation V} :
    conformation ∈ jointConformationProjection requests ↔
      ∃ request ∈ requests, request.spatial.core.conformation = conformation :=
  Iff.rfl

/-- **Coordinate projection.**  For unrestricted optional constraints, the core
conformation projection of the compatible-state domain is exactly `K`.

The forward direction reads the shared conformation of any member.  The reverse direction
uses the constructed empty witness: every conformation in `K` occurs as the shared
conformation of an actual joint request with absent optional channels, no cells and an
empty row list.  The witness is an existence proof only; the domain is defined over all
requests. -/
theorem conformationProjection_jointCompatibleRequests
    (policies : AllAuthorityPolicies) (graph : FiniteAtomInteractionHypergraph V)
    (K : Set (MolecularConformation V)) :
    jointConformationProjection (jointCompatibleRequests (P := P) graph K none none) = K := by
  ext conformation
  constructor
  · rintro ⟨request, member, conformationEq⟩
    rw [mem_jointCompatibleRequests_iff] at member
    rw [← conformationEq]
    exact member.2.1
  · intro member
    exact ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation,
      witnessJointRequest_mem policies (Fintype.equivFin V) member, rfl⟩

/-- **Coordinate projection under supplied constraints.**  If the supplied cell set
contains the empty cell list, then the empty witness satisfies the optional constraints
and the projection is still exactly `K`.  The condition is on the supplied constraint, not
a restriction of the domain. -/
theorem conformationProjection_jointCompatibleRequests_some
    (policies : AllAuthorityPolicies) (S : Set (List (SpatialMolecularCell V)))
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (empty_cells : [] ∈ S) :
    jointConformationProjection
        (jointCompatibleRequests (P := P) graph K (some policies) (some S)) = K := by
  ext conformation
  constructor
  · rintro ⟨request, member, conformationEq⟩
    rw [mem_jointCompatibleRequests_some_both_iff] at member
    rw [← conformationEq]
    exact member.2.1
  · intro member
    refine ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation,
      ?_, rfl⟩
    rw [mem_jointCompatibleRequests_some_both_iff]
    exact ⟨rfl, member, rfl, empty_cells⟩

/-- The unrestricted domain is nonempty exactly when `K` is nonempty. -/
theorem jointCompatibleRequests_nonempty (policies : AllAuthorityPolicies)
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V)) :
    (jointCompatibleRequests (P := P) graph K none none).Nonempty ↔ K.Nonempty := by
  constructor
  · rintro ⟨request, member⟩
    exact ⟨request.spatial.core.conformation, (mem_jointCompatibleRequests_iff.mp member).2.1⟩
  · rintro ⟨conformation, member⟩
    exact ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation,
      witnessJointRequest_mem policies (Fintype.equivFin V) member⟩

/-- The domain with supplied policy selection and cell set is nonempty whenever `K` is nonempty
and the empty cell list belongs to the supplied set. -/
theorem jointCompatibleRequests_some_nonempty (policies : AllAuthorityPolicies)
    (S : Set (List (SpatialMolecularCell V)))
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (nonempty : K.Nonempty) (empty_cells : [] ∈ S) :
    (jointCompatibleRequests (P := P) graph K (some policies) (some S)).Nonempty := by
  obtain ⟨conformation, member⟩ := nonempty
  refine ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation, ?_⟩
  rw [mem_jointCompatibleRequests_some_both_iff]
  exact ⟨rfl, member, rfl, empty_cells⟩

/-! ## Sparse partial observations on the joint domain -/

/-- The joint domain constrained by a sparse partial coordinate observation.  The
conformation set is the upstream `observationConformations observation`, reused verbatim. -/
def jointCompatibleRequestsOfObservation (graph : FiniteAtomInteractionHypergraph V)
    (observation : PartialCoordinateObservation V)
    (policySelection? : Option AllAuthorityPolicies)
    (cells? : Option (Set (List (SpatialMolecularCell V)))) :
    Set (JRequest V P) :=
  jointCompatibleRequests graph (observationConformations observation) policySelection? cells?

/-- Every graph together with a sparse partial observation has a nonempty compatible
joint domain. -/
theorem jointCompatibleRequests_observation_nonempty
    (policies : AllAuthorityPolicies) (graph : FiniteAtomInteractionHypergraph V)
    (observation : PartialCoordinateObservation V) :
    (jointCompatibleRequestsOfObservation (P := P) graph observation none none).Nonempty :=
  (jointCompatibleRequests_nonempty (P := P) policies graph
      (observationConformations observation)).mpr
    (observationConformations_nonempty observation)

/-- **Known-coordinate recovery.**  Every observed coordinate value is realized exactly
by the shared conformation of every member of the joint domain. -/
theorem compatibleRequest_observed_value
    {graph : FiniteAtomInteractionHypergraph V}
    {observation : PartialCoordinateObservation V}
    {policySelection? : Option AllAuthorityPolicies}
    {cells? : Option (Set (List (SpatialMolecularCell V)))} {request : JRequest V P}
    (member : request ∈ jointCompatibleRequestsOfObservation graph observation policySelection? cells?)
    {atom : V} {value : EuclideanSpace ℝ (Fin 3)} (observed : observation atom = some value) :
    request.spatial.core.conformation atom = value := by
  have conformation_mem := (mem_jointCompatibleRequests_iff.mp member).2.1
  exact conformation_mem atom value observed

/-- **Unknown-coordinate variation.**  If the observation does not mention an atom, then
every point of real three-space occurs as that atom's coordinate in some member of the
joint domain. -/
theorem compatibleRequest_unknownCoordinate_vary
    (policies : AllAuthorityPolicies) (graph : FiniteAtomInteractionHypergraph V)
    (observation : PartialCoordinateObservation V) {atom : V}
    (unknown : observation atom = none) (value : EuclideanSpace ℝ (Fin 3)) :
    ∃ request ∈ jointCompatibleRequestsOfObservation (P := P) graph observation none none,
      request.spatial.core.conformation atom = value := by
  obtain ⟨conformation, member, valueEq⟩ := unknownCoordinate_vary unknown value
  exact ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation,
    witnessJointRequest_mem policies (Fintype.equivFin V) member, by simpa using valueEq⟩

/-- **Simultaneous compatibility.**  Two sparse observations have a common member of the
joint domain exactly when they agree on their actual overlap. -/
theorem jointCompatibleRequests_inter_nonempty_iff
    (policies : AllAuthorityPolicies) (graph : FiniteAtomInteractionHypergraph V)
    (first second : PartialCoordinateObservation V) :
    ((jointCompatibleRequestsOfObservation (P := P) graph first none none) ∩
        (jointCompatibleRequestsOfObservation (P := P) graph second none none)).Nonempty ↔
      OverlapAgrees first second := by
  constructor
  · rintro ⟨request, firstMember, secondMember⟩
    have firstConformation := (mem_jointCompatibleRequests_iff.mp firstMember).2.1
    have secondConformation := (mem_jointCompatibleRequests_iff.mp secondMember).2.1
    exact (observationConformations_inter_nonempty_iff first second).mp
      ⟨request.spatial.core.conformation, firstConformation, secondConformation⟩
  · intro agrees
    obtain ⟨conformation, firstMember, secondMember⟩ :=
      (observationConformations_inter_nonempty_iff first second).mpr agrees
    refine ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation,
      ?_, ?_⟩
    · exact witnessJointRequest_mem policies (Fintype.equivFin V) firstMember
    · exact witnessJointRequest_mem policies (Fintype.equivFin V) secondMember

/-- **Simultaneous conflict.**  The joint domain intersection is empty exactly when the
two observations conflict on their actual overlap. -/
theorem jointCompatibleRequests_inter_eq_empty_iff_conflict
    (policies : AllAuthorityPolicies) (graph : FiniteAtomInteractionHypergraph V)
    (first second : PartialCoordinateObservation V) :
    (jointCompatibleRequestsOfObservation (P := P) graph first none none ∩
        jointCompatibleRequestsOfObservation (P := P) graph second none none) = ∅ ↔
      ObservationsConflict first second := by
  rw [ObservationsConflict,
    ← jointCompatibleRequests_inter_nonempty_iff policies graph first second]
  constructor
  · intro empty nonempty
    rw [empty] at nonempty
    exact Set.not_nonempty_empty nonempty
  · intro notNonempty
    rw [Set.eq_empty_iff_forall_notMem]
    intro request member
    exact notNonempty ⟨request, member⟩

/-! ## Native compatibility -/

/-- Compatibility stated directly on the upstream native representation fields:

* the canonical output graph, relabelled by the inverse of the actual atom enumeration,
  is the supplied graph;
* the canonical output conformation, reindexed in the same way, lies in `K`;
* the stored policy record satisfies the optional policy-selection constraint;
* the decoded source cell list satisfies the optional cell-set constraint.

These are exactly the fields read by `decodeJoint`; no original request is available. -/
def nativeJointCompatible (graph : FiniteAtomInteractionHypergraph V)
    (K : Set (MolecularConformation V))
    (policySelection? : Option AllAuthorityPolicies)
    (cells? : Option (Set (List (SpatialMolecularCell V))))
    (representation : JRepresentation V P) : Prop :=
  relabelGraph representation.canonical.atomEquiv.symm representation.canonical.state.graph =
      graph ∧
    MolecularConformation.reindex representation.canonical.atomEquiv.symm
        representation.canonical.state.conformation ∈ K ∧
    PolicySelectionCompatible policySelection? representation.policies ∧
    CellsCompatible cells?
      (representation.cells.map (decodeSpatialCell representation.canonical))

/-! ## Projections of `decodeJoint` -/

@[simp] theorem decodeJoint_spatial_core (representation : JRepresentation V P) :
    (decodeJoint representation).spatial.core = decodedCore representation.canonical := rfl

@[simp] theorem decodeJoint_spatial_cells (representation : JRepresentation V P) :
    (decodeJoint representation).spatial.cells =
      representation.cells.map (decodeSpatialCell representation.canonical) := rfl

/-- **Compatibility recovery through the actual decoder.**  A native representation
decodes into the compatible-state domain exactly when it is natively compatible. -/
theorem decodeJoint_mem_jointCompatibleRequests_iff
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (policySelection? : Option AllAuthorityPolicies)
    (cells? : Option (Set (List (SpatialMolecularCell V))))
    (representation : JRepresentation V P) :
    decodeJoint representation ∈ jointCompatibleRequests graph K policySelection? cells? ↔
      nativeJointCompatible graph K policySelection? cells? representation := by
  rw [mem_jointCompatibleRequests_iff, nativeJointCompatible, decodeJoint_spatial_core,
    decodeJoint_spatial_cells, decodedCore_graph, decodedCore_conformation]
  rfl

/-! ## Exact image and exact decode of all compatible joint requests -/

/-- A native representation is in canonical form when re-assembling its decoded request
returns it.  This is the exact side condition for membership in the image of
`assembleJoint`; it is not implied for an arbitrary native record. -/
def canonicalJointRepresentation (representation : JRepresentation V P) : Prop :=
  assembleJoint (decodeJoint representation) = representation

/-- **Exact image of all compatible joint requests.**  The assembled image of the entire
domain is exactly the set of canonical native representations that are natively
compatible.  Every compatible request is recovered by the upstream left inverse, and every
native member of the right-hand side is the image of its own decoded request. -/
theorem assembleJoint_image_jointCompatibleRequests
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (policySelection? : Option AllAuthorityPolicies)
    (cells? : Option (Set (List (SpatialMolecularCell V)))) :
    assembleJoint '' (jointCompatibleRequests (P := P) graph K policySelection? cells?) =
      { representation | canonicalJointRepresentation representation ∧
          nativeJointCompatible graph K policySelection? cells? representation } := by
  ext representation
  constructor
  · rintro ⟨request, member, rfl⟩
    refine ⟨?_, ?_⟩
    · show assembleJoint (decodeJoint (assembleJoint request)) = assembleJoint request
      rw [decodeJoint_assembleJoint]
    · have compatible : decodeJoint (assembleJoint request) ∈
          jointCompatibleRequests (P := P) graph K policySelection? cells? := by
        rw [decodeJoint_assembleJoint]
        exact member
      exact (decodeJoint_mem_jointCompatibleRequests_iff graph K policySelection? cells?
        (assembleJoint request)).mp compatible
  · rintro ⟨canonicalForm, nativeMember⟩
    refine ⟨decodeJoint representation, ?_, canonicalForm⟩
    exact (decodeJoint_mem_jointCompatibleRequests_iff graph K policySelection? cells?
      representation).mpr nativeMember

/-- **Exact decode of all compatible joint requests.**  Decoding the assembled image of
the whole domain recovers the domain exactly.  This reuses the upstream generic set
inverse `decodeJoint_image_assembleJoint_image`; no new inverse is introduced. -/
theorem decodeJoint_image_assembleJoint_image_jointCompatibleRequests
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (policySelection? : Option AllAuthorityPolicies)
    (cells? : Option (Set (List (SpatialMolecularCell V)))) :
    decodeJoint '' (assembleJoint ''
        (jointCompatibleRequests (P := P) graph K policySelection? cells?)) =
      jointCompatibleRequests (P := P) graph K policySelection? cells? :=
  decodeJoint_image_assembleJoint_image (jointCompatibleRequests graph K policySelection? cells?)

/-- Membership exactness at the level of a single request: the assembled image of one
compatible request lies in the assembled image of the domain exactly when the request is
compatible. -/
theorem mem_assembleJoint_image_jointCompatibleRequests_iff
    {graph : FiniteAtomInteractionHypergraph V} {K : Set (MolecularConformation V)}
    {policySelection? : Option AllAuthorityPolicies}
    {cells? : Option (Set (List (SpatialMolecularCell V)))} (request : JRequest V P) :
    assembleJoint request ∈
        assembleJoint '' (jointCompatibleRequests graph K policySelection? cells?) ↔
      request ∈ jointCompatibleRequests graph K policySelection? cells? := by
  constructor
  · rintro ⟨other, otherMember, equal⟩
    have same : other = request := assembleJoint_injective equal
    simpa [same] using otherMember
  · intro member
    exact ⟨request, member, rfl⟩

/-- Nonemptiness of the exact image of the domain. -/
theorem assembleJoint_image_jointCompatibleRequests_nonempty
    (policies : AllAuthorityPolicies) (graph : FiniteAtomInteractionHypergraph V)
    (K : Set (MolecularConformation V)) (nonempty : K.Nonempty) :
    (assembleJoint '' (jointCompatibleRequests (P := P) graph K none none)).Nonempty := by
  obtain ⟨request, member⟩ :=
    (jointCompatibleRequests_nonempty (P := P) policies graph K).mpr nonempty
  exact ⟨assembleJoint request, request, member, rfl⟩

/-! ## Supplied constraints genuinely shrink the domain -/

/-- A supplied policy-selection constraint restricts to a subset of the unrestricted domain. -/
theorem jointCompatibleRequests_some_policySelection_subset
    (supplied : AllAuthorityPolicies) (graph : FiniteAtomInteractionHypergraph V)
    (K : Set (MolecularConformation V))
    (cells? : Option (Set (List (SpatialMolecularCell V)))) :
    jointCompatibleRequests (P := P) graph K (some supplied) cells? ⊆
      jointCompatibleRequests (P := P) graph K none cells? := by
  intro request member
  rw [mem_jointCompatibleRequests_iff] at member ⊢
  exact ⟨member.1, member.2.1, policySelectionCompatible_none _, member.2.2.2⟩

/-- A supplied cell-set constraint restricts to a subset of the unrestricted domain. -/
theorem jointCompatibleRequests_some_cells_subset
    (S : Set (List (SpatialMolecularCell V)))
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (policySelection? : Option AllAuthorityPolicies) :
    jointCompatibleRequests (P := P) graph K policySelection? (some S) ⊆
      jointCompatibleRequests (P := P) graph K policySelection? none := by
  intro request member
  rw [mem_jointCompatibleRequests_iff] at member ⊢
  exact ⟨member.1, member.2.1, member.2.2.1, cellsCompatible_none _⟩

/-- **Supplied cells impose a real constraint.**  If the supplied cell set excludes the
empty cell list and `K` is nonempty, the empty-cell witness lies in the unrestricted
domain but not in the domain constrained by `S`.  In particular the constrained domain is
strictly smaller, and the full projection `K` is not asserted for such an `S`. -/
theorem jointCompatibleRequests_some_cells_strict
    (policies : AllAuthorityPolicies) (S : Set (List (SpatialMolecularCell V)))
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (not_empty_mem : [] ∉ S) (nonempty : K.Nonempty) :
    jointCompatibleRequests (P := P) graph K none (some S) ⊆
        jointCompatibleRequests (P := P) graph K none none ∧
      ∃ request ∈ jointCompatibleRequests (P := P) graph K none none,
        request ∉ jointCompatibleRequests (P := P) graph K none (some S) := by
  obtain ⟨conformation, conformation_mem⟩ := nonempty
  refine ⟨jointCompatibleRequests_some_cells_subset S graph K none, ?_⟩
  refine ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation,
    witnessJointRequest_mem policies (Fintype.equivFin V) conformation_mem, ?_⟩
  intro member
  rw [mem_jointCompatibleRequests_iff] at member
  exact not_empty_mem ((cellsCompatible_some_iff S []).mp member.2.2.2)

/-- **Supplied policy selection imposes a real constraint** (and only on the policy record).
If the supplied policy record differs from the witness policy and `K` is nonempty, the
witness lies in the unrestricted domain but not in the domain constrained by the supplied
record.  This is a policy-record restriction, not authority-evidence compatibility. -/
theorem jointCompatibleRequests_some_policySelection_strict
    (policies supplied : AllAuthorityPolicies) (distinct : policies ≠ supplied)
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (nonempty : K.Nonempty) :
    jointCompatibleRequests (P := P) graph K (some supplied) none ⊆
        jointCompatibleRequests (P := P) graph K none none ∧
      ∃ request ∈ jointCompatibleRequests (P := P) graph K none none,
        request ∉ jointCompatibleRequests (P := P) graph K (some supplied) none := by
  obtain ⟨conformation, conformation_mem⟩ := nonempty
  refine ⟨jointCompatibleRequests_some_policySelection_subset supplied graph K none, ?_⟩
  refine ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation,
    witnessJointRequest_mem policies (Fintype.equivFin V) conformation_mem, ?_⟩
  intro member
  rw [mem_jointCompatibleRequests_iff] at member
  exact distinct ((policySelectionCompatible_some_iff supplied policies).mp member.2.2.1)

/-! ## Sharp cell-list projection

The cell-set constraint is necessary but not by itself sufficient: an arbitrary list in `S`
need not satisfy the request's own geometric compatibility fields, so this module never
asserts that the cell projection is all of `S`.  It proves the exact inclusion and the exact
empty-list case. -/

/-- The cell-list projection of a set of joint requests. -/
def jointCellsProjection (requests : Set (JRequest V P)) :
    Set (List (SpatialMolecularCell V)) :=
  { cells | ∃ request ∈ requests, request.spatial.cells = cells }

@[simp] theorem mem_jointCellsProjection_iff {requests : Set (JRequest V P)}
    {cells : List (SpatialMolecularCell V)} :
    cells ∈ jointCellsProjection requests ↔
      ∃ request ∈ requests, request.spatial.cells = cells :=
  Iff.rfl

/-- **Necessary cell-set restriction.**  Under a supplied cell set `S`, every cell list
occurring in a compatible request belongs to `S`.  No converse is claimed. -/
theorem cellsProjection_jointCompatibleRequests_subset
    (S : Set (List (SpatialMolecularCell V))) (graph : FiniteAtomInteractionHypergraph V)
    (K : Set (MolecularConformation V)) (policySelection? : Option AllAuthorityPolicies) :
    jointCellsProjection
        (jointCompatibleRequests (P := P) graph K policySelection? (some S)) ⊆ S := by
  rintro cells ⟨request, member, rfl⟩
  exact (cellsCompatible_some_iff S request.spatial.cells).mp
    (mem_jointCompatibleRequests_iff.mp member).2.2.2

/-- **Exact empty-cell case.**  The empty cell list occurs in the domain constrained by `S`
exactly when it belongs to `S`, provided `K` is nonempty.  The reverse direction uses the
constructed empty witness; this is a witness existence statement, not a restriction of the
domain. -/
theorem emptyCells_mem_jointCellsProjection_iff (policies : AllAuthorityPolicies)
    (S : Set (List (SpatialMolecularCell V)))
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (nonempty : K.Nonempty) :
    ([] : List (SpatialMolecularCell V)) ∈
        jointCellsProjection (jointCompatibleRequests (P := P) graph K none (some S)) ↔
      [] ∈ S := by
  constructor
  · intro member
    exact cellsProjection_jointCompatibleRequests_subset S graph K none member
  · intro empty_mem
    obtain ⟨conformation, conformation_mem⟩ := nonempty
    refine ⟨witnessJointRequest (P := P) policies (Fintype.equivFin V) graph conformation,
      ?_, rfl⟩
    rw [mem_jointCompatibleRequests_iff]
    exact ⟨rfl, conformation_mem, policySelectionCompatible_none policies,
      (cellsCompatible_some_iff S []).mpr empty_mem⟩

/-! ## The base domain does not constrain the ordered row list -/

/-- Replace the ordered row list of a joint request at the same policies, spatial
evidence and enumeration.  All other channels are retained literally. -/
def withEntries (request : JRequest V P)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType request.policies
      request.spatial.core request.enumeration)) : JRequest V P where
  policies := request.policies
  spatial := request.spatial
  enumeration := request.enumeration
  source_well_formed := request.source_well_formed
  entries := entries

@[simp] theorem withEntries_spatial (request : JRequest V P)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType request.policies
      request.spatial.core request.enumeration)) :
    (withEntries request entries).spatial = request.spatial := rfl

@[simp] theorem withEntries_policies (request : JRequest V P)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType request.policies
      request.spatial.core request.enumeration)) :
    (withEntries request entries).policies = request.policies := rfl

@[simp] theorem withEntries_entries (request : JRequest V P)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType request.policies
      request.spatial.core request.enumeration)) :
    (withEntries request entries).entries = entries := rfl

/-- Compatibility is unchanged by replacing the ordered row list.  Consequently the base
domain does not inspect rows; a supplied row condition is an additional constraint when a
caller imposes one.  In particular the witness's empty row list is not an absence claim
about an arbitrary compatible request. -/
theorem mem_jointCompatibleRequests_withEntries_iff
    {graph : FiniteAtomInteractionHypergraph V} {K : Set (MolecularConformation V)}
    {policySelection? : Option AllAuthorityPolicies}
    {cells? : Option (Set (List (SpatialMolecularCell V)))} (request : JRequest V P)
    (entries : List (RawEntry V P.ligandId P.ligandKind P.fragmentId P.fragmentKind P.state
      P.framework P.baseName P.numbering P.locant P.prefixType request.policies
      request.spatial.core request.enumeration)) :
    withEntries request entries ∈ jointCompatibleRequests graph K policySelection? cells? ↔
      request ∈ jointCompatibleRequests graph K policySelection? cells? := by
  rw [mem_jointCompatibleRequests_iff]
  simp [withEntries]

/-! ## A nontrivial correlated two-atom coordinate set -/

/-- The joint domain at the existing nondegenerate two-atom correlation relation: the
second atom is the first shifted by a fixed nonzero displacement.  Both marginals are all
of real three-space, so the relation is not a product constraint. -/
theorem correlated_coordinateProjection (policies : AllAuthorityPolicies) :
    jointConformationProjection
        (jointCompatibleRequests (P := P) (V := Fin 2) bondedCarbonGraph
          correlationRelation none none) = correlationRelation :=
  conformationProjection_jointCompatibleRequests (P := P) (V := Fin 2) policies
    bondedCarbonGraph correlationRelation

/-- The projected relation is genuinely correlated: both marginals are everything and the
relation is a proper subset of their product. -/
theorem correlated_coordinateProjection_nontrivial (policies : AllAuthorityPolicies) :
    jointConformationProjection
          (jointCompatibleRequests (P := P) (V := Fin 2) bondedCarbonGraph
            correlationRelation none none) = correlationRelation ∧
      correlationFirstMarginal correlationRelation = Set.univ ∧
      correlationSecondMarginal correlationRelation = Set.univ ∧
      correlationRelation ≠ correlationProduct correlationRelation :=
  ⟨correlated_coordinateProjection (P := P) policies,
    correlationFirstMarginal_eq_univ, correlationSecondMarginal_eq_univ,
    correlationRelation_ne_product⟩

/-- Every member of the correlated joint domain assigns distinct points to the two atoms. -/
theorem correlated_compatible_conformation_atoms_distinct {request : JRequest (Fin 2) P}
    (member : request ∈ jointCompatibleRequests (P := P) (V := Fin 2) bondedCarbonGraph
      correlationRelation none none) :
    request.spatial.core.conformation 0 ≠ request.spatial.core.conformation 1 :=
  correlationRelation_atoms_distinct
    ((mem_jointCompatibleRequests_iff.mp member).2.1)

/-- A concrete joint request realizing the correlated relation: the first atom is at the
origin and the second at the fixed nonzero displacement. -/
theorem correlatedRequest_mem (policies : AllAuthorityPolicies) :
    witnessJointRequest (P := P) (V := Fin 2) policies (Fintype.equivFin (Fin 2))
        bondedCarbonGraph (correlationCouple (0 : EuclideanSpace ℝ (Fin 3))) ∈
      jointCompatibleRequests (P := P) (V := Fin 2) bondedCarbonGraph
        correlationRelation none none :=
  witnessJointRequest_mem (P := P) (V := Fin 2) policies (Fintype.equivFin (Fin 2))
    (correlationCouple_mem (0 : EuclideanSpace ℝ (Fin 3)))

/-- The concrete correlated request has coordinates `0` and `correlationDisplacement`, so
the two observed atom positions are distinct. -/
theorem correlatedRequest_coordinates (policies : AllAuthorityPolicies) :
    (witnessJointRequest (P := P) (V := Fin 2) policies (Fintype.equivFin (Fin 2))
        bondedCarbonGraph (correlationCouple (0 : EuclideanSpace ℝ (Fin 3)))).spatial.core.conformation
        (0 : Fin 2) = 0 ∧
      (witnessJointRequest (P := P) (V := Fin 2) policies (Fintype.equivFin (Fin 2))
        bondedCarbonGraph (correlationCouple (0 : EuclideanSpace ℝ (Fin 3)))).spatial.core.conformation
        (1 : Fin 2) = correlationDisplacement := by
  constructor <;>
    simp [witnessJointRequest_conformation, correlationCouple_zero, correlationCouple_one]

/-- The uncorrelated constantly-zero conformation is excluded from the correlated joint
domain.  This is what makes the coordinate constraint substantive rather than a product of
two independent marginals. -/
theorem uncorrelatedRequest_not_mem (policies : AllAuthorityPolicies) :
    witnessJointRequest (P := P) (V := Fin 2) policies (Fintype.equivFin (Fin 2))
        bondedCarbonGraph correlationZero ∉
      jointCompatibleRequests (P := P) (V := Fin 2) bondedCarbonGraph
        correlationRelation none none := by
  intro member
  have conformation_mem : correlationZero ∈ correlationRelation := by
    have := (mem_jointCompatibleRequests_iff.mp member).2.1
    simpa using this
  exact correlationZero_not_mem conformation_mem

end

end OrganicStereoJointCompatibleStateCoverage
end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the decisive endpoints -/

assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.mem_jointCompatibleRequests_iff
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.witnessJointRequest_mem
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.conformationProjection_jointCompatibleRequests
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.conformationProjection_jointCompatibleRequests_some
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.jointCompatibleRequests_nonempty
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.jointCompatibleRequests_observation_nonempty
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.compatibleRequest_observed_value
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.compatibleRequest_unknownCoordinate_vary
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.jointCompatibleRequests_inter_nonempty_iff
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.jointCompatibleRequests_inter_eq_empty_iff_conflict
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.decodeJoint_mem_jointCompatibleRequests_iff
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.assembleJoint_image_jointCompatibleRequests
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.decodeJoint_image_assembleJoint_image_jointCompatibleRequests
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.mem_assembleJoint_image_jointCompatibleRequests_iff
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.assembleJoint_image_jointCompatibleRequests_nonempty
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.jointCompatibleRequests_some_cells_strict
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.jointCompatibleRequests_some_policySelection_strict
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.cellsProjection_jointCompatibleRequests_subset
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.emptyCells_mem_jointCellsProjection_iff
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.mem_jointCompatibleRequests_withEntries_iff
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.correlated_coordinateProjection
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.correlated_coordinateProjection_nontrivial
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.correlated_compatible_conformation_atoms_distinct
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.correlatedRequest_mem
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.correlatedRequest_coordinates
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointCompatibleStateCoverage.uncorrelatedRequest_not_mem
