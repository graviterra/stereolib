import TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Exact admission of the reconstructed common source

`JointRequest.source_well_formed` is a certificate of
`(recoveredSource spatial.core enumeration).StructurallyWellFormed`.  This module identifies the
*exact* source-level condition that this certificate demands, proves that no other condition is
hidden in it, and derives the certificate from actual native core data without assuming the
certificate itself.

The reconstructed common source is

`recoveredSource core enumeration = (coreFiniteSource core).encode enumeration`

(`OrganicStereoAllAuthorityEntries.recoveredSource`, unfolding through
`OrganicStereoAuthorityMixedSourceAssembly.recoveredAcyclicSource` and `coreFiniteSource`), and
`OrganicFiniteSource.encode` sets

* `molecule := core.graph.encode enumeration`,
* `spatial? := OrganicFiniteSource.encodeSpatial? enumeration core.rationalPositions?`,
* `diagram? := core.diagram?.map (OrganicDiagramSource.encodeDiagram enumeration)`.

The structural certificate is the conjunction of three predicates:

* `molecule.StructurallyWellFormed` — holds for *every* finite graph and enumeration
  (`FiniteAtomInteractionHypergraph.encode_structurallyWellFormed`);
* `SpatialIndicesWellFormed` — holds whenever the spatial channel is the materialisation of an
  optional total coordinate function (`spatialEvidenceFits_encodeSpatial?`);
* `DiagramIndicesWellFormed` — positions length and atom-configuration indices are automatic, so
  the only residual obligation is that every supplied drawing bond has distinct endpoints
  (`OrganicDiagramSource.EndpointDistinct`).

## Results

`OrganicFiniteSource.encode_structurallyWellFormed_iff` and its core corollary
`recoveredSource_structurallyWellFormed_iff_diagramEndpointDistinct` are exact
necessary-and-sufficient characterisations: the reconstructed source is structurally well formed
**iff** every supplied native drawing diagram is endpoint-distinct.  No other condition on the
core — in particular no condition on the interaction graph, the conformations, the electronic,
path or band channels, the role ledger, the incidence ledger, or the rational coordinate
function — appears.

Consequently the certificate is discharged from a drawing-free core
(`recoveredSource_structurallyWellFormed_of_diagram_none`) or from a proper native diagram
(`recoveredSource_structurallyWellFormed_of_diagram_some`) without passing
`StructurallyWellFormed` itself.  `jointRequestOfDiagramEndpointDistinct` and
`jointRequestOfDrawingFree` build an actual `JointRequest` from exactly that data, and
`jointRequest_diagramEndpointDistinct` records that any existing `JointRequest` certifies the
same condition.

The sharpness of the hypothesis is shown by a concrete native self-loop drawing on two atoms:
`NativeSelfLoopCounterexample.selfLoopCore` has a structurally well-formed molecule and a fitting
spatial channel but a drawing bond `0 → 0`, so its reconstructed source is *not* structurally
well formed.  This is a statement about the actual native source data, not a claim that some
legacy raw state is unsupported merely because the joint certificate excludes it.
-/

namespace TetraStereo.OneCenter

open OrganicStereoAllAuthorityEntries
open OrganicStereoAuthorityMixedSourceAssembly
open OrganicStereoJointAuthorityCellAssembly
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoNativeP94SourceContext
open OrganicStereoSpatialSupportMolecularAssembly

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The native drawing condition -/

/-- The source-level drawing condition of a finite source: every supplied diagram has distinct
bond endpoints.  This is exactly the `NativeSourceContext.diagramEndpointDistinct` obligation,
stated on an `OrganicFiniteSource` (whose only drawing channel is `diagram?`). -/
def OrganicFiniteSource.diagramEndpointDistinct (source : OrganicFiniteSource V) : Prop :=
  ∀ diagram, source.diagram? = some diagram → diagram.EndpointDistinct

namespace OrganicStereoMolecularEvidenceAssembly

namespace OrganicMolecularEvidence

/-- The same drawing condition on an independent molecular core.  The core stores exactly one
optional native drawing annotation, so this is the minimal actual core datum that the structural
certificate of `recoveredSource core enumeration` consumes. -/
def diagramEndpointDistinct {V : Type} [DecidableEq V] [Fintype V]
    (core : OrganicMolecularEvidence V) : Prop :=
  ∀ diagram, core.diagram? = some diagram → diagram.EndpointDistinct

end OrganicMolecularEvidence

end OrganicStereoMolecularEvidenceAssembly

/-! ## Exact characterisation at the finite-source level -/

/-- **Exact necessary-and-sufficient characterisation.**  The authoritative input encoded from a
finite source is structurally well formed exactly when every supplied native diagram has distinct
bond endpoints.

The three conjuncts of `AuthoritativeChemicalInput.StructurallyWellFormed` are discharged as
follows:

* the molecule conjunct is the graph encoding theorem for every finite graph;
* the spatial conjunct is the list-length fit of `encodeSpatial?`;
* the diagram conjunct reduces to endpoint distinctness because `encodeBond` maps two atom labels
  to two `Fin` indices injectively, while in-range bounds and the parity-annotation bounds hold
  automatically. -/
theorem OrganicFiniteSource.encode_structurallyWellFormed_iff
    (source : OrganicFiniteSource V) (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encode enumeration).StructurallyWellFormed ↔
      source.diagramEndpointDistinct := by
  constructor
  · rintro wellFormed diagram observed
    intro bond member
    have diagramObserved : (source.encode enumeration).diagram? =
        some (OrganicDiagramSource.encodeDiagram enumeration diagram) := by
      simp [OrganicFiniteSource.encode, observed]
    have bounds := diagramBondBounds_of_wellFormed (source.encode enumeration) wellFormed.2.2
      (OrganicDiagramSource.encodeDiagram enumeration diagram) diagramObserved
      (OrganicDiagramSource.encodeBond enumeration bond) (by
        rw [OrganicDiagramSource.encodeDiagram_bonds]
        exact List.mem_map.mpr ⟨bond, member, rfl⟩)
    intro equal
    exact bounds.2.2 (by simp [OrganicDiagramSource.encodeBond, equal])
  · intro distinct
    have shape : source.encode enumeration =
        encodeAuthoritativeWithDiagram source.graph enumeration source.diagram?
          (OrganicFiniteSource.encodeSpatial? enumeration source.spatial?) := rfl
    rw [shape]
    exact encodeAuthoritativeWithDiagram_structurallyWellFormed source.graph enumeration
      source.diagram? (OrganicFiniteSource.encodeSpatial? enumeration source.spatial?)
      (spatialEvidenceFits_encodeSpatial? enumeration source.spatial?) distinct

/-! ## Exact characterisation of the reconstructed common source -/

/-- **Exact necessary-and-sufficient characterisation for the common source.**  The structural
certificate consumed by every P-93 authority codec — and stored by `JointRequest` — holds exactly
when the actual native core's optional drawing annotation is endpoint-distinct.  No further
condition on the graph, conformation, coordinate, electronic, path, band, role or incidence data is
imposed. -/
theorem recoveredSource_structurallyWellFormed_iff_diagramEndpointDistinct
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V)) :
    (recoveredSource core enumeration).StructurallyWellFormed ↔
      core.diagramEndpointDistinct :=
  OrganicFiniteSource.encode_structurallyWellFormed_iff (coreFiniteSource core) enumeration

/-- The certificate is *derived* from the native drawing condition.  This direction constructs the
certificate; it never assumes `StructurallyWellFormed` itself. -/
theorem recoveredSource_structurallyWellFormed_of_diagramEndpointDistinct
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V))
    (distinct : core.diagramEndpointDistinct) :
    (recoveredSource core enumeration).StructurallyWellFormed :=
  (recoveredSource_structurallyWellFormed_iff_diagramEndpointDistinct core enumeration).mpr distinct

/-! ## Drawing-free and proper native diagrams -/

/-- **Drawing-free cores are always admitted.**  When the native drawing channel is absent, the
reconstructed common source is structurally well formed with no further hypothesis. -/
theorem recoveredSource_structurallyWellFormed_of_diagram_none
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V))
    (absent : core.diagram? = none) :
    (recoveredSource core enumeration).StructurallyWellFormed := by
  apply recoveredSource_structurallyWellFormed_of_diagramEndpointDistinct
  show ∀ diagram, core.diagram? = some diagram → diagram.EndpointDistinct
  intro diagram observed
  rw [absent] at observed
  cases observed

/-- **Proper native diagrams are admitted.**  A present drawing annotation whose bonds all have
distinct endpoints yields the structural certificate.  The bond *style*, *scope* and atom-parity
annotations are unrestricted, as are all other optional core channels. -/
theorem recoveredSource_structurallyWellFormed_of_diagram_some
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V))
    (diagram : OrganicDiagramSource V) (observed : core.diagram? = some diagram)
    (distinct : diagram.EndpointDistinct) :
    (recoveredSource core enumeration).StructurallyWellFormed := by
  apply recoveredSource_structurallyWellFormed_of_diagramEndpointDistinct
  show ∀ other, core.diagram? = some other → other.EndpointDistinct
  intro other otherObserved
  rw [observed] at otherObserved
  cases otherObserved
  exact distinct

/-- The certificate direction of the exact characterisation: a structurally well-formed
reconstructed source certifies that every supplied native diagram is endpoint-distinct. -/
theorem diagramEndpointDistinct_of_recoveredSource_structurallyWellFormed
    (core : OrganicMolecularEvidence V) (enumeration : V ≃ Fin (Fintype.card V))
    (wellFormed : (recoveredSource core enumeration).StructurallyWellFormed) :
    core.diagramEndpointDistinct :=
  (recoveredSource_structurallyWellFormed_iff_diagramEndpointDistinct core enumeration).mp
    wellFormed

variable {LigandId LigandKind FragmentId FragmentKind : Type}
variable {State Framework : Type}
variable {BaseName Numbering Locant Prefix : Type}

/-! ## The condition theorem for the joint request -/

/-- **What every joint request certifies.**  The structural certificate stored by any
`JointRequest` implies the native core's drawing endpoint-distinctness condition.  This is the
necessary half of the joint-level characterisation. -/
theorem jointRequest_diagramEndpointDistinct
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    request.spatial.core.diagramEndpointDistinct :=
  diagramEndpointDistinct_of_recoveredSource_structurallyWellFormed
    request.spatial.core request.enumeration request.source_well_formed

/-- **Discharging `JointRequest.source_well_formed`.**  An actual joint request is built from
minimal native core data: the core's drawing endpoint distinctness.  The structural certificate is
derived by the exact characterisation, not supplied by the caller. -/
def jointRequestOfDiagramEndpointDistinct
    (policies : AllAuthorityPolicies)
    (spatial : OrganicSpatialMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (distinct : spatial.core.diagramEndpointDistinct)
    (entries : List (RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies spatial.core enumeration)) :
    JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix where
  policies := policies
  spatial := spatial
  enumeration := enumeration
  source_well_formed :=
    recoveredSource_structurallyWellFormed_of_diagramEndpointDistinct
      spatial.core enumeration distinct
  entries := entries

/-- **Discharging `JointRequest.source_well_formed` for a drawing-free core.**  No drawing
condition is required when the native drawing channel is absent. -/
def jointRequestOfDrawingFree
    (policies : AllAuthorityPolicies)
    (spatial : OrganicSpatialMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (absent : spatial.core.diagram? = none)
    (entries : List (RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies spatial.core enumeration)) :
    JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix where
  policies := policies
  spatial := spatial
  enumeration := enumeration
  source_well_formed :=
    recoveredSource_structurallyWellFormed_of_diagram_none spatial.core enumeration absent
  entries := entries

/-- Both discharging constructors preserve the supplied enumeration definitionally. -/
@[simp] theorem jointRequestOfDiagramEndpointDistinct_enumeration
    (policies : AllAuthorityPolicies)
    (spatial : OrganicSpatialMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (distinct : spatial.core.diagramEndpointDistinct)
    (entries : List (RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies spatial.core enumeration)) :
    (jointRequestOfDiagramEndpointDistinct policies spatial enumeration distinct entries).enumeration =
      enumeration := rfl

/-- The drawing-free constructor preserves the supplied core definitionally. -/
@[simp] theorem jointRequestOfDrawingFree_spatial
    (policies : AllAuthorityPolicies)
    (spatial : OrganicSpatialMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (absent : spatial.core.diagram? = none)
    (entries : List (RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies spatial.core enumeration)) :
    (jointRequestOfDrawingFree policies spatial enumeration absent entries).spatial = spatial := rfl

/-! ## Concrete native self-loop counterexample

A drawing bond whose two endpoints are the same atom is representable in the source vocabulary.
The example below is a *native* source (a two-atom graph, an actual `OrganicDiagramSource`, and an
actual core), not a legacy raw state.  It shows that endpoint distinctness cannot be dropped from
the characterisation: the molecule conjunct and the spatial conjunct both hold, and only the
diagram conjunct fails. -/

namespace NativeSelfLoopCounterexample

/-- One carbon atom record, used for both atoms of the two-atom source. -/
def carbonAtom : SemanticAtom where
  element := ⟨6, by decide, by decide⟩

/-- A two-atom source graph with no interactions. -/
def selfLoopGraph : FiniteAtomInteractionHypergraph (Fin 2) where
  atomData := fun _ => carbonAtom
  interactions := []
  arity_ge_two := by intro edge member; simp at member
  participants_nodup := by intro edge member; simp at member

/-- The native drawing bond `0 → 0`: the self-loop. -/
def selfLoopBond : SourceDiagramBond (Fin 2) where
  source := 0
  target := 0
  style := .plain

/-- The native drawing annotation containing exactly the self-loop bond. -/
def selfLoopDiagram : OrganicDiagramSource (Fin 2) where
  bonds := [selfLoopBond]

/-- An actual independent molecular core whose only drawing bond is a self-loop. -/
def selfLoopCore : OrganicMolecularEvidence (Fin 2) where
  graph := selfLoopGraph
  conformation := fun _ => 0
  diagram? := some selfLoopDiagram
  rationalPositions_valid := by intro positions present; cases present
  electronic_unpaired := by intro evidence present; cases present
  paths_graph_eq := by intro family present; cases present
  paths_conformation_eq := by intro family present; cases present
  bands_graph_eq := by intro bands present; cases present
  bands_conformation_eq := by intro bands present; cases present
  role_valid := by intro annotation member; simp at member
  diagram_valid := by intro row member; simp at member

/-- The canonical enumeration of the two labelled atoms. -/
def selfLoopEnumeration : Fin 2 ≃ Fin (Fintype.card (Fin 2)) := identityEnumeration 2

theorem selfLoopBond_mem : selfLoopBond ∈ selfLoopDiagram.bonds := by
  simp [selfLoopDiagram]

/-- The native drawing condition fails for the self-loop core. -/
theorem selfLoopCore_not_diagramEndpointDistinct :
    ¬ selfLoopCore.diagramEndpointDistinct := by
  intro distinct
  exact distinct selfLoopDiagram rfl selfLoopBond selfLoopBond_mem rfl

/-- The reconstructed common source of the self-loop core is not structurally well formed. -/
theorem selfLoopCore_not_structurallyWellFormed :
    ¬ (recoveredSource selfLoopCore selfLoopEnumeration).StructurallyWellFormed :=
  fun wellFormed => selfLoopCore_not_diagramEndpointDistinct
    ((recoveredSource_structurallyWellFormed_iff_diagramEndpointDistinct
      selfLoopCore selfLoopEnumeration).mp wellFormed)

/-- The molecule conjunct of the failing certificate nevertheless holds: the graph encoding is
structurally well formed for every finite graph. -/
theorem selfLoopCore_molecule_structurallyWellFormed :
    (recoveredSource selfLoopCore selfLoopEnumeration).molecule.StructurallyWellFormed := by
  change (selfLoopGraph.encode selfLoopEnumeration).StructurallyWellFormed
  exact selfLoopGraph.encode_structurallyWellFormed selfLoopEnumeration

/-- The spatial conjunct of the failing certificate holds: the coordinate channel is absent. -/
theorem selfLoopCore_spatialIndicesWellFormed :
    (recoveredSource selfLoopCore selfLoopEnumeration).SpatialIndicesWellFormed := by
  simp [recoveredSource, recoveredAcyclicSource, coreFiniteSource, OrganicFiniteSource.encode,
    selfLoopCore, AuthoritativeChemicalInput.SpatialIndicesWellFormed]

/-- Exactly the diagram conjunct fails.  Together with the two preceding theorems this shows that
the endpoint-distinctness hypothesis is sharp: it is the only residual obligation. -/
theorem selfLoopCore_diagramIndices_not_wellFormed :
    ¬ (recoveredSource selfLoopCore selfLoopEnumeration).DiagramIndicesWellFormed := by
  intro diagramWellFormed
  exact selfLoopCore_not_structurallyWellFormed
    ⟨selfLoopCore_molecule_structurallyWellFormed, selfLoopCore_spatialIndicesWellFormed,
      diagramWellFormed⟩

/-- The self-loop survives the encoding as a literally equal encoded endpoint pair. -/
theorem selfLoopCore_recovered_diagram_has_selfLoop :
    (OrganicDiagramSource.encodeDiagram selfLoopEnumeration selfLoopDiagram).bonds =
        [OrganicDiagramSource.encodeBond selfLoopEnumeration selfLoopBond] ∧
      (OrganicDiagramSource.encodeBond selfLoopEnumeration selfLoopBond).source =
        (OrganicDiagramSource.encodeBond selfLoopEnumeration selfLoopBond).target := by
  constructor
  · simp [selfLoopDiagram]
  · simp [OrganicDiagramSource.encodeBond, selfLoopBond]

end NativeSelfLoopCounterexample

end

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the decisive endpoints

Any compiler-trust, `sorryAx`, or project axiom in these closures is rejected at build time.  The
two characterisations are guarded as the actual general theorems: the finite-source iff and its
reconstructed-core corollary, together with the derived admission theorems, the joint-level
necessity theorem, and the self-loop sharpness result. -/

assert_kernel_only TetraStereo.OneCenter.OrganicFiniteSource.encode_structurallyWellFormed_iff
assert_kernel_only TetraStereo.OneCenter.recoveredSource_structurallyWellFormed_iff_diagramEndpointDistinct
assert_kernel_only TetraStereo.OneCenter.recoveredSource_structurallyWellFormed_of_diagramEndpointDistinct
assert_kernel_only TetraStereo.OneCenter.recoveredSource_structurallyWellFormed_of_diagram_none
assert_kernel_only TetraStereo.OneCenter.recoveredSource_structurallyWellFormed_of_diagram_some
assert_kernel_only TetraStereo.OneCenter.diagramEndpointDistinct_of_recoveredSource_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.jointRequest_diagramEndpointDistinct
assert_kernel_only TetraStereo.OneCenter.NativeSelfLoopCounterexample.selfLoopCore_not_diagramEndpointDistinct
assert_kernel_only TetraStereo.OneCenter.NativeSelfLoopCounterexample.selfLoopCore_not_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.NativeSelfLoopCounterexample.selfLoopCore_diagramIndices_not_wellFormed
