import TetraStereo.OneCenter.OrganicStereoAuthoritativeSourceBridge
import TetraStereo.OneCenter.OrganicStereoJointCoreEncoding
import TetraStereo.OneCenter.OrganicStereoP94AuthorityObservationIngress

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Native P-94 source context

The accepted mixed assembly keeps a whole `CertifiedAuthoritativeChemicalInput` next to every
encoded P-94 authority observation.  This module removes that escape for the final native
assembly.  The only atom source is the shared finite graph
`graph : FiniteAtomInteractionHypergraph V` together with its explicit enumeration
`V ≃ Fin (Fintype.card V)`.  A `NativeSourceContext` stores exactly:

* the optional native rational coordinate function,
* the optional native drawing annotation, and
* the proposition that the reconstructed drawing has no self-loop.

`decodeSourceContext` reconstructs the certified source from that context: its molecule is exactly
`graph.encode enumeration`, its spatial channel is the materialisation of the native coordinates,
and its drawing channel is the native drawing mapping.  Its structural certificate is derived, not
stored.  `decode_encodeSourceContext` proves that every certified source tied to the shared graph
is recovered exactly, so the context is an exact codec for the source.

`NativeAuthorityObservation` then pairs such a context with an `EncodedP94AuthorityObservation`
*reindexed onto the reconstructed source*, and `decodeNativeAuthorityObservation` returns the
actual full `P94AuthorityObservation` together with the reconstructed certified source and its
validity proof.  The observation geometry is never identified with a common physical core
geometry; only the atom-index identification is shared, exactly as in the accepted mixed
assembly.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoNativeP94SourceContext

open OrganicStereoOrderedObservationFamily
open OrganicStereoP94CompleteEvidenceIngress
open OrganicStereoP94AuthorityObservationIngress
open BlueBookP94

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Reused list helpers -/

/-- Recover a list from a function over an index type of the same length.  This is the local copy
of the bridge's private length-cast form of `List.ofFn_get` (the original is private to
`OrganicStereoAuthoritativeSourceBridge`). -/
private theorem ofFn_eq_list_of_get {α : Type*} {m : ℕ} {l : List α} (hlen : m = l.length)
    (f : Fin m → α)
    (h : ∀ index : Fin m, f index = l.get (Fin.cast hlen index)) :
    List.ofFn f = l := by
  rw [List.ofFn_congr hlen]
  have hfun : (fun index : Fin l.length => f (Fin.cast hlen.symm index)) =
      (fun index : Fin l.length => l.get index) := by
    funext index
    have hcast : Fin.cast hlen (Fin.cast hlen.symm index) = index := Fin.ext rfl
    rw [← hcast]
    exact h (Fin.cast hlen.symm index)
  rw [hfun]
  exact List.ofFn_get l

/-- `List.get` only depends on the underlying natural value of its index. -/
private theorem list_get_congr_val {α : Type*} {l : List α} {first second : Fin l.length}
    (h : first.val = second.val) : l.get first = l.get second := by
  rw [Fin.ext h]

/-! ## The native spatial channel -/

/-- The native coordinate function induced by a stored spatial configuration.  The length proof
is exactly the structural-certificate fact, transported to the shared atom cardinality. -/
def spatialAt (enumeration : V ≃ Fin (Fintype.card V)) (spatial : SpatialConfiguration)
    (fits : spatial.positions.length = Fintype.card V) : V → CartesianPoint3 :=
  fun atom => spatial.positions.get
    ⟨(enumeration atom).val, by rw [fits]; exact (enumeration atom).isLt⟩

/-- Materialising the native coordinate function in enumeration order recovers the exact stored
list. -/
theorem ofFn_spatialAt (enumeration : V ≃ Fin (Fintype.card V))
    (spatial : SpatialConfiguration) (fits : spatial.positions.length = Fintype.card V) :
    List.ofFn (fun index : Fin (Fintype.card V) =>
        spatialAt enumeration spatial fits (enumeration.symm index)) = spatial.positions := by
  apply ofFn_eq_list_of_get (m := Fintype.card V) (l := spatial.positions) fits.symm
  intro index
  apply list_get_congr_val
  simp

/-- Encoding a present native coordinate function returns the exact stored configuration. -/
theorem encodeSpatial?_spatialAt (enumeration : V ≃ Fin (Fintype.card V))
    (spatial : SpatialConfiguration) (fits : spatial.positions.length = Fintype.card V) :
    OrganicFiniteSource.encodeSpatial? enumeration
        (some (spatialAt enumeration spatial fits)) = some spatial := by
  obtain ⟨positions⟩ := spatial
  simp only [OrganicFiniteSource.encodeSpatial?_some, Option.some.injEq]
  exact congrArg SpatialConfiguration.mk (ofFn_spatialAt enumeration ⟨positions⟩ fits)

/-- The atom count of any source tied to the shared graph encoding is the native cardinality. -/
theorem atomCount_eq_of_graph_eq (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    source.input.molecule.atomCount = Fintype.card V := by
  rw [graph_eq]
  exact graph.encode_atomCount enumeration

/-- The native coordinate channel induced by a certified source.  Absence stays absent; presence
is exactly the stored list, read at native atoms, with no added length restriction. -/
def nativeSpatialOfSource (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    Option (V → CartesianPoint3) :=
  match h : source.input.spatial? with
  | none => none
  | some spatial =>
      some (spatialAt enumeration spatial (by
        rw [spatialFits_of_wf source.input source.structurallyWellFormed.2.1 spatial h,
          atomCount_eq_of_graph_eq graph enumeration source graph_eq]))

/-- The native coordinate channel encodes back to the exact stored spatial channel. -/
theorem encodeSpatial?_nativeSpatialOfSource (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    OrganicFiniteSource.encodeSpatial? enumeration
        (nativeSpatialOfSource graph enumeration source graph_eq) = source.input.spatial? := by
  simp only [nativeSpatialOfSource]
  split
  · rename_i h
    simp only [OrganicFiniteSource.encodeSpatial?_none, h]
  · rename_i spatial h
    exact (encodeSpatial?_spatialAt enumeration spatial _).trans h.symm

/-! ## The native drawing channel -/

/-- One native drawing bond: the two integer endpoints are read back through the enumeration and
every annotation field is copied verbatim. -/
def bondAt (enumeration : V ≃ Fin (Fintype.card V)) (bond : DiagramBond)
    (sourceBound : bond.source < Fintype.card V) (targetBound : bond.target < Fintype.card V) :
    SourceDiagramBond V where
  source := enumeration.symm ⟨bond.source, sourceBound⟩
  target := enumeration.symm ⟨bond.target, targetBound⟩
  style := bond.style
  scope := bond.scope

/-- Encoding a native bond returns the exact stored drawing bond, in the written order. -/
theorem encodeBond_bondAt (enumeration : V ≃ Fin (Fintype.card V)) (bond : DiagramBond)
    (sourceBound : bond.source < Fintype.card V) (targetBound : bond.target < Fintype.card V) :
    OrganicDiagramSource.encodeBond enumeration
        (bondAt enumeration bond sourceBound targetBound) = bond := by
  cases bond with
  | mk source target style scope =>
      simp [bondAt, OrganicDiagramSource.encodeBond]

/-- One native atom-parity annotation: the atom reference is read back through the enumeration
and the parity token and scope are copied syntactically. -/
def atomConfigurationAt (enumeration : V ≃ Fin (Fintype.card V))
    (configuration : DiagramAtomConfiguration) (bound : configuration.atom < Fintype.card V) :
    SourceDiagramAtom V where
  atom := enumeration.symm ⟨configuration.atom, bound⟩
  parity := configuration.parity
  scope := configuration.scope

/-- Encoding a native atom-parity annotation returns the exact stored annotation. -/
theorem encodeAtomConfiguration_atomConfigurationAt
    (enumeration : V ≃ Fin (Fintype.card V)) (configuration : DiagramAtomConfiguration)
    (bound : configuration.atom < Fintype.card V) :
    OrganicDiagramSource.encodeAtomConfiguration enumeration
        (atomConfigurationAt enumeration configuration bound) = configuration := by
  cases configuration with
  | mk atom parity scope =>
      simp [atomConfigurationAt, OrganicDiagramSource.encodeAtomConfiguration]

/-- The native drawing annotation induced by one stored `DiagramConfiguration`.  The positions
channel is all-or-nothing; the ordered bond and parity lists are retained with their exact order
and multiplicity. -/
def diagramAt (enumeration : V ≃ Fin (Fintype.card V)) (diagram : DiagramConfiguration)
    (positionsFits : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = Fintype.card V)
    (bondBounds : ∀ bond ∈ diagram.bonds,
      bond.source < Fintype.card V ∧ bond.target < Fintype.card V ∧ bond.source ≠ bond.target)
    (configurationBound : ∀ configuration ∈ diagram.atomConfigurations,
      configuration.atom < Fintype.card V) : OrganicDiagramSource V where
  positions? :=
    match h : diagram.atomPositions? with
    | none => none
    | some positions =>
        some fun atom => positions.get ⟨(enumeration atom).val, by
          rw [positionsFits positions h]
          exact (enumeration atom).isLt⟩
  bonds := diagram.bonds.attach.map fun item =>
    bondAt enumeration item.1 (bondBounds item.1 item.2).1 (bondBounds item.1 item.2).2.1
  atomConfigurations := diagram.atomConfigurations.attach.map fun item =>
    atomConfigurationAt enumeration item.1 (configurationBound item.1 item.2)

/-- The positions channel of the native drawing encodes back to the exact stored positions
channel. -/
theorem encodePositions?_diagramAt (enumeration : V ≃ Fin (Fintype.card V))
    (diagram : DiagramConfiguration)
    (positionsFits : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = Fintype.card V)
    (bondBounds : ∀ bond ∈ diagram.bonds,
      bond.source < Fintype.card V ∧ bond.target < Fintype.card V ∧ bond.source ≠ bond.target)
    (configurationBound : ∀ configuration ∈ diagram.atomConfigurations,
      configuration.atom < Fintype.card V) :
    OrganicDiagramSource.encodePositions? enumeration
        (diagramAt enumeration diagram positionsFits bondBounds configurationBound).positions? =
      diagram.atomPositions? := by
  simp only [diagramAt]
  split
  · rename_i h
    rw [h, OrganicDiagramSource.encodePositions?_none]
  · rename_i positions h
    have hfits : positions.length = Fintype.card V := positionsFits positions h
    rw [OrganicDiagramSource.encodePositions?_some]
    refine (congrArg some ?_).trans h.symm
    apply ofFn_eq_list_of_get (m := Fintype.card V) (l := positions) hfits.symm
    intro index
    apply list_get_congr_val
    simp

/-- The ordered bond list of the native drawing encodes back to the exact stored bond list. -/
theorem encodeBonds_diagramAt (enumeration : V ≃ Fin (Fintype.card V))
    (diagram : DiagramConfiguration)
    (positionsFits : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = Fintype.card V)
    (bondBounds : ∀ bond ∈ diagram.bonds,
      bond.source < Fintype.card V ∧ bond.target < Fintype.card V ∧ bond.source ≠ bond.target)
    (configurationBound : ∀ configuration ∈ diagram.atomConfigurations,
      configuration.atom < Fintype.card V) :
    (diagramAt enumeration diagram positionsFits bondBounds configurationBound).bonds.map
        (OrganicDiagramSource.encodeBond enumeration) = diagram.bonds := by
  have hbonds : (diagramAt enumeration diagram positionsFits bondBounds
        configurationBound).bonds =
      diagram.bonds.attach.map (fun item =>
        bondAt enumeration item.1 (bondBounds item.1 item.2).1
          (bondBounds item.1 item.2).2.1) := rfl
  rw [hbonds, List.map_map]
  have hmap : (fun item : { bond // bond ∈ diagram.bonds } =>
      OrganicDiagramSource.encodeBond enumeration
        (bondAt enumeration item.1 (bondBounds item.1 item.2).1
          (bondBounds item.1 item.2).2.1)) = Subtype.val := by
    funext item
    exact encodeBond_bondAt enumeration item.1 _ _
  simp only [Function.comp_def]
  rw [hmap, List.attach_map_subtype_val]

/-- The ordered atom-parity list of the native drawing encodes back to the exact stored list. -/
theorem encodeAtomConfigurations_diagramAt (enumeration : V ≃ Fin (Fintype.card V))
    (diagram : DiagramConfiguration)
    (positionsFits : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = Fintype.card V)
    (bondBounds : ∀ bond ∈ diagram.bonds,
      bond.source < Fintype.card V ∧ bond.target < Fintype.card V ∧ bond.source ≠ bond.target)
    (configurationBound : ∀ configuration ∈ diagram.atomConfigurations,
      configuration.atom < Fintype.card V) :
    (diagramAt enumeration diagram positionsFits bondBounds configurationBound).atomConfigurations.map
        (OrganicDiagramSource.encodeAtomConfiguration enumeration) =
      diagram.atomConfigurations := by
  have hconfigurations : (diagramAt enumeration diagram positionsFits bondBounds
        configurationBound).atomConfigurations =
      diagram.atomConfigurations.attach.map (fun item =>
        atomConfigurationAt enumeration item.1 (configurationBound item.1 item.2)) := rfl
  rw [hconfigurations, List.map_map]
  have hmap : (fun item : { configuration // configuration ∈ diagram.atomConfigurations } =>
      OrganicDiagramSource.encodeAtomConfiguration enumeration
        (atomConfigurationAt enumeration item.1
          (configurationBound item.1 item.2))) = Subtype.val := by
    funext item
    exact encodeAtomConfiguration_atomConfigurationAt enumeration item.1 _
  simp only [Function.comp_def]
  rw [hmap, List.attach_map_subtype_val]

/-- The native drawing annotation encodes back to the exact stored drawing configuration. -/
theorem encodeDiagram_diagramAt (enumeration : V ≃ Fin (Fintype.card V))
    (diagram : DiagramConfiguration)
    (positionsFits : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = Fintype.card V)
    (bondBounds : ∀ bond ∈ diagram.bonds,
      bond.source < Fintype.card V ∧ bond.target < Fintype.card V ∧ bond.source ≠ bond.target)
    (configurationBound : ∀ configuration ∈ diagram.atomConfigurations,
      configuration.atom < Fintype.card V) :
    OrganicDiagramSource.encodeDiagram enumeration
        (diagramAt enumeration diagram positionsFits bondBounds configurationBound) = diagram := by
  cases diagram with
  | mk positions? bonds atomConfigurations =>
      simp only [OrganicDiagramSource.encodeDiagram, DiagramConfiguration.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · exact encodePositions?_diagramAt enumeration _ positionsFits bondBounds configurationBound
      · exact encodeBonds_diagramAt enumeration _ positionsFits bondBounds configurationBound
      · exact encodeAtomConfigurations_diagramAt enumeration _ positionsFits bondBounds
          configurationBound

/-- Two distinct stored endpoint integers decode to two distinct native atoms. -/
theorem bondAt_endpoint_ne (enumeration : V ≃ Fin (Fintype.card V)) (bond : DiagramBond)
    (sourceBound : bond.source < Fintype.card V) (targetBound : bond.target < Fintype.card V)
    (distinct : bond.source ≠ bond.target) :
    (bondAt enumeration bond sourceBound targetBound).source ≠
      (bondAt enumeration bond sourceBound targetBound).target := by
  intro equal
  have values := congrArg (fun atom => (enumeration atom).val) equal
  simp [bondAt] at values
  exact distinct values

/-- The native drawing annotation has no self-loop whenever the stored bond list has none. -/
theorem endpointDistinct_diagramAt (enumeration : V ≃ Fin (Fintype.card V))
    (diagram : DiagramConfiguration)
    (positionsFits : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = Fintype.card V)
    (bondBounds : ∀ bond ∈ diagram.bonds,
      bond.source < Fintype.card V ∧ bond.target < Fintype.card V ∧ bond.source ≠ bond.target)
    (configurationBound : ∀ configuration ∈ diagram.atomConfigurations,
      configuration.atom < Fintype.card V) :
    (diagramAt enumeration diagram positionsFits bondBounds configurationBound).EndpointDistinct := by
  intro bond member
  simp only [diagramAt] at member
  rcases List.mem_map.mp member with ⟨item, -, rfl⟩
  exact bondAt_endpoint_ne enumeration item.1 _ _ (bondBounds item.1 item.2).2.2

/-! ## Structural-certificate facts for the drawing channel -/

/-- A present positions channel has exactly the molecule's atom count. -/
theorem diagramPositionsFits_of_wellFormed (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) (diagram : DiagramConfiguration)
    (observed : input.diagram? = some diagram) :
    ∀ positions, diagram.atomPositions? = some positions →
      positions.length = input.molecule.atomCount := by
  unfold AuthoritativeChemicalInput.DiagramIndicesWellFormed at wellFormed
  rw [observed] at wellFormed
  intro positions hpos
  simpa [hpos] using wellFormed.1

/-- Every stored bond has distinct in-range endpoints. -/
theorem diagramBondBounds_of_wellFormed (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) (diagram : DiagramConfiguration)
    (observed : input.diagram? = some diagram) :
    ∀ bond ∈ diagram.bonds,
      bond.source < input.molecule.atomCount ∧
        bond.target < input.molecule.atomCount ∧ bond.source ≠ bond.target := by
  unfold AuthoritativeChemicalInput.DiagramIndicesWellFormed at wellFormed
  rw [observed] at wellFormed
  intro bond member
  have allTrue := List.all_eq_true.mp wellFormed.2.1 bond member
  rw [Bool.and_eq_true, Bool.and_eq_true] at allTrue
  exact ⟨of_decide_eq_true allTrue.1.1, of_decide_eq_true allTrue.1.2,
    of_decide_eq_true allTrue.2⟩

/-- Every stored atom-parity annotation names an in-range atom. -/
theorem diagramConfigurationBound_of_wellFormed (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) (diagram : DiagramConfiguration)
    (observed : input.diagram? = some diagram) :
    ∀ configuration ∈ diagram.atomConfigurations,
      configuration.atom < input.molecule.atomCount := by
  unfold AuthoritativeChemicalInput.DiagramIndicesWellFormed at wellFormed
  rw [observed] at wellFormed
  intro configuration member
  exact of_decide_eq_true (List.all_eq_true.mp wellFormed.2.2 configuration member)

/-- The native drawing annotation induced by a certified source.  Absence is preserved; when a
drawing is present its positions, bonds and parity annotations are the actual stored fields. -/
def nativeDiagramOfSource (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    Option (OrganicDiagramSource V) :=
  match h : source.input.diagram? with
  | none => none
  | some diagram =>
      some (diagramAt enumeration diagram
        (fun positions hpos => by
          rw [diagramPositionsFits_of_wellFormed source.input
              source.structurallyWellFormed.2.2 diagram h positions hpos,
            atomCount_eq_of_graph_eq graph enumeration source graph_eq])
        (fun bond hbond => by
          have bounds := diagramBondBounds_of_wellFormed source.input
            source.structurallyWellFormed.2.2 diagram h bond hbond
          simpa only [atomCount_eq_of_graph_eq graph enumeration source graph_eq] using bounds)
        (fun configuration hconfiguration => by
          have bound := diagramConfigurationBound_of_wellFormed source.input
            source.structurallyWellFormed.2.2 diagram h configuration hconfiguration
          simpa only [atomCount_eq_of_graph_eq graph enumeration source graph_eq] using bound))

/-- The native drawing annotation encodes back to the exact stored drawing channel. -/
theorem map_encodeDiagram_nativeDiagramOfSource (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    (nativeDiagramOfSource graph enumeration source graph_eq).map
        (OrganicDiagramSource.encodeDiagram enumeration) = source.input.diagram? := by
  simp only [nativeDiagramOfSource]
  split
  · rename_i h
    rw [h]
    rfl
  · rename_i diagram h
    exact (congrArg some (encodeDiagram_diagramAt enumeration diagram _ _ _)).trans h.symm

/-- The reconstructed drawing annotation satisfies the endpoint-distinctness contract. -/
theorem nativeDiagramOfSource_endpointDistinct (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    ∀ diagram, nativeDiagramOfSource graph enumeration source graph_eq = some diagram →
      diagram.EndpointDistinct := by
  intro diagram observed
  simp only [nativeDiagramOfSource] at observed
  split at observed
  · exact absurd observed (by simp)
  · rename_i sourceDiagram h
    have equal : diagramAt enumeration sourceDiagram _ _ _ = diagram :=
      Option.some.inj observed
    rw [← equal]
    exact endpointDistinct_diagramAt enumeration sourceDiagram _ _ _

/-! ## The native source context and its codec -/

/-- The source-free native context.  It stores only the optional native rational coordinate
function, the optional native drawing annotation, and the proposition that the drawing has no
self-loop. -/
structure NativeSourceContext (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) where
  /-- Native rational coordinate function; absence is preserved exactly. -/
  spatial? : Option (V → CartesianPoint3) := none
  /-- Native rational drawing annotation; absence is preserved exactly. -/
  diagram? : Option (OrganicDiagramSource V) := none
  /-- The reconstructed drawing has distinct endpoints, as required by the certified encoding. -/
  diagramEndpointDistinct : ∀ diagram, diagram? = some diagram → diagram.EndpointDistinct

namespace NativeSourceContext

variable {graph : FiniteAtomInteractionHypergraph V}
variable {enumeration : V ≃ Fin (Fintype.card V)}

/-- The shared finite source carried by a native context.  The graph is the common one; the two
optional channels are the native fields. -/
def toFiniteSource (context : NativeSourceContext graph enumeration) : OrganicFiniteSource V where
  graph := graph
  spatial? := context.spatial?
  diagram? := context.diagram?

@[simp] theorem toFiniteSource_graph (context : NativeSourceContext graph enumeration) :
    context.toFiniteSource.graph = graph := rfl

@[simp] theorem toFiniteSource_spatial? (context : NativeSourceContext graph enumeration) :
    context.toFiniteSource.spatial? = context.spatial? := rfl

@[simp] theorem toFiniteSource_diagram? (context : NativeSourceContext graph enumeration) :
    context.toFiniteSource.diagram? = context.diagram? := rfl

end NativeSourceContext

/-- Spatial evidence fits whenever the native coordinate channel is the materialisation of an
optional coordinate function. -/
theorem spatialEvidenceFits_encodeSpatial? (enumeration : V ≃ Fin (Fintype.card V))
    (spatial? : Option (V → CartesianPoint3)) :
    SpatialEvidenceFits (OrganicFiniteSource.encodeSpatial? enumeration spatial?)
      (Fintype.card V) := by
  cases spatial? with
  | none => simp [SpatialEvidenceFits, OrganicFiniteSource.encodeSpatial?]
  | some positions =>
      simp [SpatialEvidenceFits, OrganicFiniteSource.encodeSpatial?, List.length_ofFn]

/-- **Reconstruct** the certified source carried by a native context.  The molecule is the shared
graph encoding, the spatial channel is materialised from the native coordinates and the drawing
channel is the native drawing encoding.  Certification is derived, not assumed. -/
def decodeSourceContext (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (context : NativeSourceContext graph enumeration) :
    CertifiedAuthoritativeChemicalInput :=
  certifiedWithOptionalDiagram graph enumeration context.diagram?
    (OrganicFiniteSource.encodeSpatial? enumeration context.spatial?)
    (spatialEvidenceFits_encodeSpatial? enumeration context.spatial?)
    context.diagramEndpointDistinct

@[simp] theorem decodeSourceContext_molecule (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (context : NativeSourceContext graph enumeration) :
    (decodeSourceContext graph enumeration context).input.molecule =
      graph.encode enumeration := rfl

@[simp] theorem decodeSourceContext_spatial? (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (context : NativeSourceContext graph enumeration) :
    (decodeSourceContext graph enumeration context).input.spatial? =
      OrganicFiniteSource.encodeSpatial? enumeration context.spatial? := rfl

@[simp] theorem decodeSourceContext_diagram? (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (context : NativeSourceContext graph enumeration) :
    (decodeSourceContext graph enumeration context).input.diagram? =
      context.diagram?.map (OrganicDiagramSource.encodeDiagram enumeration) := rfl

/-- **Encode** a certified source tied to the shared graph.  Only the two native optional channels
and the endpoint-distinctness proposition are retained. -/
def encodeSourceContext (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    NativeSourceContext graph enumeration where
  spatial? := nativeSpatialOfSource graph enumeration source graph_eq
  diagram? := nativeDiagramOfSource graph enumeration source graph_eq
  diagramEndpointDistinct := nativeDiagramOfSource_endpointDistinct graph enumeration source graph_eq

@[simp] theorem encodeSourceContext_spatial? (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    (encodeSourceContext graph enumeration source graph_eq).spatial? =
      nativeSpatialOfSource graph enumeration source graph_eq := rfl

@[simp] theorem encodeSourceContext_diagram? (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    (encodeSourceContext graph enumeration source graph_eq).diagram? =
      nativeDiagramOfSource graph enumeration source graph_eq := rfl

/-- Equality of certified inputs follows from equality of their authoritative inputs; the
structural certificate is a proposition. -/
theorem certifiedInput_ext {first second : CertifiedAuthoritativeChemicalInput}
    (equal : first.input = second.input) : first = second := by
  obtain ⟨firstInput, firstWellFormed⟩ := first
  obtain ⟨secondInput, secondWellFormed⟩ := second
  simp only at equal
  subst equal
  rfl

/-- **Exact source reconstruction.**  Encoding a certified source into its native context and
decoding the context returns the exact certified source. -/
theorem decode_encodeSourceContext (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    decodeSourceContext graph enumeration
        (encodeSourceContext graph enumeration source graph_eq) = source := by
  apply certifiedInput_ext
  apply authoritativeInput_ext
  · exact graph_eq.symm
  · exact encodeSpatial?_nativeSpatialOfSource graph enumeration source graph_eq
  · exact map_encodeDiagram_nativeDiagramOfSource graph enumeration source graph_eq

/-! ## The derived source-atom resolver -/

/-- Atom-count agreement induced by the exact source/graph tie. -/
theorem nativeSourceAtomCount_eq (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    source.input.molecule.atomCount =
      (graph.certifiedEncoding enumeration).input.molecule.atomCount := by
  rw [graph_eq]
  rfl

/-- The genuine equivalence between the observation's source atom indices and the shared atom
labels, derived from the certified encoding equivalence and the exact source/graph equality. -/
def nativeSourceAtomEquiv (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    V ≃ SourceAtomIndex source :=
  (JointCoreEncoding.sourceAtomEquiv graph enumeration).trans
    (finCongr (nativeSourceAtomCount_eq graph enumeration source graph_eq).symm)

/-- The resolver used for source-indexed observation payloads. -/
def nativeSourceAtomResolver (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) :
    SourceAtomIndex source ≃ V :=
  (nativeSourceAtomEquiv graph enumeration source graph_eq).symm

/-- Pointwise unfolding of the resolver's inverse on the common enumeration. -/
theorem nativeSourceAtomResolver_symm_apply
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) (atom : V) :
    (nativeSourceAtomResolver graph enumeration source graph_eq).symm atom =
      finCongr (nativeSourceAtomCount_eq graph enumeration source graph_eq).symm
        (JointCoreEncoding.sourceAtomEquiv graph enumeration atom) := rfl

/-- The resolver's inverse reads the same natural number as the common enumeration, independent of
which source-indexed certified source it is derived from. -/
@[simp] theorem nativeSourceAtomResolver_symm_apply_val
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration) (atom : V) :
    ((nativeSourceAtomResolver graph enumeration source graph_eq).symm atom).val =
      (enumeration atom).val := by
  have hcast : ∀ {n m : ℕ} (h : n = m) (index : Fin n),
      ((finCongr h index : Fin m)).val = index.val := by
    intro n m h index
    cases h
    rfl
  rw [nativeSourceAtomResolver_symm_apply, hcast,
    JointCoreEncoding.sourceAtomEquiv_apply_val]

/-- Two derived resolvers read the same underlying natural number at every atom, whatever
certified sources they are indexed by.  This is the exact hypothesis needed to transport
source-indexed decoding. -/
theorem nativeSourceAtomResolver_symm_val_eq (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (first : CertifiedAuthoritativeChemicalInput)
    (firstEq : first.input.molecule = graph.encode enumeration)
    (second : CertifiedAuthoritativeChemicalInput)
    (secondEq : second.input.molecule = graph.encode enumeration) (atom : V) :
    ((nativeSourceAtomResolver graph enumeration first firstEq).symm atom).val =
      ((nativeSourceAtomResolver graph enumeration second secondEq).symm atom).val := by
  rw [nativeSourceAtomResolver_symm_apply_val, nativeSourceAtomResolver_symm_apply_val]

/-! ## Resolver invariance of the encoded evidence

Every source-indexed decoder in the accepted observation ingress reads native atoms only through
`(resolver.symm atom).val`.  The following lemmas make that dependence explicit and let the same
encoded payload be decoded against any source whose resolver reads the same natural numbers.
-/

theorem decodeIndex_congr {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (atom : V) :
    decodeIndex firstResolver atom = decodeIndex secondResolver atom := by
  simp only [decodeIndex]
  exact sameVal atom

/-- Source-level participant decoding is invariant under natural-value agreement of resolvers. -/
theorem decodeParticipant_congr {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (participant : TorsionParticipant V) :
    decodeParticipant firstResolver participant = decodeParticipant secondResolver participant := by
  cases participant <;>
    simp only [decodeParticipant, decodeIndex, sameVal]

/-- Encoded virtual-participant decoding is invariant under natural-value agreement of
resolvers. -/
theorem decodeVirtualParticipant_congr {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (participant : EncodedVirtualTorsionParticipant V) :
    decodeVirtualParticipant firstResolver participant =
      decodeVirtualParticipant secondResolver participant := by
  cases participant <;>
    simp only [decodeVirtualParticipant, decodeIndex, sameVal]

/-- Ordered atom lists are invariant under natural-value agreement of resolvers. -/
theorem decodeAtoms_congr {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (atoms : List V) :
    decodeAtoms firstResolver atoms = decodeAtoms secondResolver atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [decodeAtoms, List.map_cons, decodeIndex] at ih ⊢
      rw [sameVal atom, ih]

/-- The transported conformation unit decodes identically under matching resolvers. -/
theorem encodedConformationUnit_toUnit_congr {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (unit : EncodedConformationUnit V) :
    EncodedConformationUnit.toUnit firstResolver unit =
      EncodedConformationUnit.toUnit secondResolver unit := by
  cases unit with
  | mk kind atoms participants? =>
      simp only [EncodedConformationUnit.toUnit,
        decodeAtoms_congr firstResolver secondResolver sameVal atoms]
      cases participants? with
      | none => rfl
      | some pair =>
          rcases pair with ⟨front, rear⟩
          simp only [Option.map_some,
            decodeParticipant_congr firstResolver secondResolver sameVal front,
            decodeParticipant_congr firstResolver secondResolver sameVal rear]

/-- Torsion selection candidates decode identically under matching resolvers. -/
theorem encodedTorsionSelectionCandidate_toSource_congr
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (candidate : EncodedTorsionSelectionCandidate V) :
    EncodedTorsionSelectionCandidate.toSource firstResolver candidate =
      EncodedTorsionSelectionCandidate.toSource secondResolver candidate := by
  cases candidate with
  | mk participant ranking =>
      simp only [EncodedTorsionSelectionCandidate.toSource,
        decodeParticipant_congr firstResolver secondResolver sameVal participant]

/-- Selected torsion frames decode identically under matching resolvers. -/
theorem encodedSelectedTorsionFrame_toSource_congr
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (frame : EncodedSelectedTorsionFrame V) :
    EncodedSelectedTorsionFrame.toSource firstResolver frame =
      EncodedSelectedTorsionFrame.toSource secondResolver frame := by
  cases frame with
  | mk front rear angle =>
      simp only [EncodedSelectedTorsionFrame.toSource,
        decodeParticipant_congr firstResolver secondResolver sameVal front,
        decodeParticipant_congr firstResolver secondResolver sameVal rear]

/-- Ordered candidate lists are invariant under natural-value agreement of resolvers. -/
theorem decodeCandidates_congr {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (candidates : List (EncodedTorsionSelectionCandidate V)) :
    decodeCandidates firstResolver candidates = decodeCandidates secondResolver candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [decodeCandidates, List.map_cons] at ih ⊢
      rw [encodedTorsionSelectionCandidate_toSource_congr firstResolver secondResolver sameVal
        candidate, ih]

/-- Conformer-pair channels decode identically under matching resolvers. -/
theorem conformerPairObservation_toSource_congr {State : Type*}
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : ConformerPairObservation V State) :
    ConformerPairObservation.toSource firstResolver record =
      ConformerPairObservation.toSource secondResolver record := by
  cases record with
  | mk unit rotation firstState secondState =>
      simp only [ConformerPairObservation.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit]

/-- Torsion channels decode identically under matching resolvers. -/
theorem torsionObservation_toSource_congr {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : TorsionObservation V) :
    TorsionObservation.toSource firstResolver record =
      TorsionObservation.toSource secondResolver record := by
  cases record with
  | mk unit frame frontCandidates rearCandidates selectedFront selectedRear rotationSense =>
      simp only [TorsionObservation.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit,
        encodedSelectedTorsionFrame_toSource_congr firstResolver secondResolver sameVal frame,
        decodeCandidates_congr firstResolver secondResolver sameVal frontCandidates,
        decodeCandidates_congr firstResolver secondResolver sameVal rearCandidates,
        encodedTorsionSelectionCandidate_toSource_congr firstResolver secondResolver sameVal
          selectedFront,
        encodedTorsionSelectionCandidate_toSource_congr firstResolver secondResolver sameVal
          selectedRear]

/-- Twist channels decode identically under matching resolvers. -/
theorem twistObservation_toSource_congr {State : Type*}
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : TwistObservation V State) :
    TwistObservation.toSource firstResolver record =
      TwistObservation.toSource secondResolver record := by
  cases record with
  | mk unit rotation distinct boat chair candidate firstLeg secondLeg =>
      simp only [TwistObservation.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit]

/-- In/out sites decode identically under matching resolvers. -/
theorem encodedInOutSite_toSource_congr {Framework : Type*}
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (site : EncodedInOutSite Framework V) :
    EncodedInOutSite.toSource firstResolver site =
      EncodedInOutSite.toSource secondResolver site := by
  cases site with
  | mk framework bridgehead directedParticipant bridgeLongEnough direction =>
      simp only [EncodedInOutSite.toSource, decodeIndex]
      rw [sameVal bridgehead,
        decodeParticipant_congr firstResolver secondResolver sameVal directedParticipant]

/-- In/out channels decode identically under matching resolvers. -/
theorem inOutObservationData_toSource_congr {Framework : Type*}
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : InOutObservationData Framework V) :
    InOutObservationData.toSource firstResolver record =
      InOutObservationData.toSource secondResolver record := by
  cases record with
  | mk unit firstSite secondSite bicyclic =>
      simp only [InOutObservationData.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit,
        encodedInOutSite_toSource_congr firstResolver secondResolver sameVal firstSite,
        encodedInOutSite_toSource_congr firstResolver secondResolver sameVal secondSite]

/-- Eclipsed/staggered channels decode identically under matching resolvers. -/
theorem encodedEclipsedStaggeredObservation_toSource_congr
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : EncodedEclipsedStaggeredObservation V) :
    EncodedEclipsedStaggeredObservation.toSource firstResolver record =
      EncodedEclipsedStaggeredObservation.toSource secondResolver record := by
  cases record with
  | mk unit angle staggeredContext =>
      simp only [EncodedEclipsedStaggeredObservation.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit]

/-- Trigonal channels decode identically under matching resolvers. -/
theorem encodedTrigonalObservation_toSource_congr
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : EncodedTrigonalObservation V) :
    EncodedTrigonalObservation.toSource firstResolver record =
      EncodedTrigonalObservation.toSource secondResolver record := by
  cases record with
  | mk unit observation =>
      simp only [EncodedTrigonalObservation.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit]

/-- Conjugated-system channels decode identically under matching resolvers. -/
theorem encodedConjugatedObservation_toSource_congr
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : EncodedConjugatedObservation V) :
    EncodedConjugatedObservation.toSource firstResolver record =
      EncodedConjugatedObservation.toSource secondResolver record := by
  cases record with
  | mk unit system angle =>
      simp only [EncodedConjugatedObservation.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit]

/-- Ring-plane channels decode identically under matching resolvers. -/
theorem encodedRingPlaneObservation_toSource_congr
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : EncodedRingPlaneObservation V) :
    EncodedRingPlaneObservation.toSource firstResolver record =
      EncodedRingPlaneObservation.toSource secondResolver record := by
  cases record with
  | mk unit sides saturatedCyclic symmetricallyEquivalent carbohydrateFiveRing =>
      simp only [EncodedRingPlaneObservation.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit]

/-- Half-chair channels decode identically under matching resolvers. -/
theorem encodedHalfChairObservation_toSource_congr
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (record : EncodedHalfChairObservation V) :
    EncodedHalfChairObservation.toSource firstResolver record =
      EncodedHalfChairObservation.toSource secondResolver record := by
  cases record with
  | mk unit observation =>
      simp only [EncodedHalfChairObservation.toSource,
        encodedConformationUnit_toUnit_congr firstResolver secondResolver sameVal unit]

/-- **Resolver invariance of the whole nine-constructor evidence payload.** -/
theorem encodedConformationEvidence_toSource_congr {State Framework : Type*}
    {first second : CertifiedAuthoritativeChemicalInput}
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (evidence : EncodedConformationEvidence V State Framework) :
    OrganicStereoP94CompleteEvidenceIngress.toSource firstResolver evidence =
      OrganicStereoP94CompleteEvidenceIngress.toSource secondResolver evidence := by
  cases evidence with
  | conformer record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        conformerPairObservation_toSource_congr firstResolver secondResolver sameVal record]
  | torsion record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        torsionObservation_toSource_congr firstResolver secondResolver sameVal record]
  | eclipsedStaggered record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        encodedEclipsedStaggeredObservation_toSource_congr firstResolver secondResolver sameVal
          record]
  | trigonal record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        encodedTrigonalObservation_toSource_congr firstResolver secondResolver sameVal record]
  | conjugated record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        encodedConjugatedObservation_toSource_congr firstResolver secondResolver sameVal record]
  | ringPlane record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        encodedRingPlaneObservation_toSource_congr firstResolver secondResolver sameVal record]
  | twist record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        twistObservation_toSource_congr firstResolver secondResolver sameVal record]
  | halfChair record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        encodedHalfChairObservation_toSource_congr firstResolver secondResolver sameVal record]
  | inOut record =>
      simp only [OrganicStereoP94CompleteEvidenceIngress.toSource,
        inOutObservationData_toSource_congr firstResolver secondResolver sameVal record]

/-! ## Transport of the source-indexed certificate

Only the `unresolved` proofs of the total virtual ledger are source-indexed.  They are transported
along the exact molecule equality, and decoding after transport returns the original ledger. -/

/-- Transport one total virtual participant to an equal molecule. -/
def reseatVirtualParticipant {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule) :
    TotalVirtualTorsionParticipant first V → TotalVirtualTorsionParticipant second V
  | .native participant => .native participant
  | .unresolved participant outOfRange =>
      .unresolved participant (by
        rw [← molecule_eq]
        exact outOfRange)

/-- Transport one total virtual point. -/
def reseatVirtualPoint {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (point : TotalVirtualTorsionPoint first V) : TotalVirtualTorsionPoint second V where
  participant := reseatVirtualParticipant molecule_eq point.participant
  point := point.point

/-- Transport one total coordinate observation.  Every opaque geometric field is retained; only
the source-indexed unresolved ledger proofs move. -/
def reseatObservation {Framework : Type} {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (observation : TotalEncodedCoordinateObservation first Framework V) :
    TotalEncodedCoordinateObservation second Framework V where
  framework := observation.framework
  spatial := observation.spatial
  virtualPoints := observation.virtualPoints.map (reseatVirtualPoint molecule_eq)
  bridgehead := observation.bridgehead
  directedParticipant := observation.directedParticipant
  interior := observation.interior

/-- Transport the optional ordered certificate pair. -/
def reseatCertificate {Framework : Type} {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule) :
    Option (TotalEncodedCoordinateObservation first Framework V ×
      TotalEncodedCoordinateObservation first Framework V) →
    Option (TotalEncodedCoordinateObservation second Framework V ×
      TotalEncodedCoordinateObservation second Framework V)
  | none => none
  | some (firstObservation, secondObservation) =>
      some (reseatObservation molecule_eq firstObservation,
        reseatObservation molecule_eq secondObservation)

/-- Transported total virtual participants decode to the same virtual participant under
resolvers that read the same natural numbers. -/
theorem decodeTotalVirtualParticipant_reseat
    {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (participant : TotalVirtualTorsionParticipant first V) :
    decodeTotalVirtualParticipant secondResolver
        (reseatVirtualParticipant molecule_eq participant) =
      decodeTotalVirtualParticipant firstResolver participant := by
  cases participant with
  | native nativeParticipant =>
      exact (decodeVirtualParticipant_congr firstResolver secondResolver sameVal
        nativeParticipant).symm
  | unresolved unresolvedParticipant outOfRange => rfl

/-- Transported total virtual points decode identically. -/
theorem decodeTotalVirtualPoint_reseat
    {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (point : TotalVirtualTorsionPoint first V) :
    decodeTotalVirtualPoint secondResolver (reseatVirtualPoint molecule_eq point) =
      decodeTotalVirtualPoint firstResolver point := by
  cases point with
  | mk participant point =>
      simp only [reseatVirtualPoint, decodeTotalVirtualPoint]
      rw [decodeTotalVirtualParticipant_reseat molecule_eq firstResolver secondResolver sameVal
        participant]

/-- Transported total virtual ledgers decode order-preservingly and identically. -/
theorem decodeTotalVirtualPoints_reseat
    {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (points : List (TotalVirtualTorsionPoint first V)) :
    decodeTotalVirtualPoints secondResolver
        (points.map (reseatVirtualPoint molecule_eq)) =
      decodeTotalVirtualPoints firstResolver points := by
  induction points with
  | nil => rfl
  | cons point rest ih =>
      simp only [decodeTotalVirtualPoints, List.map_cons] at ih ⊢
      rw [decodeTotalVirtualPoint_reseat molecule_eq firstResolver secondResolver sameVal point, ih]

/-- Transported total coordinate observations decode to the same source observation.  The
observation geometry is retained verbatim; only source-indexed ledger proofs moved. -/
theorem toSource_reseat {Framework : Type}
    {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (observation : TotalEncodedCoordinateObservation first Framework V) :
    TotalEncodedCoordinateObservation.toSource secondResolver
        (reseatObservation molecule_eq observation) =
      TotalEncodedCoordinateObservation.toSource firstResolver observation := by
  cases observation with
  | mk framework spatial virtualPoints bridgehead directedParticipant interior =>
      simp only [reseatObservation, TotalEncodedCoordinateObservation.toSource,
        decodeIndex]
      rw [decodeTotalVirtualPoints_reseat molecule_eq firstResolver secondResolver sameVal
          virtualPoints,
        sameVal bridgehead,
        decodeParticipant_congr firstResolver secondResolver sameVal directedParticipant]

/-- Transported optional certificate pairs decode identically. -/
theorem decodeTotalCertificate_reseat {Framework : Type}
    {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (certificate : Option (TotalEncodedCoordinateObservation first Framework V ×
      TotalEncodedCoordinateObservation first Framework V)) :
    decodeTotalCertificate secondResolver (reseatCertificate molecule_eq certificate) =
      decodeTotalCertificate firstResolver certificate := by
  cases certificate with
  | none => rfl
  | some pair =>
      rcases pair with ⟨firstObservation, secondObservation⟩
      simp only [reseatCertificate, decodeTotalCertificate]
      rw [toSource_reseat molecule_eq firstResolver secondResolver sameVal firstObservation,
        toSource_reseat molecule_eq firstResolver secondResolver sameVal secondObservation]

/-- Equality of authority observations from their four exact fields. -/
theorem authorityObservation_ext {policy : P94AuthorityPolicy}
    {first second : P94AuthorityObservation policy}
    (molecule : first.molecule = second.molecule)
    (evidence : first.evidence = second.evidence)
    (claim : first.claim = second.claim)
    (certificate : first.inOutCertificate? = second.inOutCertificate?) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Transport the whole encoded P-94 authority observation.  The raw molecule, the conversion
proof, the nine-constructor evidence and the typed claim are carried; only the source-indexed
certificate proofs move. -/
def reseatEncodedObservation {policy : P94AuthorityPolicy}
    {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (enc : EncodedP94AuthorityObservation policy first V) :
    EncodedP94AuthorityObservation policy second V where
  molecule := enc.molecule
  converted := enc.converted.trans (congrArg some molecule_eq)
  evidence := enc.evidence
  claim := enc.claim
  inOutCertificate? := reseatCertificate molecule_eq enc.inOutCertificate?

/-- **Decoding after transport is the original full observation.**  The source-level virtual
ledger, the nine-constructor evidence and both ordered certificates are recovered exactly. -/
theorem toAuthority_reseat {policy : P94AuthorityPolicy}
    {first second : CertifiedAuthoritativeChemicalInput}
    (molecule_eq : first.input.molecule = second.input.molecule)
    (firstResolver : SourceAtomIndex first ≃ V)
    (secondResolver : SourceAtomIndex second ≃ V)
    (sameVal : ∀ atom : V, (firstResolver.symm atom).val = (secondResolver.symm atom).val)
    (enc : EncodedP94AuthorityObservation policy first V) :
    EncodedP94AuthorityObservation.toAuthority secondResolver
        (reseatEncodedObservation molecule_eq enc) =
      EncodedP94AuthorityObservation.toAuthority firstResolver enc := by
  simp only [EncodedP94AuthorityObservation.toAuthority, reseatEncodedObservation]
  apply authorityObservation_ext
  · rfl
  · exact (encodedConformationEvidence_toSource_congr firstResolver secondResolver sameVal
      enc.evidence).symm
  · rfl
  · exact decodeTotalCertificate_reseat molecule_eq firstResolver secondResolver sameVal
      enc.inOutCertificate?

/-! ## The native authority observation and its paired codec -/

/-- A native P-94 authority observation: the source-free context plus the encoded authority
payload reindexed onto the *reconstructed* certified source, together with the actual validity of
the decoded observation for that reconstructed source. -/
structure NativeAuthorityObservation (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (policy : P94AuthorityPolicy) where
  /-- The source context: native coordinates and drawing data only. -/
  context : NativeSourceContext graph enumeration
  /-- The full encoded authority payload, indexed by the reconstructed certified source. -/
  payload : EncodedP94AuthorityObservation policy
    (decodeSourceContext graph enumeration context) V
  /-- The decoded observation is valid for the reconstructed source. -/
  valid : (payload.toAuthority
    (nativeSourceAtomResolver graph enumeration
      (decodeSourceContext graph enumeration context) rfl)).ValidFor
    policy (decodeSourceContext graph enumeration context).input

/-- The reconstructed certified source of a native observation. -/
def NativeAuthorityObservation.source (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) {policy : P94AuthorityPolicy}
    (observation : NativeAuthorityObservation graph enumeration policy) :
    CertifiedAuthoritativeChemicalInput :=
  decodeSourceContext graph enumeration observation.context

/-- The decoded full authority observation of a native observation. -/
def NativeAuthorityObservation.toAuthority (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) {policy : P94AuthorityPolicy}
    (observation : NativeAuthorityObservation graph enumeration policy) :
    P94AuthorityObservation policy :=
  observation.payload.toAuthority
    (nativeSourceAtomResolver graph enumeration
      (decodeSourceContext graph enumeration observation.context) rfl)

/-- The decoded observation is valid for the reconstructed source. -/
theorem NativeAuthorityObservation.validForSource (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) {policy : P94AuthorityPolicy}
    (observation : NativeAuthorityObservation graph enumeration policy) :
    (observation.toAuthority graph enumeration).ValidFor policy
      (observation.source graph enumeration).input :=
  observation.valid

/-- **Encode** an actual full P-94 authority observation at a certified source tied to the shared
graph.  The source is replaced by its native context; the payload is transported by the exact
source inverse (via the derived resolver) and no whole original source is retained. -/
def encodeNativeAuthorityObservation (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) {policy : P94AuthorityPolicy}
    (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration)
    (enc : EncodedP94AuthorityObservation policy source V)
    (valid : (EncodedP94AuthorityObservation.toAuthority
      (nativeSourceAtomResolver graph enumeration source graph_eq) enc).ValidFor policy
      source.input) :
    NativeAuthorityObservation graph enumeration policy where
  context := encodeSourceContext graph enumeration source graph_eq
  payload := reseatEncodedObservation
    (first := source)
    (second := decodeSourceContext graph enumeration
      (encodeSourceContext graph enumeration source graph_eq))
    (by
      rw [decodeSourceContext_molecule]
      exact graph_eq)
    enc
  valid := by
    rw [toAuthority_reseat
      (molecule_eq := by
        rw [decodeSourceContext_molecule]
        exact graph_eq)
      (firstResolver := nativeSourceAtomResolver graph enumeration source graph_eq)
      (secondResolver := nativeSourceAtomResolver graph enumeration
        (decodeSourceContext graph enumeration
          (encodeSourceContext graph enumeration source graph_eq)) rfl)
      (sameVal := nativeSourceAtomResolver_symm_val_eq graph enumeration source graph_eq
        (decodeSourceContext graph enumeration
          (encodeSourceContext graph enumeration source graph_eq)) rfl)]
    rw [decode_encodeSourceContext graph enumeration source graph_eq]
    exact valid

/-- The recovered source and full observation of a decoded native observation. -/
structure RecoveredNativeAuthority (policy : P94AuthorityPolicy) where
  source : CertifiedAuthoritativeChemicalInput
  observation : P94AuthorityObservation policy
  valid : observation.ValidFor policy source.input

/-- **Decode** a native observation: reconstruct the certified source from the shared graph and
the native fields, then decode the full authority payload against that reconstruction. -/
def decodeNativeAuthorityObservation (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) {policy : P94AuthorityPolicy}
    (observation : NativeAuthorityObservation graph enumeration policy) :
    RecoveredNativeAuthority policy where
  source := decodeSourceContext graph enumeration observation.context
  observation := observation.payload.toAuthority
    (nativeSourceAtomResolver graph enumeration
      (decodeSourceContext graph enumeration observation.context) rfl)
  valid := observation.valid

@[simp] theorem decodeNativeAuthorityObservation_source
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    {policy : P94AuthorityPolicy}
    (observation : NativeAuthorityObservation graph enumeration policy) :
    (decodeNativeAuthorityObservation graph enumeration observation).source =
      decodeSourceContext graph enumeration observation.context := rfl

@[simp] theorem decodeNativeAuthorityObservation_observation
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    {policy : P94AuthorityPolicy}
    (observation : NativeAuthorityObservation graph enumeration policy) :
    (decodeNativeAuthorityObservation graph enumeration observation).observation =
      NativeAuthorityObservation.toAuthority graph enumeration observation := rfl

/-- The decoded observation is valid for the decoded source. -/
theorem decodeNativeAuthorityObservation_valid (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) {policy : P94AuthorityPolicy}
    (observation : NativeAuthorityObservation graph enumeration policy) :
    (decodeNativeAuthorityObservation graph enumeration observation).observation.ValidFor policy
      (decodeNativeAuthorityObservation graph enumeration observation).source.input :=
  (decodeNativeAuthorityObservation graph enumeration observation).valid

/-- **Paired exact inverse.**  Encoding an actual full P-94 authority observation and decoding the
result returns the exact certified source and the exact full authority observation (at the
derived resolver).  The source component is `decode_encodeSourceContext`; the observation
component is the transport lemma `toAuthority_reseat`. -/
theorem decodeNativeAuthorityObservation_encodeNativeAuthorityObservation
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    {policy : P94AuthorityPolicy} (source : CertifiedAuthoritativeChemicalInput)
    (graph_eq : source.input.molecule = graph.encode enumeration)
    (enc : EncodedP94AuthorityObservation policy source V)
    (valid : (EncodedP94AuthorityObservation.toAuthority
      (nativeSourceAtomResolver graph enumeration source graph_eq) enc).ValidFor policy
      source.input) :
    (decodeNativeAuthorityObservation graph enumeration
        (encodeNativeAuthorityObservation graph enumeration source graph_eq enc valid)).source =
      source ∧
    (decodeNativeAuthorityObservation graph enumeration
        (encodeNativeAuthorityObservation graph enumeration source graph_eq enc valid)).observation =
      EncodedP94AuthorityObservation.toAuthority
        (nativeSourceAtomResolver graph enumeration source graph_eq) enc := by
  constructor
  · exact decode_encodeSourceContext graph enumeration source graph_eq
  · exact toAuthority_reseat
      (molecule_eq := by
        rw [decodeSourceContext_molecule]
        exact graph_eq)
      (firstResolver := nativeSourceAtomResolver graph enumeration source graph_eq)
      (secondResolver := nativeSourceAtomResolver graph enumeration
        (decodeSourceContext graph enumeration
          (encodeSourceContext graph enumeration source graph_eq)) rfl)
      (sameVal := nativeSourceAtomResolver_symm_val_eq graph enumeration source graph_eq
        (decodeSourceContext graph enumeration
          (encodeSourceContext graph enumeration source graph_eq)) rfl)
      enc

end

end OrganicStereoNativeP94SourceContext
end TetraStereo.OneCenter
