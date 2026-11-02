import TetraStereo.OneCenter.OrganicStereoJointCoreEncoding
import TetraStereo.OneCenter.OrganicStereoEmbeddedBondPaths
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Constructions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false





























































namespace TetraStereo.OneCenter
namespace OccurrenceSpatialSupportExperiment

open JointCoreEncoding
open InteractionRoles

noncomputable section

/-! ## The standard simplex -/

/-- The standard `d`-simplex, as barycentric coordinates: nonnegative real coordinates on
`Fin (d+1)` summing to one.  The topology is the subtype topology inherited from the finite
product of real lines. -/
abbrev Delta (d : ℕ) : Type :=
  { w : Fin (d + 1) → ℝ // (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 }

namespace Delta

variable {d : ℕ}

/-- The `i`-th vertex of `Delta d`. -/
def vertex (i : Fin (d + 1)) : Delta d where
  val := fun j => if j = i then (1 : ℝ) else 0
  property := by
    constructor
    · intro j
      by_cases h : j = i <;> simp [h]
    · rw [Finset.sum_ite_eq']
      simp

/-- Coordinate value at a vertex. -/
@[simp] theorem vertex_coord (i j : Fin (d + 1)) :
    (vertex i).val j = if j = i then (1 : ℝ) else 0 := rfl

/-- Points of `Delta d` are determined by their coordinates. -/
@[ext] theorem ext {first second : Delta d} (coordinates : first.val = second.val) :
    first = second :=
  Subtype.ext coordinates

/-- The barycentre of the two-simplex. -/
def barycentre : Delta 2 where
  val := fun _ => (1 / 3 : ℝ)
  property := by
    constructor
    · intro _
      norm_num
    · rw [Fin.sum_univ_three]
      norm_num

@[simp] theorem barycentre_coord (i : Fin 3) : barycentre.val i = (1 / 3 : ℝ) := rfl

/-- The boundary of the two-simplex: at least one barycentric coordinate is zero. -/
def Boundary (w : Delta 2) : Prop :=
  w.val 0 = 0 ∨ w.val 1 = 0 ∨ w.val 2 = 0

/-- Every vertex lies on the boundary. -/
theorem vertex_boundary (i : Fin 3) : Boundary (vertex (d := 2) i) := by
  fin_cases i
  · right
    left
    simp
  · right
    right
    simp
  · left
    simp

end Delta

/-! ## Two non-vacuous filling maps on the two-simplex -/


def F0Fun (w : Delta 2) : EmbeddedReal3 :=
  WithLp.toLp 2 ![(w.val 1), (w.val 2), (0 : ℝ)]


def F1Fun (w : Delta 2) : EmbeddedReal3 :=
  WithLp.toLp 2 ![(w.val 1), (w.val 2), w.val 0 * w.val 1 * w.val 2]


theorem continuous_F0Fun : Continuous F0Fun := by
  have coordinates : Continuous fun w : Delta 2 =>
      (![(w.val 1), (w.val 2), (0 : ℝ)] : Fin 3 → ℝ) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val)
    · simpa using ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)
    · simpa using (continuous_const : Continuous fun _ : Delta 2 => (0 : ℝ))
  simpa [F0Fun] using (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp coordinates


theorem continuous_F1Fun : Continuous F1Fun := by
  have coordinates : Continuous fun w : Delta 2 =>
      (![(w.val 1), (w.val 2), w.val 0 * w.val 1 * w.val 2] : Fin 3 → ℝ) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val)
    · simpa using ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)
    · have h0 : Continuous fun w : Delta 2 => w.val 0 :=
          (continuous_apply (0 : Fin 3)).comp continuous_subtype_val
      have h1 : Continuous fun w : Delta 2 => w.val 1 :=
          (continuous_apply (1 : Fin 3)).comp continuous_subtype_val
      have h2 : Continuous fun w : Delta 2 => w.val 2 :=
          (continuous_apply (2 : Fin 3)).comp continuous_subtype_val
      simpa using (h0.mul h1).mul h2
  simpa [F1Fun] using (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp coordinates

/-- The straight filling as a continuous map. -/
def F0 : C(Delta 2, EmbeddedReal3) := ⟨F0Fun, continuous_F0Fun⟩

/-- The curved filling as a continuous map. -/
def F1 : C(Delta 2, EmbeddedReal3) := ⟨F1Fun, continuous_F1Fun⟩

@[simp] theorem F0_apply (w : Delta 2) : F0 w = F0Fun w := rfl

@[simp] theorem F1_apply (w : Delta 2) : F1 w = F1Fun w := rfl

/-- The two fillings agree on the entire boundary of the simplex. -/
theorem F0Fun_eq_F1Fun_of_boundary (w : Delta 2) (boundary : Delta.Boundary w) :
    F0Fun w = F1Fun w := by
  rcases boundary with h0 | h1 | h2
  · apply PiLp.ext
    intro i
    fin_cases i <;> simp [F0Fun, F1Fun, h0]
  · apply PiLp.ext
    intro i
    fin_cases i <;> simp [F0Fun, F1Fun, h1]
  · apply PiLp.ext
    intro i
    fin_cases i <;> simp [F0Fun, F1Fun, h2]

/-- The two fillings therefore have the same three vertex anchors. -/
theorem F0Fun_vertex_eq_F1Fun_vertex (i : Fin 3) :
    F0Fun (Delta.vertex (d := 2) i) = F1Fun (Delta.vertex (d := 2) i) :=
  F0Fun_eq_F1Fun_of_boundary _ (Delta.vertex_boundary i)

/-- The curved filling has the same vertex values as the straight filling. -/
theorem F1Fun_vertex_eq_F0Fun_vertex (i : Fin 3) :
    F1Fun (Delta.vertex (d := 2) i) = F0Fun (Delta.vertex (d := 2) i) :=
  (F0Fun_vertex_eq_F1Fun_vertex i).symm


theorem F0Fun_injective : Function.Injective F0Fun := by
  intro first second equal
  have h1 : first.val 1 = second.val 1 := by
    have projected := congrArg (fun point : EmbeddedReal3 => point 0) equal
    simpa [F0Fun] using projected
  have h2 : first.val 2 = second.val 2 := by
    have projected := congrArg (fun point : EmbeddedReal3 => point 1) equal
    simpa [F0Fun] using projected
  have h0 : first.val 0 = second.val 0 := by
    have firstSum : first.val 0 + first.val 1 + first.val 2 = 1 := by
      have := first.property.2
      simpa [Fin.sum_univ_three] using this
    have secondSum : second.val 0 + second.val 1 + second.val 2 = 1 := by
      have := second.property.2
      simpa [Fin.sum_univ_three] using this
    linarith
  apply Delta.ext
  funext i
  fin_cases i <;> simp [h0, h1, h2]



theorem F1Fun_injective : Function.Injective F1Fun := by
  intro first second equal
  have h1 : first.val 1 = second.val 1 := by
    have projected := congrArg (fun point : EmbeddedReal3 => point 0) equal
    simpa [F1Fun] using projected
  have h2 : first.val 2 = second.val 2 := by
    have projected := congrArg (fun point : EmbeddedReal3 => point 1) equal
    simpa [F1Fun] using projected
  have h0 : first.val 0 = second.val 0 := by
    have firstSum : first.val 0 + first.val 1 + first.val 2 = 1 := by
      have := first.property.2
      simpa [Fin.sum_univ_three] using this
    have secondSum : second.val 0 + second.val 1 + second.val 2 = 1 := by
      have := second.property.2
      simpa [Fin.sum_univ_three] using this
    linarith
  apply Delta.ext
  funext i
  fin_cases i <;> simp [h0, h1, h2]

/-- Barycentre value of the straight filling: third coordinate is zero. -/
@[simp] theorem F0Fun_barycentre_zero : F0Fun Delta.barycentre 0 = (1 / 3 : ℝ) := by
  simp [F0Fun, Delta.barycentre]

@[simp] theorem F0Fun_barycentre_one : F0Fun Delta.barycentre 1 = (1 / 3 : ℝ) := by
  simp [F0Fun, Delta.barycentre]

@[simp] theorem F0Fun_barycentre_two : F0Fun Delta.barycentre 2 = 0 := by
  simp [F0Fun, Delta.barycentre]

/-- Barycentre value of the curved filling: third coordinate is `1/27`. -/
@[simp] theorem F1Fun_barycentre_two : F1Fun Delta.barycentre 2 = (1 / 27 : ℝ) := by
  simp [F1Fun, Delta.barycentre]
  norm_num

/-- The two fillings differ at the barycentre. -/
theorem F0Fun_barycentre_ne_F1Fun_barycentre :
    F0Fun Delta.barycentre ≠ F1Fun Delta.barycentre := by
  intro equal
  have zEqual := congrArg (fun point : EmbeddedReal3 => point 2) equal
  simp [F0Fun, F1Fun, Delta.barycentre] at zEqual

/-! ## Occurrence-bound finite spatial cells over an independent source -/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- One geometric cell of a fixed common dimension `d`, bound to an actual source interaction
occurrence and carrying participant atom anchors tied to a shared conformation.

The entire continuous map is physical data.  `rolePositions` are explicit positions in the
support's finite role ledger; they may be empty and they may repeat an occurrence. -/
structure SpatialCell (graph : FiniteAtomInteractionHypergraph V) (d : ℕ) where
  /-- The actual ordered source interaction occurrence this cell is bound to. -/
  occurrence : Fin graph.interactions.length
  /-- The full continuous spatial map, not merely a vertex image or a centroid. -/
  map : C(Delta d, EmbeddedReal3)
  /-- One participant atom anchor per simplex vertex. -/
  anchors : Fin (d + 1) → V
  /-- Every anchor is a participant of the bound source occurrence. -/
  anchors_mem : ∀ i, anchors i ∈ (graph.interactions.get occurrence).1
  /-- Explicit positions in the support's finite role ledger. -/
  rolePositions : List ℕ

@[ext] theorem SpatialCell.ext {graph : FiniteAtomInteractionHypergraph V} {d : ℕ}
    {first second : SpatialCell graph d}
    (occurrence : first.occurrence = second.occurrence)
    (map : first.map = second.map)
    (anchors : first.anchors = second.anchors)
    (rolePositions : first.rolePositions = second.rolePositions) : first = second := by
  obtain ⟨firstOccurrence, firstMap, firstAnchors, firstMem, firstRoles⟩ := first
  obtain ⟨secondOccurrence, secondMap, secondAnchors, secondMem, secondRoles⟩ := second
  cases occurrence
  cases map
  cases anchors
  cases rolePositions
  have memoryProof : firstMem = secondMem := Subsingleton.elim _ _
  rw [memoryProof]

/-- An independent finite spatial support over a source graph: one shared real conformation, one
finite ordered role ledger, and a finite family of occurrence-bound continuous cells.  The
anchor and role-reference fields tie every cell to the shared conformation and to exact ledger
positions. -/
structure SpatialSupport (graph : FiniteAtomInteractionHypergraph V) (d : ℕ) where
  /-- Honest fixed-dimension scope: the common simplex dimension is at most three. -/
  dimension_le : d ≤ 3
  /-- The one shared real conformation of the entire support. -/
  conformation : MolecularConformation V
  /-- Finite ordered role ledger; order and multiplicity are list order and multiplicity. -/
  ledger : List (BroadAnnotation graph)
  /-- The finite cell family. -/
  cells : List (SpatialCell graph d)
  /-- Each cell's vertex images are exactly the shared conformation at its atom anchors. -/
  anchor_value : ∀ cell ∈ cells, ∀ i,
    cell.map (Delta.vertex (d := d) i) = conformation (cell.anchors i)
  /-- Each explicit role position resolves to an actual ledger annotation of the same occurrence. -/
  role_reference : ∀ cell ∈ cells, ∀ position ∈ cell.rolePositions,
    ∃ annotation : BroadAnnotation graph,
      ledger[position]? = some annotation ∧ annotation.index = cell.occurrence

@[ext] theorem SpatialSupport.ext {graph : FiniteAtomInteractionHypergraph V} {d : ℕ}
    {first second : SpatialSupport graph d}
    (conformation : first.conformation = second.conformation)
    (ledger : first.ledger = second.ledger)
    (cells : first.cells = second.cells) : first = second := by
  obtain ⟨firstDimension, firstConformation, firstLedger, firstCells, firstAnchor,
    firstRoles⟩ := first
  obtain ⟨secondDimension, secondConformation, secondLedger, secondCells, secondAnchor,
    secondRoles⟩ := second
  cases conformation
  cases ledger
  cases cells
  have dimensionProof : firstDimension = secondDimension := Subsingleton.elim _ _
  have anchorProof : firstAnchor = secondAnchor := Subsingleton.elim _ _
  have roleProof : firstRoles = secondRoles := Subsingleton.elim _ _
  rw [dimensionProof, anchorProof, roleProof]

/-! ## The encoded output geometry channel -/

/-- One encoded geometric cell.  The occurrence is an actual encoded source interaction index and
every anchor is an actual encoded source atom index; the full continuous map is retained. -/
structure EncodedSpatialCell (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) where
  /-- Actual encoded source interaction occurrence index. -/
  occurrence : Fin (graph.certifiedEncoding e).input.molecule.interactions.length
  /-- The full continuous spatial map. -/
  map : C(Delta d, EmbeddedReal3)
  /-- One encoded source atom index per simplex vertex. -/
  anchors : Fin (d + 1) → SourceAtomIndex (graph.certifiedEncoding e)
  /-- Every anchor index is a participant of the encoded occurrence. -/
  anchors_mem : ∀ i,
    (anchors i).val ∈
      ((graph.certifiedEncoding e).input.molecule.interactions.get occurrence).participants
  /-- Explicit positions in the encoded decoration list. -/
  rolePositions : List ℕ

@[ext] theorem EncodedSpatialCell.ext {graph : FiniteAtomInteractionHypergraph V}
    {e : V ≃ Fin (Fintype.card V)} {d : ℕ}
    {first second : EncodedSpatialCell graph e d}
    (occurrence : first.occurrence = second.occurrence)
    (map : first.map = second.map)
    (anchors : first.anchors = second.anchors)
    (rolePositions : first.rolePositions = second.rolePositions) : first = second := by
  obtain ⟨firstOccurrence, firstMap, firstAnchors, firstMem, firstRoles⟩ := first
  obtain ⟨secondOccurrence, secondMap, secondAnchors, secondMem, secondRoles⟩ := second
  cases occurrence
  cases map
  cases anchors
  cases rolePositions
  have memoryProof : firstMem = secondMem := Subsingleton.elim _ _
  rw [memoryProof]

/-- The complete encoded spatial support: encoded conformation, encoded role decoration list,
and the encoded finite cell family. -/
structure EncodedSpatialSupport (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) where
  dimension_le : d ≤ 3
  conformation : SourceConformation (graph.certifiedEncoding e)
  decorations : List (RoleDecoration (graph.certifiedEncoding e).input.molecule)
  cells : List (EncodedSpatialCell graph e d)
  anchor_value : ∀ cell ∈ cells, ∀ i,
    cell.map (Delta.vertex (d := d) i) = conformation (cell.anchors i)
  role_reference : ∀ cell ∈ cells, ∀ position ∈ cell.rolePositions,
    ∃ decoration : RoleDecoration (graph.certifiedEncoding e).input.molecule,
      decorations[position]? = some decoration ∧ decoration.index = cell.occurrence

@[ext] theorem EncodedSpatialSupport.ext {graph : FiniteAtomInteractionHypergraph V}
    {e : V ≃ Fin (Fintype.card V)} {d : ℕ}
    {first second : EncodedSpatialSupport graph e d}
    (conformation : first.conformation = second.conformation)
    (decorations : first.decorations = second.decorations)
    (cells : first.cells = second.cells) : first = second := by
  obtain ⟨firstDimension, firstConformation, firstDecorations, firstCells, firstAnchor,
    firstRoles⟩ := first
  obtain ⟨secondDimension, secondConformation, secondDecorations, secondCells, secondAnchor,
    secondRoles⟩ := second
  cases conformation
  cases decorations
  cases cells
  have dimensionProof : firstDimension = secondDimension := Subsingleton.elim _ _
  have anchorProof : firstAnchor = secondAnchor := Subsingleton.elim _ _
  have roleProof : firstRoles = secondRoles := Subsingleton.elim _ _
  rw [dimensionProof, anchorProof, roleProof]

/-! ## Source-participant transport through the common enumeration -/

/-- Membership of an encoded participant is exactly membership of the corresponding source
participant.  Atom identities are moved by the common enumeration and nothing else. -/
theorem encoded_participants_mem_iff (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (occurrence : Fin graph.interactions.length) (atom : V) :
    ((sourceAtomEquiv graph e atom).val ∈
      ((graph.certifiedEncoding e).input.molecule.interactions.get
        (encodedIndex graph e occurrence)).participants) ↔
      atom ∈ (graph.interactions.get occurrence).1 := by
  rw [encoded_get graph e occurrence]
  constructor
  · intro member
    simp only [FiniteAtomInteractionHypergraph.encodeInteraction] at member
    rcases List.mem_map.mp member with ⟨other, otherMemory, equal⟩
    have valueEqual : (e other).val = (e atom).val := by
      simpa [sourceAtomEquiv_apply_val] using equal
    have otherEqual : other = atom := e.injective (Fin.ext valueEqual)
    simpa [otherEqual] using otherMemory
  · intro member
    exact List.mem_map.mpr
      ⟨atom, member, (sourceAtomEquiv_apply_val graph e atom).symm⟩

/-! ## Encode and decode a cell -/

/-- Encode a cell through the common atom equivalence.  The occurrence becomes the encoded source
occurrence index, the anchors become encoded source atom indices, and the full map is unchanged. -/
def encodeCell (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) (cell : SpatialCell graph d) :
    EncodedSpatialCell graph e d where
  occurrence := encodedIndex graph e cell.occurrence
  map := cell.map
  anchors := fun i => sourceAtomEquiv graph e (cell.anchors i)
  anchors_mem := fun i =>
    (encoded_participants_mem_iff graph e cell.occurrence (cell.anchors i)).mpr
      (cell.anchors_mem i)
  rolePositions := cell.rolePositions

/-- Decode a cell through the inverse common atom equivalence. -/
def decodeCell (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) (cell : EncodedSpatialCell graph e d) :
    SpatialCell graph d where
  occurrence := sourceInteractionIndex graph e cell.occurrence
  map := cell.map
  anchors := fun i => (sourceAtomEquiv graph e).symm (cell.anchors i)
  anchors_mem := by
    intro i
    have encodedMember :
        ((sourceAtomEquiv graph e
            ((sourceAtomEquiv graph e).symm (cell.anchors i))).val ∈
          ((graph.certifiedEncoding e).input.molecule.interactions.get
            (encodedIndex graph e
              (sourceInteractionIndex graph e cell.occurrence))).participants) := by
      rw [Equiv.apply_symm_apply, encodedIndex_sourceInteractionIndex]
      exact cell.anchors_mem i
    exact (encoded_participants_mem_iff graph e
      (sourceInteractionIndex graph e cell.occurrence)
      ((sourceAtomEquiv graph e).symm (cell.anchors i))).mp encodedMember
  rolePositions := cell.rolePositions

/-- Decoding an encoded cell returns exactly the original cell: occurrence, map, anchors and
role positions are all recovered. -/
@[simp] theorem decodeCell_encodeCell (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) (cell : SpatialCell graph d) :
    decodeCell graph e d (encodeCell graph e d cell) = cell := by
  apply SpatialCell.ext
  · simp [encodeCell, decodeCell, sourceInteractionIndex_encodedIndex]
  · rfl
  · funext i
    simp [encodeCell, decodeCell]
  · rfl

/-! ## Encode and decode the whole support -/

/-- Encode a whole independent spatial support.  The conformation is reindexed by the common
atom equivalence, the role ledger is transported entry by entry with the same order and
multiplicity, and every cell is encoded through the same equivalence. -/
def encodeSupport (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) (state : SpatialSupport graph d) :
    EncodedSpatialSupport graph e d where
  dimension_le := state.dimension_le
  conformation := MolecularConformation.reindex (sourceAtomEquiv graph e) state.conformation
  decorations := state.ledger.map (broadDecoration graph e)
  cells := state.cells.map (encodeCell graph e d)
  anchor_value := by
    intro cell member i
    obtain ⟨sourceCell, sourceMember, rfl⟩ := List.mem_map.mp member
    have original := state.anchor_value sourceCell sourceMember i
    simpa [encodeCell, MolecularConformation.reindex] using original
  role_reference := by
    intro cell member position positionMember
    obtain ⟨sourceCell, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨annotation, lookup, occurrenceEqual⟩ :=
      state.role_reference sourceCell sourceMember position positionMember
    refine ⟨broadDecoration graph e annotation, ?_, ?_⟩
    · rw [List.getElem?_map, lookup]
      rfl
    · rw [broadDecoration_index, occurrenceEqual]
      rfl

/-- Decode a whole encoded spatial support.  The conformation is reindexed by the inverse common
atom equivalence, the decoration list is decoded entry by entry, and every cell is decoded. -/
def decodeSupport (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) (state : EncodedSpatialSupport graph e d) :
    SpatialSupport graph d where
  dimension_le := state.dimension_le
  conformation := MolecularConformation.reindex (sourceAtomEquiv graph e).symm state.conformation
  ledger := state.decorations.map (decodeBroadAnnotation graph e)
  cells := state.cells.map (decodeCell graph e d)
  anchor_value := by
    intro cell member i
    obtain ⟨encodedCell, encodedMember, rfl⟩ := List.mem_map.mp member
    have original := state.anchor_value encodedCell encodedMember i
    simpa [decodeCell, MolecularConformation.reindex] using original
  role_reference := by
    intro cell member position positionMember
    obtain ⟨encodedCell, encodedMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨decoration, lookup, occurrenceEqual⟩ :=
      state.role_reference encodedCell encodedMember position positionMember
    refine ⟨decodeBroadAnnotation graph e decoration, ?_, ?_⟩
    · rw [List.getElem?_map, lookup]
      rfl
    · show sourceInteractionIndex graph e decoration.index =
        (decodeCell graph e d encodedCell).occurrence
      rw [occurrenceEqual]
      rfl

/-! ## Exact recovery theorem -/

/-- **Main codec theorem.**  Decoding the encoded image of an independent occurrence-bound
spatial support recovers the entire original support: the shared conformation, the whole ordered
role ledger and the whole finite cell family, including every source occurrence index, every
participant anchor and every full continuous map. -/
theorem decodeSupport_encodeSupport (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) (state : SpatialSupport graph d) :
    decodeSupport graph e d (encodeSupport graph e d state) = state := by
  apply SpatialSupport.ext
  · exact MolecularConformation.reindex_reindex (sourceAtomEquiv graph e) state.conformation
  · show (state.ledger.map (broadDecoration graph e)).map
        (decodeBroadAnnotation graph e) = state.ledger
    rw [List.map_map]
    have identity : (decodeBroadAnnotation graph e ∘ broadDecoration graph e) = id := by
      funext annotation
      exact decodeBroadAnnotation_broadDecoration graph e annotation
    rw [identity, List.map_id]
  · show (state.cells.map (encodeCell graph e d)).map (decodeCell graph e d) = state.cells
    rw [List.map_map]
    have identity : (decodeCell graph e d ∘ encodeCell graph e d) = id := by
      funext cell
      exact decodeCell_encodeCell graph e d cell
    rw [identity, List.map_id]

/-- Encoding of spatial supports is injective, because decoding is a left inverse. -/
theorem encodeSupport_injective (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (d : ℕ) :
    Function.Injective (encodeSupport graph e d) := by
  intro first second equal
  have decoded := congrArg (decodeSupport graph e d) equal
  simpa [decodeSupport_encodeSupport graph e d first,
    decodeSupport_encodeSupport graph e d second] using decoded

/-! ## Explicit non-vacuity witness on `Delta 2`

The witness uses one genuine ternary `multicenter` interaction over three atoms.  Two cells share
the graph, the conformation, the role ledger, the actual source occurrence, the three atom
anchors and the role positions; only the full interior map differs. -/

/-- Carbon. -/
def witnessCarbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

/-- The semantic carbon atom. -/
def witnessAtom : SemanticAtom := { element := witnessCarbon }

/-- One ternary multicenter interaction on atoms `0, 1, 2`. -/
def witnessGraph : FiniteAtomInteractionHypergraph (Fin 3) where
  atomData := fun _ => witnessAtom
  interactions := [([0, 1, 2], SemanticInteractionKind.multicenter 4)]
  arity_ge_two := by
    intro edge member
    simp only [List.mem_singleton] at member
    rw [member]
    norm_num
  participants_nodup := by
    intro edge member
    simp only [List.mem_singleton] at member
    rw [member]
    decide

/-- The single actual source interaction occurrence. -/
def witnessOccurrence : Fin witnessGraph.interactions.length :=
  ⟨0, by simp [witnessGraph]⟩

/-- A multicenter role in one participant order. -/
def witnessRoleA : PhysicalRole (Fin 3) :=
  PhysicalRole.multicenter [0, 1, 2] (by decide) (by decide) 4

/-- A multicenter role in another participant order.  It has the same unordered support and the
same kind/electron count, so it is compatible with the same source occurrence. -/
def witnessRoleB : PhysicalRole (Fin 3) :=
  PhysicalRole.multicenter [1, 2, 0] (by decide) (by decide) 4

/-- The first annotation of the repeated role ledger. -/
def witnessAnnotationA : BroadAnnotation witnessGraph where
  index := witnessOccurrence
  role := witnessRoleA
  compatible := by
    refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The second annotation, at the *same* occurrence but with a different explicit role. -/
def witnessAnnotationB : BroadAnnotation witnessGraph where
  index := witnessOccurrence
  role := witnessRoleB
  compatible := by
    refine ⟨?_, ?_, ?_⟩ <;> decide

/-- A finite role ledger that repeats one occurrence twice. -/
def witnessLedger : List (BroadAnnotation witnessGraph) :=
  [witnessAnnotationA, witnessAnnotationB]

/-- Repeated occurrence and distinct roles: the ledger is genuinely a repeated ledger, and exact
positional references can distinguish the two entries. -/
theorem witnessLedger_repeats :
    witnessLedger[0]? = some witnessAnnotationA ∧
      witnessLedger[1]? = some witnessAnnotationB ∧
      witnessAnnotationA.index = witnessAnnotationB.index ∧
      witnessAnnotationA.role ≠ witnessAnnotationB.role := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp [witnessLedger]
  · simp [witnessLedger]
  · intro equal
    have supportEqual := congrArg PhysicalRole.supportList equal
    have listsEqual : ([0, 1, 2] : List (Fin 3)) = [1, 2, 0] := by
      simpa only [witnessAnnotationA, witnessAnnotationB, witnessRoleA, witnessRoleB,
        PhysicalRole.supportList, PhysicalRole.supportKind] using supportEqual
    exact (by decide : ([0, 1, 2] : List (Fin 3)) ≠ [1, 2, 0]) listsEqual

/-- The shared real conformation sends the three atom anchors to the three common vertex
images. -/
def witnessConformation : MolecularConformation (Fin 3) :=
  fun i => F0Fun (Delta.vertex (d := 2) i)

/-- The straight cell. -/
def witnessCellStraight : SpatialCell witnessGraph 2 where
  occurrence := witnessOccurrence
  map := F0
  anchors := fun i => i
  anchors_mem := by
    intro i
    fin_cases i <;> simp [witnessGraph, witnessOccurrence]
  rolePositions := [0]

/-- The curved cell.  It has exactly the same occurrence, anchors and role positions. -/
def witnessCellCurved : SpatialCell witnessGraph 2 where
  occurrence := witnessOccurrence
  map := F1
  anchors := fun i => i
  anchors_mem := by
    intro i
    fin_cases i <;> simp [witnessGraph, witnessOccurrence]
  rolePositions := [0]

/-- Both cells use the same three atom anchors as simplex vertex anchors and evaluate to the
shared conformation there. -/
theorem witness_three_vertex_anchors :
    (∀ i, witnessCellStraight.map (Delta.vertex (d := 2) i) =
        witnessConformation (witnessCellStraight.anchors i)) ∧
      (∀ i, witnessCellCurved.map (Delta.vertex (d := 2) i) =
        witnessConformation (witnessCellCurved.anchors i)) := by
  constructor
  · intro i
    simp [witnessCellStraight, witnessConformation]
  · intro i
    simp [witnessCellCurved, witnessConformation, F1Fun_vertex_eq_F0Fun_vertex]

/-- The straight support. -/
def witnessSupportStraight : SpatialSupport witnessGraph 2 where
  dimension_le := by norm_num
  conformation := witnessConformation
  ledger := witnessLedger
  cells := [witnessCellStraight]
  anchor_value := by
    intro cell member i
    rcases List.mem_singleton.mp member with rfl
    simp [witnessCellStraight, witnessConformation]
  role_reference := by
    intro cell member position positionMember
    rcases List.mem_singleton.mp member with rfl
    simp only [witnessCellStraight, List.mem_singleton] at positionMember
    rcases positionMember with rfl
    exact ⟨witnessAnnotationA, by simp [witnessLedger], rfl⟩

/-- The curved support.  It shares the graph, conformation, ledger and role positions with the
straight support. -/
def witnessSupportCurved : SpatialSupport witnessGraph 2 where
  dimension_le := by norm_num
  conformation := witnessConformation
  ledger := witnessLedger
  cells := [witnessCellCurved]
  anchor_value := by
    intro cell member i
    rcases List.mem_singleton.mp member with rfl
    simp [witnessCellCurved, witnessConformation, F1Fun_vertex_eq_F0Fun_vertex]
  role_reference := by
    intro cell member position positionMember
    rcases List.mem_singleton.mp member with rfl
    simp only [witnessCellCurved, List.mem_singleton] at positionMember
    rcases positionMember with rfl
    exact ⟨witnessAnnotationA, by simp [witnessLedger], rfl⟩

/-- The common enumeration used for the witness. -/
def witnessEnumeration : Fin 3 ≃ Fin (Fintype.card (Fin 3)) :=
  Fintype.equivFin (Fin 3)

/-- Encoded straight support. -/
def witnessEncodedStraight : EncodedSpatialSupport witnessGraph witnessEnumeration 2 :=
  encodeSupport witnessGraph witnessEnumeration 2 witnessSupportStraight

/-- Encoded curved support. -/
def witnessEncodedCurved : EncodedSpatialSupport witnessGraph witnessEnumeration 2 :=
  encodeSupport witnessGraph witnessEnumeration 2 witnessSupportCurved

/-- The two encoded supports have exactly the same encoded conformation. -/
theorem witnessEncoded_same_conformation :
    witnessEncodedStraight.conformation = witnessEncodedCurved.conformation := rfl

/-- The two encoded supports have exactly the same encoded role decoration list. -/
theorem witnessEncoded_same_decorations :
    witnessEncodedStraight.decorations = witnessEncodedCurved.decorations := rfl

/-- Encoded straight interior values. -/
theorem witnessEncoded_straight_interior :
    (witnessEncodedStraight.cells.map (fun cell => cell.map Delta.barycentre)) =
      [F0Fun Delta.barycentre] := by
  simp [witnessEncodedStraight, encodeSupport, encodeCell, witnessSupportStraight,
    witnessCellStraight]

/-- Encoded curved interior values. -/
theorem witnessEncoded_curved_interior :
    (witnessEncodedCurved.cells.map (fun cell => cell.map Delta.barycentre)) =
      [F1Fun Delta.barycentre] := by
  simp [witnessEncodedCurved, encodeSupport, encodeCell, witnessSupportCurved,
    witnessCellCurved]

/-- **Information test.**  Over the identical source graph, conformation and role metadata, the
encoded interior geometry is not determined: the encoded straight and curved supports differ in
their cell family. -/
theorem witnessEncoded_cells_differ :
    witnessEncodedStraight.cells ≠ witnessEncodedCurved.cells := by
  intro equal
  have mapped :
      (witnessEncodedStraight.cells.map (fun cell => cell.map Delta.barycentre)) =
        (witnessEncodedCurved.cells.map (fun cell => cell.map Delta.barycentre)) := by
    simpa using congrArg
      (fun cells => cells.map (fun cell => cell.map Delta.barycentre)) equal
  rw [witnessEncoded_straight_interior, witnessEncoded_curved_interior] at mapped
  have pointEqual : F0Fun Delta.barycentre = F1Fun Delta.barycentre := by
    simpa using mapped
  exact F0Fun_barycentre_ne_F1Fun_barycentre pointEqual

/-- The encoded interior geometry differs at the explicit barycentre: the encoded straight cell
family evaluates to third coordinate `0`, the encoded curved cell family to `1/27`. -/
theorem witnessEncoded_interior_third_coordinates :
    ((witnessEncodedStraight.cells.map
        (fun cell => cell.map Delta.barycentre)).map (fun point => point 2)) = [0] ∧
      ((witnessEncodedCurved.cells.map
        (fun cell => cell.map Delta.barycentre)).map (fun point => point 2)) = [1 / 27] := by
  rw [witnessEncoded_straight_interior, witnessEncoded_curved_interior]
  constructor
  · simp
  · simp

end

end OccurrenceSpatialSupportExperiment
end TetraStereo.OneCenter
