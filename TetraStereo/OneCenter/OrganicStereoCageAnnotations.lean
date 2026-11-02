import Mathlib.Data.List.Nodup
import TetraStereo.OneCenter.OrganicStereoFullereneSourceEncoding
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open TetraStereo.OneCenter.BlueBookP93.Cyclic

/-!
# Numbered cage annotations over an arbitrary finite atom-reference type

This module is the numbered-cage metadata-retention layer for the whole-state join.  It is *not* a
chemical classifier and it derives no stereochemical answer.  Its purpose is to carry the source
fields of one supplied `MolecularFullereneNumberedCagePackage` across a change of the independent
finite atom type, and to recover exactly the fields that were stored.

The annotation language is an explicit finite structure, indexed by an arbitrary atom-reference
type `V`:

* `V` is used *only* for atom references.  Locant numbers are a separate `List ℕ`; an atom
  reference is never a locant number and no cast from `ℕ` to `V` is stored;
* the source locant order is retained as two parallel ordered lists (`locants`, `vertices`);
* the canonical edge table is retained in source order with its source endpoint orientation;
* every supplied facial cycle is retained as an ordered `List V`, so cyclic order and face
  multiplicity are preserved;
* the addend/appendage sidecar is retained unchanged, including interaction kinds, so the
  cage/addend boundary needed by the whole-state join is not dropped.

The adapters use an *external* enumeration `V ≃ Fin atomCount`; the annotation stores no such
enumeration and no `V → ℕ` decoder.  All finite-universe bounds come from the actual source
assumptions (`FullereneSourceEncoding`), or, for a bare package, from an explicit `PackageBounds`
certificate.  No field asserts that decoding returns the source package: recovery is proved from
the construction, both as an exact package equality and field by field.

An atom relabelling `V ≃ W` moves every atom reference and nothing else: locants, edge order,
face order, face orientation and multiplicity, and the addend sidecar are copied.  The inverse and
injectivity results show that no original `V` source is hidden in the encoded annotation.

Scope: this is representation/data transport for an already supplied cage package.  It does not
recognise fullerenes, enumerate a catalogue, or claim that every organic molecule is a fullerene.
-/

/-! ## The annotation record -/

/-- One numbered-cage annotation over an arbitrary atom-reference type `V`.

`vertices` is the source locant order (`locants` has the same length and is retained separately).
`edges` is the supplied canonical edge table in source order, with endpoints as atom references.
`faces` is the supplied list of oriented facial cycles, in source order and with source
multiplicity.  `addendInteractions` is the supplied addend/appendage sidecar.  The proof fields tie
edges and faces to the cage vertices and record the source multiplicity/arity invariants; none of
them mentions an atom number or a decoder. -/
structure NumberedCageAnnotation (V : Type*) where
  /-- Size of the finite atom universe of the source encoding. -/
  atomCount : ℕ
  /-- Source locant values, in locant order. -/
  locants : List ℕ
  /-- Atom references, in the same locant order. -/
  vertices : List V
  /-- `locants` and `vertices` are parallel ordered lists. -/
  locants_length : locants.length = vertices.length
  /-- Canonical cage edge table, in source order and source endpoint orientation. -/
  edges : List (V × V)
  /-- Every cage edge is incident with two listed cage vertices. -/
  edge_vertices : ∀ edge ∈ edges, edge.1 ∈ vertices ∧ edge.2 ∈ vertices
  /-- No cage edge is a self-loop. -/
  edge_distinct : ∀ edge ∈ edges, edge.1 ≠ edge.2
  /-- Oriented facial cycles, in source order and with source multiplicity. -/
  faces : List (List V)
  /-- Every facial atom is a listed cage vertex. -/
  face_vertices : ∀ face ∈ faces, ∀ vertex ∈ face, vertex ∈ vertices
  /-- A facial cycle has no repeated atom. -/
  face_nodup : ∀ face ∈ faces, face.Nodup
  /-- Addend/appendage sidecar: participant references and interaction kind. -/
  addendInteractions : List (List V × SemanticInteractionKind)
  /-- Addend interactions have at least two participants. -/
  addend_arity : ∀ interaction ∈ addendInteractions, 2 ≤ interaction.1.length
  /-- Addend participants are distinct. -/
  addend_nodup : ∀ interaction ∈ addendInteractions, interaction.1.Nodup

namespace NumberedCageAnnotation

variable {V W U : Type*}

/-- Structure extensionality on the retained data.  The proof fields are propositional and add no
data. -/
@[ext] theorem ext {first second : NumberedCageAnnotation V}
    (atomCount : first.atomCount = second.atomCount)
    (locants : first.locants = second.locants)
    (vertices : first.vertices = second.vertices)
    (edges : first.edges = second.edges)
    (faces : first.faces = second.faces)
    (addendInteractions : first.addendInteractions = second.addendInteractions) :
    first = second := by
  cases first
  cases second
  simp_all

/-! ## Atom relabelling and its inverse -/

/-- Ordered relabelling of one edge: both endpoints move, and the stored orientation is preserved. -/
def relabelEdge (f : V ≃ W) (edge : V × V) : W × W :=
  (f edge.1, f edge.2)

/-- Ordered relabelling of one facial cycle: atom references move, cyclic order and multiplicity
are copied verbatim. -/
def relabelFace (f : V ≃ W) (face : List V) : List W :=
  face.map f

/-- Atom relabelling of a whole cage annotation.  Only `V` references move; locant order, edge
order and orientation, face order and orientation, interaction kinds, and all proof obligations
are retained. -/
def relabel (f : V ≃ W) (annotation : NumberedCageAnnotation V) :
    NumberedCageAnnotation W where
  atomCount := annotation.atomCount
  locants := annotation.locants
  vertices := annotation.vertices.map f
  locants_length := by simp [annotation.locants_length]
  edges := annotation.edges.map (relabelEdge f)
  edge_vertices := by
    intro edge member
    simp only [List.mem_map] at member ⊢
    obtain ⟨original, originalMember, rfl⟩ := member
    exact ⟨⟨original.1, (annotation.edge_vertices original originalMember).1, rfl⟩,
      ⟨original.2, (annotation.edge_vertices original originalMember).2, rfl⟩⟩
  edge_distinct := by
    intro edge member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    intro equal
    exact annotation.edge_distinct original originalMember (f.injective equal)
  faces := annotation.faces.map (relabelFace f)
  face_vertices := by
    intro face member vertex vertexMember
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    simp only [relabelFace, List.mem_map] at vertexMember
    obtain ⟨originalVertex, originalVertexMember, rfl⟩ := vertexMember
    simp only [List.mem_map]
    exact ⟨originalVertex,
      annotation.face_vertices original originalMember originalVertex originalVertexMember, rfl⟩
  face_nodup := by
    intro face member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact (annotation.face_nodup original originalMember).map f.injective
  addendInteractions := annotation.addendInteractions.map
    (fun interaction => (relabelFace f interaction.1, interaction.2))
  addend_arity := by
    intro interaction member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    simpa [relabelFace] using annotation.addend_arity original originalMember
  addend_nodup := by
    intro interaction member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact (annotation.addend_nodup original originalMember).map f.injective

@[simp] theorem relabel_atomCount (f : V ≃ W) (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).atomCount = annotation.atomCount := rfl

@[simp] theorem relabel_locants (f : V ≃ W) (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).locants = annotation.locants := rfl

@[simp] theorem relabel_vertices (f : V ≃ W) (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).vertices = annotation.vertices.map f := rfl

@[simp] theorem relabel_edges (f : V ≃ W) (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).edges = annotation.edges.map (relabelEdge f) := rfl

@[simp] theorem relabel_faces (f : V ≃ W) (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).faces = annotation.faces.map (relabelFace f) := rfl

@[simp] theorem relabel_addendInteractions (f : V ≃ W)
    (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).addendInteractions =
      annotation.addendInteractions.map
        (fun interaction => (relabelFace f interaction.1, interaction.2)) := rfl

theorem relabelEdge_refl (edge : V × V) :
    relabelEdge (Equiv.refl V) edge = edge := by
  cases edge
  rfl

theorem relabelFace_refl (face : List V) :
    relabelFace (Equiv.refl V) face = face := by
  simp [relabelFace]

theorem relabelEdge_trans (f : V ≃ W) (g : W ≃ U) (edge : V × V) :
    relabelEdge g (relabelEdge f edge) = relabelEdge (f.trans g) edge := by
  cases edge
  rfl

theorem relabelFace_trans (f : V ≃ W) (g : W ≃ U) (face : List V) :
    relabelFace g (relabelFace f face) = relabelFace (f.trans g) face := by
  simp [relabelFace, List.map_map]

theorem relabelEdge_symm_relabel (f : V ≃ W) (edge : V × V) :
    relabelEdge f.symm (relabelEdge f edge) = edge := by
  cases edge
  simp [relabelEdge]

theorem relabelFace_symm_relabel (f : V ≃ W) (face : List V) :
    relabelFace f.symm (relabelFace f face) = face := by
  simp [relabelFace, List.map_map]

theorem relabelEdge_relabel_symm (f : V ≃ W) (edge : W × W) :
    relabelEdge f (relabelEdge f.symm edge) = edge := by
  cases edge
  simp [relabelEdge]

theorem relabelFace_relabel_symm (f : V ≃ W) (face : List W) :
    relabelFace f (relabelFace f.symm face) = face := by
  simp [relabelFace, List.map_map]

/-- Generic list-level map-of-map comparison: pointwise agreement of the composite with `result`
is enough.  This is the only auxiliary list lemma used by the relabelling laws. -/
theorem map_map_eq_map {α β γ : Type*} (list : List α) (first : α → β) (second : β → γ)
    (result : α → γ) (pointwise : ∀ value ∈ list, second (first value) = result value) :
    (list.map first).map second = list.map result := by
  rw [List.map_map]
  exact List.map_congr_left pointwise

/-- Relabelling by the identity equivalence is the identity. -/
@[simp] theorem relabel_refl (annotation : NumberedCageAnnotation V) :
    annotation.relabel (Equiv.refl V) = annotation := by
  apply ext
  · rfl
  · rfl
  · simp
  · simpa using map_map_eq_map annotation.edges (relabelEdge (Equiv.refl V)) id id
      (fun edge _ => relabelEdge_refl edge)
  · simpa using map_map_eq_map annotation.faces (relabelFace (Equiv.refl V)) id id
      (fun face _ => relabelFace_refl face)
  · simpa using map_map_eq_map annotation.addendInteractions
      (fun interaction => (relabelFace (Equiv.refl V) interaction.1, interaction.2)) id id
      (fun interaction _ => Prod.ext (relabelFace_refl interaction.1) rfl)

/-- Relabelling composes along equivalence composition. -/
theorem relabel_trans (f : V ≃ W) (g : W ≃ U) (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).relabel g = annotation.relabel (f.trans g) := by
  apply ext
  · rfl
  · rfl
  · simp
  · simpa using map_map_eq_map annotation.edges (relabelEdge f) (relabelEdge g)
      (relabelEdge (f.trans g)) (fun edge _ => relabelEdge_trans f g edge)
  · simpa using map_map_eq_map annotation.faces (relabelFace f) (relabelFace g)
      (relabelFace (f.trans g)) (fun face _ => relabelFace_trans f g face)
  · simpa using map_map_eq_map annotation.addendInteractions
      (fun interaction => (relabelFace f interaction.1, interaction.2))
      (fun interaction => (relabelFace g interaction.1, interaction.2))
      (fun interaction => (relabelFace (f.trans g) interaction.1, interaction.2))
      (fun interaction _ => Prod.ext (relabelFace_trans f g interaction.1) rfl)

/-- Relabelling by `f` and then by `f.symm` is the identity: the inverse recovers the original
annotation exactly, so no original `V` source is hidden. -/
@[simp] theorem relabel_symm_relabel (f : V ≃ W) (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).relabel f.symm = annotation := by
  apply ext
  · rfl
  · rfl
  · simp
  · simpa using map_map_eq_map annotation.edges (relabelEdge f) (relabelEdge f.symm) id
      (fun edge _ => relabelEdge_symm_relabel f edge)
  · simpa using map_map_eq_map annotation.faces (relabelFace f) (relabelFace f.symm) id
      (fun face _ => relabelFace_symm_relabel f face)
  · simpa using map_map_eq_map annotation.addendInteractions
      (fun interaction => (relabelFace f interaction.1, interaction.2))
      (fun interaction => (relabelFace f.symm interaction.1, interaction.2)) id
      (fun interaction _ => Prod.ext (relabelFace_symm_relabel f interaction.1) rfl)

/-- Relabelling by `f.symm` and then by `f` is the identity. -/
@[simp] theorem relabel_relabel_symm (f : V ≃ W) (annotation : NumberedCageAnnotation W) :
    (annotation.relabel f.symm).relabel f = annotation := by
  apply ext
  · rfl
  · rfl
  · simp
  · simpa using map_map_eq_map annotation.edges (relabelEdge f.symm) (relabelEdge f) id
      (fun edge _ => relabelEdge_relabel_symm f edge)
  · simpa using map_map_eq_map annotation.faces (relabelFace f.symm) (relabelFace f) id
      (fun face _ => relabelFace_relabel_symm f face)
  · simpa using map_map_eq_map annotation.addendInteractions
      (fun interaction => (relabelFace f.symm interaction.1, interaction.2))
      (fun interaction => (relabelFace f interaction.1, interaction.2)) id
      (fun interaction _ => Prod.ext (relabelFace_relabel_symm f interaction.1) rfl)

/-- Atom relabelling is injective on annotations. -/
theorem relabel_injective (f : V ≃ W) :
    Function.Injective (fun annotation : NumberedCageAnnotation V => annotation.relabel f) := by
  intro first second equal
  have inverse := congrArg
    (fun annotation : NumberedCageAnnotation W => annotation.relabel f.symm) equal
  simpa [relabel_symm_relabel] using inverse

/-! ## Whole lists of annotations (the Domain join surface) -/

/-- Atom relabelling of a whole list of annotations, preserving list order and multiplicity. -/
def relabelList (f : V ≃ W) (annotations : List (NumberedCageAnnotation V)) :
    List (NumberedCageAnnotation W) :=
  annotations.map (fun annotation => annotation.relabel f)

@[simp] theorem relabelList_length (f : V ≃ W)
    (annotations : List (NumberedCageAnnotation V)) :
    (relabelList f annotations).length = annotations.length := by
  simp [relabelList]

@[simp] theorem relabelList_nil (f : V ≃ W) : relabelList f [] = [] := rfl

@[simp] theorem relabelList_cons (f : V ≃ W) (annotation : NumberedCageAnnotation V)
    (annotations : List (NumberedCageAnnotation V)) :
    relabelList f (annotation :: annotations) =
      annotation.relabel f :: relabelList f annotations := rfl

@[simp] theorem relabelList_refl (annotations : List (NumberedCageAnnotation V)) :
    relabelList (Equiv.refl V) annotations = annotations := by
  simp [relabelList]

theorem relabelList_trans (f : V ≃ W) (g : W ≃ U)
    (annotations : List (NumberedCageAnnotation V)) :
    relabelList g (relabelList f annotations) = relabelList (f.trans g) annotations := by
  simp [relabelList, List.map_map, relabel_trans, Function.comp_def]

@[simp] theorem relabelList_symm_relabel (f : V ≃ W)
    (annotations : List (NumberedCageAnnotation V)) :
    relabelList f.symm (relabelList f annotations) = annotations := by
  simp [relabelList, List.map_map, relabel_symm_relabel, Function.comp_def]

@[simp] theorem relabelList_relabel_symm (f : V ≃ W)
    (annotations : List (NumberedCageAnnotation W)) :
    relabelList f (relabelList f.symm annotations) = annotations := by
  simp [relabelList, List.map_map, relabel_relabel_symm, Function.comp_def]

/-- Atom relabelling of annotation lists is injective. -/
theorem relabelList_injective (f : V ≃ W) :
    Function.Injective
      (fun annotations : List (NumberedCageAnnotation V) => relabelList f annotations) := by
  intro first second equal
  have inverse := congrArg (relabelList f.symm) equal
  simpa [relabelList_symm_relabel] using inverse

/-! ## External enumeration, decoding, and exact package recovery -/

/-- Atom reference of a bounded natural-number source atom under an external enumeration.  The
enumeration is supplied by the caller; no enumeration is stored in the annotation. -/
def sourceAtomRef {n : ℕ} (e : V ≃ Fin n) (atom : ℕ) (bound : atom < n) : V :=
  e.symm ⟨atom, bound⟩

@[simp] theorem sourceAtomRef_val {n : ℕ} (e : V ≃ Fin n) (atom : ℕ) (bound : atom < n) :
    (((e (sourceAtomRef e atom bound) : Fin n) : ℕ)) = atom := by
  simp [sourceAtomRef]

theorem sourceAtomRef_proof_irrel {n : ℕ} (e : V ≃ Fin n) (atom : ℕ)
    (first second : atom < n) : sourceAtomRef e atom first = sourceAtomRef e atom second := by
  unfold sourceAtomRef
  exact congrArg e.symm (Fin.ext rfl)

theorem sourceAtomRef_injective {n : ℕ} (e : V ≃ Fin n) {first second : ℕ}
    {firstBound : first < n} {secondBound : second < n}
    (equal : sourceAtomRef e first firstBound = sourceAtomRef e second secondBound) :
    first = second := by
  have image := congrArg (fun value => (((e value : Fin n) : ℕ))) equal
  simpa [sourceAtomRef] using image

/-- Decoding an ordered list of bounded atoms through the external enumeration returns exactly the
source list. -/
theorem map_sourceAtomRef_atoms {n : ℕ} (e : V ≃ Fin n) (atoms : List ℕ)
    (bound : ∀ atom ∈ atoms, atom < n) :
    (atoms.attach.map (fun atom => sourceAtomRef e atom.1 (bound atom.1 atom.2))).map
        (fun value => (((e value : Fin n) : ℕ))) = atoms := by
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [show (fun atom : {value // value ∈ atoms} =>
        (((e (sourceAtomRef e atom.1 (bound atom.1 atom.2)) : Fin n) : ℕ))) =
      Subtype.val from by
    funext atom
    obtain ⟨value, member⟩ := atom
    simp [sourceAtomRef]]
  exact List.attach_map_subtype_val atoms

/-- Decoding an ordered edge table through the external enumeration returns exactly the source
edge table, including endpoint order. -/
theorem map_sourceAtomRef_edges {n : ℕ} (e : V ≃ Fin n) (edges : List (ℕ × ℕ))
    (bound : ∀ edge ∈ edges, edge.1 < n ∧ edge.2 < n) :
    (edges.attach.map (fun edge =>
        (sourceAtomRef e edge.1.1 (bound edge.1 edge.2).1,
          sourceAtomRef e edge.1.2 (bound edge.1 edge.2).2))).map
        (fun edge => (((e edge.1 : Fin n) : ℕ), ((e edge.2 : Fin n) : ℕ))) = edges := by
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [show (fun edge : {value // value ∈ edges} =>
        (((e (sourceAtomRef e edge.1.1 (bound edge.1 edge.2).1) : Fin n) : ℕ),
          ((e (sourceAtomRef e edge.1.2 (bound edge.1 edge.2).2) : Fin n) : ℕ))) =
      Subtype.val from by
    funext edge
    obtain ⟨⟨left, right⟩, member⟩ := edge
    simp [sourceAtomRef]]
  exact List.attach_map_subtype_val edges

/-- Decoding an ordered list of face cycles through the external enumeration returns exactly the
source face list, so face order and multiplicity are preserved. -/
theorem map_sourceAtomRef_faces {n : ℕ} (e : V ≃ Fin n) (faces : List (List ℕ))
    (bound : ∀ face ∈ faces, ∀ atom ∈ face, atom < n) :
    (faces.attach.map (fun face =>
        face.1.attach.map (fun atom =>
          sourceAtomRef e atom.1 (bound face.1 face.2 atom.1 atom.2)))).map
        (fun face => face.map (fun value => (((e value : Fin n) : ℕ)))) = faces := by
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [show (fun face : {value // value ∈ faces} =>
        (face.1.attach.map (fun atom =>
          sourceAtomRef e atom.1 (bound face.1 face.2 atom.1 atom.2))).map
            (fun value => (((e value : Fin n) : ℕ)))) = Subtype.val from by
    funext face
    exact map_sourceAtomRef_atoms e face.1
      (fun atom member => bound face.1 face.2 atom member)]
  exact List.attach_map_subtype_val faces

/-- Explicit finite-universe bounds for constructing an annotation from a bare package.  These are
the only source facts used by the bare-package adapter.  No field asserts that decoding returns the
package; that is proved from the construction. -/
structure PackageBounds (package : MolecularFullereneNumberedCagePackage) (atomCount : ℕ) : Prop where
  /-- Every listed source atom lies in the finite universe. -/
  locantBound : ∀ atom ∈ package.atomsByLocant, atom < atomCount
  /-- Every edge endpoint lies in the finite universe. -/
  edgeBound : ∀ edge ∈ package.edgeTable, edge.1 < atomCount ∧ edge.2 < atomCount
  /-- Every edge is incident with two carrier atoms. -/
  edgeCarrier : ∀ edge ∈ package.edgeTable,
    edge.1 ∈ package.carrier ∧ edge.2 ∈ package.carrier
  /-- No listed edge is a self-loop. -/
  edgeDistinct : ∀ edge ∈ package.edgeTable, edge.1 ≠ edge.2
  /-- Every facial atom is a carrier atom. -/
  faceCarrier : ∀ face ∈ package.faces, ∀ atom ∈ face, atom ∈ package.carrier
  /-- A facial cycle has no repeated atom. -/
  faceNodup : ∀ face ∈ package.faces, face.Nodup

/-- Decode an annotation to the numbered package it records.  Only the annotation fields and the
external enumeration are used; the addend sidecar is not read, because the numbered package has no
addend field. -/
def decode (annotation : NumberedCageAnnotation V) (e : V ≃ Fin annotation.atomCount) :
    MolecularFullereneNumberedCagePackage where
  atomsByLocant := annotation.vertices.map
    (fun vertex => (((e vertex : Fin annotation.atomCount) : ℕ)))
  edgeTable := annotation.edges.map
    (fun edge => (((e edge.1 : Fin annotation.atomCount) : ℕ),
      ((e edge.2 : Fin annotation.atomCount) : ℕ)))
  faces := annotation.faces.map
    (fun face => face.map (fun vertex => (((e vertex : Fin annotation.atomCount) : ℕ))))

/-- Extensionality for the numbered package, used to split exact recovery into its three fields. -/
theorem package_ext {first second : MolecularFullereneNumberedCagePackage}
    (atomsByLocant : first.atomsByLocant = second.atomsByLocant)
    (edgeTable : first.edgeTable = second.edgeTable)
    (faces : first.faces = second.faces) : first = second := by
  cases first
  cases second
  simp_all

/-- The core bounded constructor: a bare package together with explicit `PackageBounds`, an
external enumeration, and an arbitrary addend sidecar.  Static bounds are the only assumptions
about the package; no recovery equation is assumed. -/
def ofPackageWithAddends
    (package : MolecularFullereneNumberedCagePackage) (atomCount : ℕ)
    (bounds : PackageBounds package atomCount)
    (addendInteractions : List (List V × SemanticInteractionKind))
    (addend_arity : ∀ interaction ∈ addendInteractions, 2 ≤ interaction.1.length)
    (addend_nodup : ∀ interaction ∈ addendInteractions, interaction.1.Nodup)
    (e : V ≃ Fin atomCount) : NumberedCageAnnotation V where
  atomCount := atomCount
  locants := (List.range package.atomsByLocant.length).map (fun index => index + 1)
  vertices := package.atomsByLocant.attach.map
    (fun atom => sourceAtomRef e atom.1 (bounds.locantBound atom.1 atom.2))
  locants_length := by simp
  edges := package.edgeTable.attach.map
    (fun edge => (sourceAtomRef e edge.1.1 (bounds.edgeBound edge.1 edge.2).1,
      sourceAtomRef e edge.1.2 (bounds.edgeBound edge.1 edge.2).2))
  edge_vertices := by
    intro edge member
    simp only [List.mem_map] at member ⊢
    obtain ⟨original, originalMember, rfl⟩ := member
    obtain ⟨⟨left, right⟩, tableMember⟩ := original
    have leftMem : left ∈ package.atomsByLocant :=
      List.mem_toFinset.mp (bounds.edgeCarrier (left, right) tableMember).1
    have rightMem : right ∈ package.atomsByLocant :=
      List.mem_toFinset.mp (bounds.edgeCarrier (left, right) tableMember).2
    constructor
    · refine ⟨⟨left, leftMem⟩, ?_, ?_⟩
      · simp
      · exact sourceAtomRef_proof_irrel e left _ _
    · refine ⟨⟨right, rightMem⟩, ?_, ?_⟩
      · simp
      · exact sourceAtomRef_proof_irrel e right _ _
  edge_distinct := by
    intro edge member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    obtain ⟨⟨left, right⟩, tableMember⟩ := original
    intro equal
    exact bounds.edgeDistinct (left, right) tableMember (sourceAtomRef_injective e equal)
  faces := package.faces.attach.map
    (fun face => face.1.attach.map
      (fun atom => sourceAtomRef e atom.1
        (bounds.locantBound atom.1
          (List.mem_toFinset.mp (bounds.faceCarrier face.1 face.2 atom.1 atom.2)))))
  face_vertices := by
    intro face member vertex vertexMember
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    obtain ⟨originalFace, faceMember⟩ := original
    simp only [List.mem_map] at vertexMember
    obtain ⟨atom, _, rfl⟩ := vertexMember
    obtain ⟨value, valueMember⟩ := atom
    simp only [List.mem_map]
    have valueCarrier : value ∈ package.atomsByLocant :=
      List.mem_toFinset.mp (bounds.faceCarrier originalFace faceMember value valueMember)
    refine ⟨⟨value, valueCarrier⟩, ?_, ?_⟩
    · simp
    · exact sourceAtomRef_proof_irrel e value _ _
  face_nodup := by
    intro face member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    obtain ⟨originalFace, faceMember⟩ := original
    exact List.Nodup.map_on
      (f := fun atom : {value // value ∈ originalFace} =>
        sourceAtomRef e atom.1
          (bounds.locantBound atom.1
            (List.mem_toFinset.mp (bounds.faceCarrier originalFace faceMember atom.1 atom.2))))
      (by
        intro first _ second _ equal
        exact Subtype.ext (sourceAtomRef_injective e equal))
      ((bounds.faceNodup originalFace faceMember).attach)
  addendInteractions := addendInteractions
  addend_arity := addend_arity
  addend_nodup := addend_nodup

/-- Exact recovery of the source package from the core construction: decoding returns precisely
the package that supplied the data. -/
theorem decode_ofPackageWithAddends
    (package : MolecularFullereneNumberedCagePackage) (atomCount : ℕ)
    (bounds : PackageBounds package atomCount)
    (addendInteractions : List (List V × SemanticInteractionKind))
    (addend_arity : ∀ interaction ∈ addendInteractions, 2 ≤ interaction.1.length)
    (addend_nodup : ∀ interaction ∈ addendInteractions, interaction.1.Nodup)
    (e : V ≃ Fin atomCount) :
    (ofPackageWithAddends package atomCount bounds addendInteractions addend_arity
      addend_nodup e).decode e = package := by
  apply package_ext
  · exact map_sourceAtomRef_atoms e package.atomsByLocant bounds.locantBound
  · exact map_sourceAtomRef_edges e package.edgeTable bounds.edgeBound
  · exact map_sourceAtomRef_faces e package.faces (fun face faceMember atom atomMember =>
      bounds.locantBound atom
        (List.mem_toFinset.mp (bounds.faceCarrier face faceMember atom atomMember)))

/-- Construct an annotation from a bare numbered package given an explicit `PackageBounds`
certificate and an external enumeration.  The addend sidecar is empty. -/
def ofPackage (package : MolecularFullereneNumberedCagePackage) (atomCount : ℕ)
    (bounds : PackageBounds package atomCount) (e : V ≃ Fin atomCount) :
    NumberedCageAnnotation V :=
  ofPackageWithAddends package atomCount bounds [] (by simp) (by simp) e

/-- Decoding the bare-package annotation returns the bare package exactly. -/
theorem decode_ofPackage (package : MolecularFullereneNumberedCagePackage) (atomCount : ℕ)
    (bounds : PackageBounds package atomCount) (e : V ≃ Fin atomCount) :
    (ofPackage package atomCount bounds e).decode e = package := by
  simpa only [ofPackage] using
    decode_ofPackageWithAddends package atomCount bounds [] _ _ e

/-- The bounds supplied by an actual `FullereneSourceEncoding`.  No extra assumption is added. -/
def sourceBounds (source : FullereneSourceEncoding) :
    PackageBounds source.package source.atomCount where
  locantBound := source.locantBound
  edgeBound := source.edgeBound
  edgeCarrier := source.edgeCarrier
  edgeDistinct := source.edgeDistinct
  faceCarrier := source.faceCarrier
  faceNodup := source.faceNodup

/-- Adapter from an actual bounded `FullereneSourceEncoding` to a `NumberedCageAnnotation V`,
using an external enumeration of the source atom universe.  All bounds are the source encoding's
own fields.  The cage vertices, edge table, faces, and addend sidecar are retained; the optional
spatial data is not a cage field and is not stored here. -/
def ofSource (source : FullereneSourceEncoding) (e : V ≃ Fin source.atomCount) :
    NumberedCageAnnotation V :=
  ofPackageWithAddends source.package source.atomCount (sourceBounds source)
    (source.addendInteractions.map
      (fun interaction => (interaction.1.map e.symm, interaction.2)))
    (by
      intro interaction member
      simp only [List.mem_map] at member
      obtain ⟨original, originalMember, rfl⟩ := member
      simpa using source.addendArity original originalMember)
    (by
      intro interaction member
      simp only [List.mem_map] at member
      obtain ⟨original, originalMember, rfl⟩ := member
      exact (source.addendNodup original originalMember).map e.symm.injective)
    e

/-- Exact recovery from the source adapter: decoding the annotation returns the actual package,
with its numbered locant order, canonical edge table, and oriented face list. -/
theorem decode_ofSource (source : FullereneSourceEncoding) (e : V ≃ Fin source.atomCount) :
    (ofSource source e).decode e = source.package := by
  simpa only [ofSource] using
    decode_ofPackageWithAddends source.package source.atomCount (sourceBounds source) _ _ _ e

/-- Field-by-field form of source recovery. -/
theorem decode_ofSource_fields (source : FullereneSourceEncoding)
    (e : V ≃ Fin source.atomCount) :
    ((ofSource source e).decode e).atomsByLocant = source.package.atomsByLocant ∧
      ((ofSource source e).decode e).edgeTable = source.package.edgeTable ∧
      ((ofSource source e).decode e).faces = source.package.faces := by
  rw [decode_ofSource]
  exact ⟨rfl, rfl, rfl⟩

/-- The addend sidecar is retained unchanged in the source adapter. -/
@[simp] theorem ofSource_addendInteractions (source : FullereneSourceEncoding)
    (e : V ≃ Fin source.atomCount) :
    (ofSource source e).addendInteractions =
      source.addendInteractions.map
        (fun interaction => (interaction.1.map e.symm, interaction.2)) := rfl

/-- Decoding commutes with atom relabelling: relabelling a `V`-annotation by `f` and decoding
through `e` is the same as decoding through `f.trans e`.  This shows that the decoded package is a
function of the annotation fields and the external decoder only. -/
theorem decode_relabel (annotation : NumberedCageAnnotation V) (f : V ≃ W)
    (e : W ≃ Fin annotation.atomCount) :
    (annotation.relabel f).decode e = annotation.decode (f.trans e) := by
  apply package_ext <;>
    simp [decode, relabel, relabelEdge, relabelFace, List.map_map, Function.comp_def]

/-! ## The cage/addend boundary -/

/-- All atoms occurring in the addend/appendage sidecar, in source interaction order and with
multiplicity.  This is the addend half of the cage/addend boundary needed by the whole-state
join; the cage half is `vertices`. -/
def addendAtoms (annotation : NumberedCageAnnotation V) : List V :=
  (annotation.addendInteractions.map (fun interaction => interaction.1)).flatten

@[simp] theorem addendAtoms_mem (annotation : NumberedCageAnnotation V) (atom : V) :
    atom ∈ annotation.addendAtoms ↔
      ∃ interaction ∈ annotation.addendInteractions, atom ∈ interaction.1 := by
  simp [addendAtoms]

@[simp] theorem relabel_addendAtoms (f : V ≃ W) (annotation : NumberedCageAnnotation V) :
    (annotation.relabel f).addendAtoms = annotation.addendAtoms.map f := by
  simp [addendAtoms, relabel, relabelFace, List.map_map, Function.comp_def]

end NumberedCageAnnotation

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.map_sourceAtomRef_atoms
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.map_sourceAtomRef_edges
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.map_sourceAtomRef_faces
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.decode_ofPackageWithAddends
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.decode_ofPackage
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.decode_ofSource
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.decode_ofSource_fields
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.decode_relabel
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.relabel_symm_relabel
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.relabel_relabel_symm
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.relabel_trans
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.relabel_injective
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.relabelList_symm_relabel
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.relabelList_relabel_symm
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.relabelList_injective
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.addendAtoms_mem
assert_kernel_only
  TetraStereo.OneCenter.NumberedCageAnnotation.relabel_addendAtoms
