import TetraStereo.OneCenter.IUPACP93FullereneAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoFullereneSourceEncoding
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false

/-!
# Lossless native ingress for the P-93.5.6 fullerene authority carrier

This module implements the missing full-authority codec for
`P93FullereneAuthorityObservation`, `P93FullereneType4AuthorityObservation`,
`P93FullereneSuperimposedAuthorityObservation` and
`P93FullereneMethodologyAuthorityObservation`.

The cage codec in `OrganicStereoFullereneSourceEncoding` only carries the numbered-cage package.
The authority observations additionally carry

* the ordered input family together with the separately selected input,
* the numbering and substitution evidence of every input,
* the ordered substitution test and descriptor evidence,
* the configuration assignment and the ordered substituent CIP assignments,
* the raw molecule syntax.

All of those are represented here over an arbitrary finite atom label type `V`, using the
enumeration fixed by `OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding`.  The
native representation uses genuine graph labels `V` for every source atom index that is in range.
Source indices that existing validity does *not* bound (notably unused inputs and, unless the
corresponding completeness hypothesis is available, substituent assignments) are retained as
explicit `NativeAtomRef.unresolved` metadata.  They are never silently dropped, and the admitted
domain is therefore not silently restricted.

The spatial field of a general observation is not duplicated as a payload escape.  The codec
reconstructs it from the shared coordinate channel of the binding, and the inverse is proved for
exactly the observations whose stored spatial field is the one observed at that source.

No original observation is stored in the native structures.  Literal syntax (raw molecule,
citation tokens, descriptors, substitution-test data and the full identity-class list) is copied
verbatim.  Ordered lists stay ordered lists; `Finset` fields stay `Finset` fields; and the seven
constructors of `P93FullereneSubstituentStereogenicUnit` are preserved individually, in particular
`doubleBond` and `bondAxis`, which `toPhysicalUnit` deliberately collapses.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic
open OrganicStereoP93PhysicalFrameIngress

namespace OrganicStereoFullereneAuthorityIngress

/-! ## Native atom references

An in-range source atom is stored by its actual graph label.  An out-of-range source reference is
stored with its original `Nat` value and is visibly unresolved.  The construction therefore has no
partial `Nat`-to-label conversion and no hidden domain restriction.
-/

/-- One source atom reference. -/
inductive NativeAtomRef (V : Type*) where
  | resolved (atom : V)
  | unresolved (index : Nat)
  deriving DecidableEq

namespace NativeAtomRef

/-- The reference denotes an actual graph vertex. -/
def IsResolved {V : Type*} : NativeAtomRef V → Prop
  | .resolved _ => True
  | .unresolved _ => False

/-- A native reference is canonical when it is exactly the codec image of its decoded index. -/
def IsCanonical {V : Type*} (encode : Nat → NativeAtomRef V)
    (decode : NativeAtomRef V → Nat) (ref : NativeAtomRef V) : Prop :=
  encode (decode ref) = ref

end NativeAtomRef

/-- Every reference of an ordered list is resolved. -/
def NativeAtomRefListResolved {V : Type*} (refs : List (NativeAtomRef V)) : Prop :=
  ∀ ref ∈ refs, NativeAtomRef.IsResolved ref

/-- Every reference of a finite set is resolved. -/
def NativeAtomRefFinsetResolved {V : Type*} (refs : Finset (NativeAtomRef V)) : Prop :=
  ∀ ref ∈ refs, NativeAtomRef.IsResolved ref

/-! ## Index codec -/

/-- Encode a source atom index through an enumeration.  In range it is the actual label; out of
range it is explicit unresolved source metadata. -/
def encodeAtomRef {V : Type*} {n : Nat} (enumeration : V ≃ Fin n) (index : Nat) :
    NativeAtomRef V :=
  if bound : index < n then
    .resolved (enumeration.symm ⟨index, bound⟩)
  else
    .unresolved index

/-- Decode a native reference to its original source index. -/
def decodeAtomRef {V : Type*} {n : Nat} (enumeration : V ≃ Fin n) :
    NativeAtomRef V → Nat
  | .resolved atom => (enumeration atom).val
  | .unresolved index => index

@[simp] theorem decodeAtomRef_encodeAtomRef {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (index : Nat) :
    decodeAtomRef enumeration (encodeAtomRef enumeration index) = index := by
  by_cases bounded : index < n
  · simp [encodeAtomRef, decodeAtomRef, bounded]
  · simp [encodeAtomRef, decodeAtomRef, bounded]

theorem encodeAtomRef_of_lt {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (index : Nat) (bound : index < n) :
    encodeAtomRef enumeration index = .resolved (enumeration.symm ⟨index, bound⟩) := by
  simp [encodeAtomRef, bound]

theorem encodeAtomRef_of_not_lt {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (index : Nat) (bound : ¬ index < n) :
    encodeAtomRef enumeration index = .unresolved index := by
  simp [encodeAtomRef, bound]

@[simp] theorem decodeAtomRef_resolved {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (atom : V) :
    decodeAtomRef enumeration (.resolved atom) = (enumeration atom).val := rfl

@[simp] theorem decodeAtomRef_unresolved {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (index : Nat) :
    decodeAtomRef enumeration (.unresolved index) = index := rfl

/-- An encoded index is resolved exactly when it lies in the source range. -/
theorem encodeAtomRef_isResolved_iff {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (index : Nat) :
    NativeAtomRef.IsResolved (encodeAtomRef enumeration index) ↔ index < n := by
  by_cases bounded : index < n
  · rw [encodeAtomRef_of_lt enumeration index bounded]
    exact iff_of_true trivial bounded
  · rw [encodeAtomRef_of_not_lt enumeration index bounded]
    exact iff_of_false (by simp [NativeAtomRef.IsResolved]) bounded

/-- The index codec is injective.  Out-of-range references are retained, so this is a genuine
inverse on the whole source `Nat` space. -/
theorem encodeAtomRef_injective {V : Type*} {n : Nat} (enumeration : V ≃ Fin n) :
    Function.Injective (encodeAtomRef enumeration) := by
  intro left right equal
  have := congrArg (decodeAtomRef enumeration) equal
  simpa using this

/-- Resolved references are canonical. -/
theorem encodeAtomRef_resolved_isCanonical {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (atom : V) :
    NativeAtomRef.IsCanonical (encodeAtomRef enumeration) (decodeAtomRef enumeration)
      (.resolved atom) := by
  unfold NativeAtomRef.IsCanonical
  rw [decodeAtomRef_resolved, encodeAtomRef_of_lt enumeration (enumeration atom).val
    (enumeration atom).isLt]
  congr 1
  exact enumeration.symm_apply_apply atom

/-- Out-of-range references are canonical. -/
theorem encodeAtomRef_unresolved_isCanonical {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) {index : Nat} (bound : ¬ index < n) :
    NativeAtomRef.IsCanonical (encodeAtomRef enumeration) (decodeAtomRef enumeration)
      (.unresolved index) := by
  unfold NativeAtomRef.IsCanonical
  rw [decodeAtomRef_unresolved, encodeAtomRef_of_not_lt enumeration index bound]

/-! ### Ordered lists -/

/-- Ordered list encoding.  Order, duplicates and multiplicity are preserved. -/
def encodeAtomRefList {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (indices : List Nat) : List (NativeAtomRef V) :=
  indices.map (encodeAtomRef enumeration)

/-- Ordered list decoding. -/
def decodeAtomRefList {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (refs : List (NativeAtomRef V)) : List Nat :=
  refs.map (decodeAtomRef enumeration)

@[simp] theorem decodeAtomRefList_encodeAtomRefList {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (indices : List Nat) :
    decodeAtomRefList enumeration (encodeAtomRefList enumeration indices) = indices := by
  induction indices with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [encodeAtomRefList, decodeAtomRefList, List.map_cons] at inductionHypothesis ⊢
      rw [decodeAtomRef_encodeAtomRef]
      rw [inductionHypothesis]

/-- Right inverse on an arbitrary ordered list of canonical references. -/
theorem encodeAtomRefList_decodeAtomRefList {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (refs : List (NativeAtomRef V))
    (canonical : ∀ ref ∈ refs,
      NativeAtomRef.IsCanonical (encodeAtomRef enumeration) (decodeAtomRef enumeration) ref) :
    encodeAtomRefList enumeration (decodeAtomRefList enumeration refs) = refs := by
  induction refs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [encodeAtomRefList, decodeAtomRefList, List.map_cons] at inductionHypothesis ⊢
      rw [canonical head (by simp)]
      rw [inductionHypothesis (fun ref member => canonical ref (by simp [member]))]

/-! ### Finite sets -/

/-- Finite-set encoding.  Duplicate-free set semantics are retained. -/
def encodeAtomRefFinset {V : Type*} [DecidableEq V] {n : Nat} (enumeration : V ≃ Fin n)
    (indices : Finset Nat) : Finset (NativeAtomRef V) :=
  indices.image (encodeAtomRef enumeration)

/-- Finite-set decoding. -/
def decodeAtomRefFinset {V : Type*} [DecidableEq V] {n : Nat} (enumeration : V ≃ Fin n)
    (refs : Finset (NativeAtomRef V)) : Finset Nat :=
  refs.image (decodeAtomRef enumeration)

@[simp] theorem decodeAtomRefFinset_encodeAtomRefFinset {V : Type*} [DecidableEq V] {n : Nat}
    (enumeration : V ≃ Fin n) (indices : Finset Nat) :
    decodeAtomRefFinset enumeration (encodeAtomRefFinset enumeration indices) = indices := by
  unfold decodeAtomRefFinset encodeAtomRefFinset
  rw [Finset.image_image]
  ext index
  simp only [Function.comp_apply, decodeAtomRef_encodeAtomRef, Finset.mem_image]
  constructor
  · rintro ⟨source, hsource, hEq⟩
    rwa [← hEq]
  · intro hindex
    exact ⟨index, hindex, rfl⟩

/-- Right inverse on an arbitrary finite set of canonical references. -/
theorem encodeAtomRefFinset_decodeAtomRefFinset {V : Type*} [DecidableEq V] {n : Nat}
    (enumeration : V ≃ Fin n) (refs : Finset (NativeAtomRef V))
    (canonical : ∀ ref ∈ refs,
      NativeAtomRef.IsCanonical (encodeAtomRef enumeration) (decodeAtomRef enumeration) ref) :
    encodeAtomRefFinset enumeration (decodeAtomRefFinset enumeration refs) = refs := by
  unfold encodeAtomRefFinset decodeAtomRefFinset
  rw [Finset.image_image]
  ext ref
  simp only [Function.comp_apply, Finset.mem_image]
  constructor
  · rintro ⟨source, hsource, hEq⟩
    rw [canonical source hsource] at hEq
    rwa [← hEq]
  · intro href
    exact ⟨ref, href, canonical ref href⟩

/-! ## Native records

These are the exact authority payloads with every atom-index occurrence moved into
`NativeAtomRef`.  Literal data (substitution tests, descriptors, citations, identity classes,
handedness and turn values) is copied verbatim.
-/

/-- Native numbering evidence. -/
structure NativeNumberingEvidence (V : Type*) where
  numberingKind : FullereneNumberingKind
  atomsByLocant : List (NativeAtomRef V)
  startingFace : List (NativeAtomRef V)

/-- Native substitution evidence.  The full `actualIdentityClassAt` list is retained, including
entries beyond the selected cage sites. -/
structure NativeSubstitutionEvidence (V : Type*) where
  substitutedSites : Finset (NativeAtomRef V)
  actualIdentityClassAt : List Nat
  originalDerivativeChiral : Bool
  chiralSubstituentSites : Finset (NativeAtomRef V)

/-- Native molecular fullerene configuration input. -/
structure NativeMolecularFullereneConfigurationInput (V : Type*) where
  carrier : Finset (NativeAtomRef V)
  faces : List (List (NativeAtomRef V))
  substitutionTest : FullereneSubstitutionTest
  descriptorEvidence : FullereneDescriptorEvidence

/-- Native symmetry-derived input (cage plus substitution evidence). -/
structure NativeSymmetryDerivedInput (V : Type*) where
  cage : NativeMolecularFullereneConfigurationInput V
  substitutionEvidence : NativeSubstitutionEvidence V

/-- Native spatially-derived input (symmetry input plus numbering evidence). -/
structure NativeSpatiallyDerivedInput (V : Type*) where
  symmetryInput : NativeSymmetryDerivedInput V
  numberingEvidence : NativeNumberingEvidence V

/-- Native stereogenic unit.  All seven source constructors are retained.  In particular
`doubleBond` and `bondAxis` remain distinct. -/
inductive NativeSubstituentStereogenicUnit (V : Type*) where
  | center (atom : NativeAtomRef V)
  | doubleBond (first second : NativeAtomRef V)
  | cumuleneAxis (path : List (NativeAtomRef V))
  | bondAxis (first second : NativeAtomRef V)
  | plane (members : Finset (NativeAtomRef V))
  | helix (path : List (NativeAtomRef V))
  | polyhedron (center : NativeAtomRef V) (positions : Finset (NativeAtomRef V))
  deriving DecidableEq

/-- Native substituent CIP assignment. -/
structure NativeSubstituentCIPAssignment (V : Type*) where
  substitutedSite : NativeAtomRef V
  unit : NativeSubstituentStereogenicUnit V
  citation : P93AuthorityCitationToken
  descriptor : P93FullereneSubstituentCIPDescriptor

/-- Native fullerene configuration assignment. -/
structure NativeFullereneConfigurationAssignment (V : Type*) where
  unit : List (NativeAtomRef V)
  chiralityType : FullereneChiralityType
  payloads : List FullereneDescriptorPayload

/-- Native general authority observation.  The spatial field is not stored: it is reconstructed
from the shared coordinate channel of the binding.  The raw molecule syntax is retained. -/
structure NativeFullereneAuthorityObservation (V : Type*) where
  molecule : RawMolecule
  inputs : List (NativeSpatiallyDerivedInput V)
  selectedInput : NativeSpatiallyDerivedInput V
  assignment : NativeFullereneConfigurationAssignment V
  substituentAssignments : List (NativeSubstituentCIPAssignment V)

/-- Native Type 4 authority observation. -/
structure NativeFullereneType4AuthorityObservation (V : Type*) where
  molecule : RawMolecule
  input : NativeSymmetryDerivedInput V
  substituentAssignments : List (NativeSubstituentCIPAssignment V)

/-- Native superimposed authority observation. -/
structure NativeFullereneSuperimposedAuthorityObservation (V : Type*) where
  base : NativeFullereneAuthorityObservation V

/-- Native methodology observation.  It has no molecule-specific physical payload. -/
inductive NativeFullereneMethodologyAuthorityObservation where
  | fourWayDecisionRule

/-! ## The four-row tagged authority collection

The four existing authority rows are kept as four explicit constructors.  A tagged value retains
its row and its complete payload; a list retains order, repetitions and the interleaving of rows;
a set retains whole correlated observations rather than a product of per-row marginals.  Neither
the source-side nor the encoded-side sum stores an original whole source record as an opaque
escape: the encoded constructors carry exactly the native records defined above.
-/

/-- The tagged source-side authority observation. -/
inductive SourceFullereneAuthorityObservation (policy : P93FullereneAuthorityPolicy) where
  | general (observation : P93FullereneAuthorityObservation policy)
  | type4 (observation : P93FullereneType4AuthorityObservation policy)
  | superimposed (observation : P93FullereneSuperimposedAuthorityObservation policy)
  | methodology (observation : P93FullereneMethodologyAuthorityObservation)

/-- The tagged encoded-side authority observation. -/
inductive NativeFullereneAuthorityObservationFamily (V : Type*) where
  | general (observation : NativeFullereneAuthorityObservation V)
  | type4 (observation : NativeFullereneType4AuthorityObservation V)
  | superimposed (observation : NativeFullereneSuperimposedAuthorityObservation V)
  | methodology (observation : NativeFullereneMethodologyAuthorityObservation)

namespace SourceFullereneAuthorityObservation

/-- Row-dispatched actual source validity.  Each branch is exactly the existing row predicate. -/
def ValidFor {policy : P93FullereneAuthorityPolicy} (source : AuthoritativeChemicalInput) :
    SourceFullereneAuthorityObservation policy → Prop
  | .general observation => observation.ValidFor policy source
  | .type4 observation => observation.ValidFor policy source
  | .superimposed observation => observation.ValidFor policy source
  | .methodology observation => observation.ValidFor policy source

/-- The shared observed spatial premise used by spatial reconstruction.  It is a consequence of
`ValidFor`, not an additional validity condition. -/
def ObservedSpatialAt {policy : P93FullereneAuthorityPolicy}
    (source : AuthoritativeChemicalInput) :
    SourceFullereneAuthorityObservation policy → Prop
  | .general observation => source.spatial? = some observation.spatial
  | .type4 _ => True
  | .superimposed observation => source.spatial? = some observation.base.spatial
  | .methodology _ => True

/-- The observation-specific semantic conversion equality.  `FullereneAuthorityCommonSource`'s
`conversion_eq` is an equality for `source.molecule`; it does not identify an arbitrary
observation's own `molecule` with the source molecule.  This predicate states that equality
explicitly for the observation that needs it. -/
def MoleculeBoundTo {policy : P93FullereneAuthorityPolicy}
    (source : AuthoritativeChemicalInput) :
    SourceFullereneAuthorityObservation policy → Prop
  | .general observation => observation.molecule.toSemanticMolecule? = some source.molecule
  | .type4 observation => observation.molecule.toSemanticMolecule? = some source.molecule
  | .superimposed observation =>
      observation.base.molecule.toSemanticMolecule? = some source.molecule
  | .methodology _ => True

/-- The shared spatial premise follows from the row's actual `ValidFor`: general validity stores it
as its first conjunct and superimposed validity stores it as the first conjunct of the base row. -/
theorem observedSpatialAt_of_validFor {policy : P93FullereneAuthorityPolicy}
    (source : AuthoritativeChemicalInput)
    (observation : SourceFullereneAuthorityObservation policy)
    (valid : observation.ValidFor source) :
    observation.ObservedSpatialAt source := by
  cases observation with
  | general observation => exact valid.1
  | type4 _ => trivial
  | superimposed observation => exact valid.1.1
  | methodology _ => trivial

end SourceFullereneAuthorityObservation

/-! ## The common source -/

/-- A common source binds the full authority codec to the accepted physical-frame ingress.

`conversion_eq` is deliberately an explicit equality of `RawMolecule.toSemanticMolecule?` with the
bound source molecule.  The arbitrary policy relation `RawMoleculeObserved` does not imply this
equality, and no theorem below claims that it does.  Requiring it is what makes the native
molecule genuinely the molecule of the shared graph, not merely a molecule with the same atom
count. -/
structure FullereneAuthorityCommonSource (V : Type*) [DecidableEq V] [Fintype V] where
  binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V
  molecule : RawMolecule
  conversion_eq : molecule.toSemanticMolecule? = some binding.source.molecule

namespace FullereneAuthorityCommonSource

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The enumeration supplied by the accepted source binding. -/
def enumeration (source : FullereneAuthorityCommonSource V) :
    V ≃ Fin (Fintype.card V) :=
  source.binding.enumeration

/-- The native resolver.  In range, the index becomes the actual source graph label. -/
def toNativeAtom (source : FullereneAuthorityCommonSource V) (index : Nat) :
    NativeAtomRef V :=
  encodeAtomRef source.enumeration index

/-- The native decoder.  It returns the original source index, including out-of-range metadata. -/
def ofNativeAtom (source : FullereneAuthorityCommonSource V) (ref : NativeAtomRef V) : Nat :=
  decodeAtomRef source.enumeration ref

@[simp] theorem ofNativeAtom_toNativeAtom (source : FullereneAuthorityCommonSource V)
    (index : Nat) :
    source.ofNativeAtom (source.toNativeAtom index) = index := by
  simp [toNativeAtom, ofNativeAtom]

theorem ofNativeAtom_comp_toNativeAtom (source : FullereneAuthorityCommonSource V) :
    source.ofNativeAtom ∘ source.toNativeAtom = id := by
  funext index
  simp [toNativeAtom, ofNativeAtom]

/-- The resolver is injective on the whole source `Nat` space. -/
theorem toNativeAtom_injective (source : FullereneAuthorityCommonSource V) :
    Function.Injective source.toNativeAtom := by
  intro left right equal
  have := congrArg source.ofNativeAtom equal
  simpa using this

/-- Ordered-list encoding through the common source. -/
def toNativeList (source : FullereneAuthorityCommonSource V) (indices : List Nat) :
    List (NativeAtomRef V) :=
  encodeAtomRefList source.enumeration indices

/-- Ordered-list decoding through the common source. -/
def ofNativeList (source : FullereneAuthorityCommonSource V) (refs : List (NativeAtomRef V)) :
    List Nat :=
  decodeAtomRefList source.enumeration refs

@[simp] theorem ofNativeList_toNativeList (source : FullereneAuthorityCommonSource V)
    (indices : List Nat) :
    source.ofNativeList (source.toNativeList indices) = indices := by
  simp [toNativeList, ofNativeList]

/-- Finite-set encoding through the common source. -/
def toNativeFinset (source : FullereneAuthorityCommonSource V) (indices : Finset Nat) :
    Finset (NativeAtomRef V) :=
  encodeAtomRefFinset source.enumeration indices

/-- Finite-set decoding through the common source. -/
def ofNativeFinset (source : FullereneAuthorityCommonSource V)
    (refs : Finset (NativeAtomRef V)) : Finset Nat :=
  decodeAtomRefFinset source.enumeration refs

@[simp] theorem ofNativeFinset_toNativeFinset (source : FullereneAuthorityCommonSource V)
    (indices : Finset Nat) :
    source.ofNativeFinset (source.toNativeFinset indices) = indices := by
  simp [toNativeFinset, ofNativeFinset]

/-- Actual graph atom data at an in-range source index, read through the source graph equality.
This is the native resolver's backing theorem: the resolved label is the shared graph's atom. -/
theorem toNativeAtom_atomData (source : FullereneAuthorityCommonSource V) (index : Nat)
    (bound : index < Fintype.card V) :
    listGet? source.binding.source.molecule.atoms index =
      some (source.binding.shared.graph.atomData
        (source.enumeration.symm ⟨index, bound⟩)) := by
  rw [← source.binding.graph_eq]
  exact FiniteAtomInteractionHypergraph.encode_atomAt
    source.binding.shared.graph source.enumeration ⟨index, bound⟩

/-- The source graph equality gives the exact atom count, not merely a transport assumption. -/
theorem source_atomCount_eq_card (source : FullereneAuthorityCommonSource V) :
    source.binding.source.molecule.atomCount = Fintype.card V :=
  source.binding.atomCount_eq

/-- The canonical raw molecule has the same atom count as the shared source. -/
theorem raw_atomCount_eq_card (source : FullereneAuthorityCommonSource V) :
    source.molecule.atomCount = Fintype.card V := by
  have converted := RawMolecule.toSemanticMolecule?_atomCount source.molecule
    source.binding.source.molecule source.conversion_eq
  exact converted.symm.trans source.source_atomCount_eq_card

/-- Atom-count agreement follows from the explicit semantic conversion equality plus the exact
source graph equality, not from an equality of counts assumed in advance. -/
theorem sourceBound_atomCount_eq_card (source : FullereneAuthorityCommonSource V)
    (molecule : RawMolecule)
    (bound : molecule.toSemanticMolecule? = some source.binding.source.molecule) :
    molecule.atomCount = Fintype.card V := by
  have converted := RawMolecule.toSemanticMolecule?_atomCount molecule
    source.binding.source.molecule bound
  exact converted.symm.trans source.source_atomCount_eq_card

/-- A source index below the cardinals is in real range and encodes to a real graph label. -/
theorem toNativeAtom_of_lt (source : FullereneAuthorityCommonSource V) {index : Nat}
    (bound : index < Fintype.card V) :
    source.toNativeAtom index =
      .resolved (source.enumeration.symm ⟨index, bound⟩) := by
  simpa [toNativeAtom] using encodeAtomRef_of_lt source.enumeration index bound

/-- In-range indices resolve. -/
theorem toNativeAtom_isResolved_of_lt (source : FullereneAuthorityCommonSource V)
    {index : Nat} (bound : index < Fintype.card V) :
    NativeAtomRef.IsResolved (source.toNativeAtom index) := by
  rw [source.toNativeAtom_of_lt bound]
  simp [NativeAtomRef.IsResolved]

/-! ### Resolution lemmas -/

theorem listResolved_map (source : FullereneAuthorityCommonSource V) {indices : List Nat}
    (bounded : ∀ index ∈ indices, index < Fintype.card V) :
    NativeAtomRefListResolved (indices.map source.toNativeAtom) := by
  intro ref member
  rw [List.mem_map] at member
  obtain ⟨index, indexMember, rfl⟩ := member
  exact source.toNativeAtom_isResolved_of_lt (bounded index indexMember)

theorem finsetResolved_image (source : FullereneAuthorityCommonSource V) {indices : Finset Nat}
    (bounded : ∀ index ∈ indices, index < Fintype.card V) :
    NativeAtomRefFinsetResolved (source.toNativeFinset indices) := by
  intro ref member
  simp only [toNativeFinset, encodeAtomRefFinset, Finset.mem_image] at member
  obtain ⟨index, indexMember, rfl⟩ := member
  exact source.toNativeAtom_isResolved_of_lt (bounded index indexMember)

/-! ### Face lists -/

/-- Ordered face-list encoding.  The order of faces and of atoms within a face is preserved. -/
def encodeFaces (source : FullereneAuthorityCommonSource V) (faces : List (List Nat)) :
    List (List (NativeAtomRef V)) :=
  faces.map fun face => face.map source.toNativeAtom

/-- Ordered face-list decoding. -/
def decodeFaces (source : FullereneAuthorityCommonSource V)
    (faces : List (List (NativeAtomRef V))) : List (List Nat) :=
  faces.map fun face => face.map source.ofNativeAtom

@[simp] theorem decodeFace_encodeFace (source : FullereneAuthorityCommonSource V)
    (face : List Nat) :
    (face.map source.toNativeAtom).map source.ofNativeAtom = face := by
  induction face with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons] at inductionHypothesis ⊢
      rw [ofNativeAtom_toNativeAtom]
      rw [inductionHypothesis]

theorem encodeFace_decodeFace (source : FullereneAuthorityCommonSource V)
    (face : List (NativeAtomRef V))
    (canonical : ∀ ref ∈ face,
      NativeAtomRef.IsCanonical source.toNativeAtom source.ofNativeAtom ref) :
    (face.map source.ofNativeAtom).map source.toNativeAtom = face := by
  induction face with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons] at inductionHypothesis ⊢
      rw [canonical head (by simp)]
      rw [inductionHypothesis (fun ref member => canonical ref (by simp [member]))]

@[simp] theorem decodeFaces_encodeFaces (source : FullereneAuthorityCommonSource V)
    (faces : List (List Nat)) :
    source.decodeFaces (source.encodeFaces faces) = faces := by
  induction faces with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [encodeFaces, decodeFaces, List.map_cons] at inductionHypothesis ⊢
      rw [decodeFace_encodeFace]
      rw [inductionHypothesis]

theorem encodeFaces_decodeFaces (source : FullereneAuthorityCommonSource V)
    (faces : List (List (NativeAtomRef V)))
    (canonical : ∀ face ∈ faces, ∀ ref ∈ face,
      NativeAtomRef.IsCanonical source.toNativeAtom source.ofNativeAtom ref) :
    source.encodeFaces (source.decodeFaces faces) = faces := by
  induction faces with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [encodeFaces, decodeFaces, List.map_cons] at inductionHypothesis ⊢
      rw [encodeFace_decodeFace source head
        (fun ref member => canonical head (by simp) ref member)]
      rw [inductionHypothesis (fun face member ref refMember =>
        canonical face (by simp [member]) ref refMember)]

/-! ### Spatial channel -/

/-- The shared coordinate channel, encoded exactly as the accepted ingress does. -/
def sharedSpatial? (source : FullereneAuthorityCommonSource V) : Option SpatialConfiguration :=
  OrganicFiniteSource.encodeSpatial? source.enumeration source.binding.shared.spatial?

/-- The reconstructed spatial configuration.  It is not stored in the native observation. -/
def spatialConfiguration (source : FullereneAuthorityCommonSource V) : SpatialConfiguration :=
  (source.sharedSpatial?).getD { positions := [] }

theorem sharedSpatial?_eq_source (source : FullereneAuthorityCommonSource V) :
    source.sharedSpatial? = source.binding.source.spatial? :=
  source.binding.spatial_eq

/-- Under an observed source spatial field the reconstruction is exact. -/
theorem spatialConfiguration_eq_of_source (source : FullereneAuthorityCommonSource V)
    (spatial : SpatialConfiguration)
    (observed : source.binding.source.spatial? = some spatial) :
    source.spatialConfiguration = spatial := by
  unfold spatialConfiguration sharedSpatial? enumeration
  rw [source.binding.spatial_eq, observed]
  rfl

/-- The observed source spatial field has exactly one coordinate per source atom. -/
theorem spatialConfiguration_length_of_source (source : FullereneAuthorityCommonSource V)
    (spatial : SpatialConfiguration)
    (observed : source.binding.source.spatial? = some spatial) :
    spatial.positions.length = Fintype.card V := by
  have channel : OrganicFiniteSource.encodeSpatial? source.binding.enumeration
      source.binding.shared.spatial? = some spatial := by
    rw [source.binding.spatial_eq]
    exact observed
  cases shared : source.binding.shared.spatial? with
  | none =>
      simp [OrganicFiniteSource.encodeSpatial?, shared] at channel
  | some positions =>
      rw [shared, OrganicFiniteSource.encodeSpatial?_some] at channel
      have spatialEq : spatial =
          { positions := List.ofFn fun index : Fin (Fintype.card V) =>
              positions (source.binding.enumeration.symm index) } :=
        (Option.some.inj channel).symm
      rw [spatialEq]
      simp

/-! ## Record codecs -/

def encodeNumberingEvidence (source : FullereneAuthorityCommonSource V)
    (evidence : MolecularFullereneNumberingEvidence) : NativeNumberingEvidence V where
  numberingKind := evidence.numberingKind
  atomsByLocant := evidence.atomsByLocant.map source.toNativeAtom
  startingFace := evidence.startingFace.map source.toNativeAtom

def decodeNumberingEvidence (source : FullereneAuthorityCommonSource V)
    (evidence : NativeNumberingEvidence V) : MolecularFullereneNumberingEvidence where
  numberingKind := evidence.numberingKind
  atomsByLocant := evidence.atomsByLocant.map source.ofNativeAtom
  startingFace := evidence.startingFace.map source.ofNativeAtom

@[simp] theorem decodeNumberingEvidence_encodeNumberingEvidence
    (source : FullereneAuthorityCommonSource V) (evidence : MolecularFullereneNumberingEvidence) :
    source.decodeNumberingEvidence (source.encodeNumberingEvidence evidence) = evidence := by
  cases evidence with
  | mk numberingKind atomsByLocant startingFace =>
      simp [encodeNumberingEvidence, decodeNumberingEvidence, List.map_map,
        source.ofNativeAtom_comp_toNativeAtom]

def encodeSubstitutionEvidence (source : FullereneAuthorityCommonSource V)
    (evidence : MolecularFullereneSubstitutionEvidence) : NativeSubstitutionEvidence V where
  substitutedSites := source.toNativeFinset evidence.substitutedSites
  actualIdentityClassAt := evidence.actualIdentityClassAt
  originalDerivativeChiral := evidence.originalDerivativeChiral
  chiralSubstituentSites := source.toNativeFinset evidence.chiralSubstituentSites

def decodeSubstitutionEvidence (source : FullereneAuthorityCommonSource V)
    (evidence : NativeSubstitutionEvidence V) : MolecularFullereneSubstitutionEvidence where
  substitutedSites := source.ofNativeFinset evidence.substitutedSites
  actualIdentityClassAt := evidence.actualIdentityClassAt
  originalDerivativeChiral := evidence.originalDerivativeChiral
  chiralSubstituentSites := source.ofNativeFinset evidence.chiralSubstituentSites

@[simp] theorem decodeSubstitutionEvidence_encodeSubstitutionEvidence
    (source : FullereneAuthorityCommonSource V)
    (evidence : MolecularFullereneSubstitutionEvidence) :
    source.decodeSubstitutionEvidence (source.encodeSubstitutionEvidence evidence) = evidence := by
  cases evidence with
  | mk substitutedSites actualIdentityClassAt originalDerivativeChiral chiralSubstituentSites =>
      simp [encodeSubstitutionEvidence, decodeSubstitutionEvidence]

/-- The identity-class list is copied literally, including entries beyond the cage. -/
@[simp] theorem encodeSubstitutionEvidence_actualIdentityClassAt
    (source : FullereneAuthorityCommonSource V)
    (evidence : MolecularFullereneSubstitutionEvidence) :
    (source.encodeSubstitutionEvidence evidence).actualIdentityClassAt =
      evidence.actualIdentityClassAt := rfl

@[simp] theorem encodeSubstitutionEvidence_originalDerivativeChiral
    (source : FullereneAuthorityCommonSource V)
    (evidence : MolecularFullereneSubstitutionEvidence) :
    (source.encodeSubstitutionEvidence evidence).originalDerivativeChiral =
      evidence.originalDerivativeChiral := rfl

def encodeCage (source : FullereneAuthorityCommonSource V)
    (input : MolecularFullereneConfigurationInput) :
    NativeMolecularFullereneConfigurationInput V where
  carrier := source.toNativeFinset input.carrier
  faces := source.encodeFaces input.faces
  substitutionTest := input.substitutionTest
  descriptorEvidence := input.descriptorEvidence

def decodeCage (source : FullereneAuthorityCommonSource V)
    (input : NativeMolecularFullereneConfigurationInput V) :
    MolecularFullereneConfigurationInput where
  carrier := source.ofNativeFinset input.carrier
  faces := source.decodeFaces input.faces
  substitutionTest := input.substitutionTest
  descriptorEvidence := input.descriptorEvidence

@[simp] theorem decodeCage_encodeCage (source : FullereneAuthorityCommonSource V)
    (input : MolecularFullereneConfigurationInput) :
    source.decodeCage (source.encodeCage input) = input := by
  cases input with
  | mk carrier faces substitutionTest descriptorEvidence =>
      simp [encodeCage, decodeCage]

def encodeSymmetryDerivedInput (source : FullereneAuthorityCommonSource V)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput) :
    NativeSymmetryDerivedInput V where
  cage := source.encodeCage input.cage
  substitutionEvidence := source.encodeSubstitutionEvidence input.substitutionEvidence

def decodeSymmetryDerivedInput (source : FullereneAuthorityCommonSource V)
    (input : NativeSymmetryDerivedInput V) :
    SymmetryDerivedMolecularFullereneConfigurationInput where
  cage := source.decodeCage input.cage
  substitutionEvidence := source.decodeSubstitutionEvidence input.substitutionEvidence

@[simp] theorem decodeSymmetryDerivedInput_encodeSymmetryDerivedInput
    (source : FullereneAuthorityCommonSource V)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput) :
    source.decodeSymmetryDerivedInput (source.encodeSymmetryDerivedInput input) = input := by
  cases input with
  | mk cage substitutionEvidence =>
      simp [encodeSymmetryDerivedInput, decodeSymmetryDerivedInput]

def encodeSpatiallyDerivedInput (source : FullereneAuthorityCommonSource V)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput) :
    NativeSpatiallyDerivedInput V where
  symmetryInput := source.encodeSymmetryDerivedInput input.symmetryInput
  numberingEvidence := source.encodeNumberingEvidence input.numberingEvidence

def decodeSpatiallyDerivedInput (source : FullereneAuthorityCommonSource V)
    (input : NativeSpatiallyDerivedInput V) :
    SpatiallyDerivedMolecularFullereneConfigurationInput where
  symmetryInput := source.decodeSymmetryDerivedInput input.symmetryInput
  numberingEvidence := source.decodeNumberingEvidence input.numberingEvidence

@[simp] theorem decodeSpatiallyDerivedInput_encodeSpatiallyDerivedInput
    (source : FullereneAuthorityCommonSource V)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput) :
    source.decodeSpatiallyDerivedInput (source.encodeSpatiallyDerivedInput input) = input := by
  cases input with
  | mk symmetryInput numberingEvidence =>
      simp [encodeSpatiallyDerivedInput, decodeSpatiallyDerivedInput]

@[simp] theorem decodeSpatiallyDerivedInputList_encode
    (source : FullereneAuthorityCommonSource V)
    (inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput) :
    (inputs.map source.encodeSpatiallyDerivedInput).map source.decodeSpatiallyDerivedInput =
      inputs := by
  induction inputs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons] at inductionHypothesis ⊢
      rw [decodeSpatiallyDerivedInput_encodeSpatiallyDerivedInput]
      rw [inductionHypothesis]

def encodeStereogenicUnit (source : FullereneAuthorityCommonSource V) :
    P93FullereneSubstituentStereogenicUnit → NativeSubstituentStereogenicUnit V
  | .center atom => .center (source.toNativeAtom atom)
  | .doubleBond first second => .doubleBond (source.toNativeAtom first) (source.toNativeAtom second)
  | .cumuleneAxis path => .cumuleneAxis (path.map source.toNativeAtom)
  | .bondAxis first second => .bondAxis (source.toNativeAtom first) (source.toNativeAtom second)
  | .plane members => .plane (source.toNativeFinset members)
  | .helix path => .helix (path.map source.toNativeAtom)
  | .polyhedron center positions =>
      .polyhedron (source.toNativeAtom center) (source.toNativeFinset positions)

def decodeStereogenicUnit (source : FullereneAuthorityCommonSource V) :
    NativeSubstituentStereogenicUnit V → P93FullereneSubstituentStereogenicUnit
  | .center atom => .center (source.ofNativeAtom atom)
  | .doubleBond first second => .doubleBond (source.ofNativeAtom first) (source.ofNativeAtom second)
  | .cumuleneAxis path => .cumuleneAxis (path.map source.ofNativeAtom)
  | .bondAxis first second => .bondAxis (source.ofNativeAtom first) (source.ofNativeAtom second)
  | .plane members => .plane (source.ofNativeFinset members)
  | .helix path => .helix (path.map source.ofNativeAtom)
  | .polyhedron center positions =>
      .polyhedron (source.ofNativeAtom center) (source.ofNativeFinset positions)

@[simp] theorem decodeStereogenicUnit_encodeStereogenicUnit
    (source : FullereneAuthorityCommonSource V) (unit : P93FullereneSubstituentStereogenicUnit) :
    source.decodeStereogenicUnit (source.encodeStereogenicUnit unit) = unit := by
  cases unit <;> simp [encodeStereogenicUnit, decodeStereogenicUnit, List.map_map,
    source.ofNativeAtom_comp_toNativeAtom]

theorem encodeStereogenicUnit_injective (source : FullereneAuthorityCommonSource V) :
    Function.Injective source.encodeStereogenicUnit := by
  intro left right equal
  have := congrArg source.decodeStereogenicUnit equal
  simpa using this

def encodeCIPAssignment (source : FullereneAuthorityCommonSource V)
    (assignment : P93FullereneSubstituentCIPAssignment) :
    NativeSubstituentCIPAssignment V where
  substitutedSite := source.toNativeAtom assignment.substitutedSite
  unit := source.encodeStereogenicUnit assignment.unit
  citation := assignment.citation
  descriptor := assignment.descriptor

def decodeCIPAssignment (source : FullereneAuthorityCommonSource V)
    (assignment : NativeSubstituentCIPAssignment V) :
    P93FullereneSubstituentCIPAssignment where
  substitutedSite := source.ofNativeAtom assignment.substitutedSite
  unit := source.decodeStereogenicUnit assignment.unit
  citation := assignment.citation
  descriptor := assignment.descriptor

@[simp] theorem decodeCIPAssignment_encodeCIPAssignment
    (source : FullereneAuthorityCommonSource V)
    (assignment : P93FullereneSubstituentCIPAssignment) :
    source.decodeCIPAssignment (source.encodeCIPAssignment assignment) = assignment := by
  cases assignment with
  | mk substitutedSite unit citation descriptor =>
      simp [encodeCIPAssignment, decodeCIPAssignment]

@[simp] theorem decodeCIPAssignmentList_encode
    (source : FullereneAuthorityCommonSource V)
    (assignments : List P93FullereneSubstituentCIPAssignment) :
    (assignments.map source.encodeCIPAssignment).map source.decodeCIPAssignment = assignments := by
  induction assignments with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons] at inductionHypothesis ⊢
      rw [decodeCIPAssignment_encodeCIPAssignment]
      rw [inductionHypothesis]

/-- Citation tokens are copied verbatim and are never interpreted as atom references. -/
@[simp] theorem encodeCIPAssignment_citation
    (source : FullereneAuthorityCommonSource V)
    (assignment : P93FullereneSubstituentCIPAssignment) :
    (source.encodeCIPAssignment assignment).citation = assignment.citation := rfl

/-- CIP descriptors are copied verbatim. -/
@[simp] theorem encodeCIPAssignment_descriptor
    (source : FullereneAuthorityCommonSource V)
    (assignment : P93FullereneSubstituentCIPAssignment) :
    (source.encodeCIPAssignment assignment).descriptor = assignment.descriptor := rfl

def encodeAssignment (source : FullereneAuthorityCommonSource V)
    (assignment : FullereneConfigurationAssignment) :
    NativeFullereneConfigurationAssignment V where
  unit := assignment.unit.map source.toNativeAtom
  chiralityType := assignment.chiralityType
  payloads := assignment.payloads

def decodeAssignment (source : FullereneAuthorityCommonSource V)
    (assignment : NativeFullereneConfigurationAssignment V) :
    FullereneConfigurationAssignment where
  unit := assignment.unit.map source.ofNativeAtom
  chiralityType := assignment.chiralityType
  payloads := assignment.payloads

@[simp] theorem decodeAssignment_encodeAssignment
    (source : FullereneAuthorityCommonSource V)
    (assignment : FullereneConfigurationAssignment) :
    source.decodeAssignment (source.encodeAssignment assignment) = assignment := by
  cases assignment with
  | mk unit chiralityType payloads =>
      simp [encodeAssignment, decodeAssignment, List.map_map,
        source.ofNativeAtom_comp_toNativeAtom]

/-! ### Observation codecs -/

def encodeObservation (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneAuthorityObservation policy) :
    NativeFullereneAuthorityObservation V where
  molecule := observation.molecule
  inputs := observation.inputs.map source.encodeSpatiallyDerivedInput
  selectedInput := source.encodeSpatiallyDerivedInput observation.selectedInput
  assignment := source.encodeAssignment observation.assignment
  substituentAssignments := observation.substituentAssignments.map source.encodeCIPAssignment

def decodeObservation (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneAuthorityObservation V) :
    P93FullereneAuthorityObservation policy where
  molecule := observation.molecule
  spatial := source.spatialConfiguration
  inputs := observation.inputs.map source.decodeSpatiallyDerivedInput
  selectedInput := source.decodeSpatiallyDerivedInput observation.selectedInput
  assignment := source.decodeAssignment observation.assignment
  substituentAssignments := observation.substituentAssignments.map source.decodeCIPAssignment

/-- Exact left inverse on observations whose stored spatial field is the one observed at the
bound source.  The spatial field is reconstructed, not stored, so this is the strongest exact
statement available without duplicating the source payload. -/
theorem decodeObservation_encodeObservation (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneAuthorityObservation policy)
    (spatialObserved : source.binding.source.spatial? = some observation.spatial) :
    source.decodeObservation policy (source.encodeObservation policy observation) = observation := by
  cases observation with
  | mk molecule spatial inputs selectedInput assignment substituentAssignments =>
      simp only [encodeObservation, decodeObservation]
      rw [source.spatialConfiguration_eq_of_source spatial spatialObserved]
      have inputRoundTrip :
          List.map (source.decodeSpatiallyDerivedInput ∘ source.encodeSpatiallyDerivedInput)
            inputs = inputs := by
        rw [← List.map_map]
        exact decodeSpatiallyDerivedInputList_encode source inputs
      have assignmentRoundTrip :
          List.map (source.decodeCIPAssignment ∘ source.encodeCIPAssignment)
            substituentAssignments = substituentAssignments := by
        rw [← List.map_map]
        exact decodeCIPAssignmentList_encode source substituentAssignments
      simp [inputRoundTrip, assignmentRoundTrip]

/-- Injectivity of the general codec on observations sharing the source spatial channel. -/
theorem encodeObservation_injective_of_spatial (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (left right : P93FullereneAuthorityObservation policy)
    (leftSpatial : source.binding.source.spatial? = some left.spatial)
    (rightSpatial : source.binding.source.spatial? = some right.spatial)
    (equal : source.encodeObservation policy left = source.encodeObservation policy right) :
    left = right := by
  calc
    left = source.decodeObservation policy (source.encodeObservation policy left) :=
      (source.decodeObservation_encodeObservation policy left leftSpatial).symm
    _ = source.decodeObservation policy (source.encodeObservation policy right) := by rw [equal]
    _ = right := source.decodeObservation_encodeObservation policy right rightSpatial

/-- Injectivity on valid observations at the same source and policy. -/
theorem encodeObservation_injective_of_valid (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (left right : P93FullereneAuthorityObservation policy)
    (leftValid : left.ValidFor policy source.binding.source)
    (rightValid : right.ValidFor policy source.binding.source)
    (equal : source.encodeObservation policy left = source.encodeObservation policy right) :
    left = right :=
  source.encodeObservation_injective_of_spatial policy left right leftValid.1 rightValid.1 equal

/-- Validity is preserved exactly by encode followed by decode at the same source and policy. -/
theorem decode_encode_validFor_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneAuthorityObservation policy)
    (spatialObserved : source.binding.source.spatial? = some observation.spatial) :
    observation.ValidFor policy source.binding.source ↔
      (source.decodeObservation policy
        (source.encodeObservation policy observation)).ValidFor policy source.binding.source := by
  have inverse := source.decodeObservation_encodeObservation policy observation spatialObserved
  constructor
  · intro valid
    rwa [inverse]
  · intro valid
    rwa [← inverse]

/-- Cage-handedness validity is preserved exactly by encode followed by decode. -/
theorem decode_encode_cageHandednessValidFor_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneAuthorityObservation policy)
    (spatialObserved : source.binding.source.spatial? = some observation.spatial) :
    observation.CageHandednessValidFor policy source.binding.source ↔
      (source.decodeObservation policy
        (source.encodeObservation policy observation)).CageHandednessValidFor
          policy source.binding.source := by
  have inverse := source.decodeObservation_encodeObservation policy observation spatialObserved
  constructor
  · intro valid
    rwa [inverse]
  · intro valid
    rwa [← inverse]

def encodeType4Observation (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneType4AuthorityObservation policy) :
    NativeFullereneType4AuthorityObservation V where
  molecule := observation.molecule
  input := source.encodeSymmetryDerivedInput observation.input
  substituentAssignments := observation.substituentAssignments.map source.encodeCIPAssignment

def decodeType4Observation (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneType4AuthorityObservation V) :
    P93FullereneType4AuthorityObservation policy where
  molecule := observation.molecule
  input := source.decodeSymmetryDerivedInput observation.input
  substituentAssignments := observation.substituentAssignments.map source.decodeCIPAssignment

@[simp] theorem decodeType4Observation_encodeType4Observation
    (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneType4AuthorityObservation policy) :
    source.decodeType4Observation policy (source.encodeType4Observation policy observation) =
      observation := by
  cases observation with
  | mk molecule input substituentAssignments =>
      simp only [encodeType4Observation, decodeType4Observation]
      have assignmentRoundTrip :
          List.map (source.decodeCIPAssignment ∘ source.encodeCIPAssignment)
            substituentAssignments = substituentAssignments := by
        rw [← List.map_map]
        exact decodeCIPAssignmentList_encode source substituentAssignments
      simp [assignmentRoundTrip]

theorem encodeType4Observation_injective (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy) :
    Function.Injective (source.encodeType4Observation policy) := by
  intro left right equal
  calc
    left = source.decodeType4Observation policy (source.encodeType4Observation policy left) :=
      (source.decodeType4Observation_encodeType4Observation policy left).symm
    _ = source.decodeType4Observation policy (source.encodeType4Observation policy right) := by
      rw [equal]
    _ = right := source.decodeType4Observation_encodeType4Observation policy right

theorem decode_encode_type4ValidFor_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneType4AuthorityObservation policy) :
    observation.ValidFor policy source.binding.source ↔
      (source.decodeType4Observation policy
        (source.encodeType4Observation policy observation)).ValidFor policy source.binding.source := by
  have inverse := source.decodeType4Observation_encodeType4Observation policy observation
  constructor
  · intro valid
    rwa [inverse]
  · intro valid
    rwa [← inverse]

def encodeSuperimposedObservation (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneSuperimposedAuthorityObservation policy) :
    NativeFullereneSuperimposedAuthorityObservation V where
  base := source.encodeObservation policy observation.base

def decodeSuperimposedObservation (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneSuperimposedAuthorityObservation V) :
    P93FullereneSuperimposedAuthorityObservation policy where
  base := source.decodeObservation policy observation.base

theorem decodeSuperimposedObservation_encodeSuperimposedObservation
    (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneSuperimposedAuthorityObservation policy)
    (baseSpatial : source.binding.source.spatial? = some observation.base.spatial) :
    source.decodeSuperimposedObservation policy
      (source.encodeSuperimposedObservation policy observation) = observation := by
  cases observation with
  | mk base =>
      simp [encodeSuperimposedObservation, decodeSuperimposedObservation,
        source.decodeObservation_encodeObservation policy base baseSpatial]

theorem encodeSuperimposedObservation_injective_of_valid
    (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (left right : P93FullereneSuperimposedAuthorityObservation policy)
    (leftValid : left.ValidFor policy source.binding.source)
    (rightValid : right.ValidFor policy source.binding.source)
    (equal : source.encodeSuperimposedObservation policy left =
      source.encodeSuperimposedObservation policy right) :
    left = right := by
  calc
    left = source.decodeSuperimposedObservation policy
        (source.encodeSuperimposedObservation policy left) :=
      (source.decodeSuperimposedObservation_encodeSuperimposedObservation policy left
        leftValid.1.1).symm
    _ = source.decodeSuperimposedObservation policy
        (source.encodeSuperimposedObservation policy right) := by rw [equal]
    _ = right := source.decodeSuperimposedObservation_encodeSuperimposedObservation policy right
      rightValid.1.1

theorem decode_encode_superimposedValidFor_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneSuperimposedAuthorityObservation policy)
    (valid : observation.ValidFor policy source.binding.source) :
    observation.ValidFor policy source.binding.source ↔
      (source.decodeSuperimposedObservation policy
        (source.encodeSuperimposedObservation policy observation)).ValidFor
          policy source.binding.source := by
  have inverse := source.decodeSuperimposedObservation_encodeSuperimposedObservation policy
    observation valid.1.1
  constructor
  · intro valid'
    rwa [inverse]
  · intro valid'
    rwa [← inverse]

def encodeMethodologyObservation (_source : FullereneAuthorityCommonSource V)
    (_observation : P93FullereneMethodologyAuthorityObservation) :
    NativeFullereneMethodologyAuthorityObservation :=
  .fourWayDecisionRule

def decodeMethodologyObservation (_source : FullereneAuthorityCommonSource V)
    (_observation : NativeFullereneMethodologyAuthorityObservation) :
    P93FullereneMethodologyAuthorityObservation :=
  .fourWayDecisionRule

@[simp] theorem decodeMethodologyObservation_encodeMethodologyObservation
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneMethodologyAuthorityObservation) :
    source.decodeMethodologyObservation (source.encodeMethodologyObservation observation) =
      observation := by
  cases observation
  rfl

theorem encodeMethodologyObservation_injective (source : FullereneAuthorityCommonSource V) :
    Function.Injective source.encodeMethodologyObservation := by
  intro left right _equal
  cases left
  cases right
  rfl

theorem decode_encode_methodologyValidFor_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneMethodologyAuthorityObservation) :
    observation.ValidFor policy source.binding.source ↔
      (source.decodeMethodologyObservation
        (source.encodeMethodologyObservation observation)).ValidFor
          policy source.binding.source := by
  have inverse := source.decodeMethodologyObservation_encodeMethodologyObservation observation
  constructor
  · intro valid
    rwa [inverse]
  · intro valid
    rwa [← inverse]

/-! ## Bounds derived from authority validity

No bound in this section is assumed.  Each is read from a `ValidFor` predicate or from the exact
source graph equality.
-/

/-- Atom bounds for the six physical unit constructors. -/
def PhysicalUnitAtomsBounded : P93AuthorityPhysicalUnit → Nat → Prop
  | .atomCenter center => fun bound => center < bound
  | .bond first second => fun bound => first < bound ∧ second < bound
  | .axis path => fun bound => ∀ atom ∈ path, atom < bound
  | .plane members => fun bound => ∀ atom ∈ members, atom < bound
  | .helix path => fun bound => ∀ atom ∈ path, atom < bound
  | .polyhedron center positions => fun bound => center < bound ∧ ∀ atom ∈ positions, atom < bound

/-- Bounds for the seven fullerene substituent unit constructors.  This keeps `doubleBond` and
`bondAxis` separate even though `toPhysicalUnit` identifies them. -/
def SubstituentUnitBounded : P93FullereneSubstituentStereogenicUnit → Nat → Prop
  | .center atom => fun bound => atom < bound
  | .doubleBond first second => fun bound => first < bound ∧ second < bound
  | .cumuleneAxis path => fun bound => ∀ atom ∈ path, atom < bound
  | .bondAxis first second => fun bound => first < bound ∧ second < bound
  | .plane members => fun bound => ∀ atom ∈ members, atom < bound
  | .helix path => fun bound => ∀ atom ∈ path, atom < bound
  | .polyhedron center positions => fun bound => center < bound ∧ ∀ atom ∈ positions, atom < bound

/-- Mechanical bounds for a physical unit, derived from `ValidFor` and the source spatial
well-formedness.  The polyhedral case uses the accepted ingress theorem that turns exact
coordinate incidence into in-range atom indices. -/
theorem physicalUnitAtomsBounded_of_validFor
    (policy : P93AuthorityPhysicalObservationPolicy)
    (source : AuthoritativeChemicalInput) (unit : P93AuthorityPhysicalUnit)
    (valid : unit.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    PhysicalUnitAtomsBounded unit source.molecule.atomCount := by
  cases unit with
  | atomCenter center =>
      simp only [P93AuthorityPhysicalUnit.ValidFor] at valid
      exact valid.1
  | bond first second =>
      simp only [P93AuthorityPhysicalUnit.ValidFor] at valid
      exact ⟨valid.1, valid.2.1⟩
  | axis path =>
      simp only [P93AuthorityPhysicalUnit.ValidFor,
        P93AuthorityCanonicalCumuleneAxisPerceived] at valid
      exact valid.2.1
  | plane members =>
      simp only [P93AuthorityPhysicalUnit.ValidFor] at valid
      rcases valid with ⟨frame, frameValid, _observed⟩
      simp only [P93AuthorityPlaneFrame.ValidFor] at frameValid
      rcases frameValid with ⟨membersEq, _length, _nodup, bounded, _rest⟩
      intro atom member
      have planeMember : atom ∈ frame.record.planeAtoms := by
        apply List.mem_toFinset.mp
        rwa [membersEq]
      exact bounded atom (by
        simp only [List.mem_cons]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr planeMember)))))
  | helix path =>
      simp only [P93AuthorityPhysicalUnit.ValidFor] at valid
      rcases valid with ⟨frame, frameValid, _observed⟩
      simp only [P93AuthorityHelixFrame.ValidFor] at frameValid
      rcases frameValid with ⟨pathEq, _descriptor, _length, bounded, _rest⟩
      intro atom member
      exact bounded atom (by
        simp only [List.mem_cons]
        exact Or.inr (Or.inr (by simpa [pathEq] using member)))
  | polyhedron center positions =>
      simp only [P93AuthorityPhysicalUnit.ValidFor] at valid
      rcases valid with ⟨geometry, frame, frameValid, _observed⟩
      have bounded := OrganicStereoP93PhysicalFrameIngress.polyhedralFrameBoundedIn_of_validFor
        source center positions geometry frame frameValid spatialWellFormed
      simp only [P93AuthorityPolyhedralFrame.ValidFor] at frameValid
      refine ⟨?_, ?_⟩
      · rw [← frameValid.1]
        exact bounded.centerBound
      · intro atom member
        apply bounded.ligandsBound
        apply List.mem_toFinset.mp
        rwa [frameValid.2.1]

/-- The same bounds expressed at the common source cardinality. -/
theorem physicalUnitAtomsBounded_of_validFor_card
    (policy : P93AuthorityPhysicalObservationPolicy)
    (source : FullereneAuthorityCommonSource V) (unit : P93AuthorityPhysicalUnit)
    (valid : unit.ValidFor policy source.binding.source) :
    PhysicalUnitAtomsBounded unit (Fintype.card V) := by
  have bounded := physicalUnitAtomsBounded_of_validFor policy source.binding.source unit valid
    source.binding.spatial_wellFormed
  simpa [PhysicalUnitAtomsBounded, source.source_atomCount_eq_card] using bounded

/-- Physical bounds transport to the seven-constructor substituent unit, with `doubleBond` and
`bondAxis` both retaining their source bounds. -/
theorem substituentUnitBounded_of_physicalUnitBounded
    (unit : P93FullereneSubstituentStereogenicUnit) (bound : Nat)
    (bounded : PhysicalUnitAtomsBounded unit.toPhysicalUnit bound) :
    SubstituentUnitBounded unit bound := by
  cases unit <;>
    simpa [P93FullereneSubstituentStereogenicUnit.toPhysicalUnit,
      PhysicalUnitAtomsBounded, SubstituentUnitBounded] using bounded

end FullereneAuthorityCommonSource

/-! ## Native resolution -/

def NativeNumberingEvidence.AllResolved {V : Type*}
    (evidence : NativeNumberingEvidence V) : Prop :=
  NativeAtomRefListResolved evidence.atomsByLocant ∧
    NativeAtomRefListResolved evidence.startingFace

def NativeSubstitutionEvidence.AllResolved {V : Type*}
    (evidence : NativeSubstitutionEvidence V) : Prop :=
  NativeAtomRefFinsetResolved evidence.substitutedSites ∧
    NativeAtomRefFinsetResolved evidence.chiralSubstituentSites

def NativeMolecularFullereneConfigurationInput.AllResolved {V : Type*}
    (input : NativeMolecularFullereneConfigurationInput V) : Prop :=
  NativeAtomRefFinsetResolved input.carrier ∧
    ∀ face ∈ input.faces, NativeAtomRefListResolved face

def NativeSymmetryDerivedInput.AllResolved {V : Type*}
    (input : NativeSymmetryDerivedInput V) : Prop :=
  input.cage.AllResolved ∧ input.substitutionEvidence.AllResolved

def NativeSpatiallyDerivedInput.AllResolved {V : Type*}
    (input : NativeSpatiallyDerivedInput V) : Prop :=
  input.symmetryInput.AllResolved ∧ input.numberingEvidence.AllResolved

def NativeSubstituentStereogenicUnit.AllResolved {V : Type*} :
    NativeSubstituentStereogenicUnit V → Prop
  | .center atom => atom.IsResolved
  | .doubleBond first second => first.IsResolved ∧ second.IsResolved
  | .cumuleneAxis path => NativeAtomRefListResolved path
  | .bondAxis first second => first.IsResolved ∧ second.IsResolved
  | .plane members => NativeAtomRefFinsetResolved members
  | .helix path => NativeAtomRefListResolved path
  | .polyhedron centerAtom positions =>
      centerAtom.IsResolved ∧ NativeAtomRefFinsetResolved positions

def NativeSubstituentCIPAssignment.AllResolved {V : Type*}
    (assignment : NativeSubstituentCIPAssignment V) : Prop :=
  assignment.substitutedSite.IsResolved ∧ assignment.unit.AllResolved

def NativeFullereneConfigurationAssignment.AllResolved {V : Type*}
    (assignment : NativeFullereneConfigurationAssignment V) : Prop :=
  NativeAtomRefListResolved assignment.unit

def NativeFullereneAuthorityObservation.SelectedResolved {V : Type*}
    (observation : NativeFullereneAuthorityObservation V) : Prop :=
  observation.selectedInput.AllResolved ∧ observation.assignment.AllResolved

def NativeFullereneType4AuthorityObservation.AllResolved {V : Type*}
    (observation : NativeFullereneType4AuthorityObservation V) : Prop :=
  observation.input.AllResolved ∧
    ∀ assignment ∈ observation.substituentAssignments, assignment.AllResolved

namespace NativeFullereneAuthorityObservationFamily

/-- Row-dispatched resolved content.  The general and superimposed branches require exactly the
selected input and the configuration assignment; unused `inputs` and non-chiral-type substituent
assignments are deliberately not required to be in range and remain explicit unresolved
metadata. -/
def ContentResolved {V : Type*} :
    NativeFullereneAuthorityObservationFamily V → Prop
  | .general observation => observation.SelectedResolved
  | .type4 observation => observation.AllResolved
  | .superimposed observation => observation.base.SelectedResolved
  | .methodology _ => True

end NativeFullereneAuthorityObservationFamily

namespace FullereneAuthorityCommonSource

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### Source-record bounds -/

def NumberingEvidenceBounded (bound : Nat) (evidence : MolecularFullereneNumberingEvidence) :
    Prop :=
  (∀ atom ∈ evidence.atomsByLocant, atom < bound) ∧
    ∀ atom ∈ evidence.startingFace, atom < bound

def SubstitutionEvidenceBounded (bound : Nat)
    (evidence : MolecularFullereneSubstitutionEvidence) : Prop :=
  (∀ atom ∈ evidence.substitutedSites, atom < bound) ∧
    ∀ atom ∈ evidence.chiralSubstituentSites, atom < bound

def CageBounded (bound : Nat) (input : MolecularFullereneConfigurationInput) : Prop :=
  (∀ atom ∈ input.carrier, atom < bound) ∧
    ∀ face ∈ input.faces, ∀ atom ∈ face, atom < bound

def SymmetryDerivedInputBounded (bound : Nat)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput) : Prop :=
  CageBounded bound input.cage ∧ SubstitutionEvidenceBounded bound input.substitutionEvidence

def SpatiallyDerivedInputBounded (bound : Nat)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput) : Prop :=
  SymmetryDerivedInputBounded bound input.symmetryInput ∧
    NumberingEvidenceBounded bound input.numberingEvidence

/-! ### Bounded source records encode to resolved native records -/

theorem encodeNumberingEvidence_allResolved (source : FullereneAuthorityCommonSource V)
    (evidence : MolecularFullereneNumberingEvidence)
    (bounded : NumberingEvidenceBounded (Fintype.card V) evidence) :
    (source.encodeNumberingEvidence evidence).AllResolved := by
  rcases bounded with ⟨locants, face⟩
  exact ⟨source.listResolved_map (indices := evidence.atomsByLocant) locants,
    source.listResolved_map (indices := evidence.startingFace) face⟩

theorem encodeSubstitutionEvidence_allResolved (source : FullereneAuthorityCommonSource V)
    (evidence : MolecularFullereneSubstitutionEvidence)
    (bounded : SubstitutionEvidenceBounded (Fintype.card V) evidence) :
    (source.encodeSubstitutionEvidence evidence).AllResolved := by
  rcases bounded with ⟨substituted, chiral⟩
  exact ⟨source.finsetResolved_image (indices := evidence.substitutedSites) substituted,
    source.finsetResolved_image (indices := evidence.chiralSubstituentSites) chiral⟩

theorem encodeCage_allResolved (source : FullereneAuthorityCommonSource V)
    (input : MolecularFullereneConfigurationInput)
    (bounded : CageBounded (Fintype.card V) input) :
    (source.encodeCage input).AllResolved := by
  rcases bounded with ⟨carrier, faces⟩
  constructor
  · change NativeAtomRefFinsetResolved (source.toNativeFinset input.carrier)
    exact source.finsetResolved_image (indices := input.carrier) carrier
  · change ∀ face ∈ input.faces.map (fun face => face.map source.toNativeAtom),
      NativeAtomRefListResolved face
    intro face member
    rw [List.mem_map] at member
    obtain ⟨sourceFace, sourceMember, rfl⟩ := member
    exact source.listResolved_map (indices := sourceFace) (faces sourceFace sourceMember)

theorem encodeSymmetryDerivedInput_allResolved (source : FullereneAuthorityCommonSource V)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput)
    (bounded : SymmetryDerivedInputBounded (Fintype.card V) input) :
    (source.encodeSymmetryDerivedInput input).AllResolved := by
  rcases bounded with ⟨cageBounded, substitutionBounded⟩
  constructor
  · change NativeMolecularFullereneConfigurationInput.AllResolved
      (source.encodeCage input.cage)
    exact source.encodeCage_allResolved input.cage cageBounded
  · change NativeSubstitutionEvidence.AllResolved
      (source.encodeSubstitutionEvidence input.substitutionEvidence)
    exact source.encodeSubstitutionEvidence_allResolved input.substitutionEvidence
      substitutionBounded

theorem encodeSpatiallyDerivedInput_allResolved (source : FullereneAuthorityCommonSource V)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput)
    (bounded : SpatiallyDerivedInputBounded (Fintype.card V) input) :
    (source.encodeSpatiallyDerivedInput input).AllResolved := by
  rcases bounded with ⟨symmetryBounded, numberingBounded⟩
  constructor
  · change NativeSymmetryDerivedInput.AllResolved
      (source.encodeSymmetryDerivedInput input.symmetryInput)
    exact source.encodeSymmetryDerivedInput_allResolved input.symmetryInput symmetryBounded
  · change NativeNumberingEvidence.AllResolved
      (source.encodeNumberingEvidence input.numberingEvidence)
    exact source.encodeNumberingEvidence_allResolved input.numberingEvidence numberingBounded

theorem encodeStereogenicUnit_allResolved (source : FullereneAuthorityCommonSource V)
    (unit : P93FullereneSubstituentStereogenicUnit)
    (bounded : SubstituentUnitBounded unit (Fintype.card V)) :
    (source.encodeStereogenicUnit unit).AllResolved := by
  cases unit with
  | center atom =>
      simpa [SubstituentUnitBounded, NativeSubstituentStereogenicUnit.AllResolved,
        encodeStereogenicUnit] using source.toNativeAtom_isResolved_of_lt bounded
  | doubleBond first second =>
      rcases bounded with ⟨firstBound, secondBound⟩
      exact ⟨source.toNativeAtom_isResolved_of_lt firstBound,
        source.toNativeAtom_isResolved_of_lt secondBound⟩
  | cumuleneAxis path =>
      change NativeAtomRefListResolved (path.map source.toNativeAtom)
      exact source.listResolved_map (indices := path) bounded
  | bondAxis first second =>
      rcases bounded with ⟨firstBound, secondBound⟩
      exact ⟨source.toNativeAtom_isResolved_of_lt firstBound,
        source.toNativeAtom_isResolved_of_lt secondBound⟩
  | plane members =>
      change NativeAtomRefFinsetResolved (source.toNativeFinset members)
      exact source.finsetResolved_image (indices := members) bounded
  | helix path =>
      change NativeAtomRefListResolved (path.map source.toNativeAtom)
      exact source.listResolved_map (indices := path) bounded
  | polyhedron center positions =>
      rcases bounded with ⟨centerBound, positionsBound⟩
      exact ⟨source.toNativeAtom_isResolved_of_lt centerBound,
        source.finsetResolved_image (indices := positions) positionsBound⟩

theorem encodeCIPAssignment_allResolved (source : FullereneAuthorityCommonSource V)
    (assignment : P93FullereneSubstituentCIPAssignment)
    (siteBounded : assignment.substitutedSite < Fintype.card V)
    (unitBounded : SubstituentUnitBounded assignment.unit (Fintype.card V)) :
    (source.encodeCIPAssignment assignment).AllResolved := by
  exact ⟨source.toNativeAtom_isResolved_of_lt siteBounded,
    source.encodeStereogenicUnit_allResolved assignment.unit unitBounded⟩

theorem encodeAssignment_allResolved (source : FullereneAuthorityCommonSource V)
    (assignment : FullereneConfigurationAssignment)
    (bounded : ∀ atom ∈ assignment.unit, atom < Fintype.card V) :
    (source.encodeAssignment assignment).AllResolved :=
  source.listResolved_map (indices := assignment.unit) bounded

/-! ## Bounds read from the authority observations -/

/-- The assignment unit is the sorted carrier list, hence every atom is a cage atom. -/
theorem assignment_unit_mem_carrier
    (input : MolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment)
    (judged : FullereneConfigurationAssignmentJudgment
      (MolecularFullereneConfigurationInput.toFullereneConfigurationInput input) assignment)
    {atom : Nat} (member : atom ∈ assignment.unit) :
    atom ∈ input.carrier := by
  rcases judged with ⟨chiralityType, payloads, _typeMatches, _payloads, assignmentEq⟩
  rw [assignmentEq] at member
  have sortedMember : atom ∈ input.carrier.sort (· ≤ ·) := by
    simpa [MolecularFullereneConfigurationInput.toFullereneConfigurationInput] using member
  exact (Finset.mem_sort (r := (· ≤ ·))).mp sortedMember

/-- The selected input's cage atoms are spatially complete, so they are bounded by the exact
one-coordinate-per-atom shared spatial channel. -/
theorem selectedInput_carrier_bounded (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy source.binding.source) :
    ∀ atom ∈ observation.selectedInput.symmetryInput.cage.carrier,
      atom < Fintype.card V := by
  rcases valid with ⟨spatialObserved, _rawObserved, _nonempty, _family, _selectedMember,
    _strictBound, selectedJudged, _assignmentJudged, _assignmentInputs, _complete⟩
  rcases selectedJudged with ⟨_symmetryJudged, turn, turnJudged, _numberingKind, _turnEq⟩
  rcases turnJudged with ⟨_numberingJudged, spatiallyComplete, _interior⟩
  have spatialLength := source.spatialConfiguration_length_of_source observation.spatial
    spatialObserved
  intro atom member
  obtain ⟨point, pointAt⟩ := spatiallyComplete atom member
  have bound := (List.getElem?_eq_some_iff.mp pointAt).1
  simpa [spatialLength] using bound

/-- All selected-input source records are bounded by the common source cardinality. -/
theorem selectedInput_bounded (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy source.binding.source) :
    SpatiallyDerivedInputBounded (Fintype.card V) observation.selectedInput := by
  rcases valid with ⟨spatialObserved, _rawObserved, _nonempty, _family, _selectedMember,
    _strictBound, selectedJudged, _assignmentJudged, _assignmentInputs, _complete⟩
  rcases selectedJudged with ⟨symmetryJudged, turn, turnJudged, _numberingKind, _turnEq⟩
  rcases symmetryJudged with ⟨orientedJudged, evidenceJudged, _testEq⟩
  rcases evidenceJudged with ⟨substitutedSubset, chiralSubset, _total⟩
  rcases turnJudged with ⟨numberingJudged, spatiallyComplete, _interior⟩
  have carrierJudged := orientedJudged.1
  have spatialLength := source.spatialConfiguration_length_of_source observation.spatial
    spatialObserved
  have carrierBounded : ∀ atom ∈ observation.selectedInput.symmetryInput.cage.carrier,
      atom < Fintype.card V := by
    intro atom member
    obtain ⟨point, pointAt⟩ := spatiallyComplete atom member
    have bound := (List.getElem?_eq_some_iff.mp pointAt).1
    simpa [spatialLength] using bound
  have facesBounded : ∀ face ∈ observation.selectedInput.symmetryInput.cage.faces,
      ∀ atom ∈ face, atom < Fintype.card V := by
    intro face faceMember atom atomMember
    have faceJudged := carrierJudged.facesValid face faceMember
    exact carrierBounded atom (faceJudged.2.1 (List.mem_toFinset.mpr atomMember))
  have substitutedBounded : ∀ atom ∈
      observation.selectedInput.symmetryInput.substitutionEvidence.substitutedSites,
      atom < Fintype.card V :=
    fun atom member => carrierBounded atom (substitutedSubset member)
  have chiralBounded : ∀ atom ∈
      observation.selectedInput.symmetryInput.substitutionEvidence.chiralSubstituentSites,
      atom < Fintype.card V :=
    fun atom member => substitutedBounded atom (chiralSubset member)
  rcases numberingJudged with ⟨_locantNodup, locantSetEq, startingFaceMember, _rest⟩
  have locantBounded : ∀ atom ∈
      observation.selectedInput.numberingEvidence.atomsByLocant,
      atom < Fintype.card V := by
    intro atom member
    apply carrierBounded atom
    rw [← locantSetEq]
    exact List.mem_toFinset.mpr member
  have startingFaceBounded : ∀ atom ∈
      observation.selectedInput.numberingEvidence.startingFace,
      atom < Fintype.card V :=
    facesBounded _ startingFaceMember
  exact ⟨⟨⟨carrierBounded, facesBounded⟩, ⟨substitutedBounded, chiralBounded⟩⟩,
    ⟨locantBounded, startingFaceBounded⟩⟩

/-- The encoded selected input is fully resolved. -/
theorem selectedInput_allResolved (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy source.binding.source) :
    (source.encodeSpatiallyDerivedInput observation.selectedInput).AllResolved :=
  source.encodeSpatiallyDerivedInput_allResolved observation.selectedInput
    (selectedInput_bounded policy source observation valid)

/-- The encoded assignment unit is fully resolved. -/
theorem assignment_allResolved (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy source.binding.source) :
    (source.encodeAssignment observation.assignment).AllResolved := by
  have carrierBounded := selectedInput_carrier_bounded policy source observation valid
  rcases valid with ⟨_spatial, _rawObserved, _nonempty, _family, _selectedMember, _strictBound,
    _selectedJudged, assignmentJudged, _assignmentInputs, _complete⟩
  exact source.encodeAssignment_allResolved observation.assignment
    (fun atom member => carrierBounded atom
      (assignment_unit_mem_carrier observation.selectedInput.symmetryInput.cage
        observation.assignment assignmentJudged member))

/-- Under the completeness hypothesis (or, in the general row, under the chiral-substituents
chirality type that implies it), every encoded substituent assignment is resolved. -/
theorem nativeCIPAssignment_allResolved_of_validFor (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence)
    (assignment : P93FullereneSubstituentCIPAssignment)
    (chiralBounded : ∀ atom ∈ evidence.chiralSubstituentSites, atom < Fintype.card V)
    (valid : assignment.ValidFor policy source.binding.source molecule input evidence) :
    (source.encodeCIPAssignment assignment).AllResolved := by
  have unitBounded : SubstituentUnitBounded assignment.unit (Fintype.card V) :=
    substituentUnitBounded_of_physicalUnitBounded assignment.unit (Fintype.card V)
      (physicalUnitAtomsBounded_of_validFor_card policy.physicalObservation source
        assignment.unit.toPhysicalUnit valid.2.1)
  exact source.encodeCIPAssignment_allResolved assignment
    (chiralBounded assignment.substitutedSite valid.1) unitBounded

/-- In the general row, completeness only follows for the chiral-substituents chirality type. -/
theorem substituentAssignments_allResolved_of_chiralType
    (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy source.binding.source)
    (chiralityType : observation.assignment.chiralityType = .chiralSubstituentsOnly) :
    ∀ native ∈ observation.substituentAssignments.map source.encodeCIPAssignment,
      native.AllResolved := by
  have chiralBounded : ∀ atom ∈
      observation.selectedInput.symmetryInput.substitutionEvidence.chiralSubstituentSites,
      atom < Fintype.card V :=
    (selectedInput_bounded policy source observation valid).1.2.2
  rcases valid with ⟨_spatial, _rawObserved, _nonempty, _family, _selectedMember, _strictBound,
    _selectedJudged, _assignmentJudged, _assignmentInputs, completeImplication⟩
  have complete := completeImplication chiralityType
  rcases complete with ⟨_nonemptyAssignments, _pairNodup, _unitNodup, _citationNodup,
    allValid, _allSites, _allUnits⟩
  intro native member
  rw [List.mem_map] at member
  obtain ⟨assignment, assignmentMember, rfl⟩ := member
  exact source.nativeCIPAssignment_allResolved_of_validFor policy observation.molecule
    observation.selectedInput.symmetryInput.cage
    observation.selectedInput.symmetryInput.substitutionEvidence assignment chiralBounded
    (allValid assignment assignmentMember)

/-- The selected-input and assignment part of the encoded general observation is fully
resolved.  The complete `inputs` list is intentionally not asserted to be bounded: existing
validity does not bound unused inputs, and their unresolved references are retained. -/
theorem observation_selectedResolved (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy source.binding.source) :
    (source.encodeObservation policy observation).SelectedResolved :=
  ⟨selectedInput_allResolved policy source observation valid,
    assignment_allResolved policy source observation valid⟩

/-- Type 4 input bounds.  The raw molecule's conversion equality is needed here because the
arbitrary `RawMoleculeObserved` policy relation does not imply it.  The atom count then comes from
the actual semantic conversion plus the source graph equality. -/
theorem type4_input_bounded (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneType4AuthorityObservation policy)
    (sourceBound : observation.molecule.toSemanticMolecule? =
      some source.binding.source.molecule)
    (valid : observation.ValidFor policy source.binding.source) :
    SymmetryDerivedInputBounded (Fintype.card V) observation.input := by
  rcases valid with ⟨_rawObserved, _substitutionObserved, _originalObserved, symmetryJudged,
    _typeMatches, _numberingNone, _turnNone, _everyChiral, _complete⟩
  rcases symmetryJudged with ⟨orientedJudged, evidenceJudged, _testEq⟩
  rcases evidenceJudged with ⟨substitutedSubset, chiralSubset, _total⟩
  have carrierJudged := orientedJudged.1
  have rawCount := source.sourceBound_atomCount_eq_card observation.molecule sourceBound
  have atomsLength : observation.molecule.atoms.length = Fintype.card V := by
    simpa [RawMolecule.atomCount] using rawCount
  have carrierBounded : ∀ atom ∈ observation.input.cage.carrier,
      atom < Fintype.card V := by
    intro atom member
    obtain ⟨spec, atomAt, _carbon⟩ := carrierJudged.carbonAtoms atom member
    have lookup := listGet?_eq_some_implies_lt observation.molecule.atoms atom spec
      (by simpa [RawMolecule.atomAt?] using atomAt)
    simpa [atomsLength] using lookup
  have facesBounded : ∀ face ∈ observation.input.cage.faces,
      ∀ atom ∈ face, atom < Fintype.card V := by
    intro face faceMember atom atomMember
    have faceJudged := carrierJudged.facesValid face faceMember
    exact carrierBounded atom (faceJudged.2.1 (List.mem_toFinset.mpr atomMember))
  have substitutedBounded : ∀ atom ∈ observation.input.substitutionEvidence.substitutedSites,
      atom < Fintype.card V :=
    fun atom member => carrierBounded atom (substitutedSubset member)
  have chiralBounded : ∀ atom ∈
      observation.input.substitutionEvidence.chiralSubstituentSites,
      atom < Fintype.card V :=
    fun atom member => substitutedBounded atom (chiralSubset member)
  exact ⟨⟨carrierBounded, facesBounded⟩, ⟨substitutedBounded, chiralBounded⟩⟩

/-- Type 4 substituent assignments are resolved because type-4 validity contains the complete
all-and-only CIP corpus unconditionally. -/
theorem type4_substituentAssignments_allResolved
    (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneType4AuthorityObservation policy)
    (sourceBound : observation.molecule.toSemanticMolecule? =
      some source.binding.source.molecule)
    (valid : observation.ValidFor policy source.binding.source) :
    ∀ native ∈ observation.substituentAssignments.map source.encodeCIPAssignment,
      native.AllResolved := by
  have chiralBounded : ∀ atom ∈
      observation.input.substitutionEvidence.chiralSubstituentSites,
      atom < Fintype.card V :=
    (type4_input_bounded policy source observation sourceBound valid).2.2
  rcases valid with ⟨_rawObserved, _substitutionObserved, _originalObserved, _symmetryJudged,
    _typeMatches, _numberingNone, _turnNone, _everyChiral, complete⟩
  rcases complete with ⟨_nonempty, _pairNodup, _unitNodup, _citationNodup,
    allValid, _allSites, _allUnits⟩
  intro native member
  rw [List.mem_map] at member
  obtain ⟨assignment, assignmentMember, rfl⟩ := member
  exact source.nativeCIPAssignment_allResolved_of_validFor policy observation.molecule
    observation.input.cage observation.input.substitutionEvidence assignment chiralBounded
    (allValid assignment assignmentMember)

/-- The full encoded Type 4 observation is resolved. -/
theorem type4_allResolved (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneType4AuthorityObservation policy)
    (sourceBound : observation.molecule.toSemanticMolecule? =
      some source.binding.source.molecule)
    (valid : observation.ValidFor policy source.binding.source) :
    (source.encodeType4Observation policy observation).AllResolved :=
  ⟨source.encodeSymmetryDerivedInput_allResolved observation.input
      (type4_input_bounded policy source observation sourceBound valid),
    type4_substituentAssignments_allResolved policy source observation sourceBound valid⟩

/-! ## Common-source graph integration -/

/-- The explicit conversion equality identifies the native molecule with the exact shared graph
encoding.  This is an equality of semantic molecules, not an atom-count comparison. -/
theorem sourceBound_molecule_eq_shared (source : FullereneAuthorityCommonSource V)
    (molecule : RawMolecule)
    (bound : molecule.toSemanticMolecule? = some source.binding.source.molecule) :
    molecule.toSemanticMolecule? =
      some (source.binding.shared.graph.encode source.enumeration) := by
  rw [bound, ← source.binding.graph_eq]
  simp [enumeration]

/-- The general observation's spatial field is exactly the shared coordinate channel. -/
theorem observation_spatial_from_shared (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (observation : P93FullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy source.binding.source) :
    source.sharedSpatial? = some observation.spatial := by
  rw [source.sharedSpatial?_eq_source]
  exact valid.1

/-- Coordinate-level form: decoding recovers the same coordinate channel at every atom. -/
theorem coordinateAt_decodeObservation (policy : P93FullereneAuthorityPolicy)
    (source : FullereneAuthorityCommonSource V)
    (native : NativeFullereneAuthorityObservation V)
    (spatial : SpatialConfiguration)
    (observed : source.binding.source.spatial? = some spatial)
    (atom : Nat) :
    OrganicStereoP93PhysicalFrameIngress.coordinateAt
        (source.decodeObservation policy native).spatial atom =
      OrganicStereoP93PhysicalFrameIngress.coordinateAt spatial atom := by
  change OrganicStereoP93PhysicalFrameIngress.coordinateAt source.spatialConfiguration atom =
    OrganicStereoP93PhysicalFrameIngress.coordinateAt spatial atom
  rw [source.spatialConfiguration_eq_of_source spatial observed]

/-! ## Preservation of the correlated assignment data -/

/-- The site/unit pair map is injective at the native source, including the `doubleBond` versus
`bondAxis` distinction. -/
theorem encodeSiteUnitPair_injective (source : FullereneAuthorityCommonSource V) :
    Function.Injective (fun pair : Nat × P93FullereneSubstituentStereogenicUnit =>
      (source.toNativeAtom pair.1, source.encodeStereogenicUnit pair.2)) := by
  intro left right equal
  have siteEqual : source.toNativeAtom left.1 = source.toNativeAtom right.1 :=
    congrArg Prod.fst equal
  have unitEqual : source.encodeStereogenicUnit left.2 =
      source.encodeStereogenicUnit right.2 := congrArg Prod.snd equal
  have leftSite : left.1 = right.1 := source.toNativeAtom_injective siteEqual
  have leftUnit : left.2 = right.2 := source.encodeStereogenicUnit_injective unitEqual
  exact Prod.ext leftSite leftUnit

/-- The correlated `(substitutedSite, unit)` duplicate-freedom condition is preserved exactly by
the native encoding. -/
theorem encodedAssignmentPairNodup_iff (source : FullereneAuthorityCommonSource V)
    (assignments : List P93FullereneSubstituentCIPAssignment) :
    ((assignments.map source.encodeCIPAssignment).map
      (fun assignment => (assignment.substitutedSite, assignment.unit))).Nodup ↔
      (assignments.map (fun assignment =>
        (assignment.substitutedSite, assignment.unit))).Nodup := by
  have rewrite : ((assignments.map source.encodeCIPAssignment).map
        (fun assignment => (assignment.substitutedSite, assignment.unit))) =
      (assignments.map (fun assignment =>
        (assignment.substitutedSite, assignment.unit))).map
        (fun pair : Nat × P93FullereneSubstituentStereogenicUnit =>
          (source.toNativeAtom pair.1, source.encodeStereogenicUnit pair.2)) := by
    simp only [List.map_map]
    rfl
  rw [rewrite]
  exact List.nodup_map_iff source.encodeSiteUnitPair_injective

/-- The assignment citation list is preserved as an ordered list. -/
theorem encodedCitationList_eq (source : FullereneAuthorityCommonSource V)
    (assignments : List P93FullereneSubstituentCIPAssignment) :
    (assignments.map source.encodeCIPAssignment).map (fun assignment => assignment.citation) =
      assignments.map (fun assignment => assignment.citation) := by
  rw [List.map_map]
  have functionEq : ((fun assignment : NativeSubstituentCIPAssignment V => assignment.citation) ∘
        source.encodeCIPAssignment) =
      (fun assignment => assignment.citation) := by
    funext assignment
    rfl
  rw [functionEq]

/-! ## Whole-authority tagged codec

The four accepted rows are handled by one explicit tagged codec.  The tag is retained, so the
general, Type 4, superimposed and methodology payloads are never conflated; in particular the
general and superimposed rows remain distinct even though the latter contains a general base.
-/

/-- Encode one tagged source observation into the corresponding native constructor. -/
def encodeFamily (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy) :
    SourceFullereneAuthorityObservation policy → NativeFullereneAuthorityObservationFamily V
  | .general observation => .general (source.encodeObservation policy observation)
  | .type4 observation => .type4 (source.encodeType4Observation policy observation)
  | .superimposed observation =>
      .superimposed (source.encodeSuperimposedObservation policy observation)
  | .methodology observation =>
      .methodology (source.encodeMethodologyObservation observation)

/-- Decode one tagged native observation.  The general and superimposed rows reconstruct the
spatial field from the shared coordinate channel; the tag selects the row. -/
def decodeFamily (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy) :
    NativeFullereneAuthorityObservationFamily V → SourceFullereneAuthorityObservation policy
  | .general observation => .general (source.decodeObservation policy observation)
  | .type4 observation => .type4 (source.decodeType4Observation policy observation)
  | .superimposed observation =>
      .superimposed (source.decodeSuperimposedObservation policy observation)
  | .methodology observation =>
      .methodology (source.decodeMethodologyObservation observation)

@[simp] theorem encodeFamily_general (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneAuthorityObservation policy) :
    source.encodeFamily policy (.general observation) =
      .general (source.encodeObservation policy observation) := rfl

@[simp] theorem encodeFamily_type4 (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneType4AuthorityObservation policy) :
    source.encodeFamily policy (.type4 observation) =
      .type4 (source.encodeType4Observation policy observation) := rfl

@[simp] theorem encodeFamily_superimposed (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneSuperimposedAuthorityObservation policy) :
    source.encodeFamily policy (.superimposed observation) =
      .superimposed (source.encodeSuperimposedObservation policy observation) := rfl

@[simp] theorem encodeFamily_methodology (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : P93FullereneMethodologyAuthorityObservation) :
    source.encodeFamily policy (.methodology observation) =
      .methodology (source.encodeMethodologyObservation observation) := rfl

/-- Exact tagged left inverse under the shared observed spatial premise.  The premise is required
only for the rows that carry a spatial field and is derived from actual validity below. -/
theorem decodeFamily_encodeFamily (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : SourceFullereneAuthorityObservation policy)
    (spatial : observation.ObservedSpatialAt source.binding.source) :
    source.decodeFamily policy (source.encodeFamily policy observation) = observation := by
  cases observation with
  | general observation =>
      exact congrArg SourceFullereneAuthorityObservation.general
        (source.decodeObservation_encodeObservation policy observation spatial)
  | type4 observation =>
      exact congrArg SourceFullereneAuthorityObservation.type4
        (source.decodeType4Observation_encodeType4Observation policy observation)
  | superimposed observation =>
      exact congrArg SourceFullereneAuthorityObservation.superimposed
        (source.decodeSuperimposedObservation_encodeSuperimposedObservation policy observation spatial)
  | methodology observation =>
      cases observation
      rfl

/-- Exact tagged left inverse from actual row validity alone. -/
theorem decodeFamily_encodeFamily_of_validFor (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : SourceFullereneAuthorityObservation policy)
    (valid : observation.ValidFor source.binding.source) :
    source.decodeFamily policy (source.encodeFamily policy observation) = observation :=
  source.decodeFamily_encodeFamily policy observation
    (SourceFullereneAuthorityObservation.observedSpatialAt_of_validFor
      source.binding.source observation valid)

/-- The tagged codec is injective on observations carrying the shared observed spatial premise. -/
theorem encodeFamily_injective_of_spatial (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (left right : SourceFullereneAuthorityObservation policy)
    (leftSpatial : left.ObservedSpatialAt source.binding.source)
    (rightSpatial : right.ObservedSpatialAt source.binding.source)
    (equal : source.encodeFamily policy left = source.encodeFamily policy right) :
    left = right := by
  calc
    left = source.decodeFamily policy (source.encodeFamily policy left) :=
      (source.decodeFamily_encodeFamily policy left leftSpatial).symm
    _ = source.decodeFamily policy (source.encodeFamily policy right) := by rw [equal]
    _ = right := source.decodeFamily_encodeFamily policy right rightSpatial

/-- The tagged codec is injective on valid observations at the fixed source and policy. -/
theorem encodeFamily_injective_of_valid (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (left right : SourceFullereneAuthorityObservation policy)
    (leftValid : left.ValidFor source.binding.source)
    (rightValid : right.ValidFor source.binding.source)
    (equal : source.encodeFamily policy left = source.encodeFamily policy right) :
    left = right :=
  source.encodeFamily_injective_of_spatial policy left right
    (SourceFullereneAuthorityObservation.observedSpatialAt_of_validFor
      source.binding.source left leftValid)
    (SourceFullereneAuthorityObservation.observedSpatialAt_of_validFor
      source.binding.source right rightValid)
    equal

/-- Validity is preserved exactly by encoding and decoding at the same source and policy, for the
rows whose shared spatial premise is supplied. -/
theorem decodeFamily_encodeFamily_validFor_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : SourceFullereneAuthorityObservation policy)
    (spatial : observation.ObservedSpatialAt source.binding.source) :
    observation.ValidFor source.binding.source ↔
      (source.decodeFamily policy
        (source.encodeFamily policy observation)).ValidFor source.binding.source := by
  rw [source.decodeFamily_encodeFamily policy observation spatial]

/-! ### Ordered tagged lists

Order, multiplicity and the interleaving of the four constructors are retained literally.  The
list codec never sorts, deduplicates, or regroups entries by row.
-/

/-- Encode an ordered list of tagged observations. -/
def encodeFamilyList (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : List (SourceFullereneAuthorityObservation policy)) :
    List (NativeFullereneAuthorityObservationFamily V) :=
  observations.map (source.encodeFamily policy)

/-- Decode an ordered list of tagged native observations. -/
def decodeFamilyList (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : List (NativeFullereneAuthorityObservationFamily V)) :
    List (SourceFullereneAuthorityObservation policy) :=
  observations.map (source.decodeFamily policy)

@[simp] theorem encodeFamilyList_length (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : List (SourceFullereneAuthorityObservation policy)) :
    (source.encodeFamilyList policy observations).length = observations.length := by
  simp [encodeFamilyList]

@[simp] theorem decodeFamilyList_length (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : List (NativeFullereneAuthorityObservationFamily V)) :
    (source.decodeFamilyList policy observations).length = observations.length := by
  simp [decodeFamilyList]

/-- Exact ordered-list recovery, preserving repeated entries, their order and the full payload of
every row. -/
theorem decodeFamilyList_encodeFamilyList (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : List (SourceFullereneAuthorityObservation policy))
    (spatial : ∀ observation ∈ observations,
      observation.ObservedSpatialAt source.binding.source) :
    source.decodeFamilyList policy (source.encodeFamilyList policy observations) =
      observations := by
  unfold encodeFamilyList decodeFamilyList
  rw [List.map_map]
  trans observations.map id
  · apply List.map_congr_left
    intro observation member
    exact source.decodeFamily_encodeFamily policy observation (spatial observation member)
  · simp

/-- Exact ordered-list recovery from actual per-entry validity. -/
theorem decodeFamilyList_encodeFamilyList_of_validFor
    (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : List (SourceFullereneAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor source.binding.source) :
    source.decodeFamilyList policy (source.encodeFamilyList policy observations) =
      observations :=
  source.decodeFamilyList_encodeFamilyList policy observations
    (fun observation member =>
      SourceFullereneAuthorityObservation.observedSpatialAt_of_validFor
        source.binding.source observation (valid observation member))

/-- Encoding preserves and reflects duplicate-freedom on a valid list.  Repetitions are neither
introduced nor removed; this is the list-level counterpart of exact order/multiplicity recovery. -/
theorem encodeFamilyList_nodup_iff_of_validFor (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : List (SourceFullereneAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor source.binding.source) :
    (source.encodeFamilyList policy observations).Nodup ↔ observations.Nodup := by
  unfold encodeFamilyList
  constructor
  · intro nodup
    exact List.Nodup.of_map (source.encodeFamily policy) nodup
  · intro nodup
    exact List.Nodup.map_on
      (f := source.encodeFamily policy)
      (fun left leftMember right rightMember equal =>
        source.encodeFamily_injective_of_valid policy left right
          (valid left leftMember) (valid right rightMember) equal)
      nodup

/-! ### Arbitrary correlated sets of whole observations

A set contains whole tagged observations, so cross-row correlations (which row carries which
payload, its molecule, its inputs and its assignments) are never replaced by a product of per-row
marginals.  The recovery theorem is stated at one fixed actual source, policy and binding.
-/

/-- The image of a set of tagged source observations under the fixed source/policy codec. -/
def encodeFamilySet (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : Set (SourceFullereneAuthorityObservation policy)) :
    Set (NativeFullereneAuthorityObservationFamily V) :=
  (source.encodeFamily policy) '' observations

/-- The decoding image of a set of tagged native observations. -/
def decodeFamilySet (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : Set (NativeFullereneAuthorityObservationFamily V)) :
    Set (SourceFullereneAuthorityObservation policy) :=
  (source.decodeFamily policy) '' observations

@[simp] theorem mem_encodeFamilySet_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : Set (SourceFullereneAuthorityObservation policy))
    (native : NativeFullereneAuthorityObservationFamily V) :
    native ∈ source.encodeFamilySet policy observations ↔
      ∃ observation ∈ observations,
        source.encodeFamily policy observation = native := Iff.rfl

@[simp] theorem mem_decodeFamilySet_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : Set (NativeFullereneAuthorityObservationFamily V))
    (observation : SourceFullereneAuthorityObservation policy) :
    observation ∈ source.decodeFamilySet policy observations ↔
      ∃ native ∈ observations,
        source.decodeFamily policy native = observation := Iff.rfl

/-- **Arbitrary correlated-set recovery.**  At one fixed actual source, policy and binding, encoding
and then decoding a set of whole tagged observations recovers exactly the original set.  Every
row's complete payload and every cross-row correlation are retained. -/
theorem decodeFamilySet_encodeFamilySet_of_spatial (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : Set (SourceFullereneAuthorityObservation policy))
    (spatial : ∀ observation ∈ observations,
      observation.ObservedSpatialAt source.binding.source) :
    source.decodeFamilySet policy (source.encodeFamilySet policy observations) =
      observations := by
  ext observation
  constructor
  · rintro ⟨native, ⟨sourceObservation, sourceMember, encoded⟩, decoded⟩
    rw [← encoded] at decoded
    rw [source.decodeFamily_encodeFamily policy sourceObservation
      (spatial sourceObservation sourceMember)] at decoded
    rwa [← decoded]
  · intro member
    exact ⟨source.encodeFamily policy observation,
      ⟨observation, member, rfl⟩,
      source.decodeFamily_encodeFamily policy observation (spatial observation member)⟩

/-- The same arbitrary correlated-set recovery from actual per-entry validity. -/
theorem decodeFamilySet_encodeFamilySet_of_validFor (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : Set (SourceFullereneAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor source.binding.source) :
    source.decodeFamilySet policy (source.encodeFamilySet policy observations) =
      observations :=
  source.decodeFamilySet_encodeFamilySet_of_spatial policy observations
    (fun observation member =>
      SourceFullereneAuthorityObservation.observedSpatialAt_of_validFor
        source.binding.source observation (valid observation member))

@[simp] theorem nonempty_encodeFamilySet_iff (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : Set (SourceFullereneAuthorityObservation policy)) :
    (source.encodeFamilySet policy observations).Nonempty ↔ observations.Nonempty := by
  constructor
  · rintro ⟨native, ⟨observation, member, _encoded⟩⟩
    exact ⟨observation, member⟩
  · rintro ⟨observation, member⟩
    exact ⟨source.encodeFamily policy observation, ⟨observation, member, rfl⟩⟩

/-! ### Observation-specific semantic conversion and resolved content -/

/-- The encoded tagged observation's content is resolved under actual row validity, with the
observation's own semantic conversion equality supplied explicitly where a raw atom count is
needed (the Type 4 row).  The general and superimposed rows intentionally require only the
selected input and assignment; unused `inputs` are not required to be in range. -/
theorem encodeFamily_contentResolved_of_validFor (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : SourceFullereneAuthorityObservation policy)
    (valid : observation.ValidFor source.binding.source)
    (moleculeBound : observation.MoleculeBoundTo source.binding.source) :
    (source.encodeFamily policy observation).ContentResolved := by
  cases observation with
  | general observation =>
      change (source.encodeObservation policy observation).SelectedResolved
      exact FullereneAuthorityCommonSource.observation_selectedResolved
        policy source observation valid
  | type4 observation =>
      change (source.encodeType4Observation policy observation).AllResolved
      exact FullereneAuthorityCommonSource.type4_allResolved
        policy source observation moleculeBound valid
  | superimposed observation =>
      change (source.encodeObservation policy observation.base).SelectedResolved
      exact FullereneAuthorityCommonSource.observation_selectedResolved
        policy source observation.base valid.1
  | methodology _ =>
      change True
      trivial

/-- The whole encoded list has resolved content whenever every source entry is valid and carries
its own explicit semantic conversion.  This is a list-level result, not a strengthening of actual
row validity: out-of-range unused references remain unresolved and retained. -/
theorem encodeFamilyList_contentResolved_of_validFor
    (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observations : List (SourceFullereneAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor source.binding.source)
    (moleculeBound : ∀ observation ∈ observations,
      observation.MoleculeBoundTo source.binding.source) :
    ∀ native ∈ source.encodeFamilyList policy observations, native.ContentResolved := by
  intro native member
  simp only [encodeFamilyList, List.mem_map] at member
  obtain ⟨observation, observationMember, rfl⟩ := member
  exact source.encodeFamily_contentResolved_of_validFor policy observation
    (valid observation observationMember) (moleculeBound observation observationMember)

end FullereneAuthorityCommonSource

/-! ## A source-independent decode context

The per-row decode functions use only the accepted enumeration and the reconstructed spatial
configuration.  Isolating those two facts lets the satellite decoder recover the native list
without storing or reconstructing the original `FullereneAuthorityCommonSource`; the source
molecule and its conversion proof are not payloads of the native collection.
-/

structure FullereneAuthorityDecodeContext (V : Type*) [DecidableEq V] [Fintype V] where
  enumeration : V ≃ Fin (Fintype.card V)
  spatialConfiguration : SpatialConfiguration

namespace FullereneAuthorityDecodeContext

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The context of an actual common source. -/
def ofSource (source : FullereneAuthorityCommonSource V) :
    FullereneAuthorityDecodeContext V where
  enumeration := source.enumeration
  spatialConfiguration := source.spatialConfiguration

/-- A context built from an enumeration and an optional coordinate channel.  The spatial
configuration is materialised exactly as `OrganicFiniteSource.encodeSpatial?` does; absence yields
the empty configuration, which is never used by a row that actually has a spatial field. -/
def ofEnumeration (enumeration : V ≃ Fin (Fintype.card V))
    (spatial? : Option (V → CartesianPoint3)) : FullereneAuthorityDecodeContext V where
  enumeration := enumeration
  spatialConfiguration :=
    (OrganicFiniteSource.encodeSpatial? enumeration spatial?).getD { positions := [] }

/-- The native atom decoder of the context. -/
def ofNativeAtom (context : FullereneAuthorityDecodeContext V)
    (reference : NativeAtomRef V) : Nat :=
  decodeAtomRef context.enumeration reference

/-- The native finite-set decoder of the context. -/
def ofNativeFinset (context : FullereneAuthorityDecodeContext V)
    (references : Finset (NativeAtomRef V)) : Finset Nat :=
  decodeAtomRefFinset context.enumeration references

/-- Context-level numbering-evidence decoding. -/
def decodeNumberingEvidence (context : FullereneAuthorityDecodeContext V)
    (evidence : NativeNumberingEvidence V) : MolecularFullereneNumberingEvidence where
  numberingKind := evidence.numberingKind
  atomsByLocant := evidence.atomsByLocant.map context.ofNativeAtom
  startingFace := evidence.startingFace.map context.ofNativeAtom

/-- Context-level substitution-evidence decoding. -/
def decodeSubstitutionEvidence (context : FullereneAuthorityDecodeContext V)
    (evidence : NativeSubstitutionEvidence V) : MolecularFullereneSubstitutionEvidence where
  substitutedSites := context.ofNativeFinset evidence.substitutedSites
  actualIdentityClassAt := evidence.actualIdentityClassAt
  originalDerivativeChiral := evidence.originalDerivativeChiral
  chiralSubstituentSites := context.ofNativeFinset evidence.chiralSubstituentSites

/-- Context-level cage decoding. -/
def decodeCage (context : FullereneAuthorityDecodeContext V)
    (input : NativeMolecularFullereneConfigurationInput V) :
    MolecularFullereneConfigurationInput where
  carrier := context.ofNativeFinset input.carrier
  faces := input.faces.map fun face => face.map context.ofNativeAtom
  substitutionTest := input.substitutionTest
  descriptorEvidence := input.descriptorEvidence

/-- Context-level symmetry-derived input decoding. -/
def decodeSymmetryDerivedInput (context : FullereneAuthorityDecodeContext V)
    (input : NativeSymmetryDerivedInput V) :
    SymmetryDerivedMolecularFullereneConfigurationInput where
  cage := context.decodeCage input.cage
  substitutionEvidence := context.decodeSubstitutionEvidence input.substitutionEvidence

/-- Context-level spatially-derived input decoding. -/
def decodeSpatiallyDerivedInput (context : FullereneAuthorityDecodeContext V)
    (input : NativeSpatiallyDerivedInput V) :
    SpatiallyDerivedMolecularFullereneConfigurationInput where
  symmetryInput := context.decodeSymmetryDerivedInput input.symmetryInput
  numberingEvidence := context.decodeNumberingEvidence input.numberingEvidence

/-- Context-level stereogenic-unit decoding. -/
def decodeStereogenicUnit (context : FullereneAuthorityDecodeContext V) :
    NativeSubstituentStereogenicUnit V → P93FullereneSubstituentStereogenicUnit
  | .center atom => .center (context.ofNativeAtom atom)
  | .doubleBond first second =>
      .doubleBond (context.ofNativeAtom first) (context.ofNativeAtom second)
  | .cumuleneAxis path => .cumuleneAxis (path.map context.ofNativeAtom)
  | .bondAxis first second =>
      .bondAxis (context.ofNativeAtom first) (context.ofNativeAtom second)
  | .plane members => .plane (context.ofNativeFinset members)
  | .helix path => .helix (path.map context.ofNativeAtom)
  | .polyhedron center positions =>
      .polyhedron (context.ofNativeAtom center) (context.ofNativeFinset positions)

/-- Context-level CIP-assignment decoding. -/
def decodeCIPAssignment (context : FullereneAuthorityDecodeContext V)
    (assignment : NativeSubstituentCIPAssignment V) :
    P93FullereneSubstituentCIPAssignment where
  substitutedSite := context.ofNativeAtom assignment.substitutedSite
  unit := context.decodeStereogenicUnit assignment.unit
  citation := assignment.citation
  descriptor := assignment.descriptor

/-- Context-level configuration-assignment decoding. -/
def decodeAssignment (context : FullereneAuthorityDecodeContext V)
    (assignment : NativeFullereneConfigurationAssignment V) :
    FullereneConfigurationAssignment where
  unit := assignment.unit.map context.ofNativeAtom
  chiralityType := assignment.chiralityType
  payloads := assignment.payloads

/-- Context-level general-observation decoding. -/
def decodeObservation (context : FullereneAuthorityDecodeContext V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneAuthorityObservation V) :
    P93FullereneAuthorityObservation policy where
  molecule := observation.molecule
  spatial := context.spatialConfiguration
  inputs := observation.inputs.map context.decodeSpatiallyDerivedInput
  selectedInput := context.decodeSpatiallyDerivedInput observation.selectedInput
  assignment := context.decodeAssignment observation.assignment
  substituentAssignments :=
    observation.substituentAssignments.map context.decodeCIPAssignment

/-- Context-level Type 4 observation decoding. -/
def decodeType4Observation (context : FullereneAuthorityDecodeContext V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneType4AuthorityObservation V) :
    P93FullereneType4AuthorityObservation policy where
  molecule := observation.molecule
  input := context.decodeSymmetryDerivedInput observation.input
  substituentAssignments :=
    observation.substituentAssignments.map context.decodeCIPAssignment

/-- Context-level superimposed observation decoding. -/
def decodeSuperimposedObservation (context : FullereneAuthorityDecodeContext V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneSuperimposedAuthorityObservation V) :
    P93FullereneSuperimposedAuthorityObservation policy where
  base := context.decodeObservation policy observation.base

/-- Context-level methodology observation decoding. -/
def decodeMethodologyObservation (_context : FullereneAuthorityDecodeContext V)
    (_observation : NativeFullereneMethodologyAuthorityObservation) :
    P93FullereneMethodologyAuthorityObservation :=
  .fourWayDecisionRule

/-- Context-level tagged observation decoding. -/
def decodeFamily (context : FullereneAuthorityDecodeContext V)
    (policy : P93FullereneAuthorityPolicy) :
    NativeFullereneAuthorityObservationFamily V →
      SourceFullereneAuthorityObservation policy
  | .general observation => .general (context.decodeObservation policy observation)
  | .type4 observation => .type4 (context.decodeType4Observation policy observation)
  | .superimposed observation =>
      .superimposed (context.decodeSuperimposedObservation policy observation)
  | .methodology observation =>
      .methodology (context.decodeMethodologyObservation observation)

/-! ### Compatibility with the actual common-source codec -/

@[simp] theorem ofSource_enumeration (source : FullereneAuthorityCommonSource V) :
    (ofSource source).enumeration = source.enumeration := rfl

@[simp] theorem ofSource_spatialConfiguration (source : FullereneAuthorityCommonSource V) :
    (ofSource source).spatialConfiguration = source.spatialConfiguration := rfl

@[simp] theorem ofSource_ofNativeAtom (source : FullereneAuthorityCommonSource V)
    (reference : NativeAtomRef V) :
    (ofSource source).ofNativeAtom reference = source.ofNativeAtom reference := rfl

@[simp] theorem ofSource_ofNativeFinset (source : FullereneAuthorityCommonSource V)
    (references : Finset (NativeAtomRef V)) :
    (ofSource source).ofNativeFinset references = source.ofNativeFinset references := rfl

@[simp] theorem decodeNumberingEvidence_ofSource (source : FullereneAuthorityCommonSource V)
    (evidence : NativeNumberingEvidence V) :
    (ofSource source).decodeNumberingEvidence evidence =
      source.decodeNumberingEvidence evidence := by
  cases evidence
  rfl

@[simp] theorem decodeSubstitutionEvidence_ofSource (source : FullereneAuthorityCommonSource V)
    (evidence : NativeSubstitutionEvidence V) :
    (ofSource source).decodeSubstitutionEvidence evidence =
      source.decodeSubstitutionEvidence evidence := by
  cases evidence
  rfl

@[simp] theorem decodeCage_ofSource (source : FullereneAuthorityCommonSource V)
    (input : NativeMolecularFullereneConfigurationInput V) :
    (ofSource source).decodeCage input = source.decodeCage input := by
  cases input with
  | mk carrier faces substitutionTest descriptorEvidence =>
      simp only [decodeCage, FullereneAuthorityCommonSource.decodeCage]
      have finsetEq : (ofSource source).ofNativeFinset = source.ofNativeFinset := by
        funext references
        exact ofSource_ofNativeFinset source references
      have atomEq : (ofSource source).ofNativeAtom = source.ofNativeAtom := by
        funext reference
        exact ofSource_ofNativeAtom source reference
      rw [finsetEq, atomEq]
      rfl

@[simp] theorem decodeSymmetryDerivedInput_ofSource (source : FullereneAuthorityCommonSource V)
    (input : NativeSymmetryDerivedInput V) :
    (ofSource source).decodeSymmetryDerivedInput input =
      source.decodeSymmetryDerivedInput input := by
  cases input with
  | mk cage substitutionEvidence =>
      simp only [decodeSymmetryDerivedInput,
        FullereneAuthorityCommonSource.decodeSymmetryDerivedInput]
      rw [decodeCage_ofSource, decodeSubstitutionEvidence_ofSource]

@[simp] theorem decodeSpatiallyDerivedInput_ofSource (source : FullereneAuthorityCommonSource V)
    (input : NativeSpatiallyDerivedInput V) :
    (ofSource source).decodeSpatiallyDerivedInput input =
      source.decodeSpatiallyDerivedInput input := by
  cases input with
  | mk symmetryInput numberingEvidence =>
      simp only [decodeSpatiallyDerivedInput,
        FullereneAuthorityCommonSource.decodeSpatiallyDerivedInput]
      rw [decodeSymmetryDerivedInput_ofSource, decodeNumberingEvidence_ofSource]

@[simp] theorem decodeStereogenicUnit_ofSource (source : FullereneAuthorityCommonSource V) :
    (ofSource source).decodeStereogenicUnit = source.decodeStereogenicUnit := by
  funext unit
  cases unit <;> rfl

@[simp] theorem decodeCIPAssignment_ofSource (source : FullereneAuthorityCommonSource V)
    (assignment : NativeSubstituentCIPAssignment V) :
    (ofSource source).decodeCIPAssignment assignment =
      source.decodeCIPAssignment assignment := by
  cases assignment with
  | mk substitutedSite unit citation descriptor =>
      simp only [decodeCIPAssignment, FullereneAuthorityCommonSource.decodeCIPAssignment]
      rw [ofSource_ofNativeAtom, decodeStereogenicUnit_ofSource]

@[simp] theorem decodeAssignment_ofSource (source : FullereneAuthorityCommonSource V)
    (assignment : NativeFullereneConfigurationAssignment V) :
    (ofSource source).decodeAssignment assignment = source.decodeAssignment assignment := by
  cases assignment with
  | mk unit chiralityType payloads =>
      simp only [decodeAssignment, FullereneAuthorityCommonSource.decodeAssignment]
      have atomEq : (ofSource source).ofNativeAtom = source.ofNativeAtom := by
        funext reference
        exact ofSource_ofNativeAtom source reference
      rw [atomEq]

@[simp] theorem decodeObservation_ofSource (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneAuthorityObservation V) :
    (ofSource source).decodeObservation policy observation =
      source.decodeObservation policy observation := by
  cases observation with
  | mk molecule inputs selectedInput assignment substituentAssignments =>
      simp only [decodeObservation, FullereneAuthorityCommonSource.decodeObservation]
      rw [ofSource_spatialConfiguration]
      have inputEq : (ofSource source).decodeSpatiallyDerivedInput =
          source.decodeSpatiallyDerivedInput := by
        funext input
        exact decodeSpatiallyDerivedInput_ofSource source input
      have assignmentEq : (ofSource source).decodeAssignment = source.decodeAssignment := by
        funext assignment
        exact decodeAssignment_ofSource source assignment
      have cipEq : (ofSource source).decodeCIPAssignment = source.decodeCIPAssignment := by
        funext assignment
        exact decodeCIPAssignment_ofSource source assignment
      rw [inputEq, assignmentEq, cipEq]

@[simp] theorem decodeType4Observation_ofSource (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneType4AuthorityObservation V) :
    (ofSource source).decodeType4Observation policy observation =
      source.decodeType4Observation policy observation := by
  cases observation with
  | mk molecule input substituentAssignments =>
      simp only [decodeType4Observation,
        FullereneAuthorityCommonSource.decodeType4Observation]
      have inputEq : (ofSource source).decodeSymmetryDerivedInput =
          source.decodeSymmetryDerivedInput := by
        funext input
        exact decodeSymmetryDerivedInput_ofSource source input
      have cipEq : (ofSource source).decodeCIPAssignment = source.decodeCIPAssignment := by
        funext assignment
        exact decodeCIPAssignment_ofSource source assignment
      rw [inputEq, cipEq]

@[simp] theorem decodeSuperimposedObservation_ofSource
    (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneSuperimposedAuthorityObservation V) :
    (ofSource source).decodeSuperimposedObservation policy observation =
      source.decodeSuperimposedObservation policy observation := by
  cases observation with
  | mk base =>
      simp only [decodeSuperimposedObservation,
        FullereneAuthorityCommonSource.decodeSuperimposedObservation]
      rw [decodeObservation_ofSource]

@[simp] theorem decodeMethodologyObservation_ofSource
    (source : FullereneAuthorityCommonSource V)
    (observation : NativeFullereneMethodologyAuthorityObservation) :
    (ofSource source).decodeMethodologyObservation observation =
      source.decodeMethodologyObservation observation := by
  cases observation
  rfl

@[simp] theorem decodeFamily_ofSource (source : FullereneAuthorityCommonSource V)
    (policy : P93FullereneAuthorityPolicy)
    (observation : NativeFullereneAuthorityObservationFamily V) :
    (ofSource source).decodeFamily policy observation =
      source.decodeFamily policy observation := by
  cases observation with
  | general observation =>
      exact congrArg SourceFullereneAuthorityObservation.general
        (decodeObservation_ofSource source policy observation)
  | type4 observation =>
      exact congrArg SourceFullereneAuthorityObservation.type4
        (decodeType4Observation_ofSource source policy observation)
  | superimposed observation =>
      exact congrArg SourceFullereneAuthorityObservation.superimposed
        (decodeSuperimposedObservation_ofSource source policy observation)
  | methodology observation =>
      exact congrArg SourceFullereneAuthorityObservation.methodology
        (decodeMethodologyObservation_ofSource source observation)

end FullereneAuthorityDecodeContext

/-! ## The whole-authority satellite and combined recovery

The satellite stores only the shared finite source (graph and both optional evidence channels)
and the ordered native tagged list.  It contains no source record, no source molecule, no original
observation and no opaque `FullereneAuthorityCommonSource`. -/

/-- A raw whole-authority source: one accepted common source and an ordered list of tagged source
observations, each certified valid at the bound source and explicitly bound to the source molecule
by its own semantic conversion equality. -/
structure RawFullereneAuthoritySource (policy : P93FullereneAuthorityPolicy) (V : Type*)
    [DecidableEq V] [Fintype V] where
  source : FullereneAuthorityCommonSource V
  observations : List (SourceFullereneAuthorityObservation policy)
  valid : ∀ observation ∈ observations,
    observation.ValidFor source.binding.source
  moleculeBound : ∀ observation ∈ observations,
    observation.MoleculeBoundTo source.binding.source

/-- The composable satellite.  The graph and both optional evidence channels are one independent
finite source; `observations` is the ordered native payload list. -/
structure FullereneAuthoritySatellite (policy : P93FullereneAuthorityPolicy) (V : Type*)
    [DecidableEq V] [Fintype V] where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (NativeFullereneAuthorityObservationFamily V)

namespace FullereneAuthoritySatellite

variable {policy : P93FullereneAuthorityPolicy} {V : Type*} [DecidableEq V] [Fintype V]

/-- The satellite's independent finite source. -/
def toFiniteSource (satellite : FullereneAuthoritySatellite policy V) : OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

/-- The reconstructed spatial configuration at a supplied enumeration. -/
def spatialConfiguration (satellite : FullereneAuthoritySatellite policy V)
    (enumeration : V ≃ Fin (Fintype.card V)) : SpatialConfiguration :=
  (OrganicFiniteSource.encodeSpatial? enumeration satellite.spatial?).getD { positions := [] }

/-- The source-independent decode context of the satellite. -/
def context (satellite : FullereneAuthoritySatellite policy V)
    (enumeration : V ≃ Fin (Fintype.card V)) : FullereneAuthorityDecodeContext V :=
  FullereneAuthorityDecodeContext.ofEnumeration enumeration satellite.spatial?

end FullereneAuthoritySatellite

/-- Adapt a raw whole-authority source to the satellite channel. -/
def adaptFullereneAuthoritySource {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93FullereneAuthorityPolicy)
    (raw : RawFullereneAuthoritySource policy V) :
    FullereneAuthoritySatellite policy V where
  graph := raw.source.binding.shared.graph
  spatial? := raw.source.binding.shared.spatial?
  diagram? := raw.source.binding.shared.diagram?
  observations := raw.observations.map (raw.source.encodeFamily policy)

/-- The recovered whole-authority source: the exact authoritative source and the exact ordered
tagged observation list.  The tuple is extensional so combined recovery can be stated fieldwise. -/
@[ext] structure RecoveredFullereneAuthoritySource (policy : P93FullereneAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceFullereneAuthorityObservation policy)

/-- Decode the satellite from a supplied enumeration.  Only the enumeration and optional
coordinate channel are used, never the original common source. -/
def decodeFullereneAuthoritySource {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93FullereneAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : FullereneAuthoritySatellite policy V) :
    RecoveredFullereneAuthoritySource policy where
  source := satellite.toFiniteSource.encode enumeration
  observations := satellite.observations.map
    ((satellite.context enumeration).decodeFamily policy)

@[simp] theorem toFiniteSource_adaptFullereneAuthoritySource
    {policy : P93FullereneAuthorityPolicy} {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawFullereneAuthoritySource policy V) :
    (adaptFullereneAuthoritySource policy raw).toFiniteSource =
      raw.source.binding.shared := rfl

@[simp] theorem observations_adaptFullereneAuthoritySource
    {policy : P93FullereneAuthorityPolicy} {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawFullereneAuthoritySource policy V) :
    (adaptFullereneAuthoritySource policy raw).observations =
      raw.observations.map (raw.source.encodeFamily policy) := rfl

@[simp] theorem context_adaptFullereneAuthoritySource
    {policy : P93FullereneAuthorityPolicy} {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawFullereneAuthoritySource policy V) :
    (adaptFullereneAuthoritySource policy raw).context raw.source.enumeration =
      FullereneAuthorityDecodeContext.ofSource raw.source := rfl

/-- **Combined source and observation recovery.**  Adapting a raw whole-authority source and then
decoding at its own enumeration recovers the exact bound authoritative source and the exact original
ordered tagged list, including repetitions, order and every row's complete payload. -/
theorem decodeFullereneAuthoritySource_adaptFullereneAuthoritySource
    {policy : P93FullereneAuthorityPolicy} {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawFullereneAuthoritySource policy V) :
    decodeFullereneAuthoritySource policy raw.source.enumeration
        (adaptFullereneAuthoritySource policy raw) =
      { source := raw.source.binding.source, observations := raw.observations } := by
  apply RecoveredFullereneAuthoritySource.ext
  · change (adaptFullereneAuthoritySource policy raw).toFiniteSource.encode
        raw.source.enumeration = raw.source.binding.source
    rw [toFiniteSource_adaptFullereneAuthoritySource]
    simpa [FullereneAuthorityCommonSource.enumeration] using raw.source.binding.encode_shared
  · simp only [decodeFullereneAuthoritySource, observations_adaptFullereneAuthoritySource,
      context_adaptFullereneAuthoritySource]
    rw [List.map_map]
    trans raw.observations.map id
    · apply List.map_congr_left
      intro observation member
      change (FullereneAuthorityDecodeContext.ofSource raw.source).decodeFamily policy
        (raw.source.encodeFamily policy observation) = id observation
      rw [FullereneAuthorityDecodeContext.decodeFamily_ofSource]
      exact raw.source.decodeFamily_encodeFamily_of_validFor policy observation
        (raw.valid observation member)
    · simp

/-- The adapted satellite's whole native list is content-resolved whenever each raw entry is valid
and carries its own explicit semantic conversion. -/
theorem adaptFullereneAuthoritySource_contentResolved
    {policy : P93FullereneAuthorityPolicy} {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawFullereneAuthoritySource policy V) :
    ∀ native ∈ (adaptFullereneAuthoritySource policy raw).observations,
      native.ContentResolved := by
  intro native member
  simp only [observations_adaptFullereneAuthoritySource, List.mem_map] at member
  obtain ⟨observation, observationMember, rfl⟩ := member
  exact raw.source.encodeFamily_contentResolved_of_validFor policy observation
    (raw.valid observation observationMember)
    (raw.moleculeBound observation observationMember)

end OrganicStereoFullereneAuthorityIngress

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.encodeAtomRef_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.decodeAtomRefList_encodeAtomRefList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.decodeAtomRefFinset_encodeAtomRefFinset
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decodeObservation_encodeObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.encodeObservation_injective_of_valid
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decode_encode_validFor_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decode_encode_type4ValidFor_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decode_encode_superimposedValidFor_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decode_encode_methodologyValidFor_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decodeFamily_encodeFamily
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decodeFamily_encodeFamily_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decodeFamilyList_encodeFamilyList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decodeFamilyList_encodeFamilyList_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decodeFamilySet_encodeFamilySet_of_spatial
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.decodeFamilySet_encodeFamilySet_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.encodeFamily_contentResolved_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.decodeFamily_ofSource
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.decodeFullereneAuthoritySource_adaptFullereneAuthoritySource
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.physicalUnitAtomsBounded_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.selectedInput_bounded
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.type4_input_bounded
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource.sourceBound_molecule_eq_shared
