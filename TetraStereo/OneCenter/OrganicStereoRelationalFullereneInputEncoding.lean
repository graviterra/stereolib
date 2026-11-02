import TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress

set_option autoImplicit false

















































namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic
open OrganicStereoSuppliedCitationIngress
open OrganicStereoFullereneAuthorityIngress
open OrganicStereoRelationalFullereneIngress

namespace OrganicStereoRelationalFullereneInputEncoding

/-! ## Ordered pairs of native atom references -/

/-- Encode one ordered pair of source atom indices.  Order is retained: `(site, externalAtom)`
and `(externalAtom, site)` remain distinct. -/
def encodeAtomRefPair {V : Type*} {n : Nat} (e : V ≃ Fin n) (pair : Nat × Nat) :
    NativeAtomRef V × NativeAtomRef V :=
  (encodeAtomRef e pair.1, encodeAtomRef e pair.2)

/-- Decode one ordered pair of native atom references. -/
def decodeAtomRefPair {V : Type*} {n : Nat} (e : V ≃ Fin n)
    (pair : NativeAtomRef V × NativeAtomRef V) : Nat × Nat :=
  (decodeAtomRef e pair.1, decodeAtomRef e pair.2)

@[simp] theorem decodeAtomRefPair_encodeAtomRefPair {V : Type*} {n : Nat} (e : V ≃ Fin n)
    (pair : Nat × Nat) :
    decodeAtomRefPair e (encodeAtomRefPair e pair) = pair := by
  rcases pair with ⟨first, second⟩
  simp [encodeAtomRefPair, decodeAtomRefPair]

/-- Ordered-list encoding of source atom indices.  Order, duplicates and multiplicity are
retained. -/
@[simp] theorem map_decodeAtomRef_encodeAtomRef {V : Type*} {n : Nat} (e : V ≃ Fin n)
    (indices : List Nat) :
    (indices.map (encodeAtomRef e)).map (decodeAtomRef e) = indices := by
  induction indices with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons] at inductionHypothesis ⊢
      rw [decodeAtomRef_encodeAtomRef, inductionHypothesis]

/-- Ordered face-list encoding: the order of faces and of atoms within each face is retained. -/
@[simp] theorem map_decodeAtomRefFaces_encodeAtomRefFaces {V : Type*} {n : Nat}
    (e : V ≃ Fin n) (faces : List (List Nat)) :
    (faces.map fun face => face.map (encodeAtomRef e)).map
        (fun face => face.map (decodeAtomRef e)) = faces := by
  induction faces with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons] at inductionHypothesis ⊢
      rw [map_decodeAtomRef_encodeAtomRef, inductionHypothesis]

/-- A finite set of ordered pairs of source atom indices decodes exactly. -/
@[simp] theorem image_decodeAtomRefPair_encodeAtomRefPair {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (pairs : Finset (Nat × Nat)) :
    (pairs.image (encodeAtomRefPair e)).image (decodeAtomRefPair e) = pairs := by
  rw [Finset.image_image]
  have composition : (decodeAtomRefPair e) ∘ (encodeAtomRefPair e) = id := by
    funext pair
    exact decodeAtomRefPair_encodeAtomRefPair e pair
  rw [composition, Finset.image_id]

/-! ## Complete native constitutional addends

An addend is never projected to its attachment sites.  The complete external atom set, the
complete set of ordered attachment ports and the identity class are all retained. -/

/-- One complete graph-backed addend over `NativeAtomRef V`. -/
structure NativeMolecularFullereneAddend (V : Type*) where
  externalAtoms : Finset (NativeAtomRef V)
  attachmentPorts : Finset (NativeAtomRef V × NativeAtomRef V)
  identityClass : Nat
  deriving DecidableEq

/-- Encode one complete addend. -/
def encodeAddendRef {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (addend : MolecularFullereneAddend) : NativeMolecularFullereneAddend V where
  externalAtoms := encodeAtomRefFinset e addend.externalAtoms
  attachmentPorts := addend.attachmentPorts.image (encodeAtomRefPair e)
  identityClass := addend.identityClass

/-- Decode one complete addend. -/
def decodeAddendRef {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (addend : NativeMolecularFullereneAddend V) : MolecularFullereneAddend where
  externalAtoms := decodeAtomRefFinset e addend.externalAtoms
  attachmentPorts := addend.attachmentPorts.image (decodeAtomRefPair e)
  identityClass := addend.identityClass

/-- **Exact addend recovery.**  No boundedness hypothesis is required: the native reference
codec is a total inverse on source `Nat` data, including out-of-range references. -/
@[simp] theorem decodeAddendRef_encodeAddendRef {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (addend : MolecularFullereneAddend) :
    decodeAddendRef e (encodeAddendRef e addend) = addend := by
  rcases addend with ⟨externalAtoms, attachmentPorts, identityClass⟩
  simp only [encodeAddendRef, decodeAddendRef]
  rw [decodeAtomRefFinset_encodeAtomRefFinset, image_decodeAtomRefPair_encodeAtomRefPair]

/-- The identity class is retained literally. -/
@[simp] theorem decodeAddendRef_identityClass {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (addend : NativeMolecularFullereneAddend V) :
    (decodeAddendRef e addend).identityClass = addend.identityClass := rfl

/-- The reported attachment sites of a decoded addend are a consequence of the full ordered port
set; they do not replace it. -/
theorem decodeAddendRef_attachmentSites {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (addend : NativeMolecularFullereneAddend V) :
    (decodeAddendRef e addend).attachmentSites =
      addend.attachmentPorts.image fun port => decodeAtomRef e port.1 := by
  simp only [MolecularFullereneAddend.attachmentSites, decodeAddendRef, Finset.image_image]
  rfl

/-- Encoding an ordered addend list is a map; order and multiplicity are retained. -/
def encodeAddendRefList {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (addends : List MolecularFullereneAddend) : List (NativeMolecularFullereneAddend V) :=
  addends.map (encodeAddendRef e)

/-- Decoding an ordered addend list is a map. -/
def decodeAddendRefList {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (addends : List (NativeMolecularFullereneAddend V)) : List MolecularFullereneAddend :=
  addends.map (decodeAddendRef e)

@[simp] theorem map_decodeAddendRef_encodeAddendRef {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (addends : List MolecularFullereneAddend) :
    (addends.map (encodeAddendRef e)).map (decodeAddendRef e) = addends := by
  induction addends with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons] at inductionHypothesis ⊢
      rw [decodeAddendRef_encodeAddendRef, inductionHypothesis]

/-- The chiral-addend finite set decodes exactly.  This is one component of the observation
inverse; it is not, by itself, a whole-observation inverse. -/
@[simp] theorem image_decodeAddendRef_encodeAddendRef {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (addends : Finset MolecularFullereneAddend) :
    (addends.image (encodeAddendRef e)).image (decodeAddendRef e) = addends := by
  rw [Finset.image_image]
  have composition : (decodeAddendRef e) ∘ (encodeAddendRef e) = id := by
    funext addend
    exact decodeAddendRef_encodeAddendRef e addend
  rw [composition, Finset.image_id]

/-! ## Topology and numbering (native reuse)

The native topology and numbering records of `OrganicStereoFullereneAuthorityIngress` are reused
verbatim.  Their atom occurrences are `NativeAtomRef`s; literal nomenclature fields are copied. -/

/-- Encode molecular topology: carrier, ordered faces and atom occurrences. -/
def encodeNativeTopology {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (input : MolecularFullereneConfigurationInput) :
    NativeMolecularFullereneConfigurationInput V where
  carrier := encodeAtomRefFinset e input.carrier
  faces := input.faces.map fun face => face.map (encodeAtomRef e)
  substitutionTest := input.substitutionTest
  descriptorEvidence := input.descriptorEvidence

/-- Decode molecular topology. -/
def decodeNativeTopology {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (input : NativeMolecularFullereneConfigurationInput V) :
    MolecularFullereneConfigurationInput where
  carrier := decodeAtomRefFinset e input.carrier
  faces := input.faces.map fun face => face.map (decodeAtomRef e)
  substitutionTest := input.substitutionTest
  descriptorEvidence := input.descriptorEvidence

@[simp] theorem decodeNativeTopology_encodeNativeTopology {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (input : MolecularFullereneConfigurationInput) :
    decodeNativeTopology e (encodeNativeTopology e input) = input := by
  rcases input with ⟨carrier, faces, substitutionTest, descriptorEvidence⟩
  simp only [encodeNativeTopology, decodeNativeTopology]
  rw [decodeAtomRefFinset_encodeAtomRefFinset,
    map_decodeAtomRefFaces_encodeAtomRefFaces]

/-- Encode numbering evidence. -/
def encodeNativeNumberingEvidence {V : Type*} {n : Nat} (e : V ≃ Fin n)
    (evidence : MolecularFullereneNumberingEvidence) : NativeNumberingEvidence V where
  numberingKind := evidence.numberingKind
  atomsByLocant := evidence.atomsByLocant.map (encodeAtomRef e)
  startingFace := evidence.startingFace.map (encodeAtomRef e)

/-- Decode numbering evidence. -/
def decodeNativeNumberingEvidence {V : Type*} {n : Nat} (e : V ≃ Fin n)
    (evidence : NativeNumberingEvidence V) : MolecularFullereneNumberingEvidence where
  numberingKind := evidence.numberingKind
  atomsByLocant := evidence.atomsByLocant.map (decodeAtomRef e)
  startingFace := evidence.startingFace.map (decodeAtomRef e)

@[simp] theorem decodeNativeNumberingEvidence_encodeNativeNumberingEvidence
    {V : Type*} {n : Nat} (e : V ≃ Fin n) (evidence : MolecularFullereneNumberingEvidence) :
    decodeNativeNumberingEvidence e (encodeNativeNumberingEvidence e evidence) = evidence := by
  rcases evidence with ⟨numberingKind, atomsByLocant, startingFace⟩
  simp only [encodeNativeNumberingEvidence, decodeNativeNumberingEvidence]
  rw [map_decodeAtomRef_encodeAtomRef, map_decodeAtomRef_encodeAtomRef]

/-! ## The relational addend evidence record

The data fields are encoded natively.  The proof fields are restated as obligations about the
decoded actual native fields and the retained `RawMolecule`.  Nothing from the original
proof-carrying record is kept as opaque metadata. -/

/-- Native `MolecularFullereneAddendRelationalEvidence`.

`carrier` is the actual native topology carrier of the owning input.  Every obligation below is
the source proposition after applying the exact field inverse `decodeAtomRef` /
`decodeAddendRef`; it therefore constrains decoded physical data rather than a copy of the source
record. -/
structure NativeMolecularFullereneAddendRelationalEvidence (V : Type*) [DecidableEq V]
    {n : Nat} (e : V ≃ Fin n) (molecule : RawMolecule)
    (carrier : Finset (NativeAtomRef V)) where
  addends : List (NativeMolecularFullereneAddend V)
  originalDerivativeChiral : Bool
  chiralAddends : Finset (NativeMolecularFullereneAddend V)
  addendsNonempty : (addends.map (decodeAddendRef e)) ≠ []
  addendsNodup : (addends.map (decodeAddendRef e)).Nodup
  addendsValid : ∀ addend ∈ addends.map (decodeAddendRef e),
    addend.ValidFor molecule (decodeAtomRefFinset e carrier)
  externalAtomsPairwiseDisjoint :
    (addends.map (decodeAddendRef e)).Pairwise fun first second =>
      Disjoint first.externalAtoms second.externalAtoms
  attachmentSitesPairwiseDisjoint :
    (addends.map (decodeAddendRef e)).Pairwise fun first second =>
      Disjoint first.attachmentSites second.attachmentSites
  externalAtomsPartition :
    MolecularFullereneAddendExternalAtomsPartition molecule
      (decodeAtomRefFinset e carrier) (addends.map (decodeAddendRef e))
  attachmentPortsPartition :
    MolecularFullereneAddendPortsPartition molecule
      (decodeAtomRefFinset e carrier) (addends.map (decodeAddendRef e))
  identityClassesFaithful :
    ∀ first ∈ addends.map (decodeAddendRef e),
      ∀ second ∈ addends.map (decodeAddendRef e),
        first.identityClass = second.identityClass ↔
          first.ConstitutionallyIsomorphic molecule second
  chiralAddendsOwned :
    ∀ addend ∈ chiralAddends.image (decodeAddendRef e),
      addend ∈ addends.map (decodeAddendRef e)
  chiralIdentityFaithful :
    ∀ first ∈ addends.map (decodeAddendRef e),
      ∀ second ∈ addends.map (decodeAddendRef e),
        first.identityClass = second.identityClass →
          (first ∈ chiralAddends.image (decodeAddendRef e) ↔
            second ∈ chiralAddends.image (decodeAddendRef e))

/-- Encode complete relational evidence.  `carrierEq` is the exact field inverse that identifies
the native topology carrier with the source carrier; the obligation proofs are the source proofs
transported along that inverse. -/
def encodeNativeAddendRelationalEvidence {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (molecule : RawMolecule) (nativeCarrier : Finset (NativeAtomRef V))
    (carrier : Finset Nat) (carrierEq : decodeAtomRefFinset e nativeCarrier = carrier)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) :
    NativeMolecularFullereneAddendRelationalEvidence V e molecule nativeCarrier where
  addends := evidence.addends.map (encodeAddendRef e)
  originalDerivativeChiral := evidence.originalDerivativeChiral
  chiralAddends := evidence.chiralAddends.image (encodeAddendRef e)
  addendsNonempty := by
    rw [map_decodeAddendRef_encodeAddendRef]
    exact evidence.addendsNonempty
  addendsNodup := by
    rw [map_decodeAddendRef_encodeAddendRef]
    exact evidence.addendsNodup
  addendsValid := by
    intro addend member
    rw [map_decodeAddendRef_encodeAddendRef] at member
    rw [carrierEq]
    exact evidence.addendsValid addend member
  externalAtomsPairwiseDisjoint := by
    rw [map_decodeAddendRef_encodeAddendRef]
    exact evidence.externalAtomsPairwiseDisjoint
  attachmentSitesPairwiseDisjoint := by
    rw [map_decodeAddendRef_encodeAddendRef]
    exact evidence.attachmentSitesPairwiseDisjoint
  externalAtomsPartition := by
    rw [map_decodeAddendRef_encodeAddendRef, carrierEq]
    exact evidence.externalAtomsPartition
  attachmentPortsPartition := by
    rw [map_decodeAddendRef_encodeAddendRef, carrierEq]
    exact evidence.attachmentPortsPartition
  identityClassesFaithful := by
    rw [map_decodeAddendRef_encodeAddendRef]
    exact evidence.identityClassesFaithful
  chiralAddendsOwned := by
    rw [image_decodeAddendRef_encodeAddendRef, map_decodeAddendRef_encodeAddendRef]
    exact evidence.chiralAddendsOwned
  chiralIdentityFaithful := by
    rw [map_decodeAddendRef_encodeAddendRef]
    simp only [image_decodeAddendRef_encodeAddendRef]
    exact evidence.chiralIdentityFaithful

/-- Decode complete relational evidence.  Every proof field is the obligation stored on the
native record: by construction its statement is already the source proposition about the decoded
fields. -/
def decodeNativeAddendRelationalEvidence {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (molecule : RawMolecule) (nativeCarrier : Finset (NativeAtomRef V))
    (evidence : NativeMolecularFullereneAddendRelationalEvidence V e molecule nativeCarrier) :
    MolecularFullereneAddendRelationalEvidence molecule (decodeAtomRefFinset e nativeCarrier) where
  addends := evidence.addends.map (decodeAddendRef e)
  originalDerivativeChiral := evidence.originalDerivativeChiral
  chiralAddends := evidence.chiralAddends.image (decodeAddendRef e)
  addendsNonempty := evidence.addendsNonempty
  addendsNodup := evidence.addendsNodup
  addendsValid := evidence.addendsValid
  externalAtomsPairwiseDisjoint := evidence.externalAtomsPairwiseDisjoint
  attachmentSitesPairwiseDisjoint := evidence.attachmentSitesPairwiseDisjoint
  externalAtomsPartition := evidence.externalAtomsPartition
  attachmentPortsPartition := evidence.attachmentPortsPartition
  identityClassesFaithful := evidence.identityClassesFaithful
  chiralAddendsOwned := evidence.chiralAddendsOwned
  chiralIdentityFaithful := evidence.chiralIdentityFaithful

/-- **Exact evidence recovery.**  The carrier equation is the exact field inverse supplied by the
encoding.  All data fields are recovered by the addend inverse; all proof fields are recovered by
proof irrelevance, since each is a proof of the same proposition after the inverse is applied. -/
theorem decodeNativeAddendRelationalEvidence_encodeNativeAddendRelationalEvidence
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (molecule : RawMolecule) (nativeCarrier : Finset (NativeAtomRef V))
    (carrier : Finset Nat) (carrierEq : decodeAtomRefFinset e nativeCarrier = carrier)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) :
    (carrierEq ▸ decodeNativeAddendRelationalEvidence e molecule nativeCarrier
        (encodeNativeAddendRelationalEvidence e molecule nativeCarrier carrier carrierEq
          evidence)) = evidence := by
  subst carrierEq
  rcases evidence with
    ⟨addends, originalDerivativeChiral, chiralAddends, addendsNonempty, addendsNodup,
      addendsValid, externalAtomsPairwiseDisjoint, attachmentSitesPairwiseDisjoint,
      externalAtomsPartition, attachmentPortsPartition, identityClassesFaithful,
      chiralAddendsOwned, chiralIdentityFaithful⟩
  simp only [encodeNativeAddendRelationalEvidence, decodeNativeAddendRelationalEvidence,
    map_decodeAddendRef_encodeAddendRef, image_decodeAddendRef_encodeAddendRef]

/-- Heterogeneous form of exact evidence recovery.  This is the form used when the evidence field
sits inside a structure whose earlier field (the native topology carrier) is itself recovered by a
propositional equality. -/
theorem decodeNativeAddendRelationalEvidence_encodeNativeAddendRelationalEvidence_heq
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (molecule : RawMolecule) (nativeCarrier : Finset (NativeAtomRef V))
    (carrier : Finset Nat) (carrierEq : decodeAtomRefFinset e nativeCarrier = carrier)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) :
    HEq (decodeNativeAddendRelationalEvidence e molecule nativeCarrier
        (encodeNativeAddendRelationalEvidence e molecule nativeCarrier carrier carrierEq
          evidence)) evidence := by
  have equality :=
    decodeNativeAddendRelationalEvidence_encodeNativeAddendRelationalEvidence e molecule
      nativeCarrier carrier carrierEq evidence
  exact (eqRec_heq carrierEq _).symm.trans (heq_of_eq equality)

/-! ## Native relational symmetry-derived input

The source record is
`topologyInput`, `evidence : MolecularFullereneAddendRelationalEvidence molecule topologyInput.carrier`
and `descriptorEvidence`.  All three are encoded: the first natively, the second as the native
evidence record above, and the third literally (it is nomenclature, not an atom occurrence). -/

/-- Native relational symmetry-derived input. -/
structure NativeRelationalSymmetryInput (V : Type*) [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (molecule : RawMolecule) where
  topologyInput : NativeMolecularFullereneConfigurationInput V
  evidence : NativeMolecularFullereneAddendRelationalEvidence V e molecule topologyInput.carrier
  descriptorEvidence : FullereneDescriptorEvidence

/-- Encode one relational symmetry-derived input. -/
def encodeRelationalSymmetryInput {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    NativeRelationalSymmetryInput V e molecule where
  topologyInput := encodeNativeTopology e input.topologyInput
  evidence :=
    encodeNativeAddendRelationalEvidence e molecule
      (encodeAtomRefFinset e input.topologyInput.carrier) input.topologyInput.carrier
      (decodeAtomRefFinset_encodeAtomRefFinset e input.topologyInput.carrier)
      input.evidence
  descriptorEvidence := input.descriptorEvidence

/-- Decode one relational symmetry-derived input. -/
def decodeRelationalSymmetryInput {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (molecule : RawMolecule) (input : NativeRelationalSymmetryInput V e molecule) :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule where
  topologyInput := decodeNativeTopology e input.topologyInput
  evidence :=
    decodeNativeAddendRelationalEvidence e molecule input.topologyInput.carrier input.evidence
  descriptorEvidence := input.descriptorEvidence

/-- Equality principle for the source symmetry-derived input: two records are equal when their
topology, heterogeneously-equal evidence and descriptor evidence agree. -/
theorem relationalSymmetryDerivedInput_eq_of
    {molecule : RawMolecule}
    {first second : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule}
    (topologyEq : first.topologyInput = second.topologyInput)
    (evidenceHeq : HEq first.evidence second.evidence)
    (descriptorEq : first.descriptorEvidence = second.descriptorEvidence) :
    first = second := by
  rcases first with ⟨firstTopology, firstEvidence, firstDescriptor⟩
  rcases second with ⟨secondTopology, secondEvidence, secondDescriptor⟩
  simp only at topologyEq descriptorEq
  cases topologyEq
  cases descriptorEq
  have evidenceEq : firstEvidence = secondEvidence := eq_of_heq evidenceHeq
  subst evidenceEq
  rfl

/-- **Exact symmetry-input recovery.**  No atom bound, no renumbering premise and no policy
invariance is used. -/
theorem decodeRelationalSymmetryInput_encodeRelationalSymmetryInput
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n) (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    decodeRelationalSymmetryInput e molecule (encodeRelationalSymmetryInput e molecule input) =
      input := by
  rcases input with ⟨topologyInput, evidence, descriptorEvidence⟩
  apply relationalSymmetryDerivedInput_eq_of
  · exact decodeNativeTopology_encodeNativeTopology e topologyInput
  · exact
      decodeNativeAddendRelationalEvidence_encodeNativeAddendRelationalEvidence_heq e molecule
        (encodeAtomRefFinset e topologyInput.carrier) topologyInput.carrier
        (decodeAtomRefFinset_encodeAtomRefFinset e topologyInput.carrier) evidence
  · rfl

/-! ## Native relational source-oriented input

This adds the printed numbering evidence and the source turn.  `turnSource` is a literal sum of
the supporting-spatial tag and an exterior face sense; it is copied, not interpreted. -/

/-- Native relational source-oriented input. -/
structure NativeRelationalSourceOrientedInput (V : Type*) [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (molecule : RawMolecule) where
  symmetryInput : NativeRelationalSymmetryInput V e molecule
  numberingEvidence : NativeNumberingEvidence V
  turnSource : MolecularFullereneSourceTurn

/-- Encode one relational source-oriented input. -/
def encodeRelationalSourceOrientedInput {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (molecule : RawMolecule)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) :
    NativeRelationalSourceOrientedInput V e molecule where
  symmetryInput := encodeRelationalSymmetryInput e molecule input.symmetryInput
  numberingEvidence := encodeNativeNumberingEvidence e input.numberingEvidence
  turnSource := input.turnSource

/-- Decode one relational source-oriented input. -/
def decodeRelationalSourceOrientedInput {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (molecule : RawMolecule)
    (input : NativeRelationalSourceOrientedInput V e molecule) :
    RelationalSourceOrientedMolecularFullereneConfigurationInput molecule where
  symmetryInput := decodeRelationalSymmetryInput e molecule input.symmetryInput
  numberingEvidence := decodeNativeNumberingEvidence e input.numberingEvidence
  turnSource := input.turnSource

@[simp] theorem decodeRelationalSourceOrientedInput_encodeRelationalSourceOrientedInput
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n) (molecule : RawMolecule)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) :
    decodeRelationalSourceOrientedInput e molecule
        (encodeRelationalSourceOrientedInput e molecule input) = input := by
  rcases input with ⟨symmetryInput, numberingEvidence, turnSource⟩
  simp [encodeRelationalSourceOrientedInput, decodeRelationalSourceOrientedInput,
    decodeRelationalSymmetryInput_encodeRelationalSymmetryInput,
    decodeNativeNumberingEvidence_encodeNativeNumberingEvidence]

/-- Ordered input-family encoding is an exact list map.  Repeated entries and their order are
retained. -/
@[simp] theorem map_decodeRelationalSourceOrientedInput_encode
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n) (molecule : RawMolecule)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)) :
    (inputs.map (encodeRelationalSourceOrientedInput e molecule)).map
        (decodeRelationalSourceOrientedInput e molecule) = inputs := by
  induction inputs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons] at inductionHypothesis ⊢
      rw [decodeRelationalSourceOrientedInput_encodeRelationalSourceOrientedInput,
        inductionHypothesis]

/-- The input codec is injective: decoding is a left inverse. -/
theorem encodeRelationalSourceOrientedInput_injective
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n) (molecule : RawMolecule) :
    Function.Injective
      (encodeRelationalSourceOrientedInput (V := V) e molecule) := by
  intro first second equal
  have applied := congrArg (decodeRelationalSourceOrientedInput e molecule) equal
  simpa using applied

/-- The ordered input-family encoding is injective. -/
theorem encodeRelationalSourceOrientedInputList_injective
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n) (molecule : RawMolecule) :
    Function.Injective fun inputs :
        List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) =>
      inputs.map (encodeRelationalSourceOrientedInput e molecule) := by
  intro first second equal
  have applied := congrArg
    (fun encoded => encoded.map (decodeRelationalSourceOrientedInput e molecule)) equal
  change List.map (decodeRelationalSourceOrientedInput e molecule)
      (List.map (encodeRelationalSourceOrientedInput e molecule) first) =
    List.map (decodeRelationalSourceOrientedInput e molecule)
      (List.map (encodeRelationalSourceOrientedInput e molecule) second) at applied
  rw [List.map_map, List.map_map] at applied
  have composition :
      (decodeRelationalSourceOrientedInput e molecule) ∘
        (encodeRelationalSourceOrientedInput e molecule) = id := by
    funext input
    exact decodeRelationalSourceOrientedInput_encodeRelationalSourceOrientedInput e molecule input
  rw [composition, List.map_id, List.map_id] at applied
  exact applied

/-- Selected-input membership is preserved by the native input codec. -/
theorem selectedInput_mem_encoded_inputs
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n) (molecule : RawMolecule)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule))
    (member : input ∈ inputs) :
    encodeRelationalSourceOrientedInput e molecule input ∈
      inputs.map (encodeRelationalSourceOrientedInput e molecule) :=
  List.mem_map_of_mem (f := encodeRelationalSourceOrientedInput e molecule) member

/-- If the selected input is one of the family entries, its encoded image is the corresponding
family entry.  Equality is preserved by the left inverse. -/
theorem selectedInput_encoded_eq_of_eq
    {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n) (molecule : RawMolecule)
    (input other : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
    (equal : input = other) :
    encodeRelationalSourceOrientedInput e molecule input =
      encodeRelationalSourceOrientedInput e molecule other := by
  rw [equal]

/-! ## Native relational fullerene observation

The successor observation uses the actual new input codec for `inputs` and `selectedInput`, while
reusing the existing complete bounded addend/assignment/corpus codecs for the observation-level
payload.  The `RawMolecule` is retained only as provenance; it is never used to substitute for an
atom occurrence.  The spatial channel is not duplicated: it is reconstructed from the actual
source, exactly as in the predecessor ingress. -/

/-- Native relational fullerene observation. -/
structure NativeRelationalFullereneObservation (V : Type*) [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (policy : P93RelationalFullereneAuthorityPolicy) where
  molecule : RawMolecule
  inputs : List (NativeRelationalSourceOrientedInput V e molecule)
  selectedInput : NativeRelationalSourceOrientedInput V e molecule
  addends : List (SuppliedAddend V)
  chiralAddends : Finset (SuppliedAddend V)
  assignmentUnit : List V
  chiralityType : FullereneChiralityType
  payloads : List FullereneDescriptorPayload
  substituentAssignments : List (SuppliedSubstituentCIPAssignment V)

/-- Encode one observation.  `bounded` is the existing observation-level boundedness derived from
`ValidFor`; it applies only to the observation-level addend/corpus payload, never to the input
family. -/
def relabelObservation {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (policy : P93RelationalFullereneAuthorityPolicy)
    (observation : P93RelationalFullereneAuthorityObservation policy)
    (bounded : relationalObservationBoundedIn n observation) :
    NativeRelationalFullereneObservation V e policy where
  molecule := observation.molecule
  inputs := observation.inputs.map (encodeRelationalSourceOrientedInput e observation.molecule)
  selectedInput :=
    encodeRelationalSourceOrientedInput e observation.molecule observation.selectedInput
  addends := relabelAddends e observation.addends bounded.1
  chiralAddends := relabelAddendFinset e observation.chiralAddends bounded.2.1
  assignmentUnit := relabelList e observation.assignment.unit bounded.2.2.1
  chiralityType := observation.assignment.chiralityType
  payloads := observation.assignment.payloads
  substituentAssignments :=
    relabelSubstituentAssignments e observation.substituentAssignments bounded.2.2.2

/-- Decode one observation.  The spatial channel is supplied from the actual source, never stored
in the native record. -/
def unrelabelObservation {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (policy : P93RelationalFullereneAuthorityPolicy)
    (spatial? : Option SpatialConfiguration)
    (observation : NativeRelationalFullereneObservation V e policy) :
    P93RelationalFullereneAuthorityObservation policy where
  molecule := observation.molecule
  spatial? := spatial?
  inputs := observation.inputs.map (decodeRelationalSourceOrientedInput e observation.molecule)
  selectedInput :=
    decodeRelationalSourceOrientedInput e observation.molecule observation.selectedInput
  addends := unrelabelAddends e observation.addends
  chiralAddends := unrelabelAddendFinset e observation.chiralAddends
  assignment :=
    { unit := unrelabelList e observation.assignmentUnit
      chiralityType := observation.chiralityType
      payloads := observation.payloads }
  substituentAssignments :=
    unrelabelSubstituentAssignments e observation.substituentAssignments

/-- **Exact full-record observation recovery.**  Every field participates: the ordered input
family, the selected input, the ordered addends, the chiral-addend `Finset`, the assignment unit,
the chirality type and payloads, and the whole substituent corpus.  The only side condition is the
exact spatial agreement that `ValidFor` already supplies at the actual source.

The chiral-addend `Finset` inverse alone is *not* this statement: the input family, selected
input, ordered addends, assignment and corpus are all recovered here as well. -/
theorem unrelabelObservation_relabelObservation {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (policy : P93RelationalFullereneAuthorityPolicy)
    (observation : P93RelationalFullereneAuthorityObservation policy)
    (bounded : relationalObservationBoundedIn n observation)
    (spatial? : Option SpatialConfiguration) (spatialExact : observation.spatial? = spatial?) :
    unrelabelObservation e policy spatial? (relabelObservation e policy observation bounded) =
      observation := by
  obtain ⟨molecule, spatial, inputs, selectedInput, addends, chiralAddends,
    ⟨assignmentUnit, chiralityType, payloads⟩, substituentAssignments⟩ := observation
  subst spatialExact
  simp only [relabelObservation, unrelabelObservation,
    map_decodeRelationalSourceOrientedInput_encode,
    decodeRelationalSourceOrientedInput_encodeRelationalSourceOrientedInput,
    unrelabelAddends_relabelAddends, unrelabelAddendFinset_relabelAddendFinset,
    unrelabelList_relabelList,
    unrelabelSubstituentAssignments_relabelSubstituentAssignments]

/-- The observation codec is injective on observations at a fixed spatial channel. -/
theorem relabelObservation_injective_of_spatial {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (policy : P93RelationalFullereneAuthorityPolicy)
    (spatial? : Option SpatialConfiguration)
    (left right : P93RelationalFullereneAuthorityObservation policy)
    (leftBounded : relationalObservationBoundedIn n left)
    (rightBounded : relationalObservationBoundedIn n right)
    (leftSpatial : left.spatial? = spatial?)
    (rightSpatial : right.spatial? = spatial?)
    (equal : relabelObservation e policy left leftBounded =
      relabelObservation e policy right rightBounded) :
    left = right := by
  calc
    left = unrelabelObservation e policy spatial?
        (relabelObservation e policy left leftBounded) :=
      (unrelabelObservation_relabelObservation e policy left leftBounded spatial?
        leftSpatial).symm
    _ = unrelabelObservation e policy spatial?
        (relabelObservation e policy right rightBounded) := by rw [equal]
    _ = right :=
      unrelabelObservation_relabelObservation e policy right rightBounded spatial? rightSpatial

/-- Selected-input membership is preserved in the encoded observation. -/
theorem relabelObservation_selectedInput_mem {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (policy : P93RelationalFullereneAuthorityPolicy)
    (observation : P93RelationalFullereneAuthorityObservation policy)
    (bounded : relationalObservationBoundedIn n observation)
    (member : observation.selectedInput ∈ observation.inputs) :
    (relabelObservation e policy observation bounded).selectedInput ∈
      (relabelObservation e policy observation bounded).inputs := by
  simp only [relabelObservation]
  exact List.mem_map_of_mem
    (f := encodeRelationalSourceOrientedInput e observation.molecule) member

/-- The ordered input family is preserved entry by entry, including repeated entries. -/
@[simp] theorem relabelObservation_inputs_length {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (policy : P93RelationalFullereneAuthorityPolicy)
    (observation : P93RelationalFullereneAuthorityObservation policy)
    (bounded : relationalObservationBoundedIn n observation) :
    (relabelObservation e policy observation bounded).inputs.length =
      observation.inputs.length := by
  simp [relabelObservation]

/-- Any native observation decodes to a bounded source observation, field by field. -/
def unrelabelObservationBounded {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (policy : P93RelationalFullereneAuthorityPolicy)
    (spatial? : Option SpatialConfiguration)
    (observation : NativeRelationalFullereneObservation V e policy) :
    relationalObservationBoundedIn n (unrelabelObservation e policy spatial? observation) :=
  ⟨unrelabelAddendsBounded e observation.addends,
    unrelabelAddendFinsetBounded e observation.chiralAddends,
    unrelabelList_bounded e observation.assignmentUnit,
    unrelabelSubstituentAssignmentsBounded e observation.substituentAssignments⟩

/-! ## Successor satellite and ordered collection recovery

The satellite stores the shared finite source and one ordered native observation list.  It stores
no original observation and no original authoritative input.  The spatial channel of a decoded
observation is tied to the actual shared source: `sharedSpatial?` is exactly the encode of the
shared coordinate channel, and for `adapt` it is exactly `binding.source.spatial?`. -/

/-- The successor satellite.  The enumeration is the physical enumeration carried by the source
binding; it is a type parameter, not payload metadata. -/
structure NativeRelationalFullereneObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (e : V ≃ Fin (Fintype.card V)) (policy : P93RelationalFullereneAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (NativeRelationalFullereneObservation V e policy)

namespace NativeRelationalFullereneObservationSatellite

variable {V : Type*} [DecidableEq V] [Fintype V]
  {e : V ≃ Fin (Fintype.card V)}
  {policy : P93RelationalFullereneAuthorityPolicy}

/-- The shared finite source, with observations intentionally excluded. -/
def toFiniteSource (satellite : NativeRelationalFullereneObservationSatellite V e policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

/-- The shared spatial channel encoded from the actual satellite source. -/
def sharedSpatial? (satellite : NativeRelationalFullereneObservationSatellite V e policy) :
    Option SpatialConfiguration :=
  OrganicFiniteSource.encodeSpatial? e satellite.spatial?

end NativeRelationalFullereneObservationSatellite

/-- Adapt a raw relational source into the successor satellite.  The shared finite source is
retained verbatim; every valid observation is encoded with the actual new input codec.  All
observation-level bounds are derived from `ValidFor` and the exact atom-count agreement. -/
def adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    NativeRelationalFullereneObservationSatellite V raw.binding.enumeration policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelObservation raw.binding.enumeration policy observation.1
      (relationalObservationBoundedIn_of_validFor
        (relationalObservationAtomCount_eq raw.binding observation.1
          (raw.valid observation.1 observation.2))
        (raw.valid observation.1 observation.2))

@[simp] theorem adapt_graph {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

@[simp] theorem adapt_observations {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).observations = raw.observations.attach.map (fun observation =>
      relabelObservation raw.binding.enumeration policy observation.1
        (relationalObservationBoundedIn_of_validFor
          (relationalObservationAtomCount_eq raw.binding observation.1
            (raw.valid observation.1 observation.2))
          (raw.valid observation.1 observation.2))) := rfl

/-- The reconstructed spatial channel is tied to the actual source, not to arbitrary payload
metadata. -/
theorem sharedSpatial?_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).sharedSpatial? = raw.binding.source.spatial? := by
  rw [NativeRelationalFullereneObservationSatellite.sharedSpatial?, adapt_spatial?,
    raw.binding.spatial_eq]

/-- Decode a successor satellite into the recovered source record. -/
def suppliedSource {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    {e : V ≃ Fin (Fintype.card V)}
    (satellite : NativeRelationalFullereneObservationSatellite V e policy) :
    RecoveredRelationalFullereneObservationSource policy where
  source := satellite.toFiniteSource.encode e
  observations := satellite.observations.map fun observation =>
    unrelabelObservation e policy (satellite.sharedSpatial?) observation

/-- **Exact ordered observation-list recovery.**  The list is recovered with order and
multiplicity, using the full-record inverse for every observation. -/
theorem decodedObservations_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).observations.map
        (unrelabelObservation raw.binding.enumeration policy
          (adapt raw).sharedSpatial?) =
      raw.observations := by
  obtain ⟨binding, observations, valid⟩ := raw
  rw [adapt_observations, List.map_map]
  refine Eq.trans ?_ (List.attach_map_subtype_val observations)
  apply List.map_congr_left
  intro observation _
  obtain ⟨observation, member⟩ := observation
  have validObservation : observation.ValidFor policy binding.source := valid observation member
  have spatialExact : observation.spatial? =
      (adapt ⟨binding, observations, valid⟩).sharedSpatial? := by
    rw [sharedSpatial?_adapt]
    exact validObservation.structureAgreement.2.1.symm
  exact unrelabelObservation_relabelObservation binding.enumeration policy observation
    (relationalObservationBoundedIn_of_validFor
      (relationalObservationAtomCount_eq binding observation validObservation)
      validObservation)
    _ spatialExact

/-- **Exact full source recovery.**  Adapting a raw relational source and decoding it returns the
exact authoritative input and the exact ordered observation list.  The input equality is the
genuine encode equality of the binding; the observation equality is the full-record inverse. -/
theorem suppliedSource_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    suppliedSource (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredRelationalFullereneObservationSource.ext
  · simp only [suppliedSource, NativeRelationalFullereneObservationSatellite.toFiniteSource,
      adapt]
    exact raw.binding.encode_shared
  · simp only [suppliedSource]
    exact decodedObservations_adapt raw

/-- Validity is transported to the recovered observations at the recovered source and the same
policy.  Nothing is re-judged at a different source, and no policy predicate is assumed invariant
under an arbitrary atom permutation. -/
theorem suppliedSource_adapt_validFor {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    ∀ observation ∈ (suppliedSource (adapt raw)).observations,
      observation.ValidFor policy (suppliedSource (adapt raw)).source := by
  intro observation member
  have recovered := suppliedSource_adapt raw
  have observationsEq :
      (suppliedSource (adapt raw)).observations = raw.observations := by
    simpa using congrArg
      (fun recovered : RecoveredRelationalFullereneObservationSource policy =>
        recovered.observations) recovered
  have sourceEq :
      (suppliedSource (adapt raw)).source = raw.binding.source := by
    simpa using congrArg
      (fun recovered : RecoveredRelationalFullereneObservationSource policy =>
        recovered.source) recovered
  rw [observationsEq] at member
  rw [sourceEq]
  exact raw.valid observation member

/-! ## Arbitrary correlated Set image inverse at a fixed source and policy

`S` is an arbitrary set of observations carrying, in correlation, their validity at the fixed
source and their spatial equality.  Encoding and decoding the whole record is an image inverse on
`S`.  The statement is deliberately about the full observation: the chiral-addend `Finset`
inverse is only the `chiralAddends` projection of it. -/

/-- The set of source observations valid at a fixed source, with the spatial channel fixed. -/
abbrev ValidObservationAt {V : Type*} [DecidableEq V] [Fintype V]
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (policy : P93RelationalFullereneAuthorityPolicy)
    (spatial? : Option SpatialConfiguration) : Type _ :=
  {observation : P93RelationalFullereneAuthorityObservation policy //
    observation.ValidFor policy binding.source ∧ observation.spatial? = spatial?}

/-- Encode one source observation that is valid at the fixed source and spatial channel. -/
def encodeValidObservation {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration)
    (observation : ValidObservationAt (V := V) binding policy spatial?) :
    NativeRelationalFullereneObservation V binding.enumeration policy :=
  relabelObservation binding.enumeration policy observation.1
    (relationalObservationBoundedIn_of_validFor
      (relationalObservationAtomCount_eq binding observation.1 observation.2.1)
      observation.2.1)

/-- Decoding an encoded valid observation returns the exact full record. -/
theorem unrelabelObservation_encodeValidObservation {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration)
    (observation : ValidObservationAt (V := V) binding policy spatial?) :
    unrelabelObservation binding.enumeration policy spatial?
        (encodeValidObservation binding spatial? observation) = observation.1 :=
  unrelabelObservation_relabelObservation binding.enumeration policy observation.1 _
    spatial? observation.2.2

/-- **Arbitrary correlated Set image inverse.**  For any set `S` of observations valid at the
fixed source and spatial channel, decoding the encoded image returns exactly `S` (as a set of
source observations).  The correlation between the input family, the selected input, the ordered
addends, the chiral-addend set, the assignment and the corpus is preserved because the whole
record -- not any single projection -- is inverted. -/
theorem set_image_unrelabelObservation_encodeValidObservation
    {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration)
    (observations : Set (ValidObservationAt (V := V) binding policy spatial?)) :
    (fun observation => unrelabelObservation binding.enumeration policy spatial?
        (encodeValidObservation binding spatial? observation)) '' observations =
      (fun observation : ValidObservationAt (V := V) binding policy spatial? =>
        observation.1) '' observations := by
  apply Set.image_congr
  intro observation _
  exact unrelabelObservation_encodeValidObservation binding spatial? observation

/-- Ordered-collection form of the same inverse: an arbitrary list of valid observations is
recovered entry by entry, with order and multiplicity. -/
theorem list_map_unrelabelObservation_encodeValidObservation
    {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration)
    (observations : List (ValidObservationAt (V := V) binding policy spatial?)) :
    observations.map (fun observation =>
        unrelabelObservation binding.enumeration policy spatial?
          (encodeValidObservation binding spatial? observation)) =
      observations.map (fun observation => observation.1) := by
  apply List.map_congr_left
  intro observation _
  exact unrelabelObservation_encodeValidObservation binding spatial? observation

end OrganicStereoRelationalFullereneInputEncoding

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodeAtomRefPair_encodeAtomRefPair
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.map_decodeAtomRef_encodeAtomRef
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.map_decodeAtomRefFaces_encodeAtomRefFaces
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.image_decodeAtomRefPair_encodeAtomRefPair
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodeAddendRef_encodeAddendRef
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.map_decodeAddendRef_encodeAddendRef
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.image_decodeAddendRef_encodeAddendRef
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodeNativeTopology_encodeNativeTopology
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodeNativeNumberingEvidence_encodeNativeNumberingEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodeNativeAddendRelationalEvidence_encodeNativeAddendRelationalEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodeNativeAddendRelationalEvidence_encodeNativeAddendRelationalEvidence_heq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.relationalSymmetryDerivedInput_eq_of
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodeRelationalSymmetryInput_encodeRelationalSymmetryInput
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodeRelationalSourceOrientedInput_encodeRelationalSourceOrientedInput
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.map_decodeRelationalSourceOrientedInput_encode
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.encodeRelationalSourceOrientedInput_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.encodeRelationalSourceOrientedInputList_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.selectedInput_mem_encoded_inputs
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.unrelabelObservation_relabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.relabelObservation_injective_of_spatial
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.relabelObservation_selectedInput_mem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.unrelabelObservationBounded
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.sharedSpatial?_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.decodedObservations_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.suppliedSource_adapt_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.set_image_unrelabelObservation_encodeValidObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding.list_map_unrelabelObservation_encodeValidObservation
