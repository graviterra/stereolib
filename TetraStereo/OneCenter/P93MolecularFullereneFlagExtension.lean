import TetraStereo.OneCenter.P93MolecularFullereneAutomorphismCertificate
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Non-factorial extension from a fullerene flag

An automorphism of a connected oriented cubic map is fixed by the image of one directed edge.
The reason is local: reverse the edge, or continue around the face on a selected side.  Repeating
these two moves reaches every directed edge.  An orientation-preserving map carries left-face
continuation to left-face continuation, while an orientation-reversing map carries left-face
continuation to right-face continuation.  Both cases are represented by separate source and
target continuation functions below; this polarity distinction is essential.

This file isolates and proves the propagation theorem.  A certificate now contains only one
finite word in the two flag moves for each cage atom, together with local equivariance.  It does
*not* contain a corpus of permutations and it does not quantify over candidate permutations to
construct an extension.  For any proposed image edge, the extension is obtained by replaying
those words.  The noncomputable definition selects the resulting equivalence when that one vertex
map is bijective and otherwise falls back to the identity.  Thus the mathematical candidate
family contains at most `|V|^2` generated maps; this is not yet an executable runtime claim.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-- The two generators of the flag graph of an oriented cubic surface map. -/
inductive MolecularFullereneFlagMove
  | reverseEdge
  | continueLeftFace
  deriving DecidableEq, Fintype

/-- Apply a carrier permutation simultaneously to both ends of a directed cage edge. -/
def mapMolecularFullereneDirectedEdge
    {input : MolecularFullereneConfigurationInput}
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) :
    MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input :=
  (symmetry edge.1, symmetry edge.2)

/-- A rotation system is represented by the third atom obtained by continuing along the
coherently oriented face on the left of a directed edge.  Edge reversal is intrinsic. -/
def molecularFullereneFlagStep
    {input : MolecularFullereneConfigurationInput}
    (continueLeftFace :
      (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) →
        MolecularFullereneCarrierAtom input)
    (move : MolecularFullereneFlagMove)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) :
    MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input :=
  match move with
  | .reverseEdge => (edge.2, edge.1)
  | .continueLeftFace => (edge.2, continueLeftFace edge)

/-- Replay a finite flag word from a proposed directed edge. -/
def walkMolecularFullereneFlag
    {input : MolecularFullereneConfigurationInput}
    (continueLeftFace :
      (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) →
        MolecularFullereneCarrierAtom input)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) :
    List MolecularFullereneFlagMove →
      MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input
  | [] => edge
  | move :: moves =>
      walkMolecularFullereneFlag continueLeftFace
        (molecularFullereneFlagStep continueLeftFace move edge) moves

/-! ## Concrete continuation extracted from the supplied face lists -/

/-- Executable directed-edge test for a stored cyclic face.  `nextOr` avoids a proof-bearing
lookup in the data path; validated faces are duplicate-free and have length five or six. -/
def isForwardMolecularFullereneFaceEdge
    (face : List ℕ) (left right : ℕ) : Bool :=
  face.contains left && face.nextOr left (face.head?.getD left) == right

/-- The first stored face traversing a directed edge in the coherent source orientation.  Under
`OrientedMolecularFullereneFaceMapJudgment`, exactly one such face exists for every cage edge, so
the result is independent of source list ordering. -/
def molecularFullereneForwardFace?
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) : Option (List ℕ) :=
  input.faces.find? fun face =>
    isForwardMolecularFullereneFaceEdge face edge.1.1 edge.2.1

/-- Raw next atom when the directed edge is continued around its forward-oriented incident face.
Malformed/non-edge inputs fall back to the first endpoint; all generated candidates are filtered
against the independent automorphism judgment downstream. -/
def molecularFullereneForwardContinuationAtom
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) : ℕ :=
  match molecularFullereneForwardFace? input edge with
  | some face => face.nextOr edge.2.1 (face.head?.getD edge.1.1)
  | none => edge.1.1

/-- Typed forward-face continuation computed directly from the source face map. -/
def molecularFullereneContinueForwardFace
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) : MolecularFullereneCarrierAtom input :=
  if member : molecularFullereneForwardContinuationAtom input edge ∈ input.carrier then
    ⟨molecularFullereneForwardContinuationAtom input edge, member⟩
  else
    edge.1

/-- Raw continuation on the right face of a directed edge.  The stored face containing the
reversed edge is traversed backwards, so the result is the predecessor of the second endpoint in
that stored orientation. -/
def molecularFullereneReverseContinuationAtom
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) : ℕ :=
  match molecularFullereneForwardFace? input (edge.2, edge.1) with
  | some face => face.reverse.nextOr edge.2.1 (face.reverse.head?.getD edge.1.1)
  | none => edge.1.1

/-- Typed right-face continuation used for orientation-reversing automorphisms. -/
def molecularFullereneContinueReverseFace
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) : MolecularFullereneCarrierAtom input :=
  if member : molecularFullereneReverseContinuationAtom input edge ∈ input.carrier then
    ⟨molecularFullereneReverseContinuationAtom input edge, member⟩
  else
    edge.1

@[simp] theorem molecularFullereneContinueReverseFace_eq
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) :
    molecularFullereneContinueReverseFace input edge =
      if member : molecularFullereneReverseContinuationAtom input edge ∈ input.carrier then
        ⟨molecularFullereneReverseContinuationAtom input edge, member⟩
      else edge.1 := rfl

/-! ## Functoriality of directed face edges -/

@[simp] theorem mapMolecularFullereneCarrierAtom_of_mem
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (atom : ℕ) (member : atom ∈ input.carrier) :
    mapMolecularFullereneCarrierAtom input symmetry atom =
      (symmetry ⟨atom, member⟩).1 := by
  simp [mapMolecularFullereneCarrierAtom, member]

theorem mapMolecularFullereneCarrierAtom_injective_on_carrier
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    {left right : ℕ}
    (leftMember : left ∈ input.carrier) (rightMember : right ∈ input.carrier)
    (mapped : mapMolecularFullereneCarrierAtom input symmetry left =
      mapMolecularFullereneCarrierAtom input symmetry right) :
    left = right := by
  simp only [mapMolecularFullereneCarrierAtom_of_mem input symmetry left leftMember,
    mapMolecularFullereneCarrierAtom_of_mem input symmetry right rightMember] at mapped
  exact Subtype.ext_iff.mp (symmetry.injective (Subtype.ext mapped))

/-- Mapping a duplicate-free carrier face by a carrier permutation preserves its directed cyclic
edges.  This is the local list theorem used by both orientation polarities below. -/
theorem isForwardNamedCycleEdge_mapMolecularFullereneFace
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (face : List ℕ)
    (faceCarrier : ∀ atom ∈ face, atom ∈ input.carrier)
    (faceNodup : face.Nodup)
    {left right : ℕ}
    (edge : IsForwardNamedCycleEdge face left right) :
    IsForwardNamedCycleEdge (mapMolecularFullereneFace input symmetry face)
      (mapMolecularFullereneCarrierAtom input symmetry left)
      (mapMolecularFullereneCarrierAtom input symmetry right) := by
  rcases edge with ⟨leftMember, nextEq⟩
  obtain ⟨index, indexLt, leftEq⟩ := List.getElem_of_mem leftMember
  subst left
  have mappedNodup :
      (mapMolecularFullereneFace input symmetry face).Nodup := by
    apply faceNodup.map_on
    intro first firstMember second secondMember equal
    exact mapMolecularFullereneCarrierAtom_injective_on_carrier input symmetry
      (faceCarrier first firstMember) (faceCarrier second secondMember) equal
  have mappedLeftMember :
      mapMolecularFullereneCarrierAtom input symmetry face[index] ∈
        mapMolecularFullereneFace input symmetry face := by
    exact List.mem_map.mpr ⟨face[index], leftMember, rfl⟩
  refine ⟨mappedLeftMember, ?_⟩
  have sourceNext :
      face.next face[index] (List.getElem_mem indexLt) =
        face[(index + 1) % face.length]'(Nat.mod_lt _ (by omega)) :=
    List.next_getElem face faceNodup index indexLt
  have targetNext := List.next_getElem
    (mapMolecularFullereneFace input symmetry face) mappedNodup index
      (by simpa [mapMolecularFullereneFace] using indexLt)
  have sourceNextRight : face[(index + 1) % face.length]'(Nat.mod_lt _ (by omega)) = right :=
    sourceNext.symm.trans nextEq
  simpa only [mapMolecularFullereneFace, List.length_map, List.getElem_map,
    sourceNextRight] using targetNext

/-- Directed cyclic adjacency is unchanged by rotating the written representative of a
duplicate-free face. -/
theorem isForwardNamedCycleEdge_iff_of_isRotated
    {first second : List ℕ} (rotated : first ~r second)
    (firstNodup : first.Nodup) (left right : ℕ) :
    IsForwardNamedCycleEdge first left right ↔
      IsForwardNamedCycleEdge second left right := by
  constructor
  · rintro ⟨leftMember, nextEq⟩
    refine ⟨rotated.mem_iff.mp leftMember, ?_⟩
    rw [← List.isRotated_next_eq rotated firstNodup leftMember]
    exact nextEq
  · rintro ⟨leftMember, nextEq⟩
    refine ⟨rotated.symm.mem_iff.mp leftMember, ?_⟩
    rw [← List.isRotated_next_eq rotated.symm
      (rotated.nodup_iff.mp firstNodup) leftMember]
    exact nextEq

/-- Reversing a duplicate-free cyclic face reverses each directed edge. -/
theorem isForwardNamedCycleEdge_reverse_iff
    (face : List ℕ) (faceNodup : face.Nodup) (left right : ℕ) :
    IsForwardNamedCycleEdge face.reverse left right ↔
      IsForwardNamedCycleEdge face right left := by
  constructor
  · rintro ⟨leftMember, nextEq⟩
    have leftInFace : left ∈ face := List.mem_reverse.mp leftMember
    have rightEqPrev : right = face.prev left leftInFace := by
      exact nextEq.symm.trans (List.next_reverse_eq_prev face faceNodup left leftInFace)
    refine ⟨rightEqPrev.symm ▸ List.prev_mem face left leftInFace, ?_⟩
    simpa only [rightEqPrev] using List.next_prev face faceNodup left leftInFace
  · rintro ⟨rightMember, nextEq⟩
    have leftEqNext : left = face.next right rightMember := nextEq.symm
    subst left
    refine ⟨List.mem_reverse.mpr (List.next_mem face right rightMember), ?_⟩
    simpa only using
      (List.next_reverse_eq_prev face faceNodup
        (face.next right rightMember) (List.next_mem face right rightMember)).trans
          (List.prev_next face faceNodup right rightMember)

/-- Semantic forward continuation through the uniquely oriented incident face of a directed
carrier edge.  This relation is independent of source-list ordering. -/
def MolecularFullereneForwardContinuationJudgment
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (next : MolecularFullereneCarrierAtom input) : Prop :=
  ∃ face ∈ input.faces,
    IsForwardNamedCycleEdge face edge.1.1 edge.2.1 ∧
      IsForwardNamedCycleEdge face edge.2.1 next.1

/-- Semantic continuation on the opposite orientation: the stored target face traverses
`next → right → left`. -/
def MolecularFullereneReverseContinuationJudgment
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (next : MolecularFullereneCarrierAtom input) : Prop :=
  ∃ face ∈ input.faces,
    IsForwardNamedCycleEdge face edge.2.1 edge.1.1 ∧
      IsForwardNamedCycleEdge face next.1 edge.2.1

theorem nextOr_head_getD_eq_next
    (face : List ℕ) (left : ℕ) (member : left ∈ face) :
    face.nextOr left (face.head?.getD left) = face.next left member := by
  unfold List.next
  congr 1
  cases face with
  | nil => simp at member
  | cons head tail => rfl

theorem nextOr_head_getD_eq_next_of
    (face : List ℕ) (left fallback : ℕ) (member : left ∈ face) :
    face.nextOr left (face.head?.getD fallback) = face.next left member := by
  unfold List.next
  congr 1
  cases face with
  | nil => simp at member
  | cons head tail => rfl

/-- The executable face-edge predicate is exactly the proof-bearing cyclic-edge relation. -/
@[simp] theorem isForwardMolecularFullereneFaceEdge_eq_true_iff
    (face : List ℕ) (left right : ℕ) :
    isForwardMolecularFullereneFaceEdge face left right = true ↔
      IsForwardNamedCycleEdge face left right := by
  unfold isForwardMolecularFullereneFaceEdge
  simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq]
  constructor
  · rintro ⟨member, nextEq⟩
    refine ⟨member, ?_⟩
    rw [← nextOr_head_getD_eq_next face left member]
    exact nextEq
  · rintro ⟨member, nextEq⟩
    refine ⟨member, ?_⟩
    rw [nextOr_head_getD_eq_next face left member]
    exact nextEq

/-- Any face returned by the executable search is a supplied face traversing the requested
directed edge. -/
theorem molecularFullereneForwardFace?_sound
    (input : MolecularFullereneConfigurationInput)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (face : List ℕ)
    (found : molecularFullereneForwardFace? input edge = some face) :
    face ∈ input.faces ∧ IsForwardNamedCycleEdge face edge.1.1 edge.2.1 := by
  unfold molecularFullereneForwardFace? at found
  refine ⟨List.mem_of_find?_eq_some found, ?_⟩
  exact (isForwardMolecularFullereneFaceEdge_eq_true_iff _ _ _).mp
    (List.find?_some (p := fun candidate =>
      isForwardMolecularFullereneFaceEdge candidate edge.1.1 edge.2.1) (a := face) found)

/-- Every directed molecular cage bond has an executable forward-face result. -/
theorem molecularFullereneForwardFace?_exists_of_bond
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (bond : 0 < molecule.bondOrder edge.1.1 edge.2.1) :
    ∃ face, molecularFullereneForwardFace? input edge = some face := by
  have ne : edge.1.1 ≠ edge.2.1 := by
    intro equal
    simp [equal, molecule.bondOrder_self] at bond
  have count : input.faces.countP
      (fun face => decide (IsForwardNamedCycleEdge face edge.1.1 edge.2.1)) = 1 := by
    rcases lt_or_gt_of_ne ne with less | greater
    · exact (oriented.2 edge.1.1 edge.1.2 edge.2.1 edge.2.2 less bond).1
    · have judged := oriented.2 edge.2.1 edge.2.2 edge.1.1 edge.1.2 greater
        (by simpa [molecule.bondOrder_symm] using bond)
      exact judged.2
  have positive : 0 < input.faces.countP
      (fun face => decide (IsForwardNamedCycleEdge face edge.1.1 edge.2.1)) := by
    omega
  rcases List.countP_pos_iff.mp positive with ⟨face, facePresent, forward⟩
  have executable : isForwardMolecularFullereneFaceEdge face edge.1.1 edge.2.1 = true :=
    (isForwardMolecularFullereneFaceEdge_eq_true_iff _ _ _).mpr
      (of_decide_eq_true forward)
  have foundSome : (molecularFullereneForwardFace? input edge).isSome := by
    unfold molecularFullereneForwardFace?
    exact List.find?_isSome.mpr ⟨face, facePresent, executable⟩
  cases found : molecularFullereneForwardFace? input edge with
  | none => simp [found] at foundSome
  | some face => exact ⟨face, rfl⟩

/-- On a checked directed cage bond, the executable forward continuation realizes the semantic
oriented-face continuation relation. -/
theorem molecularFullereneContinueForwardFace_judged
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (bond : 0 < molecule.bondOrder edge.1.1 edge.2.1) :
    MolecularFullereneForwardContinuationJudgment input edge
      (molecularFullereneContinueForwardFace input edge) := by
  rcases molecularFullereneForwardFace?_exists_of_bond molecule input oriented edge bond with
    ⟨face, found⟩
  rcases molecularFullereneForwardFace?_sound input edge face found with
    ⟨facePresent, firstEdge⟩
  rcases firstEdge with ⟨leftMember, firstNext⟩
  have valid := oriented.1.facesValid face facePresent
  have rightMember : edge.2.1 ∈ face := by
    rw [← firstNext]
    exact List.next_mem face edge.1.1 leftMember
  have rawEq : molecularFullereneForwardContinuationAtom input edge =
      face.next edge.2.1 rightMember := by
    unfold molecularFullereneForwardContinuationAtom
    rw [found]
    exact nextOr_head_getD_eq_next_of face edge.2.1 edge.1.1 rightMember
  have rawMember : molecularFullereneForwardContinuationAtom input edge ∈ input.carrier := by
    rw [rawEq]
    exact valid.2.1 (by simpa using List.next_mem face edge.2.1 rightMember)
  refine ⟨face, facePresent, ⟨leftMember, firstNext⟩, ?_⟩
  refine ⟨rightMember, ?_⟩
  rw [molecularFullereneContinueForwardFace, dif_pos rawMember]
  exact rawEq.symm

private theorem eq_of_mem_of_countP_eq_one
    {α : Type} [DecidableEq α] (items : List α) (predicate : α → Bool)
    (itemsNodup : items.Nodup) (count : items.countP predicate = 1)
    {first second : α}
    (firstPresent : first ∈ items) (firstTrue : predicate first = true)
    (secondPresent : second ∈ items) (secondTrue : predicate second = true) :
    first = second := by
  have filteredNodup : (items.filter predicate).Nodup := itemsNodup.filter _
  have filteredLength : (items.filter predicate).length = 1 := by
    simpa only [List.countP_eq_length_filter] using count
  have firstFiltered : first ∈ items.filter predicate :=
    List.mem_filter.mpr ⟨firstPresent, firstTrue⟩
  have secondFiltered : second ∈ items.filter predicate :=
    List.mem_filter.mpr ⟨secondPresent, secondTrue⟩
  cases filtered : items.filter predicate with
  | nil => simp [filtered] at filteredLength
  | cons head tail =>
      have tailEmpty : tail = [] := by simpa [filtered] using filteredLength
      subst tail
      simp only [filtered, List.mem_singleton] at firstFiltered secondFiltered
      exact firstFiltered.trans secondFiltered.symm

/-- The semantic forward continuation of a checked directed cage bond is unique. -/
theorem molecularFullereneForwardContinuationJudgment_functional
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (bond : 0 < molecule.bondOrder edge.1.1 edge.2.1)
    (first second : MolecularFullereneCarrierAtom input)
    (firstJudged : MolecularFullereneForwardContinuationJudgment input edge first)
    (secondJudged : MolecularFullereneForwardContinuationJudgment input edge second) :
    first = second := by
  rcases firstJudged with ⟨firstFace, firstPresent, firstEdge, firstNext⟩
  rcases secondJudged with ⟨secondFace, secondPresent, secondEdge, secondNext⟩
  have ne : edge.1.1 ≠ edge.2.1 := by
    intro equal
    simp [equal, molecule.bondOrder_self] at bond
  have count : input.faces.countP
      (fun face => decide (IsForwardNamedCycleEdge face edge.1.1 edge.2.1)) = 1 := by
    rcases lt_or_gt_of_ne ne with less | greater
    · exact (oriented.2 edge.1.1 edge.1.2 edge.2.1 edge.2.2 less bond).1
    · exact (oriented.2 edge.2.1 edge.2.2 edge.1.1 edge.1.2 greater
        (by simpa [molecule.bondOrder_symm] using bond)).2
  have facesNodup : input.faces.Nodup := oriented.1.facesNodup.of_map List.toFinset
  have facesEq : firstFace = secondFace :=
    eq_of_mem_of_countP_eq_one input.faces
      (fun face => decide (IsForwardNamedCycleEdge face edge.1.1 edge.2.1))
      facesNodup count firstPresent (by simpa using firstEdge)
        secondPresent (by simpa using secondEdge)
  subst secondFace
  rcases firstNext with ⟨firstMember, firstEq⟩
  rcases secondNext with ⟨secondMember, secondEq⟩
  apply Subtype.ext
  rw [← firstEq, ← secondEq]

private theorem next_ne_self_of_nodup_of_two_le
    (face : List ℕ) (faceNodup : face.Nodup) (twoLe : 2 ≤ face.length)
    (atom : ℕ) (member : atom ∈ face) :
    face.next atom member ≠ atom := by
  obtain ⟨index, indexLt, atomEq⟩ := List.getElem_of_mem member
  subst atom
  rw [List.next_getElem face faceNodup index indexLt]
  intro equal
  have indexNe : (index + 1) % face.length ≠ index := by
    intro indexEq
    have successorLe : index + 1 ≤ face.length := by omega
    rcases successorLe.eq_or_lt with successorEq | successorLt
    · rw [successorEq, Nat.mod_self] at indexEq
      omega
    · rw [Nat.mod_eq_of_lt successorLt] at indexEq
      omega
  exact indexNe ((faceNodup.getElem_inj_iff).mp equal)

/-- A directed edge of any validated fullerene face is an actual positive molecular bond. -/
theorem bondOrder_pos_of_forwardFaceEdge
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (carrierJudged : MolecularFullereneCarrierJudgment molecule input)
    (face : List ℕ) (facePresent : face ∈ input.faces)
    (left right : ℕ) (forward : IsForwardNamedCycleEdge face left right) :
    0 < molecule.bondOrder left right := by
  have valid := carrierJudged.facesValid face facePresent
  rcases forward with ⟨leftMember, nextEq⟩
  have rightMember : right ∈ face := by
    rw [← nextEq]
    exact List.next_mem face left leftMember
  have leftNeRight : left ≠ right := by
    intro equal
    have twoLe : 2 ≤ face.length := by rcases valid.2.2 with length | length <;> omega
    exact next_ne_self_of_nodup_of_two_le face valid.1.2.1 twoLe
      left leftMember (nextEq.trans equal.symm)
  have named : P94MolecularRingCycleScheduler.IsNamedCycleEdge face left right :=
    ⟨leftMember, Or.inl nextEq⟩
  have bonded : P94ConformationUnit.Bonded molecule left right :=
    (valid.1.2.2.2.2.2 left leftMember right rightMember leftNeRight).mpr named
  exact (molecule.bondOrder_pos_iff_exists_bond leftNeRight).mpr bonded

/-- If a typed carrier pair is not bonded, executable forward-face search returns no face. -/
theorem molecularFullereneForwardFace?_eq_none_of_not_bond
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (carrierJudged : MolecularFullereneCarrierJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (notBond : ¬0 < molecule.bondOrder edge.1.1 edge.2.1) :
    molecularFullereneForwardFace? input edge = none := by
  cases found : molecularFullereneForwardFace? input edge with
  | none => rfl
  | some face =>
      rcases molecularFullereneForwardFace?_sound input edge face found with
        ⟨facePresent, forward⟩
      exact False.elim (notBond
        (bondOrder_pos_of_forwardFaceEdge molecule input carrierJudged face facePresent
          edge.1.1 edge.2.1 forward))

@[simp] theorem molecularFullereneContinueForwardFace_eq_left_of_not_bond
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (carrierJudged : MolecularFullereneCarrierJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (notBond : ¬0 < molecule.bondOrder edge.1.1 edge.2.1) :
    molecularFullereneContinueForwardFace input edge = edge.1 := by
  have none := molecularFullereneForwardFace?_eq_none_of_not_bond
    molecule input carrierJudged edge notBond
  simp [molecularFullereneContinueForwardFace,
    molecularFullereneForwardContinuationAtom, none, edge.1.2]

@[simp] theorem molecularFullereneContinueReverseFace_eq_left_of_not_bond
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (carrierJudged : MolecularFullereneCarrierJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (notBond : ¬0 < molecule.bondOrder edge.1.1 edge.2.1) :
    molecularFullereneContinueReverseFace input edge = edge.1 := by
  let reversedEdge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input := (edge.2, edge.1)
  have reversedNotBond : ¬0 < molecule.bondOrder reversedEdge.1.1 reversedEdge.2.1 := by
    simpa [reversedEdge, molecule.bondOrder_symm] using notBond
  have none := molecularFullereneForwardFace?_eq_none_of_not_bond
    molecule input carrierJudged reversedEdge reversedNotBond
  simp [molecularFullereneContinueReverseFace,
    molecularFullereneReverseContinuationAtom, reversedEdge, none, edge.1.2]

/-- On a checked directed cage bond, the executable reverse continuation realizes the semantic
opposite-orientation continuation relation. -/
theorem molecularFullereneContinueReverseFace_judged
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (bond : 0 < molecule.bondOrder edge.1.1 edge.2.1) :
    MolecularFullereneReverseContinuationJudgment input edge
      (molecularFullereneContinueReverseFace input edge) := by
  let reversedEdge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input := (edge.2, edge.1)
  have reversedBond : 0 < molecule.bondOrder reversedEdge.1.1 reversedEdge.2.1 := by
    simpa [reversedEdge, molecule.bondOrder_symm] using bond
  rcases molecularFullereneForwardFace?_exists_of_bond molecule input oriented
      reversedEdge reversedBond with ⟨face, found⟩
  rcases molecularFullereneForwardFace?_sound input reversedEdge face found with
    ⟨facePresent, firstEdge⟩
  rcases firstEdge with ⟨rightMember, firstNext⟩
  have valid := oriented.1.facesValid face facePresent
  have reverseRightMember : edge.2.1 ∈ face.reverse := List.mem_reverse.mpr rightMember
  have rawEq : molecularFullereneReverseContinuationAtom input edge =
      face.prev edge.2.1 rightMember := by
    unfold molecularFullereneReverseContinuationAtom
    change (match molecularFullereneForwardFace? input reversedEdge with
      | some selected => selected.reverse.nextOr edge.2.1
          (selected.reverse.head?.getD edge.1.1)
      | none => edge.1.1) = _
    rw [found]
    exact (nextOr_head_getD_eq_next_of face.reverse edge.2.1 edge.1.1
      reverseRightMember).trans
        (List.next_reverse_eq_prev face valid.1.2.1 edge.2.1 rightMember)
  have rawMember : molecularFullereneReverseContinuationAtom input edge ∈ input.carrier := by
    rw [rawEq]
    exact valid.2.1 (by simpa using List.prev_mem face edge.2.1 rightMember)
  have computedEq : molecularFullereneContinueReverseFace input edge =
      ⟨molecularFullereneReverseContinuationAtom input edge, rawMember⟩ := by
    simp [molecularFullereneContinueReverseFace, rawMember]
  refine ⟨face, facePresent, ⟨rightMember, firstNext⟩, ?_⟩
  have previousMember : face.prev edge.2.1 rightMember ∈ face :=
    List.prev_mem face edge.2.1 rightMember
  have computedValEq : (molecularFullereneContinueReverseFace input edge).1 =
      face.prev edge.2.1 rightMember := by
    rw [computedEq]
    exact rawEq
  have computedMember : (molecularFullereneContinueReverseFace input edge).1 ∈ face := by
    rw [computedValEq]
    exact previousMember
  refine ⟨computedMember, ?_⟩
  have memberEq :
      (⟨(molecularFullereneContinueReverseFace input edge).1, computedMember⟩ :
          { atom : ℕ // atom ∈ face }) =
        ⟨face.prev edge.2.1 rightMember, previousMember⟩ :=
    Subtype.ext computedValEq
  exact (congrArg (fun atom : { atom : ℕ // atom ∈ face } =>
    face.next atom.1 atom.2) memberEq).trans
      (List.next_prev face valid.1.2.1 edge.2.1 rightMember)

/-- The semantic opposite-orientation continuation of a checked directed cage bond is unique. -/
theorem molecularFullereneReverseContinuationJudgment_functional
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (bond : 0 < molecule.bondOrder edge.1.1 edge.2.1)
    (first second : MolecularFullereneCarrierAtom input)
    (firstJudged : MolecularFullereneReverseContinuationJudgment input edge first)
    (secondJudged : MolecularFullereneReverseContinuationJudgment input edge second) :
    first = second := by
  rcases firstJudged with ⟨firstFace, firstPresent, firstEdge, firstPrevious⟩
  rcases secondJudged with ⟨secondFace, secondPresent, secondEdge, secondPrevious⟩
  have reversedBond : 0 < molecule.bondOrder edge.2.1 edge.1.1 := by
    simpa [molecule.bondOrder_symm] using bond
  have ne : edge.2.1 ≠ edge.1.1 := by
    intro equal
    simp [equal, molecule.bondOrder_self] at reversedBond
  have count : input.faces.countP
      (fun face => decide (IsForwardNamedCycleEdge face edge.2.1 edge.1.1)) = 1 := by
    rcases lt_or_gt_of_ne ne with less | greater
    · exact (oriented.2 edge.2.1 edge.2.2 edge.1.1 edge.1.2 less reversedBond).1
    · exact (oriented.2 edge.1.1 edge.1.2 edge.2.1 edge.2.2 greater bond).2
  have facesNodup : input.faces.Nodup := oriented.1.facesNodup.of_map List.toFinset
  have facesEq : firstFace = secondFace :=
    eq_of_mem_of_countP_eq_one input.faces
      (fun face => decide (IsForwardNamedCycleEdge face edge.2.1 edge.1.1))
      facesNodup count firstPresent (by simpa using firstEdge)
        secondPresent (by simpa using secondEdge)
  subst secondFace
  have faceNodup := (oriented.1.facesValid firstFace firstPresent).1.2.1
  have firstReversed : IsForwardNamedCycleEdge firstFace.reverse edge.2.1 first.1 :=
    (isForwardNamedCycleEdge_reverse_iff firstFace faceNodup _ _).mpr firstPrevious
  have secondReversed : IsForwardNamedCycleEdge firstFace.reverse edge.2.1 second.1 :=
    (isForwardNamedCycleEdge_reverse_iff firstFace faceNodup _ _).mpr secondPrevious
  rcases firstReversed with ⟨firstMember, firstEq⟩
  rcases secondReversed with ⟨secondMember, secondEq⟩
  apply Subtype.ext
  rw [← firstEq, ← secondEq]

/-- Proper face-map symmetries carry semantic forward continuation to forward continuation. -/
theorem molecularFullereneForwardContinuationJudgment_equivariant
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (preserving : MolecularFullereneFaceOrientationPreserving input symmetry)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (next : MolecularFullereneCarrierAtom input)
    (continued : MolecularFullereneForwardContinuationJudgment input edge next) :
    MolecularFullereneForwardContinuationJudgment input
      (mapMolecularFullereneDirectedEdge symmetry edge) (symmetry next) := by
  rcases continued with ⟨face, facePresent, firstEdge, secondEdge⟩
  rcases preserving face facePresent with ⟨target, targetPresent, rotated⟩
  have valid := oriented.1.facesValid face facePresent
  have faceNodup : face.Nodup := valid.1.2.1
  have faceCarrier : ∀ atom ∈ face, atom ∈ input.carrier := by
    intro atom member
    exact valid.2.1 (by simpa using member)
  have mappedNodup : (mapMolecularFullereneFace input symmetry face).Nodup := by
    apply faceNodup.map_on
    intro first firstMember second secondMember equal
    exact mapMolecularFullereneCarrierAtom_injective_on_carrier input symmetry
      (faceCarrier first firstMember) (faceCarrier second secondMember) equal
  refine ⟨target, targetPresent, ?_, ?_⟩
  · apply (isForwardNamedCycleEdge_iff_of_isRotated rotated mappedNodup _ _).mp
    simpa using isForwardNamedCycleEdge_mapMolecularFullereneFace input symmetry face
      faceCarrier faceNodup firstEdge
  · apply (isForwardNamedCycleEdge_iff_of_isRotated rotated mappedNodup _ _).mp
    simpa using isForwardNamedCycleEdge_mapMolecularFullereneFace input symmetry face
      faceCarrier faceNodup secondEdge

/-- Orientation-reversing face-map symmetries carry semantic forward continuation to the
opposite-orientation continuation. -/
theorem molecularFullereneReverseContinuationJudgment_equivariant
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (next : MolecularFullereneCarrierAtom input)
    (continued : MolecularFullereneForwardContinuationJudgment input edge next) :
    MolecularFullereneReverseContinuationJudgment input
      (mapMolecularFullereneDirectedEdge symmetry edge) (symmetry next) := by
  rcases continued with ⟨face, facePresent, firstEdge, secondEdge⟩
  rcases reversing face facePresent with ⟨target, targetPresent, rotated⟩
  have valid := oriented.1.facesValid face facePresent
  have faceNodup : face.Nodup := valid.1.2.1
  have faceCarrier : ∀ atom ∈ face, atom ∈ input.carrier := by
    intro atom member
    exact valid.2.1 (by simpa using member)
  have mappedNodup : (mapMolecularFullereneFace input symmetry face).Nodup := by
    apply faceNodup.map_on
    intro first firstMember second secondMember equal
    exact mapMolecularFullereneCarrierAtom_injective_on_carrier input symmetry
      (faceCarrier first firstMember) (faceCarrier second secondMember) equal
  have reverseNodup := List.nodup_reverse.mpr mappedNodup
  refine ⟨target, targetPresent, ?_, ?_⟩
  · apply (isForwardNamedCycleEdge_iff_of_isRotated rotated reverseNodup _ _).mp
    apply (isForwardNamedCycleEdge_reverse_iff _ mappedNodup _ _).mpr
    simpa using isForwardNamedCycleEdge_mapMolecularFullereneFace input symmetry face
      faceCarrier faceNodup firstEdge
  · apply (isForwardNamedCycleEdge_iff_of_isRotated rotated reverseNodup _ _).mp
    apply (isForwardNamedCycleEdge_reverse_iff _ mappedNodup _ _).mpr
    simpa using isForwardNamedCycleEdge_mapMolecularFullereneFace input symmetry face
      faceCarrier faceNodup secondEdge

/-- The actual computed forward continuation is equivariant under every orientation-preserving
cage automorphism, with no caller-supplied local equivariance theorem. -/
theorem molecularFullereneContinueForwardFace_equivariant
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (automorphism : MolecularFullereneCarrierAutomorphism molecule input symmetry)
    (preserving : MolecularFullereneFaceOrientationPreserving input symmetry)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) :
    molecularFullereneContinueForwardFace input
        (mapMolecularFullereneDirectedEdge symmetry edge) =
      symmetry (molecularFullereneContinueForwardFace input edge) := by
  by_cases bond : 0 < molecule.bondOrder edge.1.1 edge.2.1
  · have targetBond : 0 < molecule.bondOrder
        (symmetry edge.1).1 (symmetry edge.2).1 := (automorphism edge.1 edge.2).mp bond
    exact molecularFullereneForwardContinuationJudgment_functional molecule input oriented
      (mapMolecularFullereneDirectedEdge symmetry edge) targetBond _ _
      (molecularFullereneContinueForwardFace_judged molecule input oriented _ targetBond)
      (molecularFullereneForwardContinuationJudgment_equivariant molecule input oriented
        symmetry preserving edge _
          (molecularFullereneContinueForwardFace_judged molecule input oriented edge bond))
  · have targetNotBond : ¬0 < molecule.bondOrder
        (symmetry edge.1).1 (symmetry edge.2).1 := by
      exact fun targetBond => bond ((automorphism edge.1 edge.2).mpr targetBond)
    rw [molecularFullereneContinueForwardFace_eq_left_of_not_bond molecule input oriented.1
      edge bond]
    rw [molecularFullereneContinueForwardFace_eq_left_of_not_bond molecule input oriented.1
      (mapMolecularFullereneDirectedEdge symmetry edge) targetNotBond]
    rfl

/-- The actual computed reverse continuation is equivariant with computed forward continuation
under every orientation-reversing cage automorphism. -/
theorem molecularFullereneContinueReverseFace_equivariant
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (automorphism : MolecularFullereneCarrierAutomorphism molecule input symmetry)
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) :
    molecularFullereneContinueReverseFace input
        (mapMolecularFullereneDirectedEdge symmetry edge) =
      symmetry (molecularFullereneContinueForwardFace input edge) := by
  by_cases bond : 0 < molecule.bondOrder edge.1.1 edge.2.1
  · have targetBond : 0 < molecule.bondOrder
        (symmetry edge.1).1 (symmetry edge.2).1 := (automorphism edge.1 edge.2).mp bond
    exact molecularFullereneReverseContinuationJudgment_functional molecule input oriented
      (mapMolecularFullereneDirectedEdge symmetry edge) targetBond _ _
      (molecularFullereneContinueReverseFace_judged molecule input oriented _ targetBond)
      (molecularFullereneReverseContinuationJudgment_equivariant molecule input oriented
        symmetry reversing edge _
          (molecularFullereneContinueForwardFace_judged molecule input oriented edge bond))
  · have targetNotBond : ¬0 < molecule.bondOrder
        (symmetry edge.1).1 (symmetry edge.2).1 := by
      exact fun targetBond => bond ((automorphism edge.1 edge.2).mpr targetBond)
    rw [molecularFullereneContinueForwardFace_eq_left_of_not_bond molecule input oriented.1
      edge bond]
    rw [molecularFullereneContinueReverseFace_eq_left_of_not_bond molecule input oriented.1
      (mapMolecularFullereneDirectedEdge symmetry edge) targetNotBond]
    rfl

/-- Local equivariance of face continuation implies equivariance of one flag move. -/
theorem molecularFullereneFlagStep_equivariant
    {input : MolecularFullereneConfigurationInput}
    (continueSourceFace continueTargetFace :
      (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) →
        MolecularFullereneCarrierAtom input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (continueEquivariant : ∀ edge,
      continueTargetFace (mapMolecularFullereneDirectedEdge symmetry edge) =
        symmetry (continueSourceFace edge))
    (move : MolecularFullereneFlagMove)
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) :
    molecularFullereneFlagStep continueTargetFace move
        (mapMolecularFullereneDirectedEdge symmetry edge) =
      mapMolecularFullereneDirectedEdge symmetry
        (molecularFullereneFlagStep continueSourceFace move edge) := by
  cases move with
  | reverseEdge => rfl
  | continueLeftFace =>
      change (symmetry edge.2,
          continueTargetFace (mapMolecularFullereneDirectedEdge symmetry edge)) =
        (symmetry edge.2, symmetry (continueSourceFace edge))
      rw [continueEquivariant edge]

/-- Equivariance propagates from the two local flag moves to every finite flag word. -/
theorem walkMolecularFullereneFlag_equivariant
    {input : MolecularFullereneConfigurationInput}
    (continueSourceFace continueTargetFace :
      (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) →
        MolecularFullereneCarrierAtom input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (continueEquivariant : ∀ edge,
      continueTargetFace (mapMolecularFullereneDirectedEdge symmetry edge) =
        symmetry (continueSourceFace edge))
    (edge : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input)
    (moves : List MolecularFullereneFlagMove) :
    walkMolecularFullereneFlag continueTargetFace
        (mapMolecularFullereneDirectedEdge symmetry edge) moves =
      mapMolecularFullereneDirectedEdge symmetry
        (walkMolecularFullereneFlag continueSourceFace edge moves) := by
  induction moves generalizing edge with
  | nil => rfl
  | cons move moves ih =>
      rw [walkMolecularFullereneFlag, walkMolecularFullereneFlag,
        molecularFullereneFlagStep_equivariant continueSourceFace continueTargetFace symmetry
          continueEquivariant move edge,
        ih]

/-- A finite flag-spanning family rooted at one directed cage edge, plus the one local fact that
admissible symmetries preserve the selected continuation.  The `address` field contains one word
for each carrier atom; no bound on the total lengths of those words is asserted here.  Its
`recovers` proof checks the source face map.

The `admissible` predicate fixes the orientation polarity.  It is instantiated below once for
reversing automorphisms and once for proper rotations. -/
structure MolecularFullereneFlagPropagationCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (admissible : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop) where
  source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input
  sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1
  continueSourceFace :
    (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) →
      MolecularFullereneCarrierAtom input
  continueTargetFace :
    (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) →
      MolecularFullereneCarrierAtom input
  address : MolecularFullereneCarrierAtom input → List MolecularFullereneFlagMove
  recovers : ∀ atom,
    (walkMolecularFullereneFlag continueSourceFace source (address atom)).1 = atom
  continueEquivariant : ∀ symmetry,
    admissible symmetry → ∀ edge,
      continueTargetFace (mapMolecularFullereneDirectedEdge symmetry edge) =
        symmetry (continueSourceFace edge)

/-- The vertex map generated by replaying source addresses from a proposed image edge. -/
def molecularFullereneGeneratedVertexMap
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    {admissible : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop}
    (certificate :
      MolecularFullereneFlagPropagationCertificate molecule input admissible)
    (target : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input)
    (atom : MolecularFullereneCarrierAtom input) :
    MolecularFullereneCarrierAtom input :=
  (walkMolecularFullereneFlag certificate.continueTargetFace target
    (certificate.address atom)).1

/-- At the image of the source flag, replaying addresses gives exactly the original symmetry. -/
theorem molecularFullereneGeneratedVertexMap_imageSource
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    {admissible : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop}
    (certificate :
      MolecularFullereneFlagPropagationCertificate molecule input admissible)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (judged : admissible symmetry) :
    molecularFullereneGeneratedVertexMap certificate
        (mapMolecularFullereneDirectedEdge symmetry certificate.source) =
      symmetry := by
  funext atom
  unfold molecularFullereneGeneratedVertexMap
  rw [walkMolecularFullereneFlag_equivariant certificate.continueSourceFace
    certificate.continueTargetFace symmetry
    (certificate.continueEquivariant symmetry judged)]
  change symmetry
      (walkMolecularFullereneFlag certificate.continueSourceFace certificate.source
        (certificate.address atom)).1 = symmetry atom
  rw [certificate.recovers atom]

/-- Turn one generated vertex map into a permutation when it is bijective.  Nonbijective target
maps produce the identity; every resulting candidate is independently filtered later.  The
selection is noncomputable here, so this definition makes no executable complexity claim. -/
noncomputable def molecularFullereneGeneratedExtension
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    {admissible : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop}
    (certificate :
      MolecularFullereneFlagPropagationCertificate molecule input admissible)
    (target : MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) :
    Equiv.Perm (MolecularFullereneCarrierAtom input) :=
  if bijective : Function.Bijective
      (molecularFullereneGeneratedVertexMap certificate target) then
    Equiv.ofBijective (molecularFullereneGeneratedVertexMap certificate target) bijective
  else
    Equiv.refl _

/-- The generated extension at an admissible image flag is provably the symmetry that
supplied that image. -/
theorem molecularFullereneGeneratedExtension_imageSource
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    {admissible : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop}
    (certificate :
      MolecularFullereneFlagPropagationCertificate molecule input admissible)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (judged : admissible symmetry) :
    molecularFullereneGeneratedExtension certificate
        (mapMolecularFullereneDirectedEdge symmetry certificate.source) = symmetry := by
  have generatedEq :
      molecularFullereneGeneratedVertexMap certificate
          (mapMolecularFullereneDirectedEdge symmetry certificate.source) = symmetry :=
    molecularFullereneGeneratedVertexMap_imageSource certificate symmetry judged
  have bijective : Function.Bijective
      (molecularFullereneGeneratedVertexMap certificate
        (mapMolecularFullereneDirectedEdge symmetry certificate.source)) := by
    rw [generatedEq]
    exact symmetry.bijective
  rw [molecularFullereneGeneratedExtension, dif_pos bijective]
  apply Equiv.ext
  intro atom
  change molecularFullereneGeneratedVertexMap certificate
      (mapMolecularFullereneDirectedEdge symmetry certificate.source) atom = symmetry atom
  exact congrFun generatedEq atom

/-- A source-spanning flag propagation certificate produces the reversing directed-edge
extension certificate consumed by the independent chirality theorem. -/
noncomputable def MolecularFullereneFlagPropagationCertificate.toReversingExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneFlagPropagationCertificate molecule input
      (fun symmetry =>
        MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
          MolecularFullereneFaceOrientationReversing input symmetry)) :
    MolecularFullereneDirectedEdgeExtensionCertificate molecule input where
  source := certificate.source
  sourceBond := certificate.sourceBond
  extend := molecularFullereneGeneratedExtension certificate
  complete := by
    intro symmetry automorphism reversing
    simpa only [mapMolecularFullereneDirectedEdge] using
      molecularFullereneGeneratedExtension_imageSource certificate symmetry
        ⟨automorphism, reversing⟩

/-- The same propagation theorem produces the complete directed-edge-indexed proper-rotation
universe. -/
noncomputable def MolecularFullereneFlagPropagationCertificate.toProperRotationExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneFlagPropagationCertificate molecule input
      (MolecularFullereneProperRotationSymmetryJudgment molecule input)) :
    MolecularFullereneProperRotationDirectedEdgeExtensionCertificate molecule input where
  source := certificate.source
  sourceBond := certificate.sourceBond
  extend := molecularFullereneGeneratedExtension certificate
  complete := by
    intro symmetry judged
    simpa only [mapMolecularFullereneDirectedEdge] using
      molecularFullereneGeneratedExtension_imageSource certificate symmetry judged

/-! ## One concrete source-face certificate supplies both symmetry polarities -/

/-! ### Deduplicating directed-edge BFS -/

theorem walkMolecularFullereneFlag_append
    {input : MolecularFullereneConfigurationInput}
    (continueFace : (MolecularFullereneCarrierAtom input ×
      MolecularFullereneCarrierAtom input) → MolecularFullereneCarrierAtom input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (first second : List MolecularFullereneFlagMove) :
    walkMolecularFullereneFlag continueFace source (first ++ second) =
      walkMolecularFullereneFlag continueFace
        (walkMolecularFullereneFlag continueFace source first) second := by
  induction first generalizing source with
  | nil => rfl
  | cons move moves inductionHypothesis =>
      simp only [List.cons_append, walkMolecularFullereneFlag]
      exact inductionHypothesis _

/-- Positive molecular bonds among all typed directed carrier pairs. -/
def molecularFullereneBondedDirectedEdges
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) :
    Finset (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) :=
  Finset.univ.filter fun edge => decide (0 < molecule.bondOrder edge.1.1 edge.2.1)

/-- One deduplicating BFS layer.  The finite set keys only on directed-edge state, so multiple
words reaching the same state do not multiply the next frontier.  Every newly generated state is
filtered back to the positive-bond dart universe. -/
def molecularFullereneFlagReachableEdges
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) :
    ℕ → Finset (MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
  | 0 => {source}
  | fuel + 1 =>
      let previous := molecularFullereneFlagReachableEdges molecule input source fuel
      previous ∪ (((Finset.univ : Finset MolecularFullereneFlagMove) ×ˢ previous).image
        (fun state => molecularFullereneFlagStep
          (molecularFullereneContinueForwardFace input) state.1 state.2)).filter
            (fun edge => decide (0 < molecule.bondOrder edge.1.1 edge.2.1))

/-- Both flag generators preserve positive molecular cage bonds on an oriented face map. -/
theorem molecularFullereneFlagStep_bond
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (move : MolecularFullereneFlagMove)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (bond : 0 < molecule.bondOrder edge.1.1 edge.2.1) :
    0 < molecule.bondOrder
      (molecularFullereneFlagStep (molecularFullereneContinueForwardFace input) move edge).1.1
      (molecularFullereneFlagStep (molecularFullereneContinueForwardFace input) move edge).2.1 := by
  cases move with
  | reverseEdge => simpa [molecularFullereneFlagStep, molecule.bondOrder_symm] using bond
  | continueLeftFace =>
      rcases molecularFullereneContinueForwardFace_judged molecule input oriented edge bond with
        ⟨face, facePresent, _firstEdge, secondEdge⟩
      simpa only [molecularFullereneFlagStep] using
        bondOrder_pos_of_forwardFaceEdge molecule input oriented.1 face facePresent
          edge.2.1 (molecularFullereneContinueForwardFace input edge).1 secondEdge

/-- Every visited BFS state is a positive molecular dart and carries a sound (logically
reconstructible) flag address from the source.  The executable frontier stores only deduplicated
states; proof erasure removes the address witness at runtime. -/
theorem mem_molecularFullereneFlagReachableEdges_sound
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (fuel : ℕ)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (present : edge ∈ molecularFullereneFlagReachableEdges molecule input source fuel) :
    0 < molecule.bondOrder edge.1.1 edge.2.1 ∧
      ∃ moves,
        walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
          source moves = edge := by
  induction fuel generalizing edge with
  | zero =>
      simp only [molecularFullereneFlagReachableEdges, Finset.mem_singleton] at present
      subst edge
      exact ⟨sourceBond, [], rfl⟩
  | succ fuel inductionHypothesis =>
      simp only [molecularFullereneFlagReachableEdges, Finset.mem_union] at present
      rcases present with previous | generated
      · exact inductionHypothesis edge previous
      · rcases Finset.mem_filter.mp generated with ⟨generated, generatedBond⟩
        rcases Finset.mem_image.mp generated with ⟨state, statePresent, stateEq⟩
        rcases Finset.mem_product.mp statePresent with ⟨_movePresent, previousPresent⟩
        rcases inductionHypothesis state.2 previousPresent with
          ⟨_previousBond, moves, movesEq⟩
        refine ⟨of_decide_eq_true generatedBond, moves ++ [state.1], ?_⟩
        rw [walkMolecularFullereneFlag_append, movesEq]
        exact stateEq

/-- One flag transition from a visited state is present in the next deduplicated BFS layer. -/
theorem molecularFullereneFlagStep_mem_reachableEdges_succ
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (fuel : ℕ)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (present : edge ∈ molecularFullereneFlagReachableEdges molecule input source fuel)
    (move : MolecularFullereneFlagMove) :
    molecularFullereneFlagStep (molecularFullereneContinueForwardFace input) move edge ∈
      molecularFullereneFlagReachableEdges molecule input source (fuel + 1) := by
  have edgeBond := (mem_molecularFullereneFlagReachableEdges_sound molecule input
    source sourceBond fuel edge present).1
  have nextBond := molecularFullereneFlagStep_bond molecule input oriented move edge edgeBond
  apply Finset.mem_union.mpr
  apply Or.inr
  apply Finset.mem_filter.mpr
  refine ⟨?_, by simpa only [decide_eq_true_eq] using nextBond⟩
  apply Finset.mem_image.mpr
  refine ⟨(move, edge), Finset.mem_product.mpr ⟨Finset.mem_univ _, present⟩, rfl⟩

/-- Replaying from any visited state stays in BFS with fuel increased by word length. -/
theorem walkMolecularFullereneFlag_mem_reachableEdges_of_mem
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (fuel : ℕ)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (present : edge ∈ molecularFullereneFlagReachableEdges molecule input source fuel)
    (moves : List MolecularFullereneFlagMove) :
    walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input) edge moves ∈
      molecularFullereneFlagReachableEdges molecule input source (fuel + moves.length) := by
  induction moves generalizing fuel edge with
  | nil => simpa only [walkMolecularFullereneFlag, List.length_nil, Nat.add_zero] using present
  | cons move moves inductionHypothesis =>
      let next := molecularFullereneFlagStep
        (molecularFullereneContinueForwardFace input) move edge
      have nextPresent : next ∈ molecularFullereneFlagReachableEdges molecule input source
          (fuel + 1) :=
        molecularFullereneFlagStep_mem_reachableEdges_succ molecule input oriented source
          sourceBond fuel edge present move
      have tailPresent := inductionHypothesis (fuel + 1) next nextPresent
      change walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input) next moves ∈ _
      simpa only [Nat.add_assoc, Nat.add_comm 1 moves.length] using tailPresent

/-- Replaying any flag word of length `n` lands in the deduplicated BFS set after `n` rounds. -/
theorem walkMolecularFullereneFlag_mem_reachableEdges
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (moves : List MolecularFullereneFlagMove) :
    walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input) source moves ∈
      molecularFullereneFlagReachableEdges molecule input source moves.length := by
  have sourcePresent : source ∈ molecularFullereneFlagReachableEdges molecule input source 0 := by
    simp [molecularFullereneFlagReachableEdges]
  simpa using walkMolecularFullereneFlag_mem_reachableEdges_of_mem molecule input oriented
    source sourceBond 0 source sourcePresent moves

/-- Exact positive-bond directed-state count used as BFS fuel.  It is at most `|V|²` and on a
validated cubic fullerene is the much smaller dart count. -/
def molecularFullereneFlagStateBound
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) : ℕ :=
  (molecularFullereneBondedDirectedEdges molecule input).card

theorem molecularFullereneFlagStateBound_le_square
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) :
    molecularFullereneFlagStateBound molecule input ≤
      input.carrier.card * input.carrier.card := by
  calc
    molecularFullereneFlagStateBound molecule input ≤
        (Finset.univ : Finset (MolecularFullereneCarrierAtom input ×
          MolecularFullereneCarrierAtom input)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = input.carrier.card * input.carrier.card := by simp

/-- Concrete deduplicated-BFS spanning check at the full directed-pair state bound. -/
def MolecularFullereneDeduplicatedFlagSpanningJudgment
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) : Prop :=
  ∀ atom : MolecularFullereneCarrierAtom input,
    ∃ edge ∈ molecularFullereneFlagReachableEdges molecule input source
      (molecularFullereneFlagStateBound molecule input),
      edge.1 = atom

instance molecularFullereneDeduplicatedFlagSpanningJudgmentDecidable
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) :
    Decidable (MolecularFullereneDeduplicatedFlagSpanningJudgment molecule input source) := by
  unfold MolecularFullereneDeduplicatedFlagSpanningJudgment
  infer_instance

/-- Concrete safe-search certificate.  Its only coverage proof is the deduplicated bonded-dart
BFS judgment (bounded above by `|V|²` rounds); it contains no word universe and no address family. -/
structure MolecularFullereneDeduplicatedFlagSpanningCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) where
  oriented : OrientedMolecularFullereneFaceMapJudgment molecule input
  source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input
  sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1
  spanning : MolecularFullereneDeduplicatedFlagSpanningJudgment molecule input source

/-- Construct the safe-search certificate from the result of the finite BFS decision. -/
def MolecularFullereneDeduplicatedFlagSpanningCertificate.ofChecked
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (accepted : decide
      (MolecularFullereneDeduplicatedFlagSpanningJudgment molecule input source) = true) :
    MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input where
  oriented := oriented
  source := source
  sourceBond := sourceBond
  spanning := of_decide_eq_true accepted

/-- One reached directed edge whose first atom is the requested atom. -/
noncomputable def molecularFullereneDeduplicatedReachedEdge
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (atom : MolecularFullereneCarrierAtom input) :
    MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input :=
  Classical.choose (certificate.spanning atom)

theorem molecularFullereneDeduplicatedReachedEdge_spec
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (atom : MolecularFullereneCarrierAtom input) :
    molecularFullereneDeduplicatedReachedEdge molecule input certificate atom ∈
        molecularFullereneFlagReachableEdges molecule input certificate.source
          (molecularFullereneFlagStateBound molecule input) ∧
      (molecularFullereneDeduplicatedReachedEdge molecule input certificate atom).1 = atom :=
  Classical.choose_spec (certificate.spanning atom)

/-- Recover one sound address from the BFS invariant for the selected reached edge.  This choice is
proof-facing; the concrete coverage check itself evaluated only deduplicated edge states. -/
noncomputable def molecularFullereneDeduplicatedFlagAddress
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (atom : MolecularFullereneCarrierAtom input) : List MolecularFullereneFlagMove :=
  Classical.choose ((mem_molecularFullereneFlagReachableEdges_sound molecule input
    certificate.source certificate.sourceBond
      (molecularFullereneFlagStateBound molecule input)
      (molecularFullereneDeduplicatedReachedEdge molecule input certificate atom)
      (molecularFullereneDeduplicatedReachedEdge_spec molecule input certificate atom).1).2)

theorem molecularFullereneDeduplicatedFlagAddress_recovers
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (atom : MolecularFullereneCarrierAtom input) :
    (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
      certificate.source
      (molecularFullereneDeduplicatedFlagAddress molecule input certificate atom)).1 = atom := by
  have walkEq := Classical.choose_spec ((mem_molecularFullereneFlagReachableEdges_sound
    molecule input certificate.source certificate.sourceBond
      (molecularFullereneFlagStateBound molecule input)
      (molecularFullereneDeduplicatedReachedEdge molecule input certificate atom)
      (molecularFullereneDeduplicatedReachedEdge_spec molecule input certificate atom).1).2)
  unfold molecularFullereneDeduplicatedFlagAddress
  rw [walkEq]
  exact (molecularFullereneDeduplicatedReachedEdge_spec molecule input certificate atom).2

/-- Abstract finite word universe used only for existence transport below.  It is exponential in
`fuel` and is deliberately not used by the concrete fullerene checker, which uses deduplicated
directed-edge BFS above. -/
def molecularFullereneFlagWordsUpTo : ℕ → Finset (List MolecularFullereneFlagMove)
  | 0 => {[]}
  | fuel + 1 =>
      molecularFullereneFlagWordsUpTo fuel ∪
        Finset.univ.biUnion fun move =>
          (molecularFullereneFlagWordsUpTo fuel).image fun moves => move :: moves

@[simp] theorem mem_molecularFullereneFlagWordsUpTo_iff
    (moves : List MolecularFullereneFlagMove) (fuel : ℕ) :
    moves ∈ molecularFullereneFlagWordsUpTo fuel ↔ moves.length ≤ fuel := by
  induction fuel generalizing moves with
  | zero => simp [molecularFullereneFlagWordsUpTo]
  | succ fuel inductionHypothesis =>
      constructor
      · intro present
        simp only [molecularFullereneFlagWordsUpTo, Finset.mem_union,
          Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at present
        rcases present with old | ⟨move, tail, tailPresent, movesEq⟩
        · exact (inductionHypothesis moves).mp old |>.trans (Nat.le_succ _)
        · subst moves
          simp only [List.length_cons]
          exact Nat.succ_le_succ ((inductionHypothesis tail).mp tailPresent)
      · intro lengthLe
        cases moves with
        | nil =>
            apply Finset.mem_union.mpr
            exact Or.inl ((inductionHypothesis []).mpr (Nat.zero_le _))
        | cons move tail =>
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_biUnion.mpr
            refine ⟨move, Finset.mem_univ _, ?_⟩
            apply Finset.mem_image.mpr
            refine ⟨tail, (inductionHypothesis tail).mpr ?_, rfl⟩
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using lengthLe

/-- Finite, directly checkable statement that bounded flag expansion from `source` reaches the
first endpoint of every carrier atom. -/
def MolecularFullereneFiniteFlagSpanningJudgment
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (fuel : ℕ) : Prop :=
  ∀ atom : MolecularFullereneCarrierAtom input,
    ∃ moves ∈ molecularFullereneFlagWordsUpTo fuel,
      (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        source moves).1 = atom

/-- The exact remaining topological statement: the two flag generators act transitively enough
from one directed cage bond to reach every carrier atom.  This proposition contains no bound and
no address data. -/
def MolecularFullereneFlagOrbitCoversCarrier
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input) : Prop :=
  ∀ atom : MolecularFullereneCarrierAtom input,
    ∃ moves,
      (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        source moves).1 = atom

noncomputable def molecularFullereneOrbitAddress
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (covers : MolecularFullereneFlagOrbitCoversCarrier input source)
    (atom : MolecularFullereneCarrierAtom input) : List MolecularFullereneFlagMove :=
  Classical.choose (covers atom)

theorem molecularFullereneOrbitAddress_recovers
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (covers : MolecularFullereneFlagOrbitCoversCarrier input source)
    (atom : MolecularFullereneCarrierAtom input) :
    (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input) source
      (molecularFullereneOrbitAddress input source covers atom)).1 = atom :=
  Classical.choose_spec (covers atom)

/-- Maximum chosen orbit-address length.  Finiteness of the carrier makes one common fuel bound
available without storing a separate length for every atom. -/
noncomputable def molecularFullereneOrbitFuel
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (covers : MolecularFullereneFlagOrbitCoversCarrier input source) : ℕ :=
  Finset.univ.sup fun atom : MolecularFullereneCarrierAtom input =>
    (molecularFullereneOrbitAddress input source covers atom).length

/-- Unbounded flag-orbit coverage automatically has one finite common breadth bound. -/
theorem molecularFullereneFlagOrbitCoversCarrier_to_finiteSpanning
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (covers : MolecularFullereneFlagOrbitCoversCarrier input source) :
    MolecularFullereneFiniteFlagSpanningJudgment input source
      (molecularFullereneOrbitFuel input source covers) := by
  intro atom
  refine ⟨molecularFullereneOrbitAddress input source covers atom, ?_,
    molecularFullereneOrbitAddress_recovers input source covers atom⟩
  apply (mem_molecularFullereneFlagWordsUpTo_iff _ _).mpr
  exact Finset.le_sup (f := fun candidate : MolecularFullereneCarrierAtom input =>
    (molecularFullereneOrbitAddress input source covers candidate).length) (Finset.mem_univ atom)

noncomputable instance molecularFullereneFiniteFlagSpanningJudgmentDecidable
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (fuel : ℕ) :
    Decidable (MolecularFullereneFiniteFlagSpanningJudgment input source fuel) :=
  Classical.propDecidable _

/-- Deterministically select the first bounded flag word reaching `atom`.  The empty fallback is
unreachable under the finite spanning judgment proved below. -/
def molecularFullereneFiniteFlagAddress
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (fuel : ℕ) (atom : MolecularFullereneCarrierAtom input) :
    List MolecularFullereneFlagMove :=
  ((molecularFullereneFlagWordsUpTo fuel).toList.find? fun moves => decide
    ((walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
      source moves).1 = atom)).getD []

/-- The finite search address recovers its requested atom whenever bounded expansion spans. -/
theorem molecularFullereneFiniteFlagAddress_recovers
    (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (fuel : ℕ)
    (spanning : MolecularFullereneFiniteFlagSpanningJudgment input source fuel)
    (atom : MolecularFullereneCarrierAtom input) :
    (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
      source (molecularFullereneFiniteFlagAddress input source fuel atom)).1 = atom := by
  rcases spanning atom with ⟨moves, movesPresent, recovers⟩
  have searchSome :
      (((molecularFullereneFlagWordsUpTo fuel).toList.find? fun candidate => decide
        ((walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
          source candidate).1 = atom))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨moves, by simpa using movesPresent, by simpa using recovers⟩
  cases found : (molecularFullereneFlagWordsUpTo fuel).toList.find? (fun candidate => decide
      ((walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        source candidate).1 = atom)) with
  | none => simp [found] at searchSome
  | some selected =>
      have selectedRecovers :
          (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
            source selected).1 = atom := by
        exact of_decide_eq_true (List.find?_some (p := fun candidate => decide
          ((walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
            source candidate).1 = atom)) (a := selected) found)
      simpa [molecularFullereneFiniteFlagAddress, found] using selectedRecovers

/-- Proof-carrying input to finite flag search.  Unlike the concrete extension certificate below,
it contains no address function and no per-atom recovery proofs: those are generated by the
bounded search theorem. -/
structure MolecularFullereneFiniteFlagSpanningCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) where
  oriented : OrientedMolecularFullereneFaceMapJudgment molecule input
  source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input
  sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1
  fuel : ℕ
  spanning : MolecularFullereneFiniteFlagSpanningJudgment input source fuel

/-- The source-specific certificate required for a checked fullerene cage.  Its data is the
checked oriented molecular face map, one directed cage edge, and one word in two flag moves per
atom.  Continuation equivariance is now a theorem above, not a caller field.  In particular, there
is no global automorphism-completeness field and no list of permutations.

The same finite spanning tree generates both polarity classes: forward-to-reverse continuation
for reversing automorphisms and forward-to-forward continuation for proper rotations. -/
structure MolecularFullereneConcreteFlagExtensionCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) where
  oriented : OrientedMolecularFullereneFaceMapJudgment molecule input
  source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input
  sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1
  address : MolecularFullereneCarrierAtom input → List MolecularFullereneFlagMove
  recovers : ∀ atom,
    (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
      source (address atom)).1 = atom

/-- Finite bounded flag search constructs the concrete extension certificate; continuation
equivariance and per-atom addresses are both derived rather than supplied. -/
def MolecularFullereneFiniteFlagSpanningCertificate.toConcreteFlagExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneFiniteFlagSpanningCertificate molecule input) :
    MolecularFullereneConcreteFlagExtensionCertificate molecule input where
  oriented := certificate.oriented
  source := certificate.source
  sourceBond := certificate.sourceBond
  address := molecularFullereneFiniteFlagAddress input certificate.source certificate.fuel
  recovers := molecularFullereneFiniteFlagAddress_recovers input certificate.source
    certificate.fuel certificate.spanning

/-- The safe deduplicated-BFS certificate constructs the same concrete extension boundary without
enumerating flag words. -/
noncomputable def
    MolecularFullereneDeduplicatedFlagSpanningCertificate.toConcreteFlagExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    MolecularFullereneConcreteFlagExtensionCertificate molecule input where
  oriented := certificate.oriented
  source := certificate.source
  sourceBond := certificate.sourceBond
  address := molecularFullereneDeduplicatedFlagAddress molecule input certificate
  recovers := molecularFullereneDeduplicatedFlagAddress_recovers molecule input certificate

/-- Interpret the concrete face-list spanning tree at reversing polarity. -/
def MolecularFullereneConcreteFlagExtensionCertificate.toReversingPropagation
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneConcreteFlagExtensionCertificate molecule input) :
    MolecularFullereneFlagPropagationCertificate molecule input
      (fun symmetry =>
        MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
          MolecularFullereneFaceOrientationReversing input symmetry) where
  source := certificate.source
  sourceBond := certificate.sourceBond
  continueSourceFace := molecularFullereneContinueForwardFace input
  continueTargetFace := molecularFullereneContinueReverseFace input
  address := certificate.address
  recovers := certificate.recovers
  continueEquivariant := by
    intro symmetry judged edge
    exact molecularFullereneContinueReverseFace_equivariant molecule input
      certificate.oriented symmetry judged.1 judged.2 edge

/-- Interpret the same concrete face-list spanning tree at preserving polarity. -/
def MolecularFullereneConcreteFlagExtensionCertificate.toProperRotationPropagation
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneConcreteFlagExtensionCertificate molecule input) :
    MolecularFullereneFlagPropagationCertificate molecule input
      (MolecularFullereneProperRotationSymmetryJudgment molecule input) where
  source := certificate.source
  sourceBond := certificate.sourceBond
  continueSourceFace := molecularFullereneContinueForwardFace input
  continueTargetFace := molecularFullereneContinueForwardFace input
  address := certificate.address
  recovers := certificate.recovers
  continueEquivariant := by
    intro symmetry judged edge
    exact molecularFullereneContinueForwardFace_equivariant molecule input
      certificate.oriented symmetry judged.2.1 judged.2.2.1 edge

/-- Flag-generated reversing extension from the checked face lists and supplied spanning data. -/
noncomputable def
    MolecularFullereneConcreteFlagExtensionCertificate.toReversingDirectedEdgeExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneConcreteFlagExtensionCertificate molecule input) :
    MolecularFullereneDirectedEdgeExtensionCertificate molecule input :=
  (certificate.toReversingPropagation molecule input).toReversingExtension molecule input

/-- Flag-generated proper-rotation extension from the same spanning data. -/
noncomputable def
    MolecularFullereneConcreteFlagExtensionCertificate.toProperRotationDirectedEdgeExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneConcreteFlagExtensionCertificate molecule input) :
    MolecularFullereneProperRotationDirectedEdgeExtensionCertificate molecule input :=
  (certificate.toProperRotationPropagation molecule input).toProperRotationExtension molecule input

/-- End-to-end chirality transport using only the concrete source-face spanning certificate. -/
theorem molecularFullereneColoringChiral_iff_concreteFlagExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : ℕ → ℕ)
    (certificate : MolecularFullereneConcreteFlagExtensionCertificate molecule input) :
    MolecularFullereneColoringChiral molecule input color ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneDirectedEdgeReversingAutomorphisms molecule input
            (certificate.toReversingDirectedEdgeExtension molecule input),
          ¬MolecularFullereneColoringPreserved input color symmetry :=
  molecularFullereneColoringChiral_iff_directedEdgeExtension molecule input color
    (certificate.toReversingDirectedEdgeExtension molecule input)

/-- End-to-end chirality transport from finite bounded flag expansion.  No address function,
recovery family, or continuation-equivariance theorem is supplied at this boundary. -/
theorem molecularFullereneColoringChiral_iff_finiteFlagSpanning
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : ℕ → ℕ)
    (certificate : MolecularFullereneFiniteFlagSpanningCertificate molecule input) :
    MolecularFullereneColoringChiral molecule input color ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneDirectedEdgeReversingAutomorphisms molecule input
            (MolecularFullereneConcreteFlagExtensionCertificate.toReversingDirectedEdgeExtension
              molecule input
                (certificate.toConcreteFlagExtension molecule input)),
          ¬MolecularFullereneColoringPreserved input color symmetry :=
  molecularFullereneColoringChiral_iff_concreteFlagExtension molecule input color
    (certificate.toConcreteFlagExtension molecule input)

/-- End-to-end independent chirality transport from the quadratic-state deduplicated BFS checker.
No exponential flag-word universe occurs in this theorem or certificate. -/
theorem molecularFullereneColoringChiral_iff_deduplicatedFlagSpanning
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : ℕ → ℕ)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    MolecularFullereneColoringChiral molecule input color ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneDirectedEdgeReversingAutomorphisms molecule input
            (MolecularFullereneConcreteFlagExtensionCertificate.toReversingDirectedEdgeExtension
              molecule input (certificate.toConcreteFlagExtension molecule input)),
          ¬MolecularFullereneColoringPreserved input color symmetry :=
  molecularFullereneColoringChiral_iff_concreteFlagExtension molecule input color
    (certificate.toConcreteFlagExtension molecule input)

/-- End-to-end chirality transport from the finite flag-spanning tree. -/
theorem molecularFullereneColoringChiral_iff_flagPropagation
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : ℕ → ℕ)
    (certificate : MolecularFullereneFlagPropagationCertificate molecule input
      (fun symmetry =>
        MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
          MolecularFullereneFaceOrientationReversing input symmetry)) :
    MolecularFullereneColoringChiral molecule input color ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneDirectedEdgeReversingAutomorphisms molecule input
            (certificate.toReversingExtension molecule input),
          ¬MolecularFullereneColoringPreserved input color symmetry :=
  molecularFullereneColoringChiral_iff_directedEdgeExtension molecule input color
    (certificate.toReversingExtension molecule input)

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.walkMolecularFullereneFlag_equivariant
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneGeneratedVertexMap_imageSource
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneGeneratedExtension_imageSource
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneColoringChiral_iff_flagPropagation
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneColoringChiral_iff_concreteFlagExtension
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneContinueForwardFace_equivariant
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneContinueReverseFace_equivariant
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneFiniteFlagAddress_recovers
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneColoringChiral_iff_finiteFlagSpanning
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_molecularFullereneFlagReachableEdges_sound
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneDeduplicatedFlagAddress_recovers
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneColoringChiral_iff_deduplicatedFlagSpanning
