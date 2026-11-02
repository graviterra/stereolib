import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC60TableBridge
import TetraStereo.OneCenter.P93MolecularFullereneFiniteFaceCertificate

set_option autoImplicit false

/-!
# Audited P-93 C60 numbered-cage package

This module is the source-only boundary between the frozen, independently reviewed
`(C60-Ih)[5,6]` face transcription and the generic P-93.5.6 fullerene compiler.  The one
numbered cage is shared by the constitutionally distinct Type-2 and Type-3 printed derivatives.
No derivative overlay or row-closure claim is made here.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

set_option maxRecDepth 10000 in
/-- The systematic locant order is a Hamiltonian spine in the reviewed face graph. -/
theorem iupacP93CanonicalFullereneC60_consecutiveFaceEdges :
    (List.range 59).all (fun atom =>
      iupacP93CanonicalFullereneC60Transcription.hasFaceEdge atom (atom + 1)) = true := by
  decide

theorem iupacP93CanonicalFullereneC60_consecutiveLocantsBonded :
    ∀ atom, atom + 1 < 60 →
      P94ConformationUnit.Bonded
        iupacP93CanonicalFullereneC60Transcription.cageMolecule atom (atom + 1) := by
  intro atom successorBound
  have atomBound : atom < 60 := by omega
  have atomPresent : atom ∈ List.range 59 := by simp; omega
  have faceEdge := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC60_consecutiveFaceEdges) atom atomPresent
  exact (numberedFaceTranscription_bonded_iff_hasFaceEdge
    iupacP93CanonicalFullereneC60Transcription atom (atom + 1)
      atomBound successorBound (by omega)).mpr faceEdge

/-- O(V) Hamiltonian-path admission of quantified cage connectedness. -/
theorem iupacP93CanonicalFullereneC60_connectedJudgment :
    MolecularFullereneCageConnected
      iupacP93CanonicalFullereneC60Transcription.cageMolecule
      iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier := by
  apply molecularFullereneCageConnected_of_range_hamiltonian
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60Transcription.numberedPackage 60
  · rfl
  · exact iupacP93CanonicalFullereneC60_consecutiveLocantsBonded
  · decide

/-! ## Symbolic source-to-package transport -/

/-- On bounded distinct atoms, generated face incidence and the independently extracted source
edge list denote the same edge. -/
theorem iupacP93CanonicalFullereneC60_hasFaceEdge_iff_hasSourceEdge
    (left right : Nat) (leftBound : left < 60) (rightBound : right < 60)
    (distinct : left ≠ right) :
    iupacP93CanonicalFullereneC60Transcription.hasFaceEdge left right = true ↔
      iupacP93CanonicalFullereneC60HasSourceEdge left right = true := by
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · have canonical : iupacP93C60CanonicalEdge (left, right) = (left, right) := by
      simp [iupacP93C60CanonicalEdge, ordered]
    constructor
    · intro faceEdge
      have tablePresent : (left, right) ∈
          iupacP93CanonicalFullereneC60Transcription.edgeTable :=
        (numberedFaceTranscription_mem_edgeTable_iff
          iupacP93CanonicalFullereneC60Transcription left right).mpr
            ⟨leftBound, rightBound, ordered, faceEdge⟩
      have sourcePresent : (left, right) ∈ iupacP93CanonicalFullereneC60Edges.toFinset := by
        rw [← iupacP93CanonicalFullereneC60_edgeTable_toFinset]
        simpa using tablePresent
      simpa [iupacP93CanonicalFullereneC60HasSourceEdge, canonical] using sourcePresent
    · intro sourceEdge
      have sourcePresent : (left, right) ∈ iupacP93CanonicalFullereneC60Edges.toFinset := by
        simpa [iupacP93CanonicalFullereneC60HasSourceEdge, canonical] using sourceEdge
      have tablePresent : (left, right) ∈
          iupacP93CanonicalFullereneC60Transcription.edgeTable := by
        have : (left, right) ∈
            iupacP93CanonicalFullereneC60Transcription.edgeTable.toFinset := by
          rw [iupacP93CanonicalFullereneC60_edgeTable_toFinset]
          exact sourcePresent
        simpa using this
      exact ((numberedFaceTranscription_mem_edgeTable_iff
        iupacP93CanonicalFullereneC60Transcription left right).mp tablePresent).2.2.2
  · have canonical : iupacP93C60CanonicalEdge (left, right) = (right, left) := by
      simp [iupacP93C60CanonicalEdge, Nat.not_lt.mpr (Nat.le_of_lt ordered)]
    rw [numberedFaceTranscription_hasFaceEdge_symm]
    constructor
    · intro faceEdge
      have tablePresent : (right, left) ∈
          iupacP93CanonicalFullereneC60Transcription.edgeTable :=
        (numberedFaceTranscription_mem_edgeTable_iff
          iupacP93CanonicalFullereneC60Transcription right left).mpr
            ⟨rightBound, leftBound, ordered, faceEdge⟩
      have sourcePresent : (right, left) ∈ iupacP93CanonicalFullereneC60Edges.toFinset := by
        rw [← iupacP93CanonicalFullereneC60_edgeTable_toFinset]
        simpa using tablePresent
      simpa [iupacP93CanonicalFullereneC60HasSourceEdge, canonical] using sourcePresent
    · intro sourceEdge
      have sourcePresent : (right, left) ∈ iupacP93CanonicalFullereneC60Edges.toFinset := by
        simpa [iupacP93CanonicalFullereneC60HasSourceEdge, canonical] using sourceEdge
      have tablePresent : (right, left) ∈
          iupacP93CanonicalFullereneC60Transcription.edgeTable := by
        have : (right, left) ∈
            iupacP93CanonicalFullereneC60Transcription.edgeTable.toFinset := by
          rw [iupacP93CanonicalFullereneC60_edgeTable_toFinset]
          exact sourcePresent
        simpa using this
      exact ((numberedFaceTranscription_mem_edgeTable_iff
        iupacP93CanonicalFullereneC60Transcription right left).mp tablePresent).2.2.2

/-- Cubicity is transported from the cached pure face-adjacency degree, not recomputed from the
generated molecular bond table. -/
theorem iupacP93CanonicalFullereneC60_cubicJudgment :
    ∀ atom ∈ iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier,
      (molecularFullereneCageNeighbors
        iupacP93CanonicalFullereneC60Transcription.cageMolecule
        iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier atom).card = 3 := by
  intro atom atomPresent
  have atomBound : atom < 60 := by
    simpa [MolecularFullereneNumberedCagePackage.carrier,
      NumberedFaceTranscription.numberedPackage,
      NumberedFaceTranscription.atomsByLocant] using atomPresent
  rw [numberedFaceTranscription_cageNeighbors_eq_faceNeighbors
    iupacP93CanonicalFullereneC60Transcription atom atomBound]
  simpa [numberedFaceTranscriptionFaceNeighbors,
    iupacP93CanonicalFullereneC60FaceAdjacencyNeighbors,
    iupacP93CanonicalFullereneC60HasFaceEdge,
    iupacP93CanonicalFullereneC60Transcription,
    NumberedFaceTranscription.hasFaceEdge,
    iupacP93CanonicalFullereneC60HasNamedFaceEdge,
    iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge,
    isForwardMolecularFullereneFaceEdge] using
      iupacP93CanonicalFullereneC60_faceAdjacencyDegree atom atomBound



theorem iupacP93CanonicalFullereneC60_facesAccepted :
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.faces.all
      (independentP94RingTraversalAccepted
        iupacP93CanonicalFullereneC60Transcription.cageMolecule) = true := by
  apply List.all_eq_true.mpr
  intro face facePresent
  have nodup : face.Nodup := of_decide_eq_true
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC60_eachFaceNodup) face facePresent)
  have size : face.length = 5 ∨ face.length = 6 := of_decide_eq_true
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC60_faceSizes) face facePresent)
  have minimum : 3 ≤ face.length := by rcases size with h | h <;> omega
  have bounded : ∀ atom ∈ face, atom < 60 := by
    intro atom atomPresent
    exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp
      iupacP93CanonicalFullereneC60_vertex_bounds) face facePresent)) atom atomPresent)
  have sourceCycleEdges :
      ∀ edge ∈ (molecularFullereneTraversalUnit face).cycleEdges,
        iupacP93CanonicalFullereneC60Transcription.hasFaceEdge edge.1 edge.2 = true := by
    intro edge edgePresent
    have listed : edge ∈ iupacP93C60DirectedFaceEdges face := by
      simpa [iupacP93C60DirectedFaceEdges, molecularFullereneTraversalUnit,
        P94ConformationUnit.cycleEdges, P94ConformationUnit.cyclicAdjacentPairs,
        P94ConformationUnit.cyclicSuccessors] using edgePresent
    have sourceEdge := (List.all_eq_true.mp ((List.all_eq_true.mp
      iupacP93CanonicalFullereneC60_facesCyclicEdges) face facePresent)) edge listed
    have leftPresent : edge.1 ∈ face := (List.of_mem_zip listed).1
    have rightSuccessor : edge.2 ∈ face.tail ++ face.take 1 := (List.of_mem_zip listed).2
    have rightPresent : edge.2 ∈ face := by
      rcases List.mem_append.mp rightSuccessor with tailPresent | headPresent
      · exact List.mem_of_mem_tail tailPresent
      · exact List.mem_of_mem_take headPresent
    have distinct := cycleEdges_distinct_of_minimum_nodup face minimum nodup edge edgePresent
    exact (iupacP93CanonicalFullereneC60_hasFaceEdge_iff_hasSourceEdge
      edge.1 edge.2 (bounded edge.1 leftPresent) (bounded edge.2 rightPresent) distinct).mpr
        sourceEdge
  apply independentP94RingTraversalAccepted_of_sourceFaceEdges
    iupacP93CanonicalFullereneC60Transcription face minimum nodup bounded sourceCycleEdges
  intro left leftPresent right rightPresent distinct
  have checkedLeft := (List.all_eq_true.mp
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC60_facesInduced) face facePresent))
      left leftPresent
  have checked := (List.all_eq_true.mp checkedLeft) right rightPresent
  have faceNamedEq : iupacP93CanonicalFullereneC60HasFaceEdge left right =
      iupacP93CanonicalFullereneC60HasNamedFaceEdge face left right := by
    simpa only [if_neg distinct, beq_iff_eq] using checked
  constructor
  · intro faceEdge
    apply (molecularFullereneNamedFaceEdge?_eq_true_iff face nodup left right).mp
    have localFace : iupacP93CanonicalFullereneC60HasFaceEdge left right = true := by
      simpa [iupacP93CanonicalFullereneC60Transcription,
        NumberedFaceTranscription.hasFaceEdge,
        iupacP93CanonicalFullereneC60HasFaceEdge,
        iupacP93CanonicalFullereneC60HasNamedFaceEdge,
        iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge,
        isForwardMolecularFullereneFaceEdge] using faceEdge
    have localNamed :
        iupacP93CanonicalFullereneC60HasNamedFaceEdge face left right = true :=
      faceNamedEq.symm.trans localFace
    simpa [molecularFullereneNamedFaceEdge?,
      iupacP93CanonicalFullereneC60HasNamedFaceEdge,
      iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge,
      isForwardMolecularFullereneFaceEdge] using localNamed
  · intro named
    have genericNamed := (molecularFullereneNamedFaceEdge?_eq_true_iff
      face nodup left right).mpr named
    have localNamed :
        iupacP93CanonicalFullereneC60HasNamedFaceEdge face left right = true := by
      simpa [molecularFullereneNamedFaceEdge?,
        iupacP93CanonicalFullereneC60HasNamedFaceEdge,
        iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge,
        isForwardMolecularFullereneFaceEdge] using genericNamed
    have localFace : iupacP93CanonicalFullereneC60HasFaceEdge left right = true :=
      faceNamedEq.trans localNamed
    simpa [iupacP93CanonicalFullereneC60Transcription,
      NumberedFaceTranscription.hasFaceEdge,
      iupacP93CanonicalFullereneC60HasFaceEdge,
      iupacP93CanonicalFullereneC60HasNamedFaceEdge,
      iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge,
      isForwardMolecularFullereneFaceEdge] using localFace

/-- Source two-face incidence transported across the cached source/generated edge equality. -/
theorem iupacP93CanonicalFullereneC60_twoFacesForListedEdges :
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.edgeTable.all (fun edge =>
      decide (iupacP93CanonicalFullereneC60Transcription.numberedPackage.faces.countP
        (fun face => molecularFullereneNamedFaceEdge? face edge.1 edge.2) = 2)) = true := by
  apply List.all_eq_true.mpr
  intro edge edgePresent
  have sourcePresent : edge ∈ iupacP93CanonicalFullereneC60Edges := by
    have tableFinset : edge ∈
        iupacP93CanonicalFullereneC60Transcription.edgeTable.toFinset := by
      simpa using edgePresent
    rw [iupacP93CanonicalFullereneC60_edgeTable_toFinset] at tableFinset
    simpa using tableFinset
  have sourceCount := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC60_twoNamedFacesPerEdge) edge sourcePresent
  simpa [iupacP93CanonicalFullereneC60Transcription,
    NumberedFaceTranscription.numberedPackage,
    molecularFullereneNamedFaceEdge?,
    iupacP93CanonicalFullereneC60HasNamedFaceEdge,
    iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge,
    isForwardMolecularFullereneFaceEdge] using sourceCount

/-- Source orientation incidence transported across the same cached edge equality. -/
theorem iupacP93CanonicalFullereneC60_oppositeOrientationsForListedEdges :
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.edgeTable.all (fun edge =>
      decide (iupacP93CanonicalFullereneC60Transcription.numberedPackage.faces.countP
            (fun face => isForwardMolecularFullereneFaceEdge face edge.1 edge.2) = 1 ∧
        iupacP93CanonicalFullereneC60Transcription.numberedPackage.faces.countP
            (fun face => isForwardMolecularFullereneFaceEdge face edge.2 edge.1) = 1)) = true := by
  apply List.all_eq_true.mpr
  intro edge edgePresent
  have sourcePresent : edge ∈ iupacP93CanonicalFullereneC60Edges := by
    have tableFinset : edge ∈
        iupacP93CanonicalFullereneC60Transcription.edgeTable.toFinset := by
      simpa using edgePresent
    rw [iupacP93CanonicalFullereneC60_edgeTable_toFinset] at tableFinset
    simpa using tableFinset
  have sourceCount := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC60_oppositeNamedFaceOrientations) edge sourcePresent
  simpa [iupacP93CanonicalFullereneC60Transcription,
    NumberedFaceTranscription.numberedPackage,
    iupacP93CanonicalFullereneC60HasForwardNamedFaceEdge,
    isForwardMolecularFullereneFaceEdge] using sourceCount

private theorem listGet?_replicate_of_lt {Alpha : Type*}
    (value : Alpha) (count index : Nat) (bound : index < count) :
    listGet? (List.replicate count value) index = some value := by
  induction count generalizing index with
  | zero => omega
  | succ count inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          simpa [listGet?] using inductionHypothesis index (by omega)


def iupacP93CanonicalFullereneC60FiniteOrientedAudit :
    FiniteOrientedFaceMapAudit iupacP93CanonicalFullereneC60Transcription where
  table := iupacP93CanonicalFullereneC60TableAudit
  connected := iupacP93CanonicalFullereneC60_connectedJudgment
  minimumSize := by
    change 20 ≤ (Finset.range 60).card
    simp
  carbonAtoms := by
    intro atom atomPresent
    have atomBound : atom < 60 := by
      simpa [MolecularFullereneNumberedCagePackage.carrier,
        NumberedFaceTranscription.numberedPackage,
        NumberedFaceTranscription.atomsByLocant] using atomPresent
    refine ⟨NumberedFaceTranscription.carbonAtom, ?_, rfl⟩
    exact listGet?_replicate_of_lt NumberedFaceTranscription.carbonAtom 60 atom atomBound
  cubic := iupacP93CanonicalFullereneC60_cubicJudgment
  facesNodup := iupacP93CanonicalFullereneC60_facesNodup
  facesAccepted := iupacP93CanonicalFullereneC60_facesAccepted
  faceSizes := by
    intro face facePresent
    exact of_decide_eq_true ((List.all_eq_true.mp
      iupacP93CanonicalFullereneC60_faceSizes) face facePresent)
  facesCover := by
    intro atom
    change atom ∈ Finset.range 60 ↔
      ∃ face ∈ iupacP93CanonicalFullereneC60Faces, atom ∈ face
    rw [← iupacP93CanonicalFullereneC60_vertexFinset]
    simp
  twelvePentagons := iupacP93CanonicalFullereneC60_pentagon_count
  hexagonCount := by
    change iupacP93CanonicalFullereneC60Faces.countP
      (fun face => decide (face.length = 6)) = 60 / 2 - 10
    simpa using iupacP93CanonicalFullereneC60_hexagon_count
  twoFacesForListedEdges := iupacP93CanonicalFullereneC60_twoFacesForListedEdges
  oppositeOrientationsForListedEdges :=
    iupacP93CanonicalFullereneC60_oppositeOrientationsForListedEdges
  eulerCharacteristicTwo := by
    have tableJudged := iupacP93CanonicalFullereneC60TableAudit.tableJudgment
      iupacP93CanonicalFullereneC60Transcription
    rw [← tableJudged.2.2.2]
    change (Finset.range 60).card + iupacP93CanonicalFullereneC60Faces.length =
      iupacP93CanonicalFullereneC60Transcription.edgeTable.toFinset.card + 2
    rw [iupacP93CanonicalFullereneC60_edgeTable_toFinset]
    rw [List.toFinset_card_of_nodup iupacP93CanonicalFullereneC60_edgesNodup,
      iupacP93CanonicalFullereneC60Faces_length,
      iupacP93CanonicalFullereneC60_edge_count]
    decide

/-- Full independent topology certificate for the reviewed all-carbon C60 cage. -/
def iupacP93CanonicalFullereneC60Certificate :
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.Certificate
      iupacP93CanonicalFullereneC60Transcription.cageMolecule :=
  iupacP93CanonicalFullereneC60FiniteOrientedAudit.toCertificate
    iupacP93CanonicalFullereneC60Transcription

/-- Reusable proof-carrying C60 cage shared by the separately audited Type-2 and Type-3
derivatives. -/
def iupacP93CanonicalFullereneC60SharedNumberedCage : SharedNumberedCage where
  transcription := iupacP93CanonicalFullereneC60Transcription
  certificate := iupacP93CanonicalFullereneC60Certificate


end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
