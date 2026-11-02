import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76TableBridge
import TetraStereo.OneCenter.P93MolecularFullereneFiniteFaceCertificate

set_option autoImplicit false

/-!
# Audited P-93 C76 numbered-cage package

This module is the source-only boundary between the frozen, independently reviewed
`(C76-D2)[5,6]` face transcription and the generic P-93.5.6 fullerene compiler.  The source
faces determine both the numbered package and its undirected edge table; no derivative overlay
or Type-1 row claim is made here.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

/-- The 75-edge systematic-locant spine is checked directly against the reviewed faces. -/
theorem iupacP93CanonicalFullereneC76_consecutiveFaceEdges :
    (List.range 75).all (fun atom =>
      iupacP93CanonicalFullereneC76Transcription.hasFaceEdge atom (atom + 1)) = true := by
  decide

/-- Consecutive systematic locants are adjacent cage atoms.  The only finite computation is the
76-way source-face lookup; molecular bond existence follows structurally from the derived edge
table instead of rescanning the complete molecule for every ordered pair. -/
theorem iupacP93CanonicalFullereneC76_consecutiveLocantsBonded :
    ∀ atom, atom + 1 < 76 →
      P94ConformationUnit.Bonded
        iupacP93CanonicalFullereneC76Transcription.cageMolecule atom (atom + 1) := by
  intro atom successorBound
  have atomBound : atom < 76 := by omega
  have atomPresent : atom ∈ List.range 75 := by simp; omega
  have faceEdge := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC76_consecutiveFaceEdges) atom atomPresent
  have edgePresent : (atom, atom + 1) ∈
      iupacP93CanonicalFullereneC76Transcription.edgeTable := by
    apply (numberedFaceTranscription_mem_edgeTable_iff
      iupacP93CanonicalFullereneC76Transcription atom (atom + 1)).mpr
    exact ⟨atomBound, successorBound, Nat.lt_succ_self atom, faceEdge⟩
  refine ⟨NumberedFaceTranscription.singleBond (atom, atom + 1), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(atom, atom + 1), edgePresent, rfl⟩
  · simp [NumberedFaceTranscription.singleBond, RawBond.connects]

/-- O(V) Hamiltonian-path admission of quantified cage connectedness. -/
theorem iupacP93CanonicalFullereneC76_connectedJudgment :
    MolecularFullereneCageConnected
      iupacP93CanonicalFullereneC76Transcription.cageMolecule
      iupacP93CanonicalFullereneC76Transcription.numberedPackage.carrier := by
  apply molecularFullereneCageConnected_of_range_hamiltonian
    iupacP93CanonicalFullereneC76Transcription.cageMolecule
    iupacP93CanonicalFullereneC76Transcription.numberedPackage 76
  · rfl
  · exact iupacP93CanonicalFullereneC76_consecutiveLocantsBonded
  · decide

/-! ## Symbolic source-to-package transport -/

/-- On bounded distinct atoms, generated face incidence and the independently extracted source
edge list denote the same edge. -/
theorem iupacP93CanonicalFullereneC76_hasFaceEdge_iff_hasSourceEdge
    (left right : Nat) (leftBound : left < 76) (rightBound : right < 76)
    (distinct : left ≠ right) :
    iupacP93CanonicalFullereneC76Transcription.hasFaceEdge left right = true ↔
      iupacP93CanonicalFullereneC76HasSourceEdge left right = true := by
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · have canonical : iupacP93C76CanonicalEdge (left, right) = (left, right) := by
      simp [iupacP93C76CanonicalEdge, ordered]
    constructor
    · intro faceEdge
      have tablePresent : (left, right) ∈
          iupacP93CanonicalFullereneC76Transcription.edgeTable :=
        (numberedFaceTranscription_mem_edgeTable_iff
          iupacP93CanonicalFullereneC76Transcription left right).mpr
            ⟨leftBound, rightBound, ordered, faceEdge⟩
      have sourcePresent : (left, right) ∈ iupacP93CanonicalFullereneC76Edges.toFinset := by
        rw [← iupacP93CanonicalFullereneC76_edgeTable_toFinset]
        simpa using tablePresent
      simpa [iupacP93CanonicalFullereneC76HasSourceEdge, canonical] using sourcePresent
    · intro sourceEdge
      have sourcePresent : (left, right) ∈ iupacP93CanonicalFullereneC76Edges.toFinset := by
        simpa [iupacP93CanonicalFullereneC76HasSourceEdge, canonical] using sourceEdge
      have tablePresent : (left, right) ∈
          iupacP93CanonicalFullereneC76Transcription.edgeTable := by
        have : (left, right) ∈
            iupacP93CanonicalFullereneC76Transcription.edgeTable.toFinset := by
          rw [iupacP93CanonicalFullereneC76_edgeTable_toFinset]
          exact sourcePresent
        simpa using this
      exact ((numberedFaceTranscription_mem_edgeTable_iff
        iupacP93CanonicalFullereneC76Transcription left right).mp tablePresent).2.2.2
  · have canonical : iupacP93C76CanonicalEdge (left, right) = (right, left) := by
      simp [iupacP93C76CanonicalEdge, Nat.not_lt.mpr (Nat.le_of_lt ordered)]
    rw [numberedFaceTranscription_hasFaceEdge_symm]
    constructor
    · intro faceEdge
      have tablePresent : (right, left) ∈
          iupacP93CanonicalFullereneC76Transcription.edgeTable :=
        (numberedFaceTranscription_mem_edgeTable_iff
          iupacP93CanonicalFullereneC76Transcription right left).mpr
            ⟨rightBound, leftBound, ordered, faceEdge⟩
      have sourcePresent : (right, left) ∈ iupacP93CanonicalFullereneC76Edges.toFinset := by
        rw [← iupacP93CanonicalFullereneC76_edgeTable_toFinset]
        simpa using tablePresent
      simpa [iupacP93CanonicalFullereneC76HasSourceEdge, canonical] using sourcePresent
    · intro sourceEdge
      have sourcePresent : (right, left) ∈ iupacP93CanonicalFullereneC76Edges.toFinset := by
        simpa [iupacP93CanonicalFullereneC76HasSourceEdge, canonical] using sourceEdge
      have tablePresent : (right, left) ∈
          iupacP93CanonicalFullereneC76Transcription.edgeTable := by
        have : (right, left) ∈
            iupacP93CanonicalFullereneC76Transcription.edgeTable.toFinset := by
          rw [iupacP93CanonicalFullereneC76_edgeTable_toFinset]
          exact sourcePresent
        simpa using this
      exact ((numberedFaceTranscription_mem_edgeTable_iff
        iupacP93CanonicalFullereneC76Transcription right left).mp tablePresent).2.2.2

/-- Cubicity is transported from the cached pure face-adjacency degree, not recomputed from the
generated molecular bond table. -/
theorem iupacP93CanonicalFullereneC76_cubicJudgment :
    ∀ atom ∈ iupacP93CanonicalFullereneC76Transcription.numberedPackage.carrier,
      (molecularFullereneCageNeighbors
        iupacP93CanonicalFullereneC76Transcription.cageMolecule
        iupacP93CanonicalFullereneC76Transcription.numberedPackage.carrier atom).card = 3 := by
  intro atom atomPresent
  have atomBound : atom < 76 := by
    simpa [MolecularFullereneNumberedCagePackage.carrier,
      NumberedFaceTranscription.numberedPackage,
      NumberedFaceTranscription.atomsByLocant] using atomPresent
  rw [numberedFaceTranscription_cageNeighbors_eq_faceNeighbors
    iupacP93CanonicalFullereneC76Transcription atom atomBound]
  simpa [numberedFaceTranscriptionFaceNeighbors,
    iupacP93CanonicalFullereneC76FaceAdjacencyNeighbors,
    iupacP93CanonicalFullereneC76Transcription,
    NumberedFaceTranscription.hasFaceEdge,
    iupacP93CanonicalFullereneC76HasNamedFaceEdge,
    iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge,
    isForwardMolecularFullereneFaceEdge] using
      iupacP93CanonicalFullereneC76_faceAdjacencyDegree atom atomBound



theorem iupacP93CanonicalFullereneC76_facesAccepted :
    iupacP93CanonicalFullereneC76Transcription.numberedPackage.faces.all
      (independentP94RingTraversalAccepted
        iupacP93CanonicalFullereneC76Transcription.cageMolecule) = true := by
  apply List.all_eq_true.mpr
  intro face facePresent
  have nodup : face.Nodup := of_decide_eq_true
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC76_eachFaceNodup) face facePresent)
  have size : face.length = 5 ∨ face.length = 6 := of_decide_eq_true
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC76_faceSizes) face facePresent)
  have minimum : 3 ≤ face.length := by rcases size with h | h <;> omega
  have bounded : ∀ atom ∈ face, atom < 76 := by
    intro atom atomPresent
    exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp
      iupacP93CanonicalFullereneC76_vertex_bounds) face facePresent)) atom atomPresent)
  have sourceCycleEdges :
      ∀ edge ∈ (molecularFullereneTraversalUnit face).cycleEdges,
        iupacP93CanonicalFullereneC76Transcription.hasFaceEdge edge.1 edge.2 = true := by
    intro edge edgePresent
    have listed : edge ∈ iupacP93C76DirectedFaceEdges face := by
      simpa [iupacP93C76DirectedFaceEdges, molecularFullereneTraversalUnit,
        P94ConformationUnit.cycleEdges, P94ConformationUnit.cyclicAdjacentPairs,
        P94ConformationUnit.cyclicSuccessors] using edgePresent
    have sourceEdge := (List.all_eq_true.mp ((List.all_eq_true.mp
      iupacP93CanonicalFullereneC76_facesCyclicEdges) face facePresent)) edge listed
    have leftPresent : edge.1 ∈ face := (List.of_mem_zip listed).1
    have rightSuccessor : edge.2 ∈ face.tail ++ face.take 1 := (List.of_mem_zip listed).2
    have rightPresent : edge.2 ∈ face := by
      rcases List.mem_append.mp rightSuccessor with tailPresent | headPresent
      · exact List.mem_of_mem_tail tailPresent
      · exact List.mem_of_mem_take headPresent
    have distinct := cycleEdges_distinct_of_minimum_nodup face minimum nodup edge edgePresent
    exact (iupacP93CanonicalFullereneC76_hasFaceEdge_iff_hasSourceEdge
      edge.1 edge.2 (bounded edge.1 leftPresent) (bounded edge.2 rightPresent) distinct).mpr
        sourceEdge
  apply independentP94RingTraversalAccepted_of_sourceFaceEdges
    iupacP93CanonicalFullereneC76Transcription face minimum nodup bounded sourceCycleEdges
  intro left leftPresent right rightPresent distinct
  have checkedLeft := (List.all_eq_true.mp
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC76_facesInduced) face facePresent))
      left leftPresent
  have checked := (List.all_eq_true.mp checkedLeft) right rightPresent
  have sourceNamedEq : iupacP93CanonicalFullereneC76HasSourceEdge left right =
      iupacP93CanonicalFullereneC76HasNamedFaceEdge face left right := by
    simpa only [if_neg distinct, beq_iff_eq] using checked
  rw [iupacP93CanonicalFullereneC76_hasFaceEdge_iff_hasSourceEdge left right
    (bounded left leftPresent) (bounded right rightPresent) distinct]
  constructor
  · intro sourceEdge
    apply (molecularFullereneNamedFaceEdge?_eq_true_iff face nodup left right).mp
    have localNamed :
        iupacP93CanonicalFullereneC76HasNamedFaceEdge face left right = true :=
      sourceNamedEq.symm.trans sourceEdge
    simpa [molecularFullereneNamedFaceEdge?,
      iupacP93CanonicalFullereneC76HasNamedFaceEdge,
      iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge,
      isForwardMolecularFullereneFaceEdge] using localNamed
  · intro named
    have genericNamed := (molecularFullereneNamedFaceEdge?_eq_true_iff
      face nodup left right).mpr named
    have localNamed :
        iupacP93CanonicalFullereneC76HasNamedFaceEdge face left right = true := by
      simpa [molecularFullereneNamedFaceEdge?,
        iupacP93CanonicalFullereneC76HasNamedFaceEdge,
        iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge,
        isForwardMolecularFullereneFaceEdge] using genericNamed
    exact sourceNamedEq.trans localNamed

/-- Source two-face incidence transported across the cached source/generated edge equality. -/
theorem iupacP93CanonicalFullereneC76_twoFacesForListedEdges :
    iupacP93CanonicalFullereneC76Transcription.numberedPackage.edgeTable.all (fun edge =>
      decide (iupacP93CanonicalFullereneC76Transcription.numberedPackage.faces.countP
        (fun face => molecularFullereneNamedFaceEdge? face edge.1 edge.2) = 2)) = true := by
  apply List.all_eq_true.mpr
  intro edge edgePresent
  have sourcePresent : edge ∈ iupacP93CanonicalFullereneC76Edges := by
    have tableFinset : edge ∈
        iupacP93CanonicalFullereneC76Transcription.edgeTable.toFinset := by
      simpa using edgePresent
    rw [iupacP93CanonicalFullereneC76_edgeTable_toFinset] at tableFinset
    simpa using tableFinset
  have sourceCount := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC76_twoNamedFacesPerEdge) edge sourcePresent
  simpa [iupacP93CanonicalFullereneC76Transcription,
    NumberedFaceTranscription.numberedPackage,
    molecularFullereneNamedFaceEdge?,
    iupacP93CanonicalFullereneC76HasNamedFaceEdge,
    iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge,
    isForwardMolecularFullereneFaceEdge] using sourceCount

/-- Source orientation incidence transported across the same cached edge equality. -/
theorem iupacP93CanonicalFullereneC76_oppositeOrientationsForListedEdges :
    iupacP93CanonicalFullereneC76Transcription.numberedPackage.edgeTable.all (fun edge =>
      decide (iupacP93CanonicalFullereneC76Transcription.numberedPackage.faces.countP
            (fun face => isForwardMolecularFullereneFaceEdge face edge.1 edge.2) = 1 ∧
        iupacP93CanonicalFullereneC76Transcription.numberedPackage.faces.countP
            (fun face => isForwardMolecularFullereneFaceEdge face edge.2 edge.1) = 1)) = true := by
  apply List.all_eq_true.mpr
  intro edge edgePresent
  have sourcePresent : edge ∈ iupacP93CanonicalFullereneC76Edges := by
    have tableFinset : edge ∈
        iupacP93CanonicalFullereneC76Transcription.edgeTable.toFinset := by
      simpa using edgePresent
    rw [iupacP93CanonicalFullereneC76_edgeTable_toFinset] at tableFinset
    simpa using tableFinset
  have sourceCount := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC76_oppositeNamedFaceOrientations) edge sourcePresent
  simpa [iupacP93CanonicalFullereneC76Transcription,
    NumberedFaceTranscription.numberedPackage,
    iupacP93CanonicalFullereneC76HasForwardNamedFaceEdge,
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


def iupacP93CanonicalFullereneC76FiniteOrientedAudit :
    FiniteOrientedFaceMapAudit iupacP93CanonicalFullereneC76Transcription where
  table := iupacP93CanonicalFullereneC76TableAudit
  connected := iupacP93CanonicalFullereneC76_connectedJudgment
  minimumSize := by
    change 20 ≤ (Finset.range 76).card
    simp
  carbonAtoms := by
    intro atom atomPresent
    have atomBound : atom < 76 := by
      simpa [MolecularFullereneNumberedCagePackage.carrier,
        NumberedFaceTranscription.numberedPackage,
        NumberedFaceTranscription.atomsByLocant] using atomPresent
    refine ⟨NumberedFaceTranscription.carbonAtom, ?_, rfl⟩
    exact listGet?_replicate_of_lt NumberedFaceTranscription.carbonAtom 76 atom atomBound
  cubic := iupacP93CanonicalFullereneC76_cubicJudgment
  facesNodup := iupacP93CanonicalFullereneC76_facesNodup
  facesAccepted := iupacP93CanonicalFullereneC76_facesAccepted
  faceSizes := by
    intro face facePresent
    exact of_decide_eq_true ((List.all_eq_true.mp
      iupacP93CanonicalFullereneC76_faceSizes) face facePresent)
  facesCover := by
    intro atom
    change atom ∈ Finset.range 76 ↔
      ∃ face ∈ iupacP93CanonicalFullereneC76Faces, atom ∈ face
    rw [← iupacP93CanonicalFullereneC76_vertexFinset]
    simp
  twelvePentagons := iupacP93CanonicalFullereneC76_pentagon_count
  hexagonCount := by
    change iupacP93CanonicalFullereneC76Faces.countP
      (fun face => decide (face.length = 6)) = 76 / 2 - 10
    simpa using iupacP93CanonicalFullereneC76_hexagon_count
  twoFacesForListedEdges := iupacP93CanonicalFullereneC76_twoFacesForListedEdges
  oppositeOrientationsForListedEdges :=
    iupacP93CanonicalFullereneC76_oppositeOrientationsForListedEdges
  eulerCharacteristicTwo := by
    have tableJudged := iupacP93CanonicalFullereneC76TableAudit.tableJudgment
      iupacP93CanonicalFullereneC76Transcription
    rw [← tableJudged.2.2.2]
    change (Finset.range 76).card + iupacP93CanonicalFullereneC76Faces.length =
      iupacP93CanonicalFullereneC76Transcription.edgeTable.toFinset.card + 2
    rw [iupacP93CanonicalFullereneC76_edgeTable_toFinset]
    rw [List.toFinset_card_of_nodup iupacP93CanonicalFullereneC76_edgesNodup,
      iupacP93CanonicalFullereneC76Faces_length,
      iupacP93CanonicalFullereneC76_edge_count]
    decide

/-- Full independent topology certificate for the reviewed all-carbon C76 cage. -/
def iupacP93CanonicalFullereneC76Certificate :
    iupacP93CanonicalFullereneC76Transcription.numberedPackage.Certificate
      iupacP93CanonicalFullereneC76Transcription.cageMolecule :=
  iupacP93CanonicalFullereneC76FiniteOrientedAudit.toCertificate
    iupacP93CanonicalFullereneC76Transcription

/-- Reusable proof-carrying C76 cage, ready for the separately audited Type-1 derivative. -/
def iupacP93CanonicalFullereneC76SharedNumberedCage : SharedNumberedCage where
  transcription := iupacP93CanonicalFullereneC76Transcription
  certificate := iupacP93CanonicalFullereneC76Certificate

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
