import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70TableBridge
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70FiniteAudit
import TetraStereo.OneCenter.P93MolecularFullereneFiniteFaceCertificate

set_option autoImplicit false

/-!
# Audited P-93 C70 numbered-cage package

This module is the proof-carrying boundary between the frozen, independently reviewed
`(C70-D5h(6))[5,6]` face transcription and the generic P-93.5.6 fullerene compiler.  It contains
no derivative overlays and makes no claim that a bare cage closes either printed derivative row.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

set_option maxRecDepth 10000 in


theorem iupacP93CanonicalFullereneC70_consecutiveFaceEdges :
    (List.range 69).all (fun atom =>
      iupacP93CanonicalFullereneC70Transcription.hasFaceEdge atom (atom + 1)) = true := by
  decide

theorem iupacP93CanonicalFullereneC70_consecutiveBonded
    (atom : Nat) (bounded : atom + 1 < 70) :
    P94ConformationUnit.Bonded
      iupacP93CanonicalFullereneC70Transcription.cageMolecule atom (atom + 1) := by
  have atomPresent : atom ∈ List.range 69 := by simp; omega
  have faceEdge := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC70_consecutiveFaceEdges) atom atomPresent
  have edgePresent : (atom, atom + 1) ∈
      iupacP93CanonicalFullereneC70Transcription.edgeTable :=
    (numberedFaceTranscription_mem_edgeTable_iff
      iupacP93CanonicalFullereneC70Transcription atom (atom + 1)).mpr
        ⟨by change atom < 70; omega, by simpa using bounded, by omega, faceEdge⟩
  refine ⟨NumberedFaceTranscription.singleBond (atom, atom + 1), ?_, ?_⟩
  · change NumberedFaceTranscription.singleBond (atom, atom + 1) ∈
      iupacP93CanonicalFullereneC70Transcription.edgeTable.map
        NumberedFaceTranscription.singleBond
    exact List.mem_map.mpr ⟨(atom, atom + 1), edgePresent, rfl⟩
  · simp [NumberedFaceTranscription.singleBond, RawBond.connects]

theorem iupacP93CanonicalFullereneC70_connected :
    MolecularFullereneCageConnected
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier := by
  apply molecularFullereneCageConnected_of_range_hamiltonian
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70Transcription.numberedPackage 70
  · rfl
  · exact iupacP93CanonicalFullereneC70_consecutiveBonded
  · decide

/-! ## Symbolic source-to-certificate transport -/

private theorem mem_eraseDups_iff {Alpha : Type*} [BEq Alpha] [LawfulBEq Alpha]
    (value : Alpha) : ∀ values : List Alpha,
    value ∈ values.eraseDups ↔ value ∈ values
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.mem_cons, mem_eraseDups_iff, List.mem_filter,
        List.mem_cons]
      by_cases equal : value = head
      · simp [equal]
      · simp [equal]
termination_by values => values.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem nodup_eraseDups {Alpha : Type*} [BEq Alpha] [LawfulBEq Alpha] :
    ∀ values : List Alpha, values.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, nodup_eraseDups _⟩
      intro present
      have filtered := (mem_eraseDups_iff head _).mp present
      have rejected := (List.mem_filter.mp filtered).2
      simp at rejected
termination_by values => values.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Source-edge membership is exactly generated face-edge membership on bounded distinct
locants. -/
theorem iupacP93CanonicalFullereneC70_sourceEdge_iff_faceEdge
    (left right : Nat) (leftBound : left < 70) (rightBound : right < 70)
    (distinct : left ≠ right) :
    iupacP93CanonicalFullereneC70HasSourceEdge left right = true ↔
      iupacP93CanonicalFullereneC70Transcription.hasFaceEdge left right = true := by
  simp only [iupacP93CanonicalFullereneC70HasSourceEdge, List.contains_iff_mem]
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · simp only [iupacP93C70CanonicalEdge, if_pos ordered]
    rw [← List.mem_toFinset, ← iupacP93CanonicalFullereneC70_edgeTable_toFinset,
      List.mem_toFinset, numberedFaceTranscription_mem_edgeTable_iff]
    simp [iupacP93CanonicalFullereneC70Transcription, leftBound, rightBound, ordered]
  · simp only [iupacP93C70CanonicalEdge,
      if_neg (Nat.not_lt_of_ge (Nat.le_of_lt ordered))]
    rw [← List.mem_toFinset, ← iupacP93CanonicalFullereneC70_edgeTable_toFinset,
      List.mem_toFinset, numberedFaceTranscription_mem_edgeTable_iff,
      numberedFaceTranscription_hasFaceEdge_symm]
    simp [iupacP93CanonicalFullereneC70Transcription, leftBound, rightBound, ordered]

/-- The source edge-list neighbor extraction has an exact bounded adjacency specification. -/
theorem iupacP93CanonicalFullereneC70_sourceNeighbor_iff
    (atom neighbor : Nat) :
    neighbor ∈ iupacP93CanonicalFullereneC70Edges.filterMap (fun edge =>
        if edge.1 = atom then some edge.2
        else if edge.2 = atom then some edge.1 else none) ↔
      neighbor ≠ atom ∧ neighbor < 70 ∧
        iupacP93CanonicalFullereneC70HasSourceEdge atom neighbor = true := by
  simp only [iupacP93CanonicalFullereneC70HasSourceEdge, List.contains_iff_mem]
  constructor
  · intro present
    rw [List.mem_filterMap] at present
    rcases present with ⟨edge, edgePresent, mapped⟩
    have edgeData := of_decide_eq_true ((List.all_eq_true.mp
      iupacP93CanonicalFullereneC70_edgesCanonicalAndBounded) edge edgePresent)
    split at mapped
    next firstEq =>
      simp only [Option.some.injEq] at mapped
      rcases edge with ⟨left, right⟩
      simp only at firstEq mapped edgeData ⊢
      subst left
      subst right
      refine ⟨by omega, edgeData.2.2, ?_⟩
      simpa [iupacP93C70CanonicalEdge, edgeData.1] using edgePresent
    next firstNe =>
      split at mapped
      next secondEq =>
        simp only [Option.some.injEq] at mapped
        rcases edge with ⟨left, right⟩
        simp only at firstNe secondEq mapped edgeData ⊢
        subst right
        subst left
        refine ⟨by omega, edgeData.2.1, ?_⟩
        simpa [iupacP93C70CanonicalEdge,
          Nat.not_lt_of_ge (Nat.le_of_lt edgeData.1)] using edgePresent
      next secondNe => simp at mapped
  · rintro ⟨neighborDistinct, _neighborBound, present⟩
    have distinct : atom ≠ neighbor := Ne.symm neighborDistinct
    rcases lt_or_gt_of_ne distinct with ordered | ordered
    · simp only [iupacP93C70CanonicalEdge, if_pos ordered] at present
      rw [List.mem_filterMap]
      exact ⟨(atom, neighbor), present, by simp⟩
    · have notOrdered : ¬ atom < neighbor := Nat.not_lt_of_ge (Nat.le_of_lt ordered)
      simp only [iupacP93C70CanonicalEdge, if_neg notOrdered] at present
      rw [List.mem_filterMap]
      exact ⟨(neighbor, atom), present, by simp [neighborDistinct]⟩

/-- Cubicity of the molecular cage is transported from the reviewed source neighbor table through
the generic exact face-neighbor theorem. -/
theorem iupacP93CanonicalFullereneC70_cubicJudgment
    (atom : Nat)
    (atomPresent : atom ∈
      iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier) :
    (molecularFullereneCageNeighbors
      iupacP93CanonicalFullereneC70Transcription.cageMolecule
      iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier atom).card = 3 := by
  have atomBound : atom < 70 := by
    simpa [NumberedFaceTranscription.numberedPackage,
      MolecularFullereneNumberedCagePackage.carrier,
      NumberedFaceTranscription.atomsByLocant,
      iupacP93CanonicalFullereneC70Transcription] using atomPresent
  rw [numberedFaceTranscription_cageNeighbors_eq_faceNeighbors
    iupacP93CanonicalFullereneC70Transcription atom (by
      simpa [iupacP93CanonicalFullereneC70Transcription] using atomBound)]
  have neighborEq :
      numberedFaceTranscriptionFaceNeighbors
          iupacP93CanonicalFullereneC70Transcription atom =
        (iupacP93CanonicalFullereneC70Edges.filterMap (fun edge =>
          if edge.1 = atom then some edge.2
          else if edge.2 = atom then some edge.1 else none)).toFinset := by
    ext neighbor
    simp only [numberedFaceTranscriptionFaceNeighbors, Finset.mem_filter,
      Finset.mem_range, List.mem_toFinset]
    constructor
    · rintro ⟨neighborBound, neighborDistinct, faceEdge⟩
      apply (iupacP93CanonicalFullereneC70_sourceNeighbor_iff atom neighbor).mpr
      exact ⟨neighborDistinct, neighborBound,
        (iupacP93CanonicalFullereneC70_sourceEdge_iff_faceEdge atom neighbor
          atomBound neighborBound (Ne.symm neighborDistinct)).mpr faceEdge⟩
    · intro sourceNeighbor
      rcases (iupacP93CanonicalFullereneC70_sourceNeighbor_iff atom neighbor).mp
          sourceNeighbor with ⟨neighborDistinct, neighborBound, sourceEdge⟩
      exact ⟨neighborBound, neighborDistinct,
        (iupacP93CanonicalFullereneC70_sourceEdge_iff_faceEdge atom neighbor
          atomBound neighborBound (Ne.symm neighborDistinct)).mp sourceEdge⟩
  rw [neighborEq]
  have sourceNeighborFinset :
      (iupacP93CanonicalFullereneC70Edges.filterMap (fun edge =>
        if edge.1 = atom then some edge.2
        else if edge.2 = atom then some edge.1 else none)).toFinset =
        (iupacP93CanonicalFullereneC70Neighbors atom).toFinset := by
    ext neighbor
    simp only [iupacP93CanonicalFullereneC70Neighbors, List.mem_toFinset]
    exact (mem_eraseDups_iff neighbor _).symm
  rw [sourceNeighborFinset]
  rw [List.toFinset_card_of_nodup (by exact nodup_eraseDups _)]
  exact of_decide_eq_true
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC70_cubic) atom (by
      simpa using atomBound))

/-- Every reviewed face reaches the exact independent P-94 traversal judgment.  The source cycle
ledger supplies raw cyclic bonds; inducedness uses the definitionally aligned face predicates. -/
theorem iupacP93CanonicalFullereneC70_facesAccepted :
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.faces.all
      (independentP94RingTraversalAccepted
        iupacP93CanonicalFullereneC70Transcription.cageMolecule) = true := by
  rw [List.all_eq_true]
  intro face facePresent
  have faceNodup : face.Nodup := of_decide_eq_true
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC70_eachFaceNodup) face facePresent)
  have faceSize := of_decide_eq_true
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC70_faceSizes) face facePresent)
  have minimum : 3 ≤ face.length := by rcases faceSize with five | six <;> omega
  have bounded : ∀ atom ∈ face,
      atom < iupacP93CanonicalFullereneC70Transcription.atomCount := by
    intro atom atomPresent
    have accepted := (List.all_eq_true.mp
      ((List.all_eq_true.mp iupacP93CanonicalFullereneC70_vertex_bounds)
        face facePresent)) atom atomPresent
    simpa [iupacP93CanonicalFullereneC70Transcription] using accepted
  apply independentP94RingTraversalAccepted_of_sourceFaceEdges
    iupacP93CanonicalFullereneC70Transcription face minimum faceNodup bounded
  · intro edge edgePresent
    have sourceAccepted := (List.all_eq_true.mp
      ((List.all_eq_true.mp iupacP93CanonicalFullereneC70_facesCyclicEdges)
        face facePresent)) edge (by
          simpa [molecularFullereneTraversalUnit, P94ConformationUnit.cycleEdges,
            P94ConformationUnit.cyclicAdjacentPairs, P94ConformationUnit.cyclicSuccessors,
            iupacP93C70DirectedFaceEdges] using edgePresent)
    have zippedPresent : edge ∈ face.zip (face.tail ++ face.take 1) := by
      simpa [molecularFullereneTraversalUnit, P94ConformationUnit.cycleEdges,
        P94ConformationUnit.cyclicAdjacentPairs, P94ConformationUnit.cyclicSuccessors] using
          edgePresent
    have leftPresent : edge.1 ∈ face := (List.of_mem_zip zippedPresent).1
    have rightSuccessor : edge.2 ∈ face.tail ++ face.take 1 :=
      (List.of_mem_zip zippedPresent).2
    have rightPresent : edge.2 ∈ face := by
      rcases List.mem_append.mp rightSuccessor with tailPresent | headPresent
      · exact List.mem_of_mem_tail tailPresent
      · exact List.mem_of_mem_take headPresent
    exact (iupacP93CanonicalFullereneC70_sourceEdge_iff_faceEdge edge.1 edge.2
      (bounded edge.1 leftPresent) (bounded edge.2 rightPresent)
      (cycleEdges_distinct_of_minimum_nodup face minimum faceNodup edge edgePresent)).mp
        sourceAccepted
  · intro left leftPresent right rightPresent distinct
    have checked := (List.all_eq_true.mp
      ((List.all_eq_true.mp
        ((List.all_eq_true.mp iupacP93CanonicalFullereneC70_facesInduced)
          face facePresent)) left leftPresent)) right rightPresent
    have checkedEq : iupacP93CanonicalFullereneC70HasFaceEdge left right =
        iupacP93CanonicalFullereneC70HasNamedFaceEdge face left right := by
      simpa [if_neg distinct, beq_iff_eq] using checked
    rw [← molecularFullereneNamedFaceEdge?_eq_true_iff face faceNodup left right]
    simpa [iupacP93CanonicalFullereneC70Transcription,
      NumberedFaceTranscription.hasFaceEdge,
      iupacP93CanonicalFullereneC70HasFaceEdge,
      iupacP93CanonicalFullereneC70HasNamedFaceEdge,
      iupacP93CanonicalFullereneC70HasForwardNamedFaceEdge,
      molecularFullereneNamedFaceEdge?, isForwardMolecularFullereneFaceEdge] using
        (Bool.eq_iff_iff.mp checkedEq)

theorem iupacP93CanonicalFullereneC70_carbonAtoms :
    ∀ atom ∈ iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier,
      ∃ spec, iupacP93CanonicalFullereneC70Transcription.cageMolecule.atomAt? atom =
        some spec ∧ spec.element = .C := by
  intro atom atomPresent
  have atomBound : atom < 70 := by
    simpa [NumberedFaceTranscription.numberedPackage,
      MolecularFullereneNumberedCagePackage.carrier,
      NumberedFaceTranscription.atomsByLocant,
      iupacP93CanonicalFullereneC70Transcription] using atomPresent
  refine ⟨NumberedFaceTranscription.carbonAtom, ?_, rfl⟩
  let index : Fin (List.replicate 70 NumberedFaceTranscription.carbonAtom).length :=
    ⟨atom, by simpa using atomBound⟩
  have lookup := listGet?_eq_some_get
    (List.replicate 70 NumberedFaceTranscription.carbonAtom) index
  have getEq : (List.replicate 70 NumberedFaceTranscription.carbonAtom).get index =
      NumberedFaceTranscription.carbonAtom := by
    exact List.getElem_replicate index.isLt
  rw [getEq] at lookup
  change listGet? (List.replicate 70 NumberedFaceTranscription.carbonAtom) atom =
    some NumberedFaceTranscription.carbonAtom
  simpa [index] using lookup

theorem iupacP93CanonicalFullereneC70_faceSizesJudgment :
    ∀ face ∈ iupacP93CanonicalFullereneC70Transcription.numberedPackage.faces,
      face.length = 5 ∨ face.length = 6 := by
  intro face facePresent
  exact of_decide_eq_true
    ((List.all_eq_true.mp iupacP93CanonicalFullereneC70_faceSizes) face facePresent)

theorem iupacP93CanonicalFullereneC70_facesCover :
    ∀ atom,
      atom ∈ iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier ↔
        ∃ face ∈ iupacP93CanonicalFullereneC70Transcription.numberedPackage.faces,
          atom ∈ face := by
  intro atom
  change atom ∈ Finset.range 70 ↔
    ∃ face ∈ iupacP93CanonicalFullereneC70Faces, atom ∈ face
  rw [← iupacP93CanonicalFullereneC70_vertexFinset]
  simp

theorem iupacP93CanonicalFullereneC70_twoFacesForListedEdges :
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.edgeTable.all (fun edge =>
      decide (iupacP93CanonicalFullereneC70Transcription.numberedPackage.faces.countP
        (fun face => molecularFullereneNamedFaceEdge? face edge.1 edge.2) = 2)) = true := by
  rw [List.all_eq_true]
  intro edge edgePresent
  have sourcePresent : edge ∈ iupacP93CanonicalFullereneC70Edges := by
    rw [← List.mem_toFinset, ← iupacP93CanonicalFullereneC70_edgeTable_toFinset,
      List.mem_toFinset]
    exact edgePresent
  have checked := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC70_twoNamedFacesPerEdge) edge sourcePresent
  simpa [iupacP93CanonicalFullereneC70Transcription,
    iupacP93CanonicalFullereneC70HasNamedFaceEdge,
    iupacP93CanonicalFullereneC70HasForwardNamedFaceEdge,
    molecularFullereneNamedFaceEdge?, isForwardMolecularFullereneFaceEdge] using checked

theorem iupacP93CanonicalFullereneC70_oppositeOrientationsForListedEdges :
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.edgeTable.all (fun edge =>
      decide (iupacP93CanonicalFullereneC70Transcription.numberedPackage.faces.countP
          (fun face => isForwardMolecularFullereneFaceEdge face edge.1 edge.2) = 1 ∧
        iupacP93CanonicalFullereneC70Transcription.numberedPackage.faces.countP
          (fun face => isForwardMolecularFullereneFaceEdge face edge.2 edge.1) = 1)) = true := by
  rw [List.all_eq_true]
  intro edge edgePresent
  have sourcePresent : edge ∈ iupacP93CanonicalFullereneC70Edges := by
    rw [← List.mem_toFinset, ← iupacP93CanonicalFullereneC70_edgeTable_toFinset,
      List.mem_toFinset]
    exact edgePresent
  have checked := (List.all_eq_true.mp
    iupacP93CanonicalFullereneC70_oppositeNamedFaceOrientations) edge sourcePresent
  simpa [iupacP93CanonicalFullereneC70Transcription,
    iupacP93CanonicalFullereneC70HasForwardNamedFaceEdge,
    isForwardMolecularFullereneFaceEdge] using checked

theorem iupacP93CanonicalFullereneC70_eulerCharacteristicTwo :
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier.card +
        iupacP93CanonicalFullereneC70Transcription.numberedPackage.faces.length =
      (molecularFullereneCageEdges
        iupacP93CanonicalFullereneC70Transcription.cageMolecule
        iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier).card + 2 := by
  rw [← (iupacP93CanonicalFullereneC70TableAudit.tableJudgment
    iupacP93CanonicalFullereneC70Transcription).2.2.2]
  change _ = iupacP93CanonicalFullereneC70Transcription.edgeTable.toFinset.card + 2
  rw [iupacP93CanonicalFullereneC70_edgeTable_toFinset]
  simp only [NumberedFaceTranscription.numberedPackage,
    MolecularFullereneNumberedCagePackage.carrier,
    NumberedFaceTranscription.atomsByLocant,
    iupacP93CanonicalFullereneC70Transcription,
    iupacP93CanonicalFullereneC70Faces_length]
  rw [List.toFinset_card_of_nodup List.nodup_range,
    List.toFinset_card_of_nodup iupacP93CanonicalFullereneC70_edgesNodup,
    iupacP93CanonicalFullereneC70_edge_count]
  simp


def iupacP93CanonicalFullereneC70Audit : FiniteOrientedFaceMapAudit
    iupacP93CanonicalFullereneC70Transcription where
  table := iupacP93CanonicalFullereneC70TableAudit
  connected := iupacP93CanonicalFullereneC70_connected
  minimumSize := by
    change 20 ≤ (List.range 70).toFinset.card
    rw [List.toFinset_card_of_nodup List.nodup_range]
    simp
  carbonAtoms := iupacP93CanonicalFullereneC70_carbonAtoms
  cubic := iupacP93CanonicalFullereneC70_cubicJudgment
  facesNodup := iupacP93CanonicalFullereneC70_facesNodup
  facesAccepted := iupacP93CanonicalFullereneC70_facesAccepted
  faceSizes := iupacP93CanonicalFullereneC70_faceSizesJudgment
  facesCover := iupacP93CanonicalFullereneC70_facesCover
  twelvePentagons := iupacP93CanonicalFullereneC70_pentagon_count
  hexagonCount := by
    change iupacP93CanonicalFullereneC70Faces.countP
      (fun face => decide (face.length = 6)) =
        (List.range 70).toFinset.card / 2 - 10
    rw [iupacP93CanonicalFullereneC70_hexagon_count,
      List.toFinset_card_of_nodup List.nodup_range]
    simp
  twoFacesForListedEdges := iupacP93CanonicalFullereneC70_twoFacesForListedEdges
  oppositeOrientationsForListedEdges :=
    iupacP93CanonicalFullereneC70_oppositeOrientationsForListedEdges
  eulerCharacteristicTwo := iupacP93CanonicalFullereneC70_eulerCharacteristicTwo

/-- The complete proof-carrying C70 cage shared by the two printed P-93 fullerene figures. -/
def iupacP93CanonicalFullereneC70SharedNumberedCage : SharedNumberedCage where
  transcription := iupacP93CanonicalFullereneC70Transcription
  certificate := iupacP93CanonicalFullereneC70Audit.toCertificate
    iupacP93CanonicalFullereneC70Transcription

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70Audit
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70SharedNumberedCage
