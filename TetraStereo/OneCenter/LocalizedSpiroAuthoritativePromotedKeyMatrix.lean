import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeOccurrenceFrame
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6PromotedKeyExact

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Coherent authoritative promoted-key matrix for tetrahedral spiro branches

Rule 6 is reference-dependent.  Therefore the chemically honest bridge from four perceived
spiro branches is not one context-free key per branch, but a four-by-four matrix: one row for each
chosen reference branch and one column for each ranked branch.  All sixteen cells below use the
same source occurrence target, dependency view, evaluation fuel, and frame-wide Rule-3 exclusion
set.
-/

/-- The four real source-canonical cursors selected by the canonical `Fin 4` ligand positions. -/
noncomputable def authoritativeTetrahedralRootBranchCursors
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter) :
    List (input.certified.input.AromaticCanonicalRerootCursor carrierFuel) :=
  List.ofFn fun position =>
    input.authoritativeRootBranchCursor carrierFuel center
      (input.certified.input.aromaticCanonicalLigandAtom center position)
      (input.certified.input.aromaticCanonicalLigandAtom_adjacent center position)

@[simp] theorem authoritativeTetrahedralRootBranchCursors_length
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter) :
    (input.authoritativeTetrahedralRootBranchCursors carrierFuel center).length = 4 := by
  simp [authoritativeTetrahedralRootBranchCursors]

@[simp] theorem authoritativeTetrahedralRootBranchCursors_get
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (position : Fin 4) :
    (input.authoritativeTetrahedralRootBranchCursors carrierFuel center).get
        (Fin.cast
          (input.authoritativeTetrahedralRootBranchCursors_length carrierFuel center).symm
          position) =
      input.authoritativeRootBranchCursor carrierFuel center
        (input.certified.input.aromaticCanonicalLigandAtom center position)
        (input.certified.input.aromaticCanonicalLigandAtom_adjacent center position) := by
  fin_cases position <;> rfl

@[simp] theorem authoritativeTetrahedralRootBranchCursors_get_current
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (position : Fin 4) :
    ((input.authoritativeTetrahedralRootBranchCursors carrierFuel center).get
        (Fin.cast
          (input.authoritativeTetrahedralRootBranchCursors_length carrierFuel center).symm
          position)).occurrence.1.node.current? =
      some (input.certified.input.aromaticCanonicalLigandAtom center position) := by
  rw [input.authoritativeTetrahedralRootBranchCursors_get carrierFuel center position]
  exact input.authoritativeRootBranchCursor_current carrierFuel center
    (input.certified.input.aromaticCanonicalLigandAtom center position)
    (input.certified.input.aromaticCanonicalLigandAtom_adjacent center position)

@[simp] theorem authoritativeTetrahedralRootBranchCursors_get_provenance
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (position : Fin 4) :
    ((input.authoritativeTetrahedralRootBranchCursors carrierFuel center).get
        (Fin.cast
          (input.authoritativeTetrahedralRootBranchCursors_length carrierFuel center).symm
          position)).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
  rw [input.authoritativeTetrahedralRootBranchCursors_get carrierFuel center position]
  exact input.authoritativeRootBranchCursor_provenance carrierFuel center
    (input.certified.input.aromaticCanonicalLigandAtom center position)
    (input.certified.input.aromaticCanonicalLigandAtom_adjacent center position)

/-- Every selected cursor is literally in the production first ligand frame. -/
theorem mem_authoritativeTetrahedralRootBranchCursors_implies_mem_productionFrame
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (cursor : input.certified.input.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ input.authoritativeTetrahedralRootBranchCursors carrierFuel center) :
    cursor ∈ input.certified.input.aromaticCanonicalRerootChildren
      { occurrence := input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center
        previous? := none } := by
  rw [authoritativeTetrahedralRootBranchCursors, List.mem_ofFn] at present
  obtain ⟨position, rfl⟩ := present
  exact input.authoritativeRootBranchCursor_mem_rerootChildren carrierFuel center
    (input.certified.input.aromaticCanonicalLigandAtom center position)
    (input.certified.input.aromaticCanonicalLigandAtom_adjacent center position)

/-- One matrix cell: build the branch key under one reference position after resolving one common
Rule-3 physical-topology frame for all four branches. -/
noncomputable def authoritativeSpiroRule3Through6BranchKey?
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (referencePosition branchPosition : Fin 4) :
    Option input.AuthoritativeSpiroBranchKey := do
  let roots := input.authoritativeTetrahedralRootBranchCursors carrierFuel center
  let frame ← input.certified.input.buildAromaticCanonicalRule3CanonicalKeyFrame?
    evaluationFuel roots
  let reference := input.certified.input.aromaticCanonicalLigandAtom center referencePosition
  let branchCursor := roots.get
    (Fin.cast (input.authoritativeTetrahedralRootBranchCursors_length
      carrierFuel center).symm branchPosition)
  input.certified.input.buildAromaticCanonicalRule3Through6PromotedKey?
    frame.excluded
    (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
    view reference evaluationFuel branchCursor

/-- Independent canonical meaning of one matrix cell.  The existential frame is constrained by
the exact common Rule-3 frame relation, so every reference row necessarily shares the unique
frame computed from the same four cursors. -/
def CanonicalAuthoritativeSpiroRule3Through6BranchKey
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (referencePosition branchPosition : Fin 4)
    (key : input.AuthoritativeSpiroBranchKey) : Prop :=
  ∃ frame,
    input.certified.input.CanonicalAromaticCanonicalRule3CanonicalKeyFrame
      evaluationFuel
      (input.authoritativeTetrahedralRootBranchCursors carrierFuel center) frame ∧
    input.certified.input.CanonicalAromaticCanonicalRule3Through6PromotedKey
      frame.excluded
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
      view
      (input.certified.input.aromaticCanonicalLigandAtom center referencePosition)
      evaluationFuel
      ((input.authoritativeTetrahedralRootBranchCursors carrierFuel center).get
        (Fin.cast (input.authoritativeTetrahedralRootBranchCursors_length
          carrierFuel center).symm branchPosition)) key

/-- Exact cell theorem: the executable matrix cell succeeds iff the common Rule-3 frame and the
reference-specific recursive promoted key have their canonical derivations. -/
theorem authoritativeSpiroRule3Through6BranchKey?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (referencePosition branchPosition : Fin 4)
    (key : input.AuthoritativeSpiroBranchKey) :
    input.authoritativeSpiroRule3Through6BranchKey?
        carrierFuel evaluationFuel center view referencePosition branchPosition = some key ↔
      input.CanonicalAuthoritativeSpiroRule3Through6BranchKey
        carrierFuel evaluationFuel center view referencePosition branchPosition key := by
  unfold authoritativeSpiroRule3Through6BranchKey?
    CanonicalAuthoritativeSpiroRule3Through6BranchKey
  let roots := input.authoritativeTetrahedralRootBranchCursors carrierFuel center
  change
    (do
      let frame ←
        input.certified.input.buildAromaticCanonicalRule3CanonicalKeyFrame?
          evaluationFuel roots
      input.certified.input.buildAromaticCanonicalRule3Through6PromotedKey?
        frame.excluded
        (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
        view
        (input.certified.input.aromaticCanonicalLigandAtom center referencePosition)
        evaluationFuel
        (roots.get (Fin.cast
          (input.authoritativeTetrahedralRootBranchCursors_length
            carrierFuel center).symm branchPosition))) = some key ↔
      ∃ frame,
        input.certified.input.CanonicalAromaticCanonicalRule3CanonicalKeyFrame
          evaluationFuel roots frame ∧
        input.certified.input.CanonicalAromaticCanonicalRule3Through6PromotedKey
          frame.excluded
          (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
          view
          (input.certified.input.aromaticCanonicalLigandAtom center referencePosition)
          evaluationFuel
          (roots.get (Fin.cast
            (input.authoritativeTetrahedralRootBranchCursors_length
              carrierFuel center).symm branchPosition)) key
  cases frameComputed :
      input.certified.input.buildAromaticCanonicalRule3CanonicalKeyFrame?
        evaluationFuel roots with
  | none =>
      constructor
      · intro computed
        simp at computed
      · rintro ⟨frame, frameCanonical, _keyCanonical⟩
        have computed :=
          (input.certified.input.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
            evaluationFuel roots frame).mpr frameCanonical
        rw [frameComputed] at computed
        contradiction
  | some frame =>
      change
        input.certified.input.buildAromaticCanonicalRule3Through6PromotedKey?
            frame.excluded
            (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
            view
            (input.certified.input.aromaticCanonicalLigandAtom center referencePosition)
            evaluationFuel
            (roots.get (Fin.cast
              (input.authoritativeTetrahedralRootBranchCursors_length
                carrierFuel center).symm branchPosition)) = some key ↔
          ∃ otherFrame,
            input.certified.input.CanonicalAromaticCanonicalRule3CanonicalKeyFrame
              evaluationFuel roots otherFrame ∧
            input.certified.input.CanonicalAromaticCanonicalRule3Through6PromotedKey
              otherFrame.excluded
              (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
              view
              (input.certified.input.aromaticCanonicalLigandAtom center referencePosition)
              evaluationFuel
              (roots.get (Fin.cast
                (input.authoritativeTetrahedralRootBranchCursors_length
                  carrierFuel center).symm branchPosition)) key
      rw [input.certified.input.buildAromaticCanonicalRule3Through6PromotedKey?_eq_some_iff_canonical]
      constructor
      · intro keyCanonical
        exact ⟨frame,
          (input.certified.input.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
            evaluationFuel roots frame).mp frameComputed,
          keyCanonical⟩
      · rintro ⟨otherFrame, otherCanonical, keyCanonical⟩
        have otherComputed :=
          (input.certified.input.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
            evaluationFuel roots otherFrame).mpr otherCanonical
        have frameEq : otherFrame = frame := by
          apply Option.some.inj
          exact otherComputed.symm.trans frameComputed
        subst otherFrame
        exact keyCanonical

/-- Exact readiness of the complete reference-dependent key matrix. -/
def AuthoritativeSpiroRule3Through6KeyMatrixReady
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)) : Prop :=
  ∀ referencePosition branchPosition : Fin 4,
    ∃ key, input.CanonicalAuthoritativeSpiroRule3Through6BranchKey
      carrierFuel evaluationFuel center view referencePosition branchPosition key

/-- Matrix readiness has no hidden executable failure: all sixteen cells compute exactly when all
sixteen canonical reference/branch judgments exist. -/
theorem authoritativeSpiroRule3Through6KeyMatrixReady_iff_every_cell_isSome
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    input.AuthoritativeSpiroRule3Through6KeyMatrixReady
        carrierFuel evaluationFuel center view ↔
      ∀ referencePosition branchPosition : Fin 4,
        (input.authoritativeSpiroRule3Through6BranchKey?
          carrierFuel evaluationFuel center view
          referencePosition branchPosition).isSome = true := by
  unfold AuthoritativeSpiroRule3Through6KeyMatrixReady
  constructor
  · intro ready referencePosition branchPosition
    obtain ⟨key, canonical⟩ := ready referencePosition branchPosition
    rw [Option.isSome_iff_exists]
    exact ⟨key,
      (input.authoritativeSpiroRule3Through6BranchKey?_eq_some_iff_canonical
        carrierFuel evaluationFuel center view referencePosition branchPosition key).mpr
          canonical⟩
  · intro successful referencePosition branchPosition
    have cellSuccessful := successful referencePosition branchPosition
    rw [Option.isSome_iff_exists] at cellSuccessful
    obtain ⟨key, computed⟩ := cellSuccessful
    exact ⟨key,
      (input.authoritativeSpiroRule3Through6BranchKey?_eq_some_iff_canonical
        carrierFuel evaluationFuel center view referencePosition branchPosition key).mp
          computed⟩

/-- Under exact readiness, one total 4×4 family of actual production keys exists. -/
theorem AuthoritativeSpiroRule3Through6KeyMatrixReady.exists_complete_matrix
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady
      carrierFuel evaluationFuel center view) :
    ∃ keys : Fin 4 → Fin 4 → input.AuthoritativeSpiroBranchKey,
      ∀ referencePosition branchPosition,
        input.authoritativeSpiroRule3Through6BranchKey?
            carrierFuel evaluationFuel center view referencePosition branchPosition =
          some (keys referencePosition branchPosition) := by
  classical
  have successful :=
    (input.authoritativeSpiroRule3Through6KeyMatrixReady_iff_every_cell_isSome
      carrierFuel evaluationFuel center view).mp ready
  choose keys computed using fun referencePosition branchPosition =>
    Option.isSome_iff_exists.mp (successful referencePosition branchPosition)
  exact ⟨keys, computed⟩

/-- Exact matrix readiness makes every reference row operational in the production Rule-6
ranking backend.  This is the concrete attachment point to the P-92 reference-family scheduler. -/
theorem AuthoritativeSpiroRule3Through6KeyMatrixReady.rankingBackend_isSome
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady
      carrierFuel evaluationFuel center view)
    (referencePosition : Fin 4) :
    (input.certified.input.aromaticCanonicalRule3Through6RankingBackend
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center)
      view evaluationFuel
      (input.authoritativeTetrahedralRootBranchCursors carrierFuel center)
      referencePosition.val).isSome = true := by
  classical
  let source := input.certified.input
  let roots := input.authoritativeTetrahedralRootBranchCursors carrierFuel center
  change (source.aromaticCanonicalRule3Through6RankingBackend
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)
    view evaluationFuel roots referencePosition.val).isSome = true
  have rootsLength : roots.length = 4 := by
    exact input.authoritativeTetrahedralRootBranchCursors_length carrierFuel center
  obtain ⟨_witnessKey, frame, frameCanonical, _witnessCanonical⟩ :=
    ready referencePosition (0 : Fin 4)
  have frameComputed :
      source.buildAromaticCanonicalRule3CanonicalKeyFrame?
          evaluationFuel roots = some frame :=
    (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
      evaluationFuel roots frame).mpr frameCanonical
  have frameLength : frame.keys.length = 4 := by
    rw [frameCanonical.keys_length_eq, rootsLength]
  obtain ⟨keys, matrixComputed⟩ := ready.exists_complete_matrix input
    carrierFuel evaluationFuel center view
  have direct (branchPosition : Fin 4) :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
          frame.excluded
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)
          view
          (source.aromaticCanonicalLigandAtom center referencePosition)
          evaluationFuel
          (roots.get (Fin.cast rootsLength.symm branchPosition)) =
        some (keys referencePosition branchPosition) := by
    have computed := matrixComputed referencePosition branchPosition
    unfold authoritativeSpiroRule3Through6BranchKey? at computed
    simpa [source, roots, frameComputed] using computed
  have direct0 := direct (0 : Fin 4)
  have direct1 := direct (1 : Fin 4)
  have direct2 := direct (2 : Fin 4)
  have direct3 := direct (3 : Fin 4)
  have rootsEq : roots = List.ofFn fun position : Fin 4 =>
      roots.get (Fin.cast rootsLength.symm position) := by
    symm
    simpa using List.ofFn_get roots
  have referenceBound : referencePosition.val < roots.length := by
    rw [rootsLength]
    exact referencePosition.isLt
  have referenceCursorComputed : roots[referencePosition.val]? =
      some (roots.get (Fin.cast rootsLength.symm referencePosition)) := by
    rw [List.getElem?_eq_getElem referenceBound]
    rfl
  have referenceCurrent :
      (roots.get (Fin.cast rootsLength.symm referencePosition)).occurrence.1.node.current? =
        some (source.aromaticCanonicalLigandAtom center referencePosition) := by
    exact input.authoritativeTetrahedralRootBranchCursors_get_current
      carrierFuel center referencePosition
  have referenceCurrentAt :
      (roots[referencePosition.val]'referenceBound).occurrence.1.node.current? =
        some (source.aromaticCanonicalLigandAtom center referencePosition) := by
    simpa using referenceCurrent
  have directAt0 :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
          frame.excluded
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)
          view (source.aromaticCanonicalLigandAtom center referencePosition)
          evaluationFuel roots[0] = some (keys referencePosition 0) := by
    simpa using direct0
  have directAt1 :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
          frame.excluded
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)
          view (source.aromaticCanonicalLigandAtom center referencePosition)
          evaluationFuel roots[1] = some (keys referencePosition 1) := by
    simpa using direct1
  have directAt2 :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
          frame.excluded
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)
          view (source.aromaticCanonicalLigandAtom center referencePosition)
          evaluationFuel roots[2] = some (keys referencePosition 2) := by
    simpa using direct2
  have directAt3 :
      source.buildAromaticCanonicalRule3Through6PromotedKey?
          frame.excluded
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)
          view (source.aromaticCanonicalLigandAtom center referencePosition)
          evaluationFuel roots[3] = some (keys referencePosition 3) := by
    simpa using direct3
  have entriesSuccessful :
      ∃ entries,
        roots.zipIdx.mapM
            (source.buildAromaticCanonicalRule3Through6IndexedKey?
              frame.excluded
              (source.aromaticCanonicalFinalOccurrence carrierFuel center)
              view (source.aromaticCanonicalLigandAtom center referencePosition)
              evaluationFuel) = some entries := by
    rw [rootsEq]
    simp [AuthoritativeChemicalInput.buildAromaticCanonicalRule3Through6IndexedKey?,
      directAt0, directAt1, directAt2, directAt3]
  obtain ⟨entries, entriesComputed⟩ := entriesSuccessful
  unfold AuthoritativeChemicalInput.aromaticCanonicalRule3Through6RankingBackend
  rw [dif_pos rootsLength, frameComputed]
  rw [referenceCursorComputed]
  simp [frameLength, referenceCurrentAt, entriesComputed]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
