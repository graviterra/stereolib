import TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingOccurrenceModel

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Source-perception closure for terminal auxiliary inputs

The continuing daughter children are the actual outward Br/I/H cursors, not the daughters'
four-root reroot frames. None is a perceived source tetrahedral center. The scheduled drawing
model consequently gives all six terminal inputs, and the central F/Cl roots, no auxiliary
label. Refusal is proved from actual source atom eligibility and causal model evaluation;
no arbitrary empty state or old spatial model label is supplied.

The central actual dependency-label vector carries the corrected daughter labels: left `S`,
right `R` (negative priority-ordered determinant `R`, positive `S`).
-/

theorem occurrenceOrdinaryDescriptor?_eq_none_of_center_none
    (input : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : input.AromaticCanonicalOccurrence carrierFuel)
    (view : input.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (absent : input.aromaticCanonicalOccurrenceTetrahedralCenter? target = none) :
    occurrenceOrdinaryDescriptor? input target view ruleFuel = none := by
  simp [occurrenceOrdinaryDescriptor?, occurrenceOrdinaryPriorityEvidence?, absent]

theorem occurrenceOrdinaryModel_eq_none_of_center_none
    (input : AuthoritativeChemicalInput) {carrierFuel ruleFuel : Nat}
    (state : input.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (input.aromaticCanonicalOccurrenceSystem
      (occurrenceOrdinaryAuxiliarySemantics input carrierFuel ruleFuel)).CIPModel state)
    (target : input.AromaticCanonicalOccurrence carrierFuel)
    (absent : input.aromaticCanonicalOccurrenceTetrahedralCenter? target = none) :
    state target = none := by
  rw [← occurrenceOrdinaryModel_evaluates input state model target]
  exact occurrenceOrdinaryDescriptor?_eq_none_of_center_none input target _ ruleFuel absent

noncomputable def leftContinuingChildren :=
  source.aromaticCanonicalRerootChildren (centralRootAt ⟨2, by decide +kernel⟩)

noncomputable def rightContinuingChildren :=
  source.aromaticCanonicalRerootChildren (centralRootAt ⟨3, by decide +kernel⟩)

theorem continuing_children_lengths :
    leftContinuingChildren.length = 3 ∧ rightContinuingChildren.length = 3 := ⟨rfl, rfl⟩

noncomputable def leftContinuingChildAt (slot : Fin 3) :=
  leftContinuingChildren.get (Fin.cast continuing_children_lengths.1.symm slot)

noncomputable def rightContinuingChildAt (slot : Fin 3) :=
  rightContinuingChildren.get (Fin.cast continuing_children_lengths.2.symm slot)

def leftContinuingAtom : Fin 3 → source.AromaticCanonicalAtom
  | ⟨0, _⟩ => ⟨4, by decide +kernel⟩
  | ⟨1, _⟩ => ⟨5, by decide +kernel⟩
  | ⟨2, _⟩ => ⟨9, by decide +kernel⟩

def rightContinuingAtom : Fin 3 → source.AromaticCanonicalAtom
  | ⟨0, _⟩ => ⟨7, by decide +kernel⟩
  | ⟨1, _⟩ => ⟨8, by decide +kernel⟩
  | ⟨2, _⟩ => ⟨10, by decide +kernel⟩

theorem continuing_children_actual_ids :
    leftContinuingChildren.map (cursorAtomID source) = [some 4, some 5, some 9] ∧
      rightContinuingChildren.map (cursorAtomID source) = [some 7, some 8, some 10] := ⟨rfl, rfl⟩

theorem continuing_children_actual_coordinates :
    leftContinuingChildren.map (fun cursor => (cursor.occurrence.1.address, cursor.occurrence.1.remaining)) =
      [([2, 0], 0), ([2, 1], 0), ([2, 2], 0)] ∧
    rightContinuingChildren.map (fun cursor => (cursor.occurrence.1.address, cursor.occurrence.1.remaining)) =
      [([3, 0], 0), ([3, 1], 0), ([3, 2], 0)] := ⟨rfl, rfl⟩

theorem leftContinuingChild_real_current (slot : Fin 3) :
    (leftContinuingChildAt slot).occurrence.1.node.provenance = .realAtom ∧
      (leftContinuingChildAt slot).occurrence.1.node.current? = some (leftContinuingAtom slot) := by
  fin_cases slot <;> exact ⟨rfl, rfl⟩

theorem rightContinuingChild_real_current (slot : Fin 3) :
    (rightContinuingChildAt slot).occurrence.1.node.provenance = .realAtom ∧
      (rightContinuingChildAt slot).occurrence.1.node.current? = some (rightContinuingAtom slot) := by
  fin_cases slot <;> exact ⟨rfl, rfl⟩

theorem leftContinuingAtom_not_center (slot : Fin 3) :
    leftContinuingAtom slot ∉ source.aromaticCanonicalTetrahedralCenterSet := by
  intro perceived
  have eligible := ((source.mem_aromaticCanonicalTetrahedralCenterSet_iff _).mp perceived).1
  have ineligible : ¬source.ConnectivityOnlyTetrahedralCenterAtom (leftContinuingAtom slot) := by
    unfold ConnectivityOnlyTetrahedralCenterAtom
    fin_cases slot <;> decide +kernel
  exact ineligible eligible

theorem rightContinuingAtom_not_center (slot : Fin 3) :
    rightContinuingAtom slot ∉ source.aromaticCanonicalTetrahedralCenterSet := by
  intro perceived
  have eligible := ((source.mem_aromaticCanonicalTetrahedralCenterSet_iff _).mp perceived).1
  have ineligible : ¬source.ConnectivityOnlyTetrahedralCenterAtom (rightContinuingAtom slot) := by
    unfold ConnectivityOnlyTetrahedralCenterAtom
    fin_cases slot <;> decide +kernel
  exact ineligible eligible

theorem leftContinuingChild_center_none (slot : Fin 3) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? (leftContinuingChildAt slot).occurrence = none := by
  classical
  unfold aromaticCanonicalOccurrenceTetrahedralCenter?
  rw [dif_pos (leftContinuingChild_real_current slot).1, (leftContinuingChild_real_current slot).2]
  simp [leftContinuingAtom_not_center slot]

theorem rightContinuingChild_center_none (slot : Fin 3) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? (rightContinuingChildAt slot).occurrence = none := by
  classical
  unfold aromaticCanonicalOccurrenceTetrahedralCenter?
  rw [dif_pos (rightContinuingChild_real_current slot).1, (rightContinuingChild_real_current slot).2]
  simp [rightContinuingAtom_not_center slot]

theorem leftContinuingChild_state_none (slot : Fin 3) :
    drawingScheduledState (leftContinuingChildAt slot).occurrence = none :=
  occurrenceOrdinaryModel_eq_none_of_center_none source drawingScheduledState
    drawingScheduledState_cipModel _ (leftContinuingChild_center_none slot)

theorem rightContinuingChild_state_none (slot : Fin 3) :
    drawingScheduledState (rightContinuingChildAt slot).occurrence = none :=
  occurrenceOrdinaryModel_eq_none_of_center_none source drawingScheduledState
    drawingScheduledState_cipModel _ (rightContinuingChild_center_none slot)

theorem central_dependency_label_none_of_state_none
    (cursor : source.AromaticCanonicalRerootCursor branchCarrierFuel)
    (absent : drawingScheduledState cursor.occurrence = none) :
    source.aromaticCanonicalDependencyLabel centralTarget centralView cursor = none := by
  unfold aromaticCanonicalDependencyLabel
  split
  · exact absent
  · rfl

theorem leftContinuingChild_central_dependency_none (slot : Fin 3) :
    source.aromaticCanonicalDependencyLabel centralTarget centralView (leftContinuingChildAt slot) = none :=
  central_dependency_label_none_of_state_none _ (leftContinuingChild_state_none slot)

theorem rightContinuingChild_central_dependency_none (slot : Fin 3) :
    source.aromaticCanonicalDependencyLabel centralTarget centralView (rightContinuingChildAt slot) = none :=
  central_dependency_label_none_of_state_none _ (rightContinuingChild_state_none slot)

private theorem halogenAtom_not_center (atom : source.AromaticCanonicalAtom)
    (ineligible : ¬source.ConnectivityOnlyTetrahedralCenterAtom atom) :
    atom ∉ source.aromaticCanonicalTetrahedralCenterSet := by
  intro perceived
  exact ineligible ((source.mem_aromaticCanonicalTetrahedralCenterSet_iff atom).mp perceived).1

theorem central_fluorine_center_none :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? (centralRootAt 0).occurrence = none := by
  classical
  have notCenter : (⟨0, by decide +kernel⟩ : source.AromaticCanonicalAtom) ∉
      source.aromaticCanonicalTetrahedralCenterSet :=
    halogenAtom_not_center _ (by unfold ConnectivityOnlyTetrahedralCenterAtom; decide +kernel)
  unfold aromaticCanonicalOccurrenceTetrahedralCenter?
  rw [dif_pos (show (centralRootAt 0).occurrence.1.node.provenance = .realAtom from rfl),
    (show (centralRootAt 0).occurrence.1.node.current? =
      some (⟨0, by decide +kernel⟩ : source.AromaticCanonicalAtom) from rfl)]
  dsimp only
  rw [dif_neg notCenter]

theorem central_chlorine_center_none :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? (centralRootAt 1).occurrence = none := by
  classical
  have notCenter : (⟨2, by decide +kernel⟩ : source.AromaticCanonicalAtom) ∉
      source.aromaticCanonicalTetrahedralCenterSet :=
    halogenAtom_not_center _ (by unfold ConnectivityOnlyTetrahedralCenterAtom; decide +kernel)
  unfold aromaticCanonicalOccurrenceTetrahedralCenter?
  rw [dif_pos (show (centralRootAt 1).occurrence.1.node.provenance = .realAtom from rfl),
    (show (centralRootAt 1).occurrence.1.node.current? =
      some (⟨2, by decide +kernel⟩ : source.AromaticCanonicalAtom) from rfl)]
  dsimp only
  rw [dif_neg notCenter]

theorem central_halogen_states_none :
    drawingScheduledState (centralRootAt 0).occurrence = none ∧
      drawingScheduledState (centralRootAt 1).occurrence = none :=
  ⟨occurrenceOrdinaryModel_eq_none_of_center_none source drawingScheduledState
      drawingScheduledState_cipModel _ central_fluorine_center_none,
    occurrenceOrdinaryModel_eq_none_of_center_none source drawingScheduledState
      drawingScheduledState_cipModel _ central_chlorine_center_none⟩

theorem central_halogen_dependency_labels_none :
    source.aromaticCanonicalDependencyLabel centralTarget centralView (centralRootAt 0) = none ∧
      source.aromaticCanonicalDependencyLabel centralTarget centralView (centralRootAt 1) = none :=
  ⟨central_dependency_label_none_of_state_none _ central_halogen_states_none.1,
    central_dependency_label_none_of_state_none _ central_halogen_states_none.2⟩

theorem leftContinuingChild_children_empty (slot : Fin 3) :
    source.aromaticCanonicalRerootChildren (leftContinuingChildAt slot) = [] := by
  fin_cases slot <;> rfl

theorem rightContinuingChild_children_empty (slot : Fin 3) :
    source.aromaticCanonicalRerootChildren (rightContinuingChildAt slot) = [] := by
  fin_cases slot <;> rfl

/-- Actual root-label vector consumed by the central compound-key compiler.  The daughter labels
are the corrected ones: left `S`, right `R`. -/
theorem central_actual_dependency_label_vector :
    centralRoots.map (source.aromaticCanonicalDependencyLabel centralTarget centralView) =
      [none, none, some (.chiral RS.S), some (.chiral RS.R)] := by
  change [source.aromaticCanonicalDependencyLabel centralTarget centralView (centralRootAt 0),
    source.aromaticCanonicalDependencyLabel centralTarget centralView (centralRootAt 1),
    source.aromaticCanonicalDependencyLabel centralTarget centralView
      (centralRootAt ⟨2, by decide +kernel⟩),
    source.aromaticCanonicalDependencyLabel centralTarget centralView
      (centralRootAt ⟨3, by decide +kernel⟩)] = _
  rw [central_halogen_dependency_labels_none.1, central_halogen_dependency_labels_none.2,
    central_left_dependency_label_R, central_right_dependency_label_S]

end TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource
