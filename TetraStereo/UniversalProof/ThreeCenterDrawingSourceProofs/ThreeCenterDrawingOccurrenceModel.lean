import TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceDescriptorConstruction

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# The actual scheduled occurrence model of the three-center drawing source

The new source's carrier is reconstructed at central atom 1. The daughter targets retain root 1,
addresses [2]/[3] and actual incoming/outgoing histories. Source constitution and perception
facts are reused; no old occurrence, spatial descriptor or auxiliary model label is transferred.
The actual drawing geometry constructs daughter `S`/`R` for every restricted view, then the causal
model supplies those values to the original central dependency view. The downstream decisive
Rule-4/5 comparison and the central pseudoasymmetric descriptor remain separate obligations.

Calibration: negative priority-ordered oriented volume is `R` and positive is `S`.  The left
daughter priority-ordered volume is `+6` (label `S`); the right daughter volume is `-6` (label
`R`).  Identifiers such as `left_occurrence_drawing_descriptor_R` and
`centralView_reads_left_R` are kernel-certificate-pinned historical API keys: they retain their
names, now carry the corrected statements, and have accurately named aliases for new code.
-/

def branchCarrierFuel : Nat := 1

def centralPerceivedCenter : source.AromaticCanonicalTetrahedralCenter :=
  ⟨IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.center.1,
    IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.center.2⟩

def leftPerceivedCenter : source.AromaticCanonicalTetrahedralCenter :=
  ⟨IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.leftCenter.1,
    IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.leftCenter.2⟩

def rightPerceivedCenter : source.AromaticCanonicalTetrahedralCenter :=
  ⟨IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.rightCenter.1,
    IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.rightCenter.2⟩

noncomputable def centralTarget : source.AromaticCanonicalOccurrence branchCarrierFuel :=
  source.aromaticCanonicalFinalOccurrence branchCarrierFuel centralPerceivedCenter

noncomputable def centralRoots : List (source.AromaticCanonicalRerootCursor branchCarrierFuel) :=
  source.aromaticCanonicalRerootChildren { occurrence := centralTarget, previous? := none }

theorem central_roots_length : centralRoots.length = 4 := by rfl

noncomputable def centralRootAt (slot : Fin 4) :=
  centralRoots.get (Fin.cast central_roots_length.symm slot)

noncomputable def leftOccurrence : source.AromaticCanonicalOccurrence branchCarrierFuel :=
  (centralRootAt ⟨2, by decide +kernel⟩).occurrence

noncomputable def rightOccurrence : source.AromaticCanonicalOccurrence branchCarrierFuel :=
  (centralRootAt ⟨3, by decide +kernel⟩).occurrence

noncomputable def leftRoots : List (source.AromaticCanonicalRerootCursor branchCarrierFuel) :=
  source.aromaticCanonicalRerootChildren { occurrence := leftOccurrence, previous? := none }

noncomputable def rightRoots : List (source.AromaticCanonicalRerootCursor branchCarrierFuel) :=
  source.aromaticCanonicalRerootChildren { occurrence := rightOccurrence, previous? := none }

theorem central_root_ids :
    centralRoots.map (cursorAtomID source) = [some 0, some 2, some 3, some 6] := rfl

theorem central_root_ids_perm_written_endpoints :
    (centralRoots.map (cursorAtomID source)).Perm (centralFrame.endpoints.map some) := by
  rw [central_root_ids, actual_endpoint_orders.1]
  exact List.Perm.refl _

theorem central_perceived_center_recovered :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? centralTarget = some centralPerceivedCenter :=
  occurrenceTetrahedralCenter?_final source branchCarrierFuel centralPerceivedCenter

theorem daughter_roots_length : leftRoots.length = 4 ∧ rightRoots.length = 4 :=
  ⟨rfl, rfl⟩

noncomputable def leftRootAt (slot : Fin 4) :=
  leftRoots.get (Fin.cast daughter_roots_length.1.symm slot)

noncomputable def rightRootAt (slot : Fin 4) :=
  rightRoots.get (Fin.cast daughter_roots_length.2.symm slot)

noncomputable def leftBase : source.AromaticCanonicalOccurrenceFourLigandFrame branchCarrierFuel :=
  { roots := leftRoots, rootsLength := daughter_roots_length.1 }

noncomputable def rightBase : source.AromaticCanonicalOccurrenceFourLigandFrame branchCarrierFuel :=
  { roots := rightRoots, rootsLength := daughter_roots_length.2 }

theorem actual_occurrence_coordinates :
    centralTarget.1.root.val = 1 ∧ centralTarget.1.address = [] ∧
      leftOccurrence.1.root.val = 1 ∧ leftOccurrence.1.address = [2] ∧
      rightOccurrence.1.root.val = 1 ∧ rightOccurrence.1.address = [3] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem actual_occurrence_nodes :
    leftOccurrence.1.node.provenance = .realAtom ∧
      leftOccurrence.1.node.current? = some leftCenter ∧
      rightOccurrence.1.node.provenance = .realAtom ∧
      rightOccurrence.1.node.current? = some rightCenter := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem daughter_centers_recovered :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? leftOccurrence = some leftPerceivedCenter ∧
      source.aromaticCanonicalOccurrenceTetrahedralCenter? rightOccurrence = some rightPerceivedCenter := by
  classical
  constructor
  · unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceTetrahedralCenter?
    rw [dif_pos actual_occurrence_nodes.1, actual_occurrence_nodes.2.1]
    change (if h : leftCenter ∈ source.aromaticCanonicalTetrahedralCenterSet then
      some ⟨leftCenter, h⟩ else none) = some leftPerceivedCenter
    rw [dif_pos (show leftCenter ∈ source.aromaticCanonicalTetrahedralCenterSet from
      leftPerceivedCenter.2)]
    rfl
  · unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceTetrahedralCenter?
    rw [dif_pos actual_occurrence_nodes.2.2.1, actual_occurrence_nodes.2.2.2]
    change (if h : rightCenter ∈ source.aromaticCanonicalTetrahedralCenterSet then
      some ⟨rightCenter, h⟩ else none) = some rightPerceivedCenter
    rw [dif_pos (show rightCenter ∈ source.aromaticCanonicalTetrahedralCenterSet from
      rightPerceivedCenter.2)]
    rfl

theorem actual_ligand_frames :
    source.aromaticCanonicalOccurrenceLigandFrame? centralTarget = some centralRoots ∧
      source.aromaticCanonicalOccurrenceLigandFrame? leftOccurrence = some leftRoots ∧
      source.aromaticCanonicalOccurrenceLigandFrame? rightOccurrence = some rightRoots :=
  ⟨rfl, rfl, rfl⟩

theorem actual_four_ligand_frames :
    source.aromaticCanonicalOccurrenceFourLigandFrame? leftOccurrence = some leftBase ∧
      source.aromaticCanonicalOccurrenceFourLigandFrame? rightOccurrence = some rightBase :=
  ⟨rfl, rfl⟩

theorem daughter_roots_valid :
    (∀ cursor ∈ leftRoots, source.AromaticCanonicalRerootCursorValid cursor) ∧
      (∀ cursor ∈ rightRoots, source.AromaticCanonicalRerootCursorValid cursor) :=
  ⟨source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid
      leftOccurrence leftRoots actual_ligand_frames.2.1,
    source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid
      rightOccurrence rightRoots actual_ligand_frames.2.2⟩

theorem daughter_root_ids :
    leftRoots.map (cursorAtomID source) = [some 1, some 4, some 5, some 9] ∧
      rightRoots.map (cursorAtomID source) = [some 1, some 7, some 8, some 10] :=
  ⟨rfl, rfl⟩

theorem daughter_root_ids_perm_written_endpoints :
    (leftRoots.map (cursorAtomID source)).Perm (leftFrame.endpoints.map some) ∧
      (rightRoots.map (cursorAtomID source)).Perm (rightFrame.endpoints.map some) := by
  rw [daughter_root_ids.1, daughter_root_ids.2]
  decide +kernel

theorem daughter_root_nodes_real (slot : Fin 4) :
    (leftRootAt slot).occurrence.1.node.provenance = .realAtom ∧
      (rightRootAt slot).occurrence.1.node.provenance = .realAtom := by
  fin_cases slot <;> exact ⟨rfl, rfl⟩

theorem actual_daughter_root_histories :
    leftRoots.map (fun cursor => cursor.occurrence.1.node.history.map Fin.val) =
        [[1], [4, 3, 1], [5, 3, 1], [9, 3, 1]] ∧
      rightRoots.map (fun cursor => cursor.occurrence.1.node.history.map Fin.val) =
        [[1], [7, 6, 1], [8, 6, 1], [10, 6, 1]] :=
  ⟨rfl, rfl⟩

theorem source_no_ordinary_double_bond : source.NoAromaticCanonicalOrdinaryDoubleBond :=
  IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.source_no_ordinary_double_bond


/-- Actual daughter nodes have real current atoms; their existing long histories are preserved. -/
theorem left_roots_real : OccurrenceRootsReal source leftBase := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

theorem right_roots_real : OccurrenceRootsReal source rightBase := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

/-- Drawing-only `S` seed at root 1, address [2], for every restricted deeper dependency view.
Historical API key: the old suffix says `R`; the corrected statement is `S`. -/
theorem left_occurrence_drawing_descriptor_R
    (view : source.AromaticCanonicalDependencyView leftOccurrence) :
    occurrenceOrdinaryDescriptor? source leftOccurrence view 4 = some (.chiral RS.S) := by
  exact occurrenceOrdinaryDescriptor?_eq_chiral_of_written_priority source leftOccurrence view
    leftPerceivedCenter daughter_centers_recovered.1 leftBase actual_ligand_frames.2.1
    leftFrame left_source_frame left_roots_real daughter_root_ids_perm_written_endpoints.1
    left_endpoint_atomic_separation source_no_ordinary_double_bond writtenPriorityOrder
    written_priority_is_actual_atomic_order.1 written_priority_is_actual_atomic_order.2.1
    RS.S actual_sorted_source_geometry.1

/-- Accurate-name alias for the left daughter drawing seed. -/
theorem left_occurrence_drawing_descriptor_S
    (view : source.AromaticCanonicalDependencyView leftOccurrence) :
    occurrenceOrdinaryDescriptor? source leftOccurrence view 4 = some (.chiral RS.S) :=
  left_occurrence_drawing_descriptor_R view

/-- Drawing-only `R` seed at root 1, address [3], without importing the old spatial label.
Historical API key: the old suffix says `S`; the corrected statement is `R`. -/
theorem right_occurrence_drawing_descriptor_S
    (view : source.AromaticCanonicalDependencyView rightOccurrence) :
    occurrenceOrdinaryDescriptor? source rightOccurrence view 4 = some (.chiral RS.R) := by
  exact occurrenceOrdinaryDescriptor?_eq_chiral_of_written_priority source rightOccurrence view
    rightPerceivedCenter daughter_centers_recovered.2 rightBase actual_ligand_frames.2.2
    rightFrame right_source_frame right_roots_real daughter_root_ids_perm_written_endpoints.2
    right_endpoint_atomic_separation source_no_ordinary_double_bond writtenPriorityOrder
    written_priority_is_actual_atomic_order.1 written_priority_is_actual_atomic_order.2.2
    RS.R actual_sorted_source_geometry.2

/-- Accurate-name alias for the right daughter drawing seed. -/
theorem right_occurrence_drawing_descriptor_R
    (view : source.AromaticCanonicalDependencyView rightOccurrence) :
    occurrenceOrdinaryDescriptor? source rightOccurrence view 4 = some (.chiral RS.R) :=
  right_occurrence_drawing_descriptor_S view

noncomputable def drawingScheduledState : source.AromaticCanonicalAuxiliaryState branchCarrierFuel :=
  occurrenceOrdinaryScheduledState source branchCarrierFuel 4

theorem drawingScheduledState_cipModel :
    (source.aromaticCanonicalOccurrenceSystem
      (occurrenceOrdinaryAuxiliarySemantics source branchCarrierFuel 4)).CIPModel drawingScheduledState :=
  occurrenceOrdinaryScheduledState_cipModel source branchCarrierFuel 4

/-- The causal model constructs a nonfinal drawing seed `S`; no auxiliary label is supplied.
Historical API key with corrected statement. -/
theorem left_scheduled_drawing_R : drawingScheduledState leftOccurrence = some (.chiral RS.S) := by
  have fixed := occurrenceOrdinaryModel_evaluates source drawingScheduledState
    drawingScheduledState_cipModel leftOccurrence
  rw [← fixed]
  exact left_occurrence_drawing_descriptor_R _

/-- Accurate-name alias for the left scheduled drawing seed. -/
theorem left_scheduled_drawing_S : drawingScheduledState leftOccurrence = some (.chiral RS.S) :=
  left_scheduled_drawing_R

/-- The causal model constructs a nonfinal drawing seed `R`; no auxiliary label is supplied.
Historical API key with corrected statement. -/
theorem right_scheduled_drawing_S : drawingScheduledState rightOccurrence = some (.chiral RS.R) := by
  have fixed := occurrenceOrdinaryModel_evaluates source drawingScheduledState
    drawingScheduledState_cipModel rightOccurrence
  rw [← fixed]
  exact right_occurrence_drawing_descriptor_S _

/-- Accurate-name alias for the right scheduled drawing seed. -/
theorem right_scheduled_drawing_R : drawingScheduledState rightOccurrence = some (.chiral RS.R) :=
  right_scheduled_drawing_S

theorem left_drawing_descriptor_independent_meaning
    (view : source.AromaticCanonicalDependencyView leftOccurrence) :
    OccurrenceOrdinaryDescriptorMeaning source leftOccurrence view 4 (.chiral RS.S) :=
  occurrenceOrdinaryDescriptor?_sound source leftOccurrence view 4 (.chiral RS.S)
    (left_occurrence_drawing_descriptor_R view)

theorem right_drawing_descriptor_independent_meaning
    (view : source.AromaticCanonicalDependencyView rightOccurrence) :
    OccurrenceOrdinaryDescriptorMeaning source rightOccurrence view 4 (.chiral RS.R) :=
  occurrenceOrdinaryDescriptor?_sound source rightOccurrence view 4 (.chiral RS.R)
    (right_occurrence_drawing_descriptor_S view)


/-- The central evaluator sees the actual internally scheduled state through a restricted view. -/
noncomputable def centralView : source.AromaticCanonicalDependencyView centralTarget :=
  source.aromaticCanonicalDependencyView drawingScheduledState centralTarget

theorem left_deeper_than_central : source.AromaticCanonicalDepthDependency leftOccurrence centralTarget :=
  ⟨rfl, by decide +kernel⟩

theorem right_deeper_than_central : source.AromaticCanonicalDepthDependency rightOccurrence centralTarget :=
  ⟨rfl, by decide +kernel⟩

/-- Historical API key with corrected statement: the central view reads the left `S` seed. -/
theorem centralView_reads_left_R :
    centralView leftOccurrence left_deeper_than_central = some (.chiral RS.S) :=
  left_scheduled_drawing_R

/-- Accurate-name alias for the central view's left seed. -/
theorem centralView_reads_left_S :
    centralView leftOccurrence left_deeper_than_central = some (.chiral RS.S) :=
  centralView_reads_left_R

/-- Historical API key with corrected statement: the central view reads the right `R` seed. -/
theorem centralView_reads_right_S :
    centralView rightOccurrence right_deeper_than_central = some (.chiral RS.R) :=
  right_scheduled_drawing_S

/-- Accurate-name alias for the central view's right seed. -/
theorem centralView_reads_right_R :
    centralView rightOccurrence right_deeper_than_central = some (.chiral RS.R) :=
  centralView_reads_right_S

/-- Actual canonical Rule-4/5 dependency-label lookup at the central left root, not an assumed
seed.  Historical API key with corrected statement (`S`). -/
theorem central_left_dependency_label_R :
    source.aromaticCanonicalDependencyLabel centralTarget centralView
      (centralRootAt ⟨2, by decide +kernel⟩) = some (.chiral RS.S) := by
  change (if dependency : source.AromaticCanonicalDepthDependency leftOccurrence centralTarget
    then centralView leftOccurrence dependency else none) = some (.chiral RS.S)
  rw [dif_pos left_deeper_than_central]
  exact centralView_reads_left_R

/-- Accurate-name alias for the central left dependency label. -/
theorem central_left_dependency_label_S :
    source.aromaticCanonicalDependencyLabel centralTarget centralView
      (centralRootAt ⟨2, by decide +kernel⟩) = some (.chiral RS.S) :=
  central_left_dependency_label_R

/-- Actual canonical Rule-4/5 dependency-label lookup at the central right root, not an assumed
seed.  Historical API key with corrected statement (`R`). -/
theorem central_right_dependency_label_S :
    source.aromaticCanonicalDependencyLabel centralTarget centralView
      (centralRootAt ⟨3, by decide +kernel⟩) = some (.chiral RS.R) := by
  change (if dependency : source.AromaticCanonicalDepthDependency rightOccurrence centralTarget
    then centralView rightOccurrence dependency else none) = some (.chiral RS.R)
  rw [dif_pos right_deeper_than_central]
  exact centralView_reads_right_S

/-- Accurate-name alias for the central right dependency label. -/
theorem central_right_dependency_label_R :
    source.aromaticCanonicalDependencyLabel centralTarget centralView
      (centralRootAt ⟨3, by decide +kernel⟩) = some (.chiral RS.R) :=
  central_right_dependency_label_S

/-- A drawing-only scheduled source with actual deeper `S`/`R` inputs. This statement establishes
no central priority order, central pseudo label, or scientific approval. -/
theorem three_center_drawing_model_has_real_auxiliary_inputs :
    source.spatial? = none ∧ diagram.atomConfigurations = [] ∧
      leftOccurrence.1.root.val = 1 ∧ leftOccurrence.1.address = [2] ∧
      rightOccurrence.1.root.val = 1 ∧ rightOccurrence.1.address = [3] ∧
      centralView leftOccurrence left_deeper_than_central = some (.chiral RS.S) ∧
      centralView rightOccurrence right_deeper_than_central = some (.chiral RS.R) :=
  ⟨source_has_only_drawing_configuration.1, source_has_only_drawing_configuration.2,
    actual_occurrence_coordinates.2.2.1, actual_occurrence_coordinates.2.2.2.1,
    actual_occurrence_coordinates.2.2.2.2.1, actual_occurrence_coordinates.2.2.2.2.2,
    centralView_reads_left_R, centralView_reads_right_S⟩

end TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource
