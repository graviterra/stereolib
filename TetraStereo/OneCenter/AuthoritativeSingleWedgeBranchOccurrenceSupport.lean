import TetraStereo.OneCenter.AuthoritativeSingleWedgeBranchSourceFixture
import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyNonvacuityRightEvidence

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.OneCenter.SingleWedgeBranchSourceFixture

open AuthoritativeChemicalInput AuthoritativeChemicalInput.SingleWedgeSource

/-!
Actual carrier coordinates on the drawing-only branch fixture. The daughters are descendants
of the central final occurrence, not fresh final occurrences. Reconstructing their reroot
frames includes the incoming central atom and preserves the longer outward histories.
Only constitution and carrier support are transported from the old spatial fixture; no
spatial descriptor, auxiliary state, or parser configuration is transported.
-/

def branchCarrierFuel : Nat := 1

def centralCenter : source.AromaticCanonicalTetrahedralCenter :=
  ⟨IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.center.1,
    IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.center.2⟩

def leftPerceivedCenter : source.AromaticCanonicalTetrahedralCenter :=
  ⟨IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.leftCenter.1,
    IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.leftCenter.2⟩

def rightPerceivedCenter : source.AromaticCanonicalTetrahedralCenter :=
  ⟨IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.rightCenter.1,
    IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.rightCenter.2⟩

noncomputable def centralTarget : source.AromaticCanonicalOccurrence branchCarrierFuel :=
  source.aromaticCanonicalFinalOccurrence branchCarrierFuel centralCenter

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

end TetraStereo.OneCenter.SingleWedgeBranchSourceFixture
