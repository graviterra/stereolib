import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyNonvacuityRightEvidence
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3AutomorphismNaturality
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule45ReflectionNaturality

set_option autoImplicit false

namespace TetraStereo.OneCenter.IUPACNormativeProvision
namespace Rule45CanonicalFamilyNonvacuity

open AuthoritativeChemicalInput
open CertifiedLocalizedCIPInput

noncomputable def branchSwapRerootCursor
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.AromaticCanonicalRerootCursor carrierFuel :=
  { occurrence := branchSwapOccurrencePermutation cursor.occurrence
    previous? := cursor.previous?.map branchSwapOccurrencePermutation }

theorem source_aromaticMancudeEdgeSetExact :
    source.molecule.SemanticAromaticMancudeEdgeSetExact source.molecule := by
  exact (source.molecule.semanticAromaticMancudeEdgeSetExact?_eq_true_iff
    source.molecule).mp (by decide)

theorem central_key_canonical (position : Fin 4) :
    source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
      partition.frame.rule3Frame.excluded target view ruleFuel (rootAt position)
        (partition.frame.keyAt position) := by
  have pointwise := partition_canonical.1.2.2.2.1
  exact pointwise.get
    (by rw [roots_length]; exact position.2)
    (by rw [partition.frame.keysLength]; exact position.2)

set_option maxRecDepth 10000 in
theorem central_dependency_label_two :
    source.aromaticCanonicalDependencyLabel target view (rootAt positionTwo) =
      some (.chiral .S) := by
  unfold AuthoritativeChemicalInput.aromaticCanonicalDependencyLabel
  have dependency : source.AromaticCanonicalDepthDependency
      (rootAt positionTwo).occurrence target := by
    exact ⟨rfl, by decide⟩
  rw [dif_pos dependency]
  change state (rootAt positionTwo).occurrence = some (.chiral .S)
  change state leftOccurrence = some (.chiral .S)
  exact left_state_chiral_S

set_option maxRecDepth 10000 in
theorem central_dependency_label_three :
    source.aromaticCanonicalDependencyLabel target view (rootAt positionThree) =
      some (.chiral .R) := by
  unfold AuthoritativeChemicalInput.aromaticCanonicalDependencyLabel
  have dependency : source.AromaticCanonicalDepthDependency
      (rootAt positionThree).occurrence target := by
    exact ⟨rfl, by decide⟩
  rw [dif_pos dependency]
  change state (rootAt positionThree).occurrence = some (.chiral .R)
  change state rightOccurrence = some (.chiral .R)
  exact right_state_chiral_R

set_option maxRecDepth 10000 in
theorem branchSwapRerootCursor_maps_central_two :
    branchSwapRerootCursor (rootAt positionTwo) = rootAt positionThree := by
  apply AuthoritativeChemicalInput.AromaticCanonicalRerootCursor.ext
  · exact branchSwapOccurrencePermutation_maps_leftOccurrence
  · rfl

set_option maxRecDepth 10000 in
theorem branchSwapRerootCursor_node
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    (branchSwapRerootCursor cursor).occurrence.1.node =
      mapAromaticCanonicalOfficialCIPNode branchSwapAtomPermutation
        cursor.occurrence.1.node := by
  rfl

set_option maxRecDepth 10000 in
theorem seed_left_children_length :
    (source.aromaticCanonicalRerootChildren (rootAt positionTwo)).length = 3 := by rfl

set_option maxRecDepth 10000 in
theorem seed_right_children_length :
    (source.aromaticCanonicalRerootChildren (rootAt positionThree)).length = 3 := by rfl

def seedPositionZero : Fin 3 := ⟨0, by decide⟩
def seedPositionOne : Fin 3 := ⟨1, by decide⟩
def seedPositionTwo : Fin 3 := ⟨2, by decide⟩

noncomputable def seedLeftChildAt (position : Fin 3) :=
  (source.aromaticCanonicalRerootChildren (rootAt positionTwo)).get
    (Fin.cast seed_left_children_length.symm position)

noncomputable def seedRightChildAt (position : Fin 3) :=
  (source.aromaticCanonicalRerootChildren (rootAt positionThree)).get
    (Fin.cast seed_right_children_length.symm position)

theorem list_eq_three_get {α : Type*} (values : List α)
    (length : values.length = 3) :
    values = [values.get (Fin.cast length.symm seedPositionZero),
      values.get (Fin.cast length.symm seedPositionOne),
      values.get (Fin.cast length.symm seedPositionTwo)] := by
  rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
  all_goals simp at length
  subst tail
  rfl

theorem seedLeftChildren_explicit :
    source.aromaticCanonicalRerootChildren (rootAt positionTwo) =
      [seedLeftChildAt seedPositionZero, seedLeftChildAt seedPositionOne,
        seedLeftChildAt seedPositionTwo] :=
  list_eq_three_get _ seed_left_children_length

theorem seedRightChildren_explicit :
    source.aromaticCanonicalRerootChildren (rootAt positionThree) =
      [seedRightChildAt seedPositionZero, seedRightChildAt seedPositionOne,
        seedRightChildAt seedPositionTwo] :=
  list_eq_three_get _ seed_right_children_length

set_option maxRecDepth 10000 in
theorem branchSwapRerootCursor_maps_seedChildAt (position : Fin 3) :
    branchSwapRerootCursor (seedLeftChildAt position) = seedRightChildAt position := by
  fin_cases position <;>
    apply AuthoritativeChemicalInput.AromaticCanonicalRerootCursor.ext
  all_goals rfl

def seedLeftChildAtom : Fin 3 → source.AromaticCanonicalAtom
  | ⟨0, _⟩ => ⟨4, by decide⟩
  | ⟨1, _⟩ => ⟨5, by decide⟩
  | ⟨2, _⟩ => ⟨9, by decide⟩

def seedRightChildAtom : Fin 3 → source.AromaticCanonicalAtom
  | ⟨0, _⟩ => ⟨7, by decide⟩
  | ⟨1, _⟩ => ⟨8, by decide⟩
  | ⟨2, _⟩ => ⟨10, by decide⟩

set_option maxRecDepth 10000 in
theorem seedLeftChild_real_current (position : Fin 3) :
    (seedLeftChildAt position).occurrence.1.node.provenance = .realAtom ∧
      (seedLeftChildAt position).occurrence.1.node.current? =
        some (seedLeftChildAtom position) := by
  fin_cases position <;> exact ⟨rfl, rfl⟩

set_option maxRecDepth 10000 in
theorem seedRightChild_real_current (position : Fin 3) :
    (seedRightChildAt position).occurrence.1.node.provenance = .realAtom ∧
      (seedRightChildAt position).occurrence.1.node.current? =
        some (seedRightChildAtom position) := by
  fin_cases position <;> exact ⟨rfl, rfl⟩

theorem seedLeftChildAtom_not_eligible (position : Fin 3) :
    ¬ source.ConnectivityOnlyTetrahedralCenterAtom (seedLeftChildAtom position) := by
  unfold AuthoritativeChemicalInput.ConnectivityOnlyTetrahedralCenterAtom
  fin_cases position <;> decide

theorem seedLeftChildAtom_not_center (position : Fin 3) :
    seedLeftChildAtom position ∉ source.aromaticCanonicalTetrahedralCenterSet := by
  intro detected
  exact seedLeftChildAtom_not_eligible position
    ((source.mem_aromaticCanonicalTetrahedralCenterSet_iff _).mp detected).1

theorem seedRightChildAtom_not_eligible (position : Fin 3) :
    ¬ source.ConnectivityOnlyTetrahedralCenterAtom (seedRightChildAtom position) := by
  unfold AuthoritativeChemicalInput.ConnectivityOnlyTetrahedralCenterAtom
  fin_cases position <;> decide

theorem seedRightChildAtom_not_center (position : Fin 3) :
    seedRightChildAtom position ∉ source.aromaticCanonicalTetrahedralCenterSet := by
  intro detected
  exact seedRightChildAtom_not_eligible position
    ((source.mem_aromaticCanonicalTetrahedralCenterSet_iff _).mp detected).1

set_option maxRecDepth 10000 in
theorem seedLeftChild_center_none (position : Fin 3) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter?
      (seedLeftChildAt position).occurrence = none := by
  classical
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceTetrahedralCenter?
  rw [dif_pos (seedLeftChild_real_current position).1,
    (seedLeftChild_real_current position).2]
  simp [seedLeftChildAtom_not_center position]

set_option maxRecDepth 10000 in
theorem seedRightChild_center_none (position : Fin 3) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter?
      (seedRightChildAt position).occurrence = none := by
  classical
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceTetrahedralCenter?
  rw [dif_pos (seedRightChild_real_current position).1,
    (seedRightChild_real_current position).2]
  simp [seedRightChildAtom_not_center position]

theorem seedLeftChild_state_none (position : Fin 3) :
    state (seedLeftChildAt position).occurrence = none :=
  source.aromaticCanonicalOccurrenceRule3Through5Model_eq_none_of_no_center
    state (source.aromaticCanonicalScheduledAuxiliaryState_cipModel semantics)
      _ (seedLeftChild_center_none position)

theorem seedRightChild_state_none (position : Fin 3) :
    state (seedRightChildAt position).occurrence = none :=
  source.aromaticCanonicalOccurrenceRule3Through5Model_eq_none_of_no_center
    state (source.aromaticCanonicalScheduledAuxiliaryState_cipModel semantics)
      _ (seedRightChild_center_none position)

set_option maxRecDepth 10000 in
theorem seedLeftChild_children_empty (position : Fin 3) :
    source.aromaticCanonicalRerootChildren (seedLeftChildAt position) = [] := by
  fin_cases position <;> rfl

set_option maxRecDepth 10000 in
theorem seedRightChild_children_empty (position : Fin 3) :
    source.aromaticCanonicalRerootChildren (seedRightChildAt position) = [] := by
  fin_cases position <;> rfl

theorem seedLeftChild_dependencyLabel_none (position : Fin 3) :
    source.aromaticCanonicalDependencyLabel target view (seedLeftChildAt position) = none := by
  unfold AuthoritativeChemicalInput.aromaticCanonicalDependencyLabel
  have dependency : source.AromaticCanonicalDepthDependency
      (seedLeftChildAt position).occurrence target := by
    fin_cases position <;> exact ⟨rfl, by decide⟩
  rw [dif_pos dependency]
  change state (seedLeftChildAt position).occurrence = none
  exact seedLeftChild_state_none position

theorem seedRightChild_dependencyLabel_none (position : Fin 3) :
    source.aromaticCanonicalDependencyLabel target view (seedRightChildAt position) = none := by
  unfold AuthoritativeChemicalInput.aromaticCanonicalDependencyLabel
  have dependency : source.AromaticCanonicalDepthDependency
      (seedRightChildAt position).occurrence target := by
    fin_cases position <;> exact ⟨rfl, by decide⟩
  rw [dif_pos dependency]
  change state (seedRightChildAt position).occurrence = none
  exact seedRightChild_state_none position

theorem declarative_rerootChildren_eq_nil_of_actual
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (children : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (canonical : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
    (actual : source.aromaticCanonicalRerootChildren cursor = []) : children = [] := by
  have actualCanonical := (source.aromaticCanonicalRerootChildren_sound cursor).1
  rw [actual] at actualCanonical
  have mapped : children.map (fun child => child.occurrence.1) = [] :=
    canonical.1.trans actualCanonical.symm
  exact List.length_eq_zero_iff.mp (by simpa using congrArg List.length mapped)

theorem declarative_rerootChildren_eq_actual
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (children : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (canonical : source.DeclarativeAromaticCanonicalRerootChildren cursor children) :
    children = source.aromaticCanonicalRerootChildren cursor := by
  have computed := (source.aromaticCanonicalRerootChildren?_eq_some_iff
    cursor children).mpr canonical
  simpa [AuthoritativeChemicalInput.aromaticCanonicalRerootChildren?] using computed.symm

set_option maxRecDepth 10000 in
theorem seedChild_cumulative_reflection
    (position : Fin 3) (stage : LocalizedCumulativeRule45Stage)
    (leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key)
    (leftCanonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      stage target view 3 (seedLeftChildAt position) leftKey)
    (rightCanonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      (reflectedRule4bcStage stage) target view 3
        (seedRightChildAt position) rightKey) :
    source.AromaticCanonicalCumulativeRule45UppercaseReflection leftKey rightKey := by
  cases leftCanonical with
  | terminal leftFrame _ leftObserved =>
      cases rightCanonical with
      | terminal rightFrame _ rightObserved =>
          have leftLabel := (source.aromaticCanonicalDependencyLabel_eq_iff
            target view (seedLeftChildAt position) _).mpr leftObserved
          have rightLabel := (source.aromaticCanonicalDependencyLabel_eq_iff
            target view (seedRightChildAt position) _).mpr rightObserved
          rw [seedLeftChild_dependencyLabel_none position] at leftLabel
          rw [seedRightChild_dependencyLabel_none position] at rightLabel
          subst_vars
          constructor
          · have natural := exactOfficialRule1aObservation_natural_of_constitution_of_no_edges
              source branchSwapAtomPermutation branchSwapAtomPermutation_constitution
                source_aromaticMancudeEdgeSetExact source_no_aromatic_edges
                  (seedLeftChildAt position).occurrence.1.node
            rw [← branchSwapRerootCursor_maps_seedChildAt position,
              branchSwapRerootCursor_node]
            simpa [MoleculeGraph.exactOfficialRuleMajorRootKey,
              ExactOfficialRuleMajorKey.observedRule1aLayers,
              OfficialRuleMajorKey.mapSourceLayers,
              OfficialRuleMajorKey.mapObservation,
              source.molecule.semanticExactOfficialRule1aObservation_eq_independent]
                using natural.symm
          · have natural := rule1bRootDistance_mapAromaticCanonicalOfficialCIPNode
              branchSwapAtomPermutation (seedLeftChildAt position).occurrence.1.node
            rw [← branchSwapRerootCursor_maps_seedChildAt position,
              branchSwapRerootCursor_node]
            simpa [MoleculeGraph.exactOfficialRuleMajorRootKey,
              ExactOfficialRuleMajorKey.rule1bLayers,
              OfficialRuleMajorKey.mapSourceLayers,
              OfficialRuleMajorKey.mapObservation] using natural.symm
          · have natural := officialNodeRule2_natural_of_constitution source
              branchSwapAtomPermutation branchSwapAtomPermutation_constitution
                (seedLeftChildAt position).occurrence.1.node
            rw [← branchSwapRerootCursor_maps_seedChildAt position,
              branchSwapRerootCursor_node]
            simpa [MoleculeGraph.exactOfficialRuleMajorRootKey,
              ExactOfficialRuleMajorKey.rule2Layers,
              OfficialRuleMajorKey.mapSourceLayers,
              OfficialRuleMajorKey.mapObservation] using natural.symm
          · exact congrArg (fun priority => [[([], priority)]])
              (localizedCumulativeRule45Priority_reflectedRule4bcStage stage none).symm
          · rfl
          · rfl
      | branch rightFrame rightNonempty _ _ _ =>
          exact (rightNonempty (declarative_rerootChildren_eq_nil_of_actual _ _
            rightFrame (seedRightChild_children_empty position))).elim
  | branch leftFrame leftNonempty _ _ _ =>
      exact (leftNonempty (declarative_rerootChildren_eq_nil_of_actual _ _
        leftFrame (seedLeftChild_children_empty position))).elim

theorem seedChildKeyLists_reflection
    (stage : LocalizedCumulativeRule45Stage)
    {leftKeys rightKeys : List source.AromaticCanonicalCumulativeRule45Key}
    (leftCanonical : source.CanonicalAromaticCanonicalCumulativeRule45KeyList
      stage target view 3
        (source.aromaticCanonicalRerootChildren (rootAt positionTwo)) leftKeys)
    (rightCanonical : source.CanonicalAromaticCanonicalCumulativeRule45KeyList
      (reflectedRule4bcStage stage) target view 3
        (source.aromaticCanonicalRerootChildren (rootAt positionThree)) rightKeys) :
    List.Forall₂ source.AromaticCanonicalCumulativeRule45UppercaseReflection
      leftKeys rightKeys := by
  rw [seedLeftChildren_explicit] at leftCanonical
  rw [seedRightChildren_explicit] at rightCanonical
  cases leftCanonical with
  | cons leftZero leftTail =>
    cases leftTail with
    | cons leftOne leftTail =>
      cases leftTail with
      | cons leftTwo leftTail =>
        cases leftTail
        cases rightCanonical with
        | cons rightZero rightTail =>
          cases rightTail with
          | cons rightOne rightTail =>
            cases rightTail with
            | cons rightTwo rightTail =>
              cases rightTail
              exact .cons
                (seedChild_cumulative_reflection seedPositionZero stage _ _
                  leftZero rightZero) <| .cons
                (seedChild_cumulative_reflection seedPositionOne stage _ _
                  leftOne rightOne) <| .cons
                (seedChild_cumulative_reflection seedPositionTwo stage _ _
                  leftTwo rightTwo) .nil

end Rule45CanonicalFamilyNonvacuity
end TetraStereo.OneCenter.IUPACNormativeProvision
