import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorOrderingKey

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TetraStereo.OneCenter.FramedDescriptorProjectedOrderingKey

open RawMolecule FrameRuntime FramedOrderingKeyCore FramedDescriptorOrderingKey

/-! Framed tied-root unary keys and Rule-4a/Rule-5 projections. Adapted from the
legacy production law proof, with every runtime query replaced by its actual shared-profile
counterpart. This module does not call a legacy branch comparator. -/

def localDescriptorStage (leftSide : Bool) (stage : RawDescriptorRuleStage) :
    RawDescriptorRuleStage :=
  if leftSide then stage.leftInternal else stage.rightInternal

def buildDenseTiedRootDescriptorKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool) (state : OccurrenceAuxState)
    (fuel : ℕ) (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (cursor : Cursor) : List Key :=
  let before := compareDescriptorBranchAt? mol profile authoritative state fuel
    (localDescriptorStage leftSide stage)
  let field := fun selected =>
    buildKey mol authoritative state before fuel selected leftSide cursor
  field .rule4a :: match stage with
    | .rule4a => []
    | .rule4b leftReference rightReference =>
        [field (.rule4b leftReference rightReference)]
    | .rule4c =>
        if state.any fun fact => !fact.uppercase then [field .rule4c] else []
    | .rule5 leftReference rightReference =>
        if state.any fun fact => !fact.uppercase then
          [field .rule4c, field (.rule5 leftReference rightReference)]
        else [field (.rule5 leftReference rightReference)]

def compareDenseTiedRootDescriptorKeys :
    List Key → List Key → Ordering :=
  List.compareLex compareKey

theorem compareDenseTiedRootDescriptorKeys_transCmp :
    Std.TransCmp compareDenseTiedRootDescriptorKeys := by
  unfold compareDenseTiedRootDescriptorKeys compareKey
  change Std.TransCmp
    (List.compareLex (List.compareLex (compare : ℕ → ℕ → Ordering)))
  infer_instance

theorem compareOccurrenceDescriptorAtTiedRoot_success_factors
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool) (state : OccurrenceAuxState) (fuel : ℕ)
    (stage : RawDescriptorRuleStage) (left right : Cursor)
    (decision : Ordering)
    (computed : compareDescriptorAtTiedRoot? mol profile authoritative state fuel stage left right =
      some decision) :
    compareDenseTiedRootDescriptorKeys
        (buildDenseTiedRootDescriptorKey mol profile authoritative state fuel stage true left)
        (buildDenseTiedRootDescriptorKey mol profile authoritative state fuel stage false right) = decision := by
  let beforeLeft := compareDescriptorBranchAt? mol profile authoritative state fuel stage.leftInternal
  let beforeRight := compareDescriptorBranchAt? mol profile authoritative state fuel stage.rightInternal
  cases rule4aEq : compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4a fuel
      [(left, right)] with
  | none =>
      simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq] at computed
  | some rule4a =>
      have rule4aFactor := rule_success_factors mol profile authoritative state
        beforeLeft beforeRight .rule4a fuel left right rule4a rule4aEq
      dsimp [beforeLeft, beforeRight] at rule4aFactor
      cases rule4a with
      | lt =>
          simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq] at computed
          subst decision
          cases stage <;>
            simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
              localDescriptorStage, rule4aFactor]
      | gt =>
          simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq] at computed
          subst decision
          cases stage <;>
            simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
              localDescriptorStage, rule4aFactor]
      | eq =>
          cases stage with
          | rule4a =>
              simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq]
                at computed
              subst decision
              simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                localDescriptorStage, beforeLeft, beforeRight, rule4aFactor]
          | rule4b leftReference rightReference =>
              cases selectedEq : compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight
                  (.rule4b leftReference rightReference) fuel [(left, right)] with
              | none =>
                  simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                    rule4aEq, selectedEq] at computed
              | some selected =>
                  have selectedFactor :=
                    rule_success_factors mol profile authoritative state
                      beforeLeft beforeRight (.rule4b leftReference rightReference) fuel left right
                      selected selectedEq
                  dsimp [beforeLeft, beforeRight] at selectedFactor
                  simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                    rule4aEq, selectedEq] at computed
                  subst decision
                  simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                    localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, selectedFactor]
                  cases selected <;> rfl
          | rule4c =>
              cases lowercase : state.any fun fact => !fact.uppercase
              · simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                  rule4aEq, lowercase] at computed
                subst decision
                simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                  localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, lowercase]
              · cases selectedEq : compareDescriptorRule? mol profile authoritative state beforeLeft
                    beforeRight .rule4c fuel [(left, right)] with
                | none =>
                    simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, selectedEq] at computed
                | some selected =>
                    have selectedFactor :=
                      rule_success_factors mol profile authoritative state
                        beforeLeft beforeRight .rule4c fuel left right selected selectedEq
                    dsimp [beforeLeft, beforeRight] at selectedFactor
                    simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, selectedEq] at computed
                    subst decision
                    simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                      localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, selectedFactor,
                      lowercase]
                    cases selected <;> rfl
          | rule5 leftReference rightReference =>
              cases lowercase : state.any fun fact => !fact.uppercase
              · cases selectedEq : compareDescriptorRule? mol profile authoritative state beforeLeft
                    beforeRight (.rule5 leftReference rightReference) fuel [(left, right)] with
                | none =>
                    simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, selectedEq] at computed
                | some selected =>
                    have selectedFactor :=
                      rule_success_factors mol profile authoritative state
                        beforeLeft beforeRight (.rule5 leftReference rightReference) fuel left right
                        selected selectedEq
                    dsimp [beforeLeft, beforeRight] at selectedFactor
                    simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, selectedEq] at computed
                    subst decision
                    simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                      localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, selectedFactor,
                      lowercase]
                    cases selected <;> rfl
              · cases rule4cEq : compareDescriptorRule? mol profile authoritative state beforeLeft
                    beforeRight .rule4c fuel [(left, right)] with
                | none =>
                    simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, rule4cEq] at computed
                | some rule4c =>
                    have rule4cFactor :=
                      rule_success_factors mol profile authoritative state
                        beforeLeft beforeRight .rule4c fuel left right rule4c rule4cEq
                    dsimp [beforeLeft, beforeRight] at rule4cFactor
                    cases rule4c with
                    | lt =>
                        simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                          rule4aEq, lowercase, rule4cEq] at computed
                        subst decision
                        simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                          localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, rule4cFactor,
                          lowercase]
                    | gt =>
                        simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                          rule4aEq, lowercase, rule4cEq] at computed
                        subst decision
                        simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                          localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, rule4cFactor,
                          lowercase]
                    | eq =>
                        cases selectedEq : compareDescriptorRule? mol profile authoritative state beforeLeft
                            beforeRight (.rule5 leftReference rightReference) fuel [(left, right)] with
                        | none =>
                            simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                              rule4aEq, lowercase, rule4cEq, selectedEq] at computed
                        | some selected =>
                            have selectedFactor :=
                              rule_success_factors mol profile authoritative state
                                beforeLeft beforeRight (.rule5 leftReference rightReference) fuel
                                left right selected selectedEq
                            dsimp [beforeLeft, beforeRight] at selectedFactor
                            simp [compareDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                              rule4aEq, lowercase, rule4cEq, selectedEq] at computed
                            subst decision
                            simp [buildDenseTiedRootDescriptorKey,
                              compareDenseTiedRootDescriptorKeys, List.compareLex, localDescriptorStage,
                              beforeLeft, beforeRight, rule4aFactor, rule4cFactor, selectedFactor,
                              lowercase]
                            cases selected <;> rfl

theorem occurrenceNodePriority_rule4a_side_independent (state : OccurrenceAuxState) :
    occurrenceNodePriority state .rule4a true =
      occurrenceNodePriority state .rule4a false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule4c_side_independent (state : OccurrenceAuxState) :
    occurrenceNodePriority state .rule4c true =
      occurrenceNodePriority state .rule4c false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule4b_same_reference_side_independent
    (state : OccurrenceAuxState) (reference : RS) :
    occurrenceNodePriority state (.rule4b reference reference) true =
      occurrenceNodePriority state (.rule4b reference reference) false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule4b_left_local (state : OccurrenceAuxState)
    (leftReference rightReference : RS) :
    occurrenceNodePriority state (.rule4b leftReference rightReference) true =
      occurrenceNodePriority state (.rule4b leftReference leftReference) true := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule4b_right_local (state : OccurrenceAuxState)
    (leftReference rightReference : RS) :
    occurrenceNodePriority state (.rule4b leftReference rightReference) false =
      occurrenceNodePriority state (.rule4b rightReference rightReference) false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule5_same_reference_side_independent
    (state : OccurrenceAuxState) (reference : RS) :
    occurrenceNodePriority state (.rule5 reference reference) true =
      occurrenceNodePriority state (.rule5 reference reference) false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

private theorem priority_rule4a_side_independent (mol : RawMolecule) (state : OccurrenceAuxState) :
    priority mol state .rule4a true = priority mol state .rule4a false := by
  funext cursor
  exact congrFun (occurrenceNodePriority_rule4a_side_independent state) (cursor.original mol)

private theorem priority_rule4c_side_independent (mol : RawMolecule) (state : OccurrenceAuxState) :
    priority mol state .rule4c true = priority mol state .rule4c false := by
  funext cursor
  exact congrFun (occurrenceNodePriority_rule4c_side_independent state) (cursor.original mol)

private theorem priority_rule4b_same_reference_side_independent
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference : RS) :
    priority mol state (.rule4b reference reference) true =
      priority mol state (.rule4b reference reference) false := by
  funext cursor
  exact congrFun (occurrenceNodePriority_rule4b_same_reference_side_independent state reference)
    (cursor.original mol)

private theorem priority_rule4b_left_local
    (mol : RawMolecule) (state : OccurrenceAuxState) (leftReference rightReference : RS) :
    priority mol state (.rule4b leftReference rightReference) true =
      priority mol state (.rule4b leftReference leftReference) true := by
  funext cursor
  exact congrFun (occurrenceNodePriority_rule4b_left_local state leftReference rightReference)
    (cursor.original mol)

private theorem priority_rule4b_right_local
    (mol : RawMolecule) (state : OccurrenceAuxState) (leftReference rightReference : RS) :
    priority mol state (.rule4b leftReference rightReference) false =
      priority mol state (.rule4b rightReference rightReference) false := by
  funext cursor
  exact congrFun (occurrenceNodePriority_rule4b_right_local state leftReference rightReference)
    (cursor.original mol)

private theorem priority_rule5_same_reference_side_independent
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference : RS) :
    priority mol state (.rule5 reference reference) true =
      priority mol state (.rule5 reference reference) false := by
  funext cursor
  exact congrFun (occurrenceNodePriority_rule5_same_reference_side_independent state reference)
    (cursor.original mol)

theorem buildDenseTiedRoot_rule4a_side_independent (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ) (cursor : Cursor) :
    buildDenseTiedRootDescriptorKey mol profile authoritative state fuel .rule4a true cursor =
      buildDenseTiedRootDescriptorKey mol profile authoritative state fuel .rule4a false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildKey,
    priority_rule4a_side_independent mol state]

theorem buildDenseTiedRoot_rule4c_side_independent (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ) (cursor : Cursor) :
    buildDenseTiedRootDescriptorKey mol profile authoritative state fuel .rule4c true cursor =
      buildDenseTiedRootDescriptorKey mol profile authoritative state fuel .rule4c false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildKey,
    priority_rule4a_side_independent mol state,
    priority_rule4c_side_independent mol state]

theorem buildDenseTiedRoot_rule4b_same_reference_side_independent (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ) (reference : RS)
    (cursor : Cursor) :
    buildDenseTiedRootDescriptorKey mol profile authoritative state fuel (.rule4b reference reference) true cursor =
      buildDenseTiedRootDescriptorKey mol profile authoritative state fuel (.rule4b reference reference) false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildKey,
    priority_rule4a_side_independent mol state,
    priority_rule4b_same_reference_side_independent mol state reference]

theorem buildDenseTiedRoot_rule4b_left_local (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ) (leftReference rightReference : RS)
    (cursor : Cursor) :
    buildDenseTiedRootDescriptorKey mol profile authoritative state fuel
        (.rule4b leftReference rightReference) true cursor =
      buildDenseTiedRootDescriptorKey mol profile authoritative state fuel
        (.rule4b leftReference leftReference) true cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildKey,
    priority_rule4b_left_local mol state leftReference rightReference]

theorem buildDenseTiedRoot_rule4b_right_local (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ) (leftReference rightReference : RS)
    (cursor : Cursor) :
    buildDenseTiedRootDescriptorKey mol profile authoritative state fuel
        (.rule4b leftReference rightReference) false cursor =
      buildDenseTiedRootDescriptorKey mol profile authoritative state fuel
        (.rule4b rightReference rightReference) false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildKey,
    priority_rule4b_right_local mol state leftReference rightReference]

theorem buildDenseTiedRoot_rule5_same_reference_side_independent (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ) (reference : RS)
    (cursor : Cursor) :
    buildDenseTiedRootDescriptorKey mol profile authoritative state fuel (.rule5 reference reference) true cursor =
      buildDenseTiedRootDescriptorKey mol profile authoritative state fuel (.rule5 reference reference) false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildKey,
    priority_rule4a_side_independent mol state,
    priority_rule4c_side_independent mol state,
    priority_rule5_same_reference_side_independent mol state reference]

abbrev DenseRule4aProjectedKey := List Key

def buildDenseRule4aProjectedKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool) (state : OccurrenceAuxState)
    (fuel : ℕ) (cursor : Cursor) : DenseRule4aProjectedKey :=
  buildDenseTiedRootDescriptorKey mol profile authoritative state fuel .rule4a true cursor

def compareDenseRule4aProjectedKeys :
    DenseRule4aProjectedKey → DenseRule4aProjectedKey → Ordering :=
  compareDenseTiedRootDescriptorKeys

theorem compareDenseRule4aProjectedKeys_transCmp :
    Std.TransCmp compareDenseRule4aProjectedKeys :=
  compareDenseTiedRootDescriptorKeys_transCmp

theorem compareOccurrenceRule4a_tied_success_factors (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : Cursor) (decision : Ordering)
    (computed : compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a left right =
      some decision) :
    compareDenseRule4aProjectedKeys
        (buildDenseRule4aProjectedKey mol profile authoritative state fuel left)
        (buildDenseRule4aProjectedKey mol profile authoritative state fuel right) = decision := by
  have factored := compareOccurrenceDescriptorAtTiedRoot_success_factors mol profile authoritative state fuel .rule4a
    left right decision computed
  rw [← buildDenseTiedRoot_rule4a_side_independent mol profile authoritative state fuel right] at factored
  exact factored

abbrev DenseRule5ProjectedKey := List Key

def buildDenseRule5ProjectedKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool) (state : OccurrenceAuxState)
    (fuel : ℕ) (cursor : Cursor) : DenseRule5ProjectedKey :=
  buildDenseTiedRootDescriptorKey mol profile authoritative state fuel (.rule5 RS.R RS.R) true cursor

def compareDenseRule5ProjectedKeys :
    DenseRule5ProjectedKey → DenseRule5ProjectedKey → Ordering :=
  compareDenseTiedRootDescriptorKeys

theorem compareDenseRule5ProjectedKeys_transCmp :
    Std.TransCmp compareDenseRule5ProjectedKeys :=
  compareDenseTiedRootDescriptorKeys_transCmp

/-- Production Rule 5's ordering projection is exactly its R-reference unary-key comparison.
The S-reference run supplies only the pseudoasymmetry bit and cannot change `ordering`. -/
theorem compareOccurrenceRule5_ordering_success_factors (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : Cursor) (result : RawRule5Comparison)
    (computed : compareRule5? mol profile authoritative state fuel left right = some result) :
    compareDenseRule5ProjectedKeys
        (buildDenseRule5ProjectedKey mol profile authoritative state fuel left)
        (buildDenseRule5ProjectedKey mol profile authoritative state fuel right) = result.ordering := by
  cases cmpREq : compareDescriptorAtTiedRoot? mol profile authoritative state fuel
      (.rule5 RS.R RS.R) left right with
  | none => simp [compareRule5?, cmpREq] at computed
  | some cmpR =>
      have cmpRFactor := compareOccurrenceDescriptorAtTiedRoot_success_factors mol profile authoritative state fuel
        (.rule5 RS.R RS.R) left right cmpR cmpREq
      cases cmpSEq : compareDescriptorAtTiedRoot? mol profile authoritative state fuel
          (.rule5 RS.S RS.S) left right with
      | none => simp [compareRule5?, cmpREq, cmpSEq] at computed
      | some cmpS =>
          cases cmpR <;> cases cmpS <;>
            simp [compareRule5?, cmpREq, cmpSEq] at computed <;>
            subst result <;>
            simpa [compareDenseRule5ProjectedKeys, buildDenseRule5ProjectedKey,
              buildDenseTiedRoot_rule5_same_reference_side_independent mol profile authoritative state fuel RS.R right]
              using cmpRFactor


end TetraStereo.OneCenter.FramedDescriptorProjectedOrderingKey
