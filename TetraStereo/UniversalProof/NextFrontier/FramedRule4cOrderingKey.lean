import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorProjectedOrderingKey

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TetraStereo.OneCenter.FramedRule4cOrderingKey

open RawMolecule FrameRuntime FramedDescriptorOrderingKey FramedDescriptorProjectedOrderingKey

/-- The witness carrier is metadata; its ordering field is the actual plain Rule4c comparison. -/
theorem pairWitness_ordering (mol : RawMolecule) (state : OccurrenceAuxState) : ∀ pairs,
    (compareRule4cPairLabelsWithWitness mol state pairs).ordering =
      compareDescriptorPairLabels mol state .rule4c pairs
  | [] => rfl
  | pair :: pairs => by
      simp only [compareRule4cPairLabelsWithWitness, compareDescriptorPairLabels]
      cases hc : compare (occurrenceNodePriority state .rule4c true (pair.1.original mol))
          (occurrenceNodePriority state .rule4c false (pair.2.original mol)) with
      | lt => rfl
      | gt => rfl
      | eq => exact pairWitness_ordering mol state pairs

theorem checkedPairWitness_ordering (mol : RawMolecule) (profile : Profile)
    (state : OccurrenceAuxState) (pairs : List Pair) :
    (compareRule4cPairLabelsWithWitness? mol profile state pairs).map
        OccurrenceRule4cDecision.ordering =
      compareDescriptorPairLabels? mol profile state .rule4c pairs := by
  cases valid : validatePairs? mol profile pairs with
  | none => simp [compareRule4cPairLabelsWithWitness?, compareDescriptorPairLabels?, valid]
  | some checked =>
      simp [compareRule4cPairLabelsWithWitness?, compareDescriptorPairLabels?, valid,
        pairWitness_ordering]

/-- Exact projection equality, including refusal. Profile checking, width cap and fuel are
identical to the actual plain descriptor traversal. No metadata-composition claim is made. -/
theorem witness_ordering (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) :
    ∀ fuel pairs,
    (compareRule4cWithWitness? mol profile authoritative state beforeLeft beforeRight fuel pairs).map
        OccurrenceRule4cDecision.ordering =
      compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4c fuel pairs
  | 0, pairs => by
      by_cases cap : !authoritative && defaultBranchWidthCap < pairs.length
      · simp [compareRule4cWithWitness?, compareDescriptorRule?, cap]
      · have labels := checkedPairWitness_ordering mol profile state pairs
        cases hw : compareRule4cPairLabelsWithWitness? mol profile state pairs with
        | none =>
            have hp : compareDescriptorPairLabels? mol profile state .rule4c pairs = none := by
              simpa [hw] using labels.symm
            simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp]
        | some w =>
            have hp : compareDescriptorPairLabels? mol profile state .rule4c pairs =
                some w.ordering := by simpa [hw] using labels.symm
            rcases w with ⟨ordering, carrier⟩
            cases ordering with
            | lt => simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp]
            | gt => simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp]
            | eq =>
                cases hn : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
                | none => simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp, hn]
                | some next =>
                    cases next <;>
                      simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp, hn]
  | fuel + 1, pairs => by
      by_cases cap : !authoritative && defaultBranchWidthCap < pairs.length
      · simp [compareRule4cWithWitness?, compareDescriptorRule?, cap]
      · have labels := checkedPairWitness_ordering mol profile state pairs
        cases hw : compareRule4cPairLabelsWithWitness? mol profile state pairs with
        | none =>
            have hp : compareDescriptorPairLabels? mol profile state .rule4c pairs = none := by
              simpa [hw] using labels.symm
            simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp]
        | some w =>
            have hp : compareDescriptorPairLabels? mol profile state .rule4c pairs =
                some w.ordering := by simpa [hw] using labels.symm
            rcases w with ⟨ordering, carrier⟩
            cases ordering with
            | lt => simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp]
            | gt => simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp]
            | eq =>
                cases hn : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
                | none => simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp, hn]
                | some next =>
                    cases next with
                    | nil => simp [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp, hn]
                    | cons head tail =>
                        simpa [compareRule4cWithWitness?, compareDescriptorRule?, cap, hw, hp, hn] using
                          witness_ordering mol profile authoritative state beforeLeft beforeRight fuel
                            (head :: tail)

abbrev ProjectedKey := Key

def buildProjectedKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (cursor : Cursor) : ProjectedKey :=
  buildKey mol authoritative state
    (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
    fuel .rule4c true cursor

/-- Successful actual Rule4c witness output factors through a unary key on each side. -/
theorem witness_success_factors (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : Cursor)
    (result : OccurrenceRule4cDecision)
    (computed : compareRule4cWithWitness? mol profile authoritative state
      (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
      (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
      fuel [(left, right)] = some result) :
    compareKey (buildProjectedKey mol profile authoritative state fuel left)
      (buildProjectedKey mol profile authoritative state fuel right) = result.ordering := by
  let before := compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c
  have projected := witness_ordering mol profile authoritative state before before fuel [(left, right)]
  have plain : compareDescriptorRule? mol profile authoritative state before before .rule4c
      fuel [(left, right)] = some result.ordering := by
    simpa [before, computed] using projected.symm
  have factored := rule_success_factors mol profile authoritative state before before .rule4c
    fuel left right result.ordering plain
  have sideEq : buildKey mol authoritative state before fuel .rule4c false right =
      buildKey mol authoritative state before fuel .rule4c true right := by
    have priorityEq : priority mol state .rule4c false = priority mol state .rule4c true := by
      funext cursor
      exact congrFun (occurrenceNodePriority_rule4c_side_independent state).symm (cursor.original mol)
    simp [buildKey, priorityEq]
  rw [sideEq] at factored
  exact factored

abbrev OptionalKey := List ProjectedKey

def buildOptionalKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (cursor : Cursor) : OptionalKey :=
  if state.any (fun fact => !fact.uppercase) then
    [buildProjectedKey mol profile authoritative state fuel cursor] else []

def compareOptionalKey : OptionalKey → OptionalKey → Ordering := List.compareLex compareKey

theorem compareOptionalKey_transCmp : Std.TransCmp compareOptionalKey := by
  unfold compareOptionalKey
  letI := compareKey_transCmp
  infer_instance

end TetraStereo.OneCenter.FramedRule4cOrderingKey
