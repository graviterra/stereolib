import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false



























































namespace TetraStereo.OneCenter

open RawMolecule

namespace FrameRuntime

/-! ### Kernel-checkable bridge laws and validation-refusal laws -/

/-- Strict-result preservation: a non-tied constitutional result is returned verbatim, with no
automorphism gate premise. -/
theorem decisionComplete?_strict
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (ordering : Ordering)
    (h : compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) =
      some ordering)
    (hn : (ordering != Ordering.eq) = true) :
    decisionComplete? mol profile authoritative state fuel left right =
      some { ordering := ordering } := by
  have hne : ordering ≠ Ordering.eq := by
    intro heq
    simp [heq] at hn
  simp [decisionComplete?, h, hne]

/-- Empty-state tie preservation: an empty auxiliary state ties exactly, matching `decision?`. -/
theorem decisionComplete?_empty_tie
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (h : compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) =
      some Ordering.eq)
    (empty : state.isEmpty = true) :
    decisionComplete? mol profile authoritative state fuel left right =
      some { ordering := Ordering.eq } := by
  simp [decisionComplete?, h, empty]

/-- Rule-4a staged outcome: a non-tied Rule-4a comparison is the decision. -/
theorem decisionComplete?_rule4a
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (ordering : Ordering)
    (hconst : compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) =
      some Ordering.eq)
    (hnonempty : state.isEmpty = false)
    (hrule : compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
      (.actual left) (.actual right) = some ordering)
    (hn : (ordering != Ordering.eq) = true) :
    decisionComplete? mol profile authoritative state fuel left right =
      some { ordering := ordering } := by
  have hne : ordering ≠ Ordering.eq := by
    intro heq
    simp [heq] at hn
  simp [decisionComplete?, hconst, hnonempty, hrule, hne]

/-- Rule-4b staged outcome after a tied Rule-4a, through the shared-profile `compareRule4b?`. -/
theorem decisionComplete?_rule4b
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (ordering : Ordering)
    (hconst : compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) =
      some Ordering.eq)
    (hnonempty : state.isEmpty = false)
    (hrule4a : compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
      (.actual left) (.actual right) = some Ordering.eq)
    (hrule : compareRule4b? mol profile authoritative state fuel (.actual left) (.actual right) =
      some ordering)
    (hn : (ordering != Ordering.eq) = true) :
    decisionComplete? mol profile authoritative state fuel left right =
      some { ordering := ordering } := by
  have hne : ordering ≠ Ordering.eq := by
    intro heq
    simp [heq] at hn
  simp [decisionComplete?, hconst, hnonempty, hrule4a, hrule, hne]

/-- Rule-4c staged outcome retaining the exact descriptor carrier and a false `pseudo`. -/
theorem decisionComplete?_rule4c
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (decision : OccurrenceRule4cDecision)
    (hconst : compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) =
      some Ordering.eq)
    (hnonempty : state.isEmpty = false)
    (hrule4a : compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
      (.actual left) (.actual right) = some Ordering.eq)
    (hrule4b : compareRule4b? mol profile authoritative state fuel (.actual left) (.actual right) =
      some Ordering.eq)
    (hany : state.any (fun fact => !fact.uppercase) = true)
    (hrule : compareRule4cWithWitness? mol profile authoritative state
      (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
      (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
      fuel [(.actual left, .actual right)] = some decision)
    (hord : (decision.ordering != Ordering.eq) = true) :
    decisionComplete? mol profile authoritative state fuel left right =
      some { ordering := decision.ordering, rule4cCarrier? := decision.carrier? } := by
  have hne : decision.ordering ≠ Ordering.eq := by
    intro heq
    simp [heq] at hord
  simp [decisionComplete?, hconst, hnonempty, hrule4a, hrule4b, hany, hrule, hne]

/-- Rule-5 staged outcome after tied Rule-4a/Rule-4b and an absent lowercase Rule-4c class. -/
theorem decisionComplete?_rule5
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (ordering : Ordering) (pseudo : Bool)
    (hconst : compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) =
      some Ordering.eq)
    (hnonempty : state.isEmpty = false)
    (hrule4a : compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
      (.actual left) (.actual right) = some Ordering.eq)
    (hrule4b : compareRule4b? mol profile authoritative state fuel (.actual left) (.actual right) =
      some Ordering.eq)
    (hnolower : state.any (fun fact => !fact.uppercase) = false)
    (hrule : compareRule5? mol profile authoritative state fuel (.actual left) (.actual right) =
      some { ordering := ordering, pseudo := pseudo }) :
    decisionComplete? mol profile authoritative state fuel left right =
      some { ordering := ordering, pseudo := pseudo } := by
  simp [decisionComplete?, hconst, hnonempty, hrule4a, hrule4b, hnolower, hrule]

/-- Validation failure is refused: an out-of-profile cursor makes the checked pair-label
projection fail closed. -/
theorem compareDescriptorPairLabels?_refuses_out_of_profile
    (mol : RawMolecule) (profile : Profile) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (left right : Cursor)
    (h : cursor? mol profile left = none) :
    compareDescriptorPairLabels? mol profile state stage [(left, right)] = none := by
  simp [compareDescriptorPairLabels?, validatePairs?, h]

/-- Validation failure is refused before the terminal/empty-success short-circuit. -/
theorem nextDescriptorPairs?_refuses_out_of_profile
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) (left right : Cursor)
    (h : cursor? mol profile left = none) :
    nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight [(left, right)] = none := by
  simp [nextDescriptorPairs?, h]

/-- Validation failure is refused by the shared-profile Rule-4b reference BFS. -/
theorem rule4bReferences?_refuses_out_of_profile
    (mol : RawMolecule) (profile : Profile) (state : OccurrenceAuxState) (fuel : Nat)
    (cursor : Cursor) (h : cursor? mol profile cursor = none) :
    rule4bReferences? mol profile state (fuel + 1) [cursor] = none := by
  simp [rule4bReferences?, validateCursors?, h]

/-- Unrestricted authoritative Rule 4b orders the empty reference shape strictly below a one-list. -/
theorem compareRule4b?_mixed_empty_unrestricted
    (mol : RawMolecule) (profile : Profile) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : Cursor)
    (hl : rule4bReferences? mol profile state fuel [left] = some [])
    (hr : rule4bReferences? mol profile state fuel [right] = some [RS.R]) :
    compareRule4b? mol profile true state fuel left right = some Ordering.lt := by
  simp [compareRule4b?, hl, hr]

/-- Conservative fast Rule 4b refuses the mixed empty/nonempty reference shape. -/
theorem compareRule4b?_mixed_empty_conservative
    (mol : RawMolecule) (profile : Profile) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : Cursor)
    (hl : rule4bReferences? mol profile state fuel [left] = some [])
    (hr : rule4bReferences? mol profile state fuel [right] = some [RS.R]) :
    compareRule4b? mol profile false state fuel left right = none := by
  simp [compareRule4b?, hl, hr]

end FrameRuntime

end TetraStereo.OneCenter
