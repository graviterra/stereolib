import TetraStereo.OneCenter.IUPACNormativeSemanticsPartition

set_option autoImplicit false




















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

@[simp] theorem primitiveProvedProvisionCount : primitiveProvedProvisions.length = 35 := by
  exact primitive35ProvisionCount

@[simp] theorem partiallyCoveredProvisionCount : partiallyCoveredProvisions.length = 69 := by
  decide

@[simp] theorem endToEndProvedProvisionCount : endToEndProvedProvisions.length = 0 := by
  rfl

/-- The provisions with any current implementation coverage.  Membership is proved equivalent to
`currentMaturity provision ≠ .absent`, so this list is the exact covered set, and its complement
in the manifest is the exact coverage work queue. -/
def currentCoveredProvisions : List IUPACNormativeProvision :=
  endToEndProvedProvisions ++ primitiveProvedProvisions ++ partiallyCoveredProvisions

@[simp] theorem currentCoveredProvisionCount : currentCoveredProvisions.length = 104 := by
  simp [currentCoveredProvisions]

set_option maxRecDepth 4096 in
theorem currentCoveredProvisions_nodup : currentCoveredProvisions.Nodup := by
  decide

theorem primitiveProved_disjoint_partiallyCovered :
    ∀ provision ∈ primitiveProvedProvisions, provision ∉ partiallyCoveredProvisions := by
  decide

theorem endToEndProved_disjoint_primitiveProved :
    ∀ provision ∈ endToEndProvedProvisions, provision ∉ primitiveProvedProvisions := by
  simp [endToEndProvedProvisions]

theorem endToEndProved_disjoint_partiallyCovered :
    ∀ provision ∈ endToEndProvedProvisions, provision ∉ partiallyCoveredProvisions := by
  simp [endToEndProvedProvisions]

/-- The explicit terminal coverage inventory characterizes the coarse terminal maturity tag. -/
theorem currentMaturity_eq_endToEndProved_iff (provision : IUPACNormativeProvision) :
    currentMaturity provision = .endToEndProved ↔
      provision ∈ endToEndProvedProvisions := by
  constructor
  · intro maturity
    by_cases endToEnd : provision ∈ endToEndProvedProvisions
    · exact endToEnd
    · by_cases primitive : provision ∈ primitiveProvedProvisions
      · simp [currentMaturity, endToEnd, primitive] at maturity
      · by_cases partial_ : provision ∈ partiallyCoveredProvisions <;>
          simp [currentMaturity, endToEnd, primitive, partial_] at maturity
  · intro endToEnd
    simp [currentMaturity, endToEnd]

/-- The two curated coverage lists characterize their maturity states exactly; the `if`-chain
precedence in `currentMaturity` never reclassifies a row because the lists are disjoint. -/
theorem currentMaturity_eq_primitiveProved_iff (provision : IUPACNormativeProvision) :
    currentMaturity provision = .primitiveProved ↔
      provision ∈ primitiveProvedProvisions := by
  constructor
  · intro maturity
    by_cases endToEnd : provision ∈ endToEndProvedProvisions
    · simp [currentMaturity, endToEnd] at maturity
    · by_cases primitive : provision ∈ primitiveProvedProvisions
      · exact primitive
      · by_cases partial_ : provision ∈ partiallyCoveredProvisions <;>
          simp [currentMaturity, endToEnd, primitive, partial_] at maturity
  · intro primitive
    have notEndToEnd : provision ∉ endToEndProvedProvisions := fun endToEnd =>
      endToEndProved_disjoint_primitiveProved provision endToEnd primitive
    simp [currentMaturity, notEndToEnd, primitive]

theorem currentMaturity_eq_partiallyCovered_iff (provision : IUPACNormativeProvision) :
    currentMaturity provision = .partiallyCovered ↔
      provision ∈ partiallyCoveredProvisions := by
  constructor
  · intro maturity
    by_cases endToEnd : provision ∈ endToEndProvedProvisions
    · simp [currentMaturity, endToEnd] at maturity
    · by_cases primitive : provision ∈ primitiveProvedProvisions
      · simp [currentMaturity, endToEnd, primitive] at maturity
      · by_cases partial_ : provision ∈ partiallyCoveredProvisions
        · exact partial_
        · simp [currentMaturity, endToEnd, primitive, partial_] at maturity
  · intro partial_
    have notEndToEnd : provision ∉ endToEndProvedProvisions := fun endToEnd =>
      endToEndProved_disjoint_partiallyCovered provision endToEnd partial_
    have primitive : provision ∉ primitiveProvedProvisions := fun primitive =>
      primitiveProved_disjoint_partiallyCovered provision primitive partial_
    simp [currentMaturity, notEndToEnd, primitive, partial_]

/-- No provision reaches end-to-end coverage yet: the maturity function cannot return it.  This
is the pointwise strengthening of the existing `current_manifest_not_end_to_end_complete`
witness. -/
theorem currentMaturity_ne_endToEndProved (provision : IUPACNormativeProvision) :
    currentMaturity provision ≠ .endToEndProved := by
  intro maturity
  have member := (currentMaturity_eq_endToEndProved_iff provision).mp maturity
  simp [endToEndProvedProvisions] at member

/-- The open-set characterization for implementation coverage: a provision is coverage-absent
exactly when it lies outside the 104 covered rows. -/
theorem currentMaturity_eq_absent_iff (provision : IUPACNormativeProvision) :
    currentMaturity provision = .absent ↔ provision ∉ currentCoveredProvisions := by
  constructor
  · intro maturity member
    rcases List.mem_append.mp member with primitive | partial_
    · rw [(currentMaturity_eq_primitiveProved_iff provision).mpr primitive] at maturity
      exact absurd maturity (by decide)
    · rw [(currentMaturity_eq_partiallyCovered_iff provision).mpr partial_] at maturity
      exact absurd maturity (by decide)
  · intro notCovered
    have endToEnd : provision ∉ endToEndProvedProvisions := fun member =>
      notCovered (List.mem_append_left _ (List.mem_append_left _ member))
    have primitive : provision ∉ primitiveProvedProvisions := fun member =>
      notCovered (List.mem_append_left _ (List.mem_append_right _ member))
    have partial_ : provision ∉ partiallyCoveredProvisions := fun member =>
      notCovered (List.mem_append_right _ member)
    simp [currentMaturity, endToEnd, primitive, partial_]

/-- Cross-dimension coupling: every locally-proved implementation row already has at least a
partial independent semantic target.  The implementation and semantics inventories are distinct,
so a future implementation promotion cannot satisfy this theorem without a corresponding,
independently audited semantics entry. -/
theorem primitiveProved_has_independent_semantic_target :
    ∀ provision ∈ primitiveProvedProvisions,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  exact currentSemanticsMaturity_eq_partiallyFormalized_of_mem
    (List.mem_append_left _
      (primitiveProved_mem_independentPrimitiveSemantics provision member))



theorem authority_data_partial_semantics_and_partial_implementation :
    currentMaturity .periodicAtomicNumbers = .partiallyCovered ∧
      currentSemanticsMaturity .periodicAtomicNumbers = .partiallyFormalized ∧
      currentMaturity .standardAtomicWeights = .partiallyCovered ∧
      currentSemanticsMaturity .standardAtomicWeights = .partiallyFormalized ∧
      currentMaturity .isotopeAtomicMasses = .partiallyCovered ∧
      currentSemanticsMaturity .isotopeAtomicMasses = .partiallyFormalized := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (currentMaturity_eq_partiallyCovered_iff _).mpr (by decide)
  · exact periodicAtomicNumbers_semantics_partiallyFormalized
  · exact (currentMaturity_eq_partiallyCovered_iff _).mpr (by decide)
  · exact standardAtomicWeights_semantics_partiallyFormalized
  · exact (currentMaturity_eq_partiallyCovered_iff _).mpr (by decide)
  · exact isotopeAtomicMasses_semantics_partiallyFormalized

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.endToEndProvedProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitiveProvedProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.partiallyCoveredProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentCoveredProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentCoveredProvisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitiveProved_disjoint_partiallyCovered
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.endToEndProved_disjoint_primitiveProved
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.endToEndProved_disjoint_partiallyCovered
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentMaturity_eq_endToEndProved_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentMaturity_eq_primitiveProved_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentMaturity_eq_partiallyCovered_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentMaturity_ne_endToEndProved
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.currentMaturity_eq_absent_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitiveProved_has_independent_semantic_target
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.authority_data_partial_semantics_and_partial_implementation
