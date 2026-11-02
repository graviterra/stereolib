import TetraStereo.OneCenter.LocalizedOrdinaryMonocyclicDoubleBondAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Exact-once completeness for ordinary monocyclic E/Z list assembly

This module closes the structural list seam after the already proved local P-91/P-93 cyclic
assignment theorem.  Canonical physical double bonds are enumerated without duplication; a
successful per-bond assignment retains its source bond; consequently the family analyzer is
duplicate-free and every successful canonical bond occurs literally once.
-/

/-- The molecule-wide lower-to-higher physical double-bond enumeration contains every pair at
most once. -/
theorem localizedCanonicalDoubleBondPairs_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.localizedCanonicalDoubleBondPairs.Nodup := by
  classical
  unfold localizedCanonicalDoubleBondPairs
  rw [List.nodup_flatMap]
  constructor
  · intro left leftPresent
    apply List.Nodup.filterMap
    · intro first second pair firstPresent secondPresent
      simp only [Option.mem_def] at firstPresent secondPresent
      split at firstPresent <;> split at secondPresent <;> simp_all
      exact congrArg Prod.snd (firstPresent.trans secondPresent.symm)
    · exact List.nodup_finRange _
  · have outerNodup :
    (List.finRange input.certified.input.molecule.atomCount).Nodup :=
      List.nodup_finRange _
    apply outerNodup.imp
    intro left right different
    change List.Disjoint _ _
    rw [List.disjoint_iff_ne]
    intro leftPair leftPresent rightPair rightPresent equal
    simp only [List.mem_filterMap] at leftPresent rightPresent
    rcases leftPresent with ⟨leftAtom, _leftAtomPresent, leftComputed⟩
    rcases rightPresent with ⟨rightAtom, _rightAtomPresent, rightComputed⟩
    split at leftComputed <;> split at rightComputed <;> simp_all
    exact different (congrArg Prod.fst (leftComputed.trans rightComputed.symm))

/-- The proof-carrying canonical physical double-bond carrier list is duplicate-free. -/
theorem localizedCanonicalDoubleBonds_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.localizedCanonicalDoubleBondPairs.attach.Nodup :=
  input.localizedCanonicalDoubleBondPairs_nodup.attach

/-- The state-parameterized ordinary-monocyclic analyzer cannot duplicate an assignment. -/
theorem analyzeLocalizedOrdinaryMonocyclicEZWithState_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    (input.analyzeLocalizedOrdinaryMonocyclicEZWithState fuel state).Nodup := by
  classical
  unfold analyzeLocalizedOrdinaryMonocyclicEZWithState
  apply List.Nodup.filterMap
  · intro left right assignment leftComputed rightComputed
    have leftBond := input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond
      fuel state left assignment leftComputed
    have rightBond := input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond
      fuel state right assignment rightComputed
    exact leftBond.symm.trans rightBond
  · exact input.localizedCanonicalDoubleBonds_nodup

/-- The scheduled ordinary-monocyclic analyzer is duplicate-free. -/
theorem analyzeLocalizedOrdinaryMonocyclicEZ_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.analyzeLocalizedOrdinaryMonocyclicEZ fuel).Nodup :=
  input.analyzeLocalizedOrdinaryMonocyclicEZWithState_nodup fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)

/-- Mapping every result to its physical bond remains duplicate-free. -/
theorem analyzeLocalizedOrdinaryMonocyclicEZ_bonds_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ((input.analyzeLocalizedOrdinaryMonocyclicEZ fuel).map
      LocalizedOrdinaryMonocyclicEZSpatialAssignment.bond).Nodup := by
  classical
  apply (input.analyzeLocalizedOrdinaryMonocyclicEZ_nodup fuel).map_on
  intro left leftPresent right rightPresent sameBond
  have leftComputed :=
    (input.mem_analyzeLocalizedOrdinaryMonocyclicEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) left).mp
        leftPresent
  have rightComputed :=
    (input.mem_analyzeLocalizedOrdinaryMonocyclicEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) right).mp
        rightPresent
  rw [sameBond] at leftComputed
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

/-- Exact-once physical-unit completeness for any canonical bond whose scheduled local analysis
succeeds. The success equality retains the complete topology, endpoint-priority, geometry, and
descriptor payload checked by the existing local soundness theorem. -/
theorem localizedOrdinaryMonocyclicEZ_success_bond_count_eq_one
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (computed : input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState? fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) bond =
        some assignment) :
    List.count bond
      ((input.analyzeLocalizedOrdinaryMonocyclicEZ fuel).map
        LocalizedOrdinaryMonocyclicEZSpatialAssignment.bond) = 1 := by
  have present : assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZ fuel :=
    (input.mem_analyzeLocalizedOrdinaryMonocyclicEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) assignment).mpr
        (by
          have retained := input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond
            fuel (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
              bond assignment computed
          simpa [analyzeLocalizedOrdinaryMonocyclicEZ, retained] using computed)
  have retained := input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond
    fuel (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
      bond assignment computed
  exact List.count_eq_one_of_mem
    (input.analyzeLocalizedOrdinaryMonocyclicEZ_bonds_nodup fuel)
    (List.mem_map.mpr ⟨assignment, present, retained⟩)

/-- Every successful canonical ordinary-monocyclic bond has one independently conforming public
assignment with literal list multiplicity one. -/
theorem every_successful_localizedOrdinaryMonocyclicEZ_occurs_exactly_once
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (computed : input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState? fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) bond =
        some assignment) :
    input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignment fuel assignment ∧
      List.count bond
        ((input.analyzeLocalizedOrdinaryMonocyclicEZ fuel).map
          LocalizedOrdinaryMonocyclicEZSpatialAssignment.bond) = 1 := by
  constructor
  · exact input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_sound fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
        bond assignment computed
  · exact input.localizedOrdinaryMonocyclicEZ_success_bond_count_eq_one
      fuel bond assignment computed

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
