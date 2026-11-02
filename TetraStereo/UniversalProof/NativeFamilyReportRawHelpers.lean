import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery

/-! Reporter-only production/list/normalization helpers extracted unchanged.
No FirstZTagDomain, original-frame ranking, source scheduler or caller-label premise. -/

def computedState (result : ChemistryNormalizationResult) (fuel : Nat) : RawDescriptorState :=
  discoverRawDescriptors result (materialized result) fuel

/-- Actual untagged consumer, with its actual internally computed state. -/
def residualEntry (result : ChemistryNormalizationResult) (fuel index : Nat) :
    Option StereoAssignment :=
  (unannotatedTetrahedralOutcome? result (materialized result) (computedState result fuel)
    fuel index).map fun outcome => { unit := .tetrahedral index, outcome := outcome }

/-- Exhaustive executable refusal vocabulary, independent of comparator success or fuel. -/
theorem unannotated_outcome_only_refusals (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel index : Nat) (outcome : StereoOutcome)
    (computed : unannotatedTetrahedralOutcome? result mol state fuel index = some outcome) :
    outcome = .refused .notSpecified ∨ outcome = .refused .rankingUnresolved := by
  cases observed : result.parsed.atomAt? index with
  | none => simp [unannotatedTetrahedralOutcome?, observed] at computed
  | some spec =>
      cases hasTag : spec.tetrahedral?.isSome with
      | true => simp [unannotatedTetrahedralOutcome?, observed, hasTag] at computed
      | false =>
          cases perception : tetrahedralStereogenicity result mol state fuel index <;>
            simp [unannotatedTetrahedralOutcome?, observed, hasTag, perception] at computed
          all_goals simp_all

theorem residual_entry_only_refusals (result : ChemistryNormalizationResult)
    (fuel index : Nat) (assignment : StereoAssignment)
    (computed : residualEntry result fuel index = some assignment) :
    assignment.unit = .tetrahedral index ∧
      (assignment.outcome = .refused .notSpecified ∨
        assignment.outcome = .refused .rankingUnresolved) := by
  cases observed : unannotatedTetrahedralOutcome? result (materialized result)
      (computedState result fuel) fuel index with
  | none => simp [residualEntry, observed] at computed
  | some outcome =>
      have equal : ({ unit := .tetrahedral index, outcome := outcome } : StereoAssignment) =
          assignment := by simpa [residualEntry, observed] using computed
      subst assignment
      exact ⟨rfl, unannotated_outcome_only_refusals result (materialized result)
        (computedState result fuel) fuel index outcome observed⟩

theorem residual_entry_unassigned (result : ChemistryNormalizationResult)
    (fuel index : Nat) (assignment : StereoAssignment)
    (computed : residualEntry result fuel index = some assignment) :
    assignment.outcome.assigned = false := by
  rcases (residual_entry_only_refusals result fuel index assignment computed).2 with first | second
  · rw [first]; rfl
  · rw [second]; rfl

private theorem filterMap_nil_of_none {Alpha Beta : Type*} (values : List Alpha)
    (f : Alpha → Option Beta) (absent : ∀ value ∈ values, f value = none) :
    values.filterMap f = [] := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have tail : ∀ value ∈ rest, f value = none :=
        fun value retained => absent value (List.mem_cons_of_mem first retained)
      simp only [List.filterMap_cons, absent first (by simp)]
      exact ih tail

theorem single_double_neighbors_nil (raw : RawMolecule)
    (single : ∀ bond ∈ raw.bonds, bond.kind = .single) (index : Nat) :
    raw.doubleBondNeighbors index = [] := by
  have none : (raw.bonds.filterMap fun bond =>
      if bond.kind != ParsedBondKind.double then none
      else if bond.source == index then some bond.target
      else if bond.target == index then some bond.source else none) = [] := by
    apply filterMap_nil_of_none
    intro bond retained
    simp [single bond retained]
  change (raw.bonds.filterMap fun bond =>
    if bond.kind != ParsedBondKind.double then Option.none
    else if bond.source == index then some bond.target
    else if bond.target == index then some bond.source else Option.none).eraseDups = []
  rw [none]; rfl

theorem single_extended_chains_nil (raw : RawMolecule)
    (single : ∀ bond ∈ raw.bonds, bond.kind = .single) : raw.extendedDoubleBondChains = [] := by
  unfold extendedDoubleBondChains
  apply filterMap_nil_of_none
  intro index _
  simp only [single_double_neighbors_nil raw single index]

theorem single_stereobond_assignments_nil (raw : RawMolecule)
    (single : ∀ bond ∈ raw.bonds, bond.kind = .single) :
    (stereobondSemantics raw).doubleBondAssignments = [] := by
  change (raw.bonds.filterMap fun bond =>
    if bond.kind = ParsedBondKind.double then some (bond.source, bond.target, DoubleBondStereo.unspecified)
    else none) = []
  apply filterMap_nil_of_none
  intro bond retained
  simp [single bond retained]

theorem normalize_single_identity (raw : RawMolecule)
    (single : ∀ bond ∈ raw.bonds, bond.kind = .single) : raw.normalizeUnspecifiedBonds = raw := by
  have mapped : raw.bonds.map raw.normalizeUnspecifiedBond = raw.bonds := by
    calc
      raw.bonds.map raw.normalizeUnspecifiedBond = raw.bonds.map id := by
        apply List.map_congr_left
        intro bond retained
        simp [normalizeUnspecifiedBond, single bond retained]
      _ = raw.bonds := List.map_id _
  cases raw
  simp only [normalizeUnspecifiedBonds, mapped]

end TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge
