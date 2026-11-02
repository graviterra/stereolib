import TetraStereo.UniversalProof.NativeSecondSphereSeedDiscovery
import TetraStereo.UniversalProof.SecondSphereNativeBlockParser
import TetraStereo.UniversalProof.NativeFamilyReportRawHelpers
import TetraStereo.OneCenter.RawExtendedTetrahedralCarrierFrameDisjointness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereFamilyReportBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation

/-! Proposed actual twelve-role-family public report adapter. The native
STRING dependency is separately accepted at commit712c3b3c (parser05); this report pair
still requires its own independently reviewed ROOT kernel gate. The tracked
ranking dependency is separately accepted at commit a32910c1, source78b996/cert9c2c.
No FirstZTagDomain is instantiated: the physical written heads are [6,1,9,6]. Generic local
adapter inputs expose actual descriptor lookup and physical written degree; every family use
derives them internally. All final family report/String statements take only ps (and valid i for per-tag statements). No report,
parser success, desired state/output, sorted roots or descriptor result is supplied. -/


def familyResult (ps : List TetrahedralInputParity) : ChemistryNormalizationResult :=
  normalizeRawMolecule (familyRaw ps)

def familyExpanded (ps : List TetrahedralInputParity) : RawMolecule :=
  (familyResult ps).parsed.withExplicitHydrogens

def familyFuel (ps : List TetrahedralInputParity) : Nat := analysisFuel (familyExpanded ps)

def familyState (ps : List TetrahedralInputParity) : RawDescriptorState :=
  discoverRawDescriptors (familyResult ps) (familyExpanded ps) (familyFuel ps)

theorem actual_normalized_parsed (ps : List TetrahedralInputParity) :
    (familyResult ps).parsed = familyRaw ps := familyRaw_normalized_parsed ps

theorem actual_materialized_identity (ps : List TetrahedralInputParity) :
    familyExpanded ps = familyRaw ps := by
  unfold familyExpanded familyResult
  rw [familyRaw_normalized_parsed, SecondSphereInitialSeedBridge.actual_materialized_identity]

theorem actual_fuel (ps : List TetrahedralInputParity) :
    familyFuel ps = analysisFuel (familyRaw ps) := by
  unfold familyFuel
  rw [actual_materialized_identity]

private theorem role_tag_index (i : Nat) : SecondSphereInitialSeedBridge.roleIndex i 5 = tagIndex i := by
  unfold SecondSphereInitialSeedBridge.roleIndex tagIndex
  omega

theorem actual_tag_atom (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).atomAt? (tagIndex i.val) = some (roleAtom (ps.get i) .tagCarbon) := by
  have observed := familyRaw_role_atom ps i 5 (by decide)
  have index : 1 + 12 * i.val + 5 = tagIndex i.val := by unfold tagIndex; omega
  simpa only [index, roleOfOffset] using observed

theorem actual_discovered_tag (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyState ps).factAt? (tagIndex i.val) = some (SecondSphereInitialSeedBridge.seedFact ps i) := by
  have found := SecondSphereFamilyTrackedRanking.actual_discovered_tag ps i
  simpa only [familyState, familyExpanded, familyFuel, familyResult,
    familyRaw_normalized_parsed, SecondSphereInitialSeedBridge.actual_materialized_identity,
    SecondSphereFamilyTrackedRanking.familyResult, SecondSphereFamilyTrackedRanking.familyFuel] using found

/-- Generic actual adapter. A descriptor-state lookup is an explicit local interface here;
the family theorem below derives it, and no public adapter/report result is assumed. -/
theorem tagged_public_adapter (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (fact : RawDescriptorFact)
    (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity)
    (lookup : state.factAt? index = some fact)
    (four : (mol.writtenNeighbors index).length = 4) :
    tetrahedralAssignment? result mol state fuel index =
      some { unit := .tetrahedral index, outcome := rawDescriptorFactOutcome fact } := by
  have notExtended :=
    isExtendedTetrahedralParityCarrier_eq_false_of_writtenNeighbors_length_eq_four mol index four
  simp [tetrahedralAssignment?, annotatedTetrahedralAssignment?, annotatedTetrahedralOutcome?,
    observed, tagged, notExtended, lookup]

def parityRow (index : Nat) (parity : TetrahedralInputParity) : StereoAssignment :=
  { unit := .tetrahedral index, outcome := .tetrahedral (descriptorOfParity parity false) }

def familyTagRow (ps : List TetrahedralInputParity) (i : Fin ps.length) : StereoAssignment :=
  parityRow (tagIndex i.val) (ps.get i)

def familyTagEntry (ps : List TetrahedralInputParity) (index : Nat) : Option StereoAssignment := do
  let spec ← (familyResult ps).parsed.atomAt? index
  let parity ← spec.tetrahedral?
  some (parityRow index parity)

def familyResidualEntry (ps : List TetrahedralInputParity) (index : Nat) : Option StereoAssignment :=
  ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.residualEntry (familyResult ps) (familyFuel ps) index

/-- Actual atom enumeration order is retained, including computed unannotated refusals. -/
def familyFullEntry (ps : List TetrahedralInputParity) (index : Nat) : Option StereoAssignment :=
  match (familyResult ps).parsed.atomAt? index with
  | none => none
  | some spec => match spec.tetrahedral? with
    | none => familyResidualEntry ps index
    | some parity => some (parityRow index parity)

def familyTagRows (ps : List TetrahedralInputParity) : List StereoAssignment :=
  (List.range (familyResult ps).parsed.atomCount).filterMap (familyTagEntry ps)

def familyFullRows (ps : List TetrahedralInputParity) : List StereoAssignment :=
  (List.range (familyResult ps).parsed.atomCount).filterMap (familyFullEntry ps)

theorem actual_tag_public_row (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    tetrahedralAssignment? (familyResult ps) (familyExpanded ps) (familyState ps)
      (familyFuel ps) (tagIndex i.val) = some (familyTagRow ps i) := by
  have observed : (familyResult ps).parsed.atomAt? (tagIndex i.val) =
      some (roleAtom (ps.get i) .tagCarbon) := by
    rw [actual_normalized_parsed]
    exact actual_tag_atom ps i
  have four : ((familyExpanded ps).writtenNeighbors (tagIndex i.val)).length = 4 := by
    rw [actual_materialized_identity, ← role_tag_index i.val]
    change ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)).length = 4
    rw [familyRaw_tag_written ps i]
    rfl
  have joined := tagged_public_adapter (familyResult ps) (familyExpanded ps) (familyState ps)
    (familyFuel ps) (tagIndex i.val) (roleAtom (ps.get i) .tagCarbon) (ps.get i)
    (SecondSphereInitialSeedBridge.seedFact ps i) observed rfl (actual_discovered_tag ps i) four
  simpa only [rawDescriptorFactOutcome, SecondSphereInitialSeedBridge.seedFact, ↓reduceIte,
    familyTagRow, parityRow] using joined

theorem actual_tetrahedral_entry (ps : List TetrahedralInputParity) (index : Nat) :
    tetrahedralAssignment? (familyResult ps) (familyExpanded ps) (familyState ps)
      (familyFuel ps) index = familyFullEntry ps index := by
  cases observed : (familyResult ps).parsed.atomAt? index with
  | none => simp [tetrahedralAssignment?, familyFullEntry, observed]
  | some spec =>
      cases tagged : spec.tetrahedral? with
      | none =>
          simp only [tetrahedralAssignment?, familyFullEntry, observed, tagged]
          rfl
      | some parity =>
          have rawObserved : observedTag (familyRaw ps) index = some parity := by
            have rawLookup : (familyRaw ps).atomAt? index = some spec := by
              simpa only [familyResult, familyRaw_normalized_parsed] using observed
            simp only [observedTag, rawLookup, Option.bind_some, tagged]
          obtain ⟨i, position, parityEq⟩ := (familyRaw_observedTag_iff ps index parity).mp rawObserved
          have sameParity : ps.get i = parity := by
            simpa only [List.get_eq_getElem] using parityEq
          have entry : familyFullEntry ps index = some (familyTagRow ps i) := by
            simp only [familyFullEntry, observed, tagged]
            change some (parityRow index parity) =
              some (parityRow (tagIndex i.val) (ps.get i))
            rw [position, sameParity]
          rw [entry, position]
          exact actual_tag_public_row ps i

theorem actual_full_tetrahedral_report (ps : List TetrahedralInputParity) :
    tetrahedralAssignments (familyResult ps) (familyExpanded ps) (familyState ps)
      (familyFuel ps) = familyFullRows ps := by
  unfold tetrahedralAssignments familyFullRows
  apply congrArg (fun entry => (List.range (familyResult ps).parsed.atomCount).filterMap entry)
  funext index
  exact actual_tetrahedral_entry ps index

private theorem filter_full_entries_eq_tags (ps : List TetrahedralInputParity) (indices : List Nat) :
    ((indices.filterMap (familyFullEntry ps)).filter fun assignment => assignment.outcome.assigned) =
      indices.filterMap (familyTagEntry ps) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      cases observed : (familyResult ps).parsed.atomAt? index with
      | none => simp [familyFullEntry, familyTagEntry, observed, ih]
      | some spec =>
          cases tagged : spec.tetrahedral? with
          | some parity =>
              have fullEntry : familyFullEntry ps index = some (parityRow index parity) := by
                simp only [familyFullEntry, observed, tagged]
              have tagEntry : familyTagEntry ps index = some (parityRow index parity) := by
                simp only [familyTagEntry, Bind.bind, Option.bind, observed, tagged]
              have assigned : (parityRow index parity).outcome.assigned = true := rfl
              rw [List.filterMap_cons_some fullEntry, List.filterMap_cons_some tagEntry,
                List.filter_cons_of_pos
                  (p := fun assignment : StereoAssignment => assignment.outcome.assigned)
                  (a := parityRow index parity) assigned, ih]
          | none =>
              cases residual : familyResidualEntry ps index with
              | none => simp [familyFullEntry, familyTagEntry, observed, tagged, residual, ih]
              | some assignment =>
                  have unassigned := ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.residual_entry_unassigned (familyResult ps)
                    (familyFuel ps) index assignment residual
                  simp [familyFullEntry, familyTagEntry, observed, tagged, residual, unassigned, ih]

theorem actual_assigned_projection (ps : List TetrahedralInputParity) :
    (familyFullRows ps).filter (fun assignment => assignment.outcome.assigned) = familyTagRows ps :=
  filter_full_entries_eq_tags ps _

theorem actual_tag_rows_units (ps : List TetrahedralInputParity) :
    (familyTagRows ps).map StereoAssignment.unit =
      (rawAnnotatedCenters (familyResult ps)).map StereoUnit.tetrahedral := by
  unfold familyTagRows rawAnnotatedCenters
  generalize List.range (familyResult ps).parsed.atomCount = indices
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      cases observed : (familyResult ps).parsed.atomAt? index with
      | none => simp [familyTagEntry, observed, ih]
      | some spec =>
          cases tagged : spec.tetrahedral? <;> simp [familyTagEntry, observed, tagged, parityRow, ih]

theorem actual_observed_centers_mem (ps : List TetrahedralInputParity) (index : Nat) :
    index ∈ rawAnnotatedCenters (familyResult ps) ↔ ∃ i : Fin ps.length, index = tagIndex i.val := by
  unfold rawAnnotatedCenters
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, annotation⟩
    cases observed : (familyResult ps).parsed.atomAt? index with
    | none => simp [observed] at annotation
    | some spec =>
        have hasParity : spec.tetrahedral?.isSome = true := by simpa only [observed] using annotation
        obtain ⟨parity, tagged⟩ := Option.isSome_iff_exists.mp hasParity
        have rawLookup : (familyRaw ps).atomAt? index = some spec := by
          simpa only [familyResult, familyRaw_normalized_parsed] using observed
        have rawObserved : observedTag (familyRaw ps) index = some parity := by
          simp only [observedTag, rawLookup, Option.bind_some, tagged]
        obtain ⟨i, position, _⟩ := (familyRaw_observedTag_iff ps index parity).mp rawObserved
        exact ⟨i, position⟩
  · rintro ⟨i, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [actual_normalized_parsed]
      apply List.mem_range.mpr
      rw [← role_tag_index]
      change 1 + 12 * i.val + 5 < (familyRaw ps).atomCount
      exact familyRaw_role_bound ps i 5 (by decide)
    · simp only [familyResult, familyRaw_normalized_parsed, actual_tag_atom,
        roleAtom, GeneralParserStateBridge.atomSpec, Option.isSome_some]

theorem actual_observed_centers (ps : List TetrahedralInputParity) :
    rawAnnotatedCenters (familyResult ps) = (List.range ps.length).map tagIndex := by
  have sourceNodup : (rawAnnotatedCenters (familyResult ps)).Nodup :=
    (List.nodup_range (n := (familyResult ps).parsed.atomCount)).filter _
  have targetNodup : ((List.range ps.length).map tagIndex).Nodup := by
    have injective : Function.Injective tagIndex := by
      intro left right same
      unfold tagIndex at same
      omega
    exact List.Nodup.map injective (List.nodup_range (n := ps.length))
  have permutation : (rawAnnotatedCenters (familyResult ps)).Perm ((List.range ps.length).map tagIndex) := by
    apply (List.perm_ext_iff_of_nodup sourceNodup targetNodup).mpr
    intro index
    rw [actual_observed_centers_mem, List.mem_map]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
    · rintro ⟨i, bounded, rfl⟩
      exact ⟨⟨i, List.mem_range.mp bounded⟩, rfl⟩
  have sourceSorted : (rawAnnotatedCenters (familyResult ps)).Pairwise (· < ·) :=
    (List.pairwise_lt_range).filter _
  have targetSorted : ((List.range ps.length).map tagIndex).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (by intro left right lower; unfold tagIndex; omega)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ first second => False.elim (Nat.lt_asymm first second))
    sourceSorted targetSorted permutation

theorem actual_tag_units (ps : List TetrahedralInputParity) :
    (familyTagRows ps).map StereoAssignment.unit =
      (List.range ps.length).map (fun i => StereoUnit.tetrahedral (tagIndex i)) := by
  rw [actual_tag_rows_units, actual_observed_centers]
  exact List.map_map

theorem actual_tag_count (ps : List TetrahedralInputParity) :
    (familyTagRows ps).length = ps.length := by
  have lengths := congrArg List.length (actual_tag_units ps)
  simpa only [List.length_map, List.length_range] using lengths

theorem actual_refusal_vocabulary (ps : List TetrahedralInputParity) (assignment : StereoAssignment)
    (retained : assignment ∈ familyFullRows ps) (unassigned : assignment.outcome.assigned = false) :
    assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved := by
  obtain ⟨index, _, computed⟩ := List.mem_filterMap.mp retained
  cases observed : (familyResult ps).parsed.atomAt? index with
  | none => simp [familyFullEntry, observed] at computed
  | some spec =>
      cases tagged : spec.tetrahedral? with
      | none =>
          have residual : ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.residualEntry (familyResult ps) (familyFuel ps) index = some assignment := by
            simpa only [familyFullEntry, observed, tagged, familyResidualEntry] using computed
          exact (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.residual_entry_only_refusals (familyResult ps)
            (familyFuel ps) index assignment residual).2
      | some parity =>
          have equal : parityRow index parity = assignment := by
            simpa only [familyFullEntry, observed, tagged, Option.some.injEq] using computed
          rw [← equal] at unassigned
          simp [parityRow, StereoOutcome.assigned] at unassigned

theorem actual_stereobonds_nil (ps : List TetrahedralInputParity) :
    (familyResult ps).stereobonds.doubleBondAssignments = [] := by
  change (stereobondSemantics (familyRaw ps).normalizeUnspecifiedBonds).doubleBondAssignments = []
  rw [ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.normalize_single_identity (familyRaw ps) (familyRaw_all_single ps)]
  exact ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.single_stereobond_assignments_nil (familyRaw ps) (familyRaw_all_single ps)

theorem actual_other_four_segments_nil (ps : List TetrahedralInputParity) :
    let branches := normalizedStereoAnalysisBranches (familyResult ps)
    branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
      branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = [] := by
  have ordinary := actual_stereobonds_nil ps
  have chains : (familyResult ps).parsed.extendedDoubleBondChains = [] := by
    rw [actual_normalized_parsed]
    exact ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.single_extended_chains_nil (familyRaw ps) (familyRaw_all_single ps)
  have expandedChains : (familyExpanded ps).extendedDoubleBondChains = [] := by
    rw [actual_materialized_identity]
    exact ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.single_extended_chains_nil (familyRaw ps) (familyRaw_all_single ps)
  have carriers : (familyExpanded ps).extendedTetrahedralParityCarriers = [] := by
    simp [extendedTetrahedralParityCarriers, expandedChains]
  change ((normalizedStereoAnalysisBranches (familyResult ps)).ordinaryDoubleBond = []) ∧
    ((normalizedStereoAnalysisBranches (familyResult ps)).coupledDoubleBond = []) ∧
    ((normalizedStereoAnalysisBranches (familyResult ps)).oddCumuleneDoubleBond = []) ∧
    ((normalizedStereoAnalysisBranches (familyResult ps)).extendedAxial = [])
  simp [normalizedStereoAnalysisBranches, ordinaryDoubleBondAssignments,
    oddCumuleneDoubleBondAssignments, ordinary, chains,
    show (familyResult ps).parsed.withExplicitHydrogens.extendedTetrahedralParityCarriers = [] from carriers]

theorem actual_mass_guard (ps : List TetrahedralInputParity) :
    (familyResult ps).parsed.rule2MassesKnown? = true := by
  apply (RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr
  rw [actual_normalized_parsed]
  exact familyRaw_masses_known ps

theorem actual_expanded_guard (ps : List TetrahedralInputParity) :
    (familyResult ps).expandedStereochemicalAdmissible? = true := by
  apply ((familyResult ps).expandedStereochemicalAdmissible?_eq_true_iff).mpr
  change (familyExpanded ps).StereochemicalAdmissible
  rw [actual_materialized_identity]
  exact familyRaw_stereochemical_admissible ps

/-- Complete guarded normalized report, including the actual unannotated refusal rows. -/
theorem actual_normalized_whole_report (ps : List TetrahedralInputParity) :
    analyzeNormalized (familyResult ps) = familyFullRows ps ∧
    ((analyzeNormalized (familyResult ps)).filter fun assignment => assignment.outcome.assigned) = familyTagRows ps ∧
    (familyTagRows ps).map StereoAssignment.unit =
      (List.range ps.length).map (fun i => StereoUnit.tetrahedral (tagIndex i)) ∧
    (familyTagRows ps).length = ps.length ∧
    (∀ assignment ∈ analyzeNormalized (familyResult ps), assignment.outcome.assigned = false →
      assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved) := by
  obtain ⟨ordinary, coupled, cumulene, axial⟩ := actual_other_four_segments_nil ps
  have tetra : (normalizedStereoAnalysisBranches (familyResult ps)).tetrahedral = familyFullRows ps :=
    actual_full_tetrahedral_report ps
  have full : analyzeNormalized (familyResult ps) = familyFullRows ps := by
    unfold analyzeNormalized
    rw [actual_mass_guard, actual_expanded_guard]
    change (normalizedStereoAnalysisBranches (familyResult ps)).tetrahedral ++
      (normalizedStereoAnalysisBranches (familyResult ps)).ordinaryDoubleBond ++
      (normalizedStereoAnalysisBranches (familyResult ps)).coupledDoubleBond ++
      (normalizedStereoAnalysisBranches (familyResult ps)).oddCumuleneDoubleBond ++
      (normalizedStereoAnalysisBranches (familyResult ps)).extendedAxial = familyFullRows ps
    rw [ordinary, coupled, cumulene, axial]
    simpa only [List.append_nil] using tetra
  refine ⟨full, ?_, actual_tag_units ps, actual_tag_count ps, ?_⟩
  · rw [full]
    exact actual_assigned_projection ps
  · intro assignment retained unassigned
    rw [full] at retained
    exact actual_refusal_vocabulary ps assignment retained unassigned

/-- The concrete public row is retained at the same physical tagged center, with the
internally derived uppercase descriptor. No row-membership premise is supplied. -/
theorem actual_tag_public_membership (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ({ unit := .tetrahedral (tagIndex i.val),
       outcome := .tetrahedral (descriptorOfParity (ps.get i) false) } : StereoAssignment) ∈
      analyzeNormalized (certifiedFamily ps).result := by
  change familyTagRow ps i ∈ analyzeNormalized (familyResult ps)
  rw [(actual_normalized_whole_report ps).1]
  apply List.mem_filterMap.mpr
  refine ⟨tagIndex i.val, ?_, ?_⟩
  · apply List.mem_range.mpr
    change tagIndex i.val < (familyResult ps).parsed.atomCount
    rw [actual_normalized_parsed, ← role_tag_index i.val]
    change 1 + 12 * i.val + 5 < (familyRaw ps).atomCount
    exact familyRaw_role_bound ps i 5 (by decide)
  · have observed : (familyResult ps).parsed.atomAt? (tagIndex i.val) =
        some (roleAtom (ps.get i) .tagCarbon) := by
      rw [actual_normalized_parsed]
      exact actual_tag_atom ps i
    simp [familyFullEntry, observed, roleAtom, GeneralParserStateBridge.atomSpec,
      familyTagRow]

/-- Compiler-facing package of every actual normalized report segment and projection. -/
def FamilyReport (ps : List TetrahedralInputParity) : Prop :=
  analyzeNormalized (familyResult ps) = familyFullRows ps ∧
  ((analyzeNormalized (familyResult ps)).filter fun assignment => assignment.outcome.assigned) = familyTagRows ps ∧
  (familyTagRows ps).map StereoAssignment.unit =
    (List.range ps.length).map (fun i => StereoUnit.tetrahedral (tagIndex i)) ∧
  (familyTagRows ps).length = ps.length ∧
  (∀ assignment ∈ analyzeNormalized (familyResult ps), assignment.outcome.assigned = false →
    assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved) ∧
  (normalizedStereoAnalysisBranches (familyResult ps)).ordinaryDoubleBond = [] ∧
  (normalizedStereoAnalysisBranches (familyResult ps)).coupledDoubleBond = [] ∧
  (normalizedStereoAnalysisBranches (familyResult ps)).oddCumuleneDoubleBond = [] ∧
  (normalizedStereoAnalysisBranches (familyResult ps)).extendedAxial = [] ∧
  (∀ i : Fin ps.length,
    ({ unit := .tetrahedral (tagIndex i.val),
       outcome := .tetrahedral (descriptorOfParity (ps.get i) false) } : StereoAssignment) ∈
      analyzeNormalized (certifiedFamily ps).result)

theorem familyReport_holds (ps : List TetrahedralInputParity) : FamilyReport ps := by
  obtain ⟨full, assigned, units, count, refusals⟩ := actual_normalized_whole_report ps
  obtain ⟨ordinary, coupled, cumulene, axial⟩ := actual_other_four_segments_nil ps
  exact ⟨full, assigned, units, count, refusals, ordinary, coupled, cumulene, axial,
    actual_tag_public_membership ps⟩

/-- Exact singleton/zero/multiple-tag early gate, derived from actual annotation enumeration.
The single-tag branch uses the accepted actual legacy uppercase classifier outcome. -/
theorem actual_early_assignment_none (ps : List TetrahedralInputParity) :
    singleInvariantEarlyAssignment? (familyResult ps) = none := by
  have ordinary := actual_stereobonds_nil ps
  have chains : (familyResult ps).parsed.extendedDoubleBondChains = [] := by
    rw [actual_normalized_parsed]
    exact ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.single_extended_chains_nil (familyRaw ps) (familyRaw_all_single ps)
  unfold singleInvariantEarlyAssignment?
  simp only [ordinary, chains, List.isEmpty_nil, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte]
  cases centers : rawAnnotatedCenters (familyResult ps) with
  | nil => rfl
  | cons center rest =>
      cases rest with
      | nil =>
          have present : center ∈ rawAnnotatedCenters (familyResult ps) := by rw [centers]; simp
          obtain ⟨i, position⟩ := (actual_observed_centers_mem ps center).mp present
          have legacy : (familyResult ps).parsed.withExplicitHydrogens.tetrahedralOutcome
              (analysisFuel (familyResult ps).parsed.withExplicitHydrogens) center =
                .tetrahedral (descriptorOfParity (ps.get i) false) := by
            rw [position, ← role_tag_index i.val]
            change (familyExpanded ps).tetrahedralOutcome (familyFuel ps) (SecondSphereInitialSeedBridge.roleIndex i.val 5) = _
            rw [actual_materialized_identity, actual_fuel]
            exact SecondSphereInitialSeedBridge.actual_legacy_outcome ps i
          simp only [actual_expanded_guard, Bool.not_true, Bool.false_eq_true, ↓reduceIte, legacy]
      | cons next remaining => rfl

theorem actual_certified_string_intake (ps : List TetrahedralInputParity) :
    parseAndNormalizeOpenSMILESCertified (SecondSphereNativeBlockParser.nativeFamilyString ps) =
      Except.ok (certifiedFamily ps) := by
  have certified := familyRaw_actual_certified_intake ps
  change (normalizeRawMolecule (familyRaw ps)).certify? = some (certifiedFamily ps) at certified
  unfold parseAndNormalizeOpenSMILESCertified parseAndNormalizeOpenSMILES
  rw [SecondSphereNativeBlockParser.parse_native_family_string]
  change (match (normalizeRawMolecule (familyRaw ps)).certify? with
    | some accepted => Except.ok accepted
    | none => Except.error "normalized molecule failed structural, valence, or Rule-2 mass admission") =
      Except.ok (certifiedFamily ps)
  rw [certified]

/-- Literal actual String reporter returns the complete admitted normalized report. -/
theorem actual_string_report (ps : List TetrahedralInputParity) :
    analyzeSmiles (SecondSphereNativeBlockParser.nativeFamilyString ps) =
      Except.ok (analyzeNormalized (certifiedFamily ps).result) := by
  have masses : (familyRaw ps).rule2MassesKnown? = true :=
    (RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr (familyRaw_masses_known ps)
  have certified := familyRaw_actual_certified_intake ps
  change (normalizeRawMolecule (familyRaw ps)).certify? = some (certifiedFamily ps) at certified
  have guarded : (certifiedFamily ps).result.expandedStereochemicalAdmissible? = true :=
    actual_expanded_guard ps
  have early : singleInvariantEarlyAssignment? (certifiedFamily ps).result = none :=
    actual_early_assignment_none ps
  simp only [analyzeSmiles, SecondSphereNativeBlockParser.parse_native_family_string, masses,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, certified, guarded, early]

theorem actual_string_full_report (ps : List TetrahedralInputParity) :
    analyzeSmiles (SecondSphereNativeBlockParser.nativeFamilyString ps) = Except.ok (familyFullRows ps) := by
  rw [actual_string_report]
  change Except.ok (analyzeNormalized (familyResult ps)) = _
  rw [(actual_normalized_whole_report ps).1]

theorem actual_string_assigned_projection (ps : List TetrahedralInputParity) :
    (analyzeSmiles (SecondSphereNativeBlockParser.nativeFamilyString ps)).map
      (fun rows => rows.filter fun assignment => assignment.outcome.assigned) =
        Except.ok (familyTagRows ps) := by
  rw [actual_string_full_report]
  change Except.ok ((familyFullRows ps).filter fun assignment => assignment.outcome.assigned) = _
  rw [actual_assigned_projection]

end TetraStereo.UniversalProof.SecondSphereFamilyReportBridge
