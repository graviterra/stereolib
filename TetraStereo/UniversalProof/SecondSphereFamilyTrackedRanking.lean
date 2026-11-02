import TetraStereo.UniversalProof.NativeSecondSphereSeedDiscovery
import TetraStereo.UniversalProof.NextFrontier.NativeFamilyFramedOccurrenceCaller
import Mathlib.Tactic.FinCases
import TetraStereo.UniversalProof.SecondSphereFamilyRuntimeInstantiation
import TetraStereo.UniversalProof.SecondSphereInitialSeedBridge
import TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereFamilyTrackedRanking

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyGeneratedHistories
open TetraStereo.UniversalProof.SecondSphereFamilyRuntimeInstantiation
open TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment







def leafCursor (i offset : Nat) : CanonicalRerootCursor :=
  { node := pathNode (backboneIndex i + offset) (tagNode i).history,
    previous? := some (tagNode i) }

def priorityCursor (ps : List TetrahedralInputParity) (i : Fin ps.length) : Fin 4 → CanonicalRerootCursor
  | ⟨0, _⟩ => leafCursor i.val 7
  | ⟨1, _⟩ => familyBridgeCursor ps i
  | ⟨2, _⟩ => familyMethylCursor ps i
  | ⟨3, _⟩ => leafCursor i.val 6

def writtenCursors (ps : List TetrahedralInputParity) (i : Fin ps.length) : List CanonicalRerootCursor :=
  [familyBridgeCursor ps i, leafCursor i.val 6, leafCursor i.val 7, familyMethylCursor ps i]

def priorityCursors (ps : List TetrahedralInputParity) (i : Fin ps.length) : List CanonicalRerootCursor :=
  [leafCursor i.val 7, familyBridgeCursor ps i, familyMethylCursor ps i, leafCursor i.val 6]

private theorem cursor_observed (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (slot : Fin 4) : ObservedReal (familyRaw ps) (priorityCursor ps i slot) := by
  fin_cases slot
  · exact ⟨rfl, _, familyRaw_role_atom ps i 7 (by decide)⟩
  · exact ⟨rfl, _, familyRaw_role_atom ps i 2 (by decide)⟩
  · exact ⟨rfl, _, familyRaw_role_atom ps i 8 (by decide)⟩
  · exact ⟨rfl, _, familyRaw_role_atom ps i 6 (by decide)⟩

private theorem cursor_Z (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (slot : Fin 4) :
    (familyRaw ps).atomZAt (priorityCursor ps i slot).node.atom =
      ([9, 6, 6, 1] : List Nat).get slot := by
  fin_cases slot
  · exact (familyRaw_terminal_Z ps i).2.2.2.2.1
  · exact (familyRaw_interior_carbon_Z ps i).2.1
  · exact (familyRaw_interior_carbon_Z ps i).2.2.2
  · exact (familyRaw_terminal_Z ps i).2.2.2.1

private theorem unequal_comparison (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (a b : Fin 4) (different :
      ([9, 6, 6, 1] : List Nat).get a ≠ ([9, 6, 6, 1] : List Nat).get b) :
    ∀ state : OccurrenceAuxState,
    compareOccurrenceBranchesComplete? (familyRaw ps) state fuel
      (priorityCursor ps i a) (priorityCursor ps i b) =
      some { ordering := (compare (([9, 6, 6, 1] : List Nat).get a)
        (([9, 6, 6, 1] : List Nat).get b)) } := by
  intro state
  have ranks : (familyRaw ps).atomZAt (priorityCursor ps i a).node.atom ≠
      (familyRaw ps).atomZAt (priorityCursor ps i b).node.atom := by
    rw [cursor_Z, cursor_Z]
    exact different
  rw [actual_complete_comparison _ state fuel _ _ (cursor_observed ps i a)
    (cursor_observed ps i b) ranks, cursor_Z, cursor_Z]

/-- All twelve strict ordered pairs, including both repeated-carbon directions.
Only a positive comparison-fuel bound is required; arbitrary auxiliary state is in the conclusion. -/
theorem actual_all_pairs (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (positive : 1 ≤ fuel) :
    ∀ state : OccurrenceAuxState, ∀ a b : Fin 4, a ≠ b →
    compareOccurrenceBranchesComplete? (familyRaw ps) state fuel
      (priorityCursor ps i a) (priorityCursor ps i b) =
      some { ordering := compare (4 - a.val) (4 - b.val) } := by
  intro state a b different
  fin_cases a <;> fin_cases b
  · exact False.elim (different rfl)
  · exact unequal_comparison ps i fuel 0 1 (by decide +kernel) state
  · exact unequal_comparison ps i fuel 0 2 (by decide +kernel) state
  · exact unequal_comparison ps i fuel 0 3 (by decide +kernel) state
  · exact unequal_comparison ps i fuel 1 0 (by decide +kernel) state
  · exact False.elim (different rfl)
  · exact (family_complete_protocol_positive ps i fuel positive state).1
  · exact unequal_comparison ps i fuel 1 3 (by decide +kernel) state
  · exact unequal_comparison ps i fuel 2 0 (by decide +kernel) state
  · exact (family_complete_protocol_positive ps i fuel positive state).2
  · exact False.elim (different rfl)
  · exact unequal_comparison ps i fuel 2 3 (by decide +kernel) state
  · exact unequal_comparison ps i fuel 3 0 (by decide +kernel) state
  · exact unequal_comparison ps i fuel 3 1 (by decide +kernel) state
  · exact unequal_comparison ps i fuel 3 2 (by decide +kernel) state
  · exact False.elim (different rfl)

private theorem tag_child_fresh (i offset : Nat) (larger : 5 < offset) :
    backboneIndex i + offset ∉ (tagNode i).history := by
  intro member
  simp only [tagNode, pathNode, List.mem_cons] at member
  rcases member with same | same | same | member
  · omega
  · omega
  · omega
  · have lower := backboneTail_lt i _ member
    omega

private theorem actual_tag_children (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).canonicalChildren (tagNode i.val) =
      [(leafCursor i.val 6).node, (leafCursor i.val 7).node, (familyMethylCursor ps i).node] := by
  have copies := canonicalChildCopies_of_single (familyRaw ps) (tagNode i.val)
    (familyRaw_incident_order ps _)
  change (familyRaw ps).canonicalChildCopies (tagNode i.val) =
    ((recordNeighbors (familyRaw ps) (backboneIndex i.val + 5)).erase
      (backboneIndex i.val + 2)).map (fun other => (other, 0)) at copies
  have row : recordNeighbors (familyRaw ps) (backboneIndex i.val + 5) =
      [backboneIndex i.val + 2, backboneIndex i.val + 6,
       backboneIndex i.val + 7, backboneIndex i.val + 8] := familyRaw_tag_records ps i
  rw [row, List.erase_cons_head] at copies
  have f6 := tag_child_fresh i.val 6 (by decide)
  have f7 := tag_child_fresh i.val 7 (by decide)
  have f8 := tag_child_fresh i.val 8 (by decide)
  have forced : (tagNode i.val).forcedLeaf = false := rfl
  rw [canonicalChildren, forced]
  simp only [Bool.false_eq_true, ↓reduceIte, copies, List.map_cons, List.map_nil]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.contains_eq_mem, f6, f7, f8, decide_false]
  rfl

/-- Exact production frame of the actual generated tag occurrence, rooted at backbone atom 1. -/
theorem actual_original_frame (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    occurrenceLigandFrame? (familyRaw ps) (tagNode i.val) = some (writtenCursors ps i) := by
  have parent : canonicalOriginalParent? (tagNode i.val) = some (bridgeNode i.val) := rfl
  have forced : (tagNode i.val).forcedLeaf = false := rfl
  have cursors : occurrenceLigandCursors (familyRaw ps) (tagNode i.val) = writtenCursors ps i := by
    unfold occurrenceLigandCursors CanonicalRerootCursor.children CanonicalRerootCursor.neighbors
    rw [forced]
    simp only [Bool.false_eq_true, ↓reduceIte, parent, actual_tag_children,
      Option.toList_some, List.singleton_append, List.filterMap_cons, List.filterMap_nil]
    rfl
  have ligands := SecondSphereInitialSeedBridge.actual_tag_ligands ps i
  change (familyRaw ps).ligandsWithLonePair (tagNode i.val).atom = _ at ligands
  have four : ((familyRaw ps).ligandsWithLonePair (tagNode i.val).atom).length = 4 := by
    rw [ligands]
    change ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)).length = 4
    rw [familyRaw_tag_written ps i]
    rfl
  simp only [occurrenceLigandFrame?, four, cursors, writtenCursors,
    List.length_cons, List.length_nil, Nat.reduceAdd, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- All four tracked cursors have genuine generation in the atom1-rooted tree. -/
theorem actual_four_generated (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ∀ cursor ∈ writtenCursors ps i, CanonicalCenterRerootCursor (familyRaw ps) 1 cursor := by
  intro cursor member
  simp only [writtenCursors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact family_incoming_generated ps i
  · apply CanonicalCenterRerootCursor.descending (familyRaw_tag_generated ps i)
    apply pathNode_real_child_mem (familyRaw ps) _ _ (familyRaw_incident_order ps _) _
    · change backboneIndex i.val + 6 ∈ recordNeighbors (familyRaw ps) (backboneIndex i.val + 5)
      have row : recordNeighbors (familyRaw ps) (backboneIndex i.val + 5) =
          [backboneIndex i.val + 2, backboneIndex i.val + 6,
           backboneIndex i.val + 7, backboneIndex i.val + 8] := familyRaw_tag_records ps i
      rw [row]
      simp
    · change backboneIndex i.val + 6 ≠ backboneIndex i.val + 2
      omega
    · exact tag_child_fresh i.val 6 (by decide)
  · apply CanonicalCenterRerootCursor.descending (familyRaw_tag_generated ps i)
    apply pathNode_real_child_mem (familyRaw ps) _ _ (familyRaw_incident_order ps _) _
    · change backboneIndex i.val + 7 ∈ recordNeighbors (familyRaw ps) (backboneIndex i.val + 5)
      have row : recordNeighbors (familyRaw ps) (backboneIndex i.val + 5) =
          [backboneIndex i.val + 2, backboneIndex i.val + 6,
           backboneIndex i.val + 7, backboneIndex i.val + 8] := familyRaw_tag_records ps i
      rw [row]
      simp
    · change backboneIndex i.val + 7 ≠ backboneIndex i.val + 2
      omega
    · exact tag_child_fresh i.val 7 (by decide)
  · exact family_outgoing_generated ps i

/-- The real production tracked sorter, zero pseudo-count, original-history cursors. -/
theorem actual_tracked_sort (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (positive : 1 ≤ fuel) :
    ∀ state : OccurrenceAuxState,
    sortOccurrencesTrackedAuthoritative? (familyRaw ps) state fuel (writtenCursors ps i) =
      some (priorityCursors ps i, 0) := by
  intro state
  have p10 := actual_all_pairs ps i fuel positive state 1 0 (by decide)
  have p02 := actual_all_pairs ps i fuel positive state 0 2 (by decide)
  have p12 := actual_all_pairs ps i fuel positive state 1 2 (by decide)
  have p30 := actual_all_pairs ps i fuel positive state 3 0 (by decide)
  have p32 := actual_all_pairs ps i fuel positive state 3 2 (by decide)
  simp only [priorityCursor] at p10 p02 p12 p30 p32
  simp [writtenCursors, priorityCursors, sortOccurrencesTrackedAuthoritative?,
    insertOccurrenceTrackedAuthoritative?, p10, p02, p12, p30, p32,
    Nat.compare_eq_ite_lt]

/-- Lookup positions in the actual written ligand row, independent of a desired permutation input. -/
theorem actual_written_positions (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    runtimePriorityPositions? (familyRaw ps) (tagNode i.val).atom (priorityCursors ps i) =
      some [2, 0, 3, 1] := by
  have ligands := SecondSphereInitialSeedBridge.actual_tag_ligands ps i
  have written : (familyRaw ps).writtenNeighbors (backboneIndex i.val + 5) =
      [backboneIndex i.val + 2, backboneIndex i.val + 6,
       backboneIndex i.val + 7, backboneIndex i.val + 8] := familyRaw_tag_written ps i
  change (familyRaw ps).ligandsWithLonePair (backboneIndex i.val + 5) =
    (familyRaw ps).writtenNeighbors (backboneIndex i.val + 5) at ligands
  have n26 : backboneIndex i.val + 2 ≠ backboneIndex i.val + 6 := by omega
  have n27 : backboneIndex i.val + 2 ≠ backboneIndex i.val + 7 := by omega
  have n28 : backboneIndex i.val + 2 ≠ backboneIndex i.val + 8 := by omega
  have n67 : backboneIndex i.val + 6 ≠ backboneIndex i.val + 7 := by omega
  have n68 : backboneIndex i.val + 6 ≠ backboneIndex i.val + 8 := by omega
  have n78 : backboneIndex i.val + 7 ≠ backboneIndex i.val + 8 := by omega
  unfold runtimePriorityPositions?
  change (priorityCursors ps i).mapM (fun cursor =>
    (((familyRaw ps).ligandsWithLonePair (backboneIndex i.val + 5)).zipIdx.find?
      (fun entry => entry.1 == cursor.node.atom)).map Prod.snd) = _
  rw [ligands, written]
  simp [priorityCursors, leafCursor, familyBridgeCursor, familyMethylCursor,
    bridgeNode, methylNode, pathNode]

/-- Adjacent decisive comparisons exactly consumed by occurrenceFactAuthoritative?. -/
theorem actual_adjacent (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (positive : 1 ≤ fuel) :
    ∀ state : OccurrenceAuxState,
    compareOccurrenceAdjacentPairsAuthoritative? (familyRaw ps) state fuel (priorityCursors ps i) =
      some [{ ordering := Ordering.gt }, { ordering := Ordering.gt }, { ordering := Ordering.gt }] := by
  intro state
  have p01 := actual_all_pairs ps i fuel positive state 0 1 (by decide)
  have p12 := actual_all_pairs ps i fuel positive state 1 2 (by decide)
  have p23 := actual_all_pairs ps i fuel positive state 2 3 (by decide)
  simp only [priorityCursor] at p01 p12 p23
  simp [priorityCursors, compareOccurrenceAdjacentPairsAuthoritative?, p01, p12, p23,
    Nat.compare_eq_ite_lt]

/-- Actual original-history occurrence consumer, valid for every auxiliary state.
No environment-construction success or supplied descriptor is a premise. -/
theorem actual_occurrence_fact (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (positive : 1 ≤ fuel) :
    ∀ state : OccurrenceAuxState,
    occurrenceFactAuthoritative? (familyRaw ps) fuel state (tagNode i.val) =
      some { key := canonicalOccurrenceKey (tagNode i.val)
             atom := (tagNode i.val).atom
             descriptor := descriptorOfParity (ps.get i) false
             uppercase := true
             priorityPositions := [2, 0, 3, 1] } := by
  intro state
  obtain ⟨remaining, fuelEq⟩ : ∃ remaining, fuel = remaining + 1 := by
    exact ⟨fuel - 1, by omega⟩
  rw [fuelEq]
  exact NativeFamilyFramedOccurrenceCaller.family_actual_authoritative_occurrence_fact ps i
    (familyRaw_root_bound ps) (familyRaw_tag_generated ps i) rfl state remaining

/-! Discovery uses its actual analysisFuel seed. No FirstZTagDomain is asserted. -/

-- familyResult is re-exported from NativeSecondSphereSeedDiscovery.


-- familyFuel is re-exported from NativeSecondSphereSeedDiscovery.


-- familyInitial is re-exported from NativeSecondSphereSeedDiscovery.


private theorem actual_seed_lookup (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyInitial ps).factAt? (tagIndex i.val) =
      some (SecondSphereInitialSeedBridge.seedFact ps i) := by
  have found := SecondSphereInitialSeedBridge.actual_initial_seed_lookup ps i
  rw [familyRaw_normalized_parsed,
    SecondSphereInitialSeedBridge.actual_materialized_identity] at found
  have index : SecondSphereInitialSeedBridge.roleIndex i.val 5 = tagIndex i.val := by
    unfold SecondSphereInitialSeedBridge.roleIndex tagIndex
    omega
  rw [index] at found
  simpa only [familyInitial, familyResult, familyFuel] using found

private theorem seed_covers_observed_tag (ps : List TetrahedralInputParity)
    (index : Nat) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (observed : (familyRaw ps).atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    ∃ fact, (familyInitial ps).factAt? index = some fact := by
  have actual : observedTag (familyRaw ps) index = some parity := by
    simp only [observedTag, observed, Option.bind_some, tagged]
  obtain ⟨i, position, _⟩ := (familyRaw_observedTag_iff ps index parity).mp actual
  rw [position]
  exact ⟨_, actual_seed_lookup ps i⟩

private theorem initial_fact_fields (ps : List TetrahedralInputParity) (fact : RawDescriptorFact)
    (member : fact ∈ familyInitial ps) : fact.evidenceSize = 0 ∧ fact.uppercase = true := by
  change fact ∈ (List.range (familyResult ps).parsed.atomCount).filterMap
    (SecondSphereInitialSeedBridge.seedEntry ps) at member
  obtain ⟨index, _, computed⟩ := List.mem_filterMap.mp member
  unfold SecondSphereInitialSeedBridge.seedEntry at computed
  cases outcome : tetrahedralOutcomeThroughRule3 (normalizeRawMolecule (familyRaw ps))
    (familyRaw ps) (analysisFuel (familyRaw ps)) index <;> simp_all
  subst fact
  exact ⟨rfl, rfl⟩


-- actual_update_fixed is re-exported from NativeSecondSphereSeedDiscovery.



-- actual_schedule_fixed is re-exported from NativeSecondSphereSeedDiscovery.


-- actual_pass_fixed is re-exported from NativeSecondSphereSeedDiscovery.



-- actual_stabilized is re-exported from NativeSecondSphereSeedDiscovery.


-- actual_unresolved_nil is re-exported from NativeSecondSphereSeedDiscovery.


-- actual_auxiliary_fixed is re-exported from NativeSecondSphereSeedDiscovery.


-- actual_exact_auxiliary_fixed is re-exported from NativeSecondSphereSeedDiscovery.


-- actual_finish_fixed is re-exported from NativeSecondSphereSeedDiscovery.


-- actual_constructive_fixed is re-exported from NativeSecondSphereSeedDiscovery.


private theorem actual_initial_nonempty (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyInitial ps).isEmpty = false := by
  have found := actual_seed_lookup ps i
  have member := List.mem_of_find?_eq_some found
  cases initial : familyInitial ps with
  | nil => rw [initial] at member; exact False.elim (List.not_mem_nil member)
  | cons first rest => rfl

-- actual_source_selected is re-exported from NativeSecondSphereSeedDiscovery.


-- actual_rule6_neutral is re-exported from NativeSecondSphereSeedDiscovery.



-- actual_discovery_is_initial is re-exported from NativeSecondSphereSeedDiscovery.



-- actual_discovered_tag is re-exported from NativeSecondSphereSeedDiscovery.


end TetraStereo.UniversalProof.SecondSphereFamilyTrackedRanking
