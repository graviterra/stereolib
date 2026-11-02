import TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery
import TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery
open TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery













/-- Independent physical record conditions; distant branches may be cyclic and nonterminal. -/
structure AtomicCenterDomain (raw : RawMolecule) (center : Nat) : Prop where
  wellFormed : raw.WellFormed
  centerBound : center < raw.atomCount
  single : ∀ atom ∈ recordNeighbors raw center, raw.bondOrder center atom = 1
  distinctRanks : ((recordNeighbors raw center).map raw.atomZAt).Nodup

theorem AtomicCenterDomain.neighbors_nodup {raw : RawMolecule} {center : Nat}
    (domain : AtomicCenterDomain raw center) : (recordNeighbors raw center).Nodup :=
  List.Nodup.of_map raw.atomZAt domain.distinctRanks

private theorem unitCopies_eq_neighbors (molecule : RawMolecule) (center : ℕ)
    (bonds : List RawBond)
    (single : ∀ bond ∈ bonds, ∀ atom, recordNeighbor? center bond = some atom →
      molecule.bondOrder center atom = 1) :
    (bonds.flatMap fun bond =>
      match recordNeighbor? center bond with
      | none => []
      | some atom => (List.range (molecule.bondOrder center atom)).map (fun copy => (atom, copy))) =
      (bonds.filterMap (recordNeighbor? center)).map (fun atom => (atom, 0)) := by
  induction bonds with
  | nil => rfl
  | cons bond bonds inductionHypothesis =>
      have tailSingle : ∀ selected ∈ bonds, ∀ atom, recordNeighbor? center selected = some atom →
          molecule.bondOrder center atom = 1 := by
        intro selected member atom observed
        exact single selected (List.mem_cons_of_mem bond member) atom observed
      simp only [List.flatMap_cons, List.filterMap_cons]
      cases observed : recordNeighbor? center bond with
      | none => simpa only [List.nil_append] using inductionHypothesis tailSingle
      | some atom =>
          have order := single bond (List.mem_cons_self) atom observed
          simp only [order, List.range_succ, List.range_zero, List.nil_append,
            List.map_cons, List.map_nil, List.cons_append]
          rw [inductionHypothesis tailSingle]

private theorem eraseParent_eq_self (parent : ℕ) (copies : List (ℕ × ℕ))
    (outside : ∀ copy ∈ copies, copy.1 ≠ parent) :
    eraseCanonicalParentCopy parent copies = copies := by
  induction copies with
  | nil => rfl
  | cons copy copies inductionHypothesis =>
      have notParent := outside copy (List.mem_cons_self)
      have remaining : ∀ item ∈ copies, item.1 ≠ parent := by
        intro item member
        exact outside item (List.mem_cons_of_mem copy member)
      simp [eraseCanonicalParentCopy, notParent, inductionHypothesis remaining]

theorem canonicalChildren_centerRoot_eq (molecule : RawMolecule) (center : ℕ)
    (domain : AtomicCenterDomain molecule center) :
    molecule.canonicalChildren (canonicalCenterRoot center) =
      (recordNeighbors molecule center).map (canonicalRoot center) := by
  have seeds := unitCopies_eq_neighbors molecule center molecule.bonds (by
    intro bond member atom observed
    exact domain.single atom (List.mem_filterMap.mpr ⟨bond, member, observed⟩))
  have copies : molecule.canonicalChildCopies (canonicalCenterRoot center) =
      (recordNeighbors molecule center).map (fun atom => (atom, 0)) := by
    change eraseCanonicalParentCopy center
      (molecule.bonds.flatMap fun bond =>
        match recordNeighbor? center bond with
        | none => []
        | some atom => (List.range (molecule.bondOrder center atom)).map (fun copy => (atom, copy))) = _
    rw [seeds]
    apply eraseParent_eq_self
    intro copy member
    obtain ⟨atom, inNeighbors, rfl⟩ := List.mem_map.mp member
    exact (recordNeighbor_bounds domain.wellFormed inNeighbors).2
  unfold canonicalChildren
  have forced : (canonicalCenterRoot center).forcedLeaf = false := rfl
  rw [forced]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [copies, List.map_map]
  apply List.map_congr_left
  intro atom member
  have different := (recordNeighbor_bounds domain.wellFormed member).2
  simp [canonicalCenterRoot, canonicalRoot, different]

/-- Exact same-source runtime cursor generation, including the real previous reference root. -/
theorem generatedRuntimeRoots_eq (molecule : RawMolecule) (center : ℕ)
    (domain : AtomicCenterDomain molecule center) :
    generatedRuntimeRoots molecule center = (recordNeighbors molecule center).map
      (fun atom => { node := canonicalRoot center atom, previous? := some (canonicalCenterRoot center) }) := by
  unfold generatedRuntimeRoots occurrenceLigandCursors CanonicalRerootCursor.children
    CanonicalRerootCursor.neighbors
  have forced : (canonicalCenterRoot center).forcedLeaf = false := rfl
  have parent : canonicalOriginalParent? (canonicalCenterRoot center) = none := rfl
  rw [forced]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [parent]
  simp only [Option.toList_none, List.nil_append]
  rw [canonicalChildren_centerRoot_eq molecule center domain]
  simp only [List.filterMap_map]
  induction recordNeighbors molecule center with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      simp only [List.filterMap_cons, List.map_cons]
      exact congrArg (List.cons _) inductionHypothesis

theorem actual_root_observed (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) (cursor : CanonicalRerootCursor)
    (member : cursor ∈ generatedRuntimeRoots raw center) : ObservedReal raw cursor := by
  rw [generatedRuntimeRoots_eq raw center domain] at member
  obtain ⟨atom, inNeighbors, rfl⟩ := List.mem_map.mp member
  have bound := (recordNeighbor_bounds domain.wellFormed inNeighbors).1
  obtain ⟨spec, observed⟩ := NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.atomAt?_exists_of_lt_atomCount
    raw atom bound
  exact ⟨rfl, spec, observed⟩

theorem actual_root_distinct_ranks (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) :
    ((generatedRuntimeRoots raw center).map (fun cursor => raw.atomZAt cursor.node.atom)).Nodup := by
  rw [generatedRuntimeRoots_eq raw center domain, List.map_map]
  exact domain.distinctRanks

theorem actual_neighbor_positive (raw : RawMolecule) (center atom : Nat)
    (domain : AtomicCenterDomain raw center) :
    atom ∈ recordNeighbors raw center ↔ 0 < raw.bondOrder center atom := by
  constructor
  · intro member
    rw [domain.single atom member]
    exact Nat.zero_lt_one
  · intro positive
    have different : center ≠ atom := by
      intro equal
      subst atom
      have impossible : 0 < (0 : Nat) := by simpa only [raw.bondOrder_self] using positive
      exact (Nat.lt_irrefl 0) impossible
    obtain ⟨bond, retained, connects⟩ := (raw.bondOrder_pos_iff_exists_bond different).mp positive
    apply List.mem_filterMap.mpr
    refine ⟨bond, retained, ?_⟩
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
    rcases connects with ⟨first, second⟩ | ⟨first, second⟩
    · simp [recordNeighbor?, first, second]
    · simp [recordNeighbor?, first, second, Ne.symm different]

theorem actual_written_permutation (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) (written : raw.WrittenNeighborExact) :
    (raw.writtenNeighbors center).Perm (recordNeighbors raw center) := by
  have clauses := RawMolecule.WrittenNeighborExact.at raw written ⟨center, domain.centerBound⟩
  apply List.perm_of_nodup_nodup_toFinset_eq clauses.1 domain.neighbors_nodup
  apply Finset.ext
  intro neighbor
  simp only [List.mem_toFinset]
  rw [HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.source_writtenNeighbors_mem_iff
    raw domain.wellFormed written center domain.centerBound neighbor,
    actual_neighbor_positive raw center neighbor domain]

theorem actual_four_frame (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) :
    occurrenceLigandFrame? raw (canonicalCenterRoot center) =
      some (generatedRuntimeRoots raw center) := by
  have writtenFour := (actual_written_permutation raw center domain written).length_eq.trans four
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center writtenFour
  have rootLength : (generatedRuntimeRoots raw center).length = 4 := by
    rw [generatedRuntimeRoots_eq raw center domain, List.length_map, four]
  unfold occurrenceLigandFrame?
  change (if (raw.ligandsWithLonePair center).length != 4 then none else
    if (generatedRuntimeRoots raw center).length == 4 then some (generatedRuntimeRoots raw center)
      else _) = some (generatedRuntimeRoots raw center)
  simp [ligands, writtenFour, rootLength]

theorem actual_generated_sort (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ result, sortOccurrencesTrackedAuthoritative? raw state fuel
        (generatedRuntimeRoots raw center) = some result ∧
      result.1.Perm (generatedRuntimeRoots raw center) ∧
      result.1.Pairwise (NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.AtomicDesc raw) ∧ result.2 = 0 :=
  actual_sort_distinct_observed raw state fuel (generatedRuntimeRoots raw center)
    (actual_root_observed raw center domain) (actual_root_distinct_ranks raw center domain)

/-- This exact actual adjacent consumer derives its refusal guards from strict observed ranks. -/
theorem actual_observed_adjacent (raw : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) :
    (∀ cursor ∈ roots, ObservedReal raw cursor) →
    roots.Pairwise (NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.AtomicDesc raw) →
    ∃ decisions,
      compareOccurrenceAdjacentPairsAuthoritative? raw state fuel roots = some decisions ∧
      decisions.all (fun decision => decision.ordering != Ordering.eq) = true ∧
      decisions.filter (fun decision => decision.pseudo) = [] ∧
      decisions.length = roots.length - 1 := by
  induction roots with
  | nil => intro _ _; exact ⟨[], rfl, rfl, rfl, rfl⟩
  | cons left remaining ih =>
      intro members sorted
      cases remaining with
      | nil => exact ⟨[], rfl, rfl, rfl, rfl⟩
      | cons right tail =>
          have rightMembers : ∀ cursor ∈ right :: tail, ObservedReal raw cursor := by
            intro cursor member
            exact members cursor (List.mem_cons.mpr (Or.inr member))
          have rightSorted := (List.pairwise_cons.mp sorted).2
          obtain ⟨decisions, computed, strict, pseudo, length⟩ := ih rightMembers rightSorted
          have higher := (List.pairwise_cons.mp sorted).1 right List.mem_cons_self
          have different : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom := by
            intro equal
            exact (Nat.ne_of_lt higher) equal.symm
          have comparison := actual_complete_comparison raw state fuel left right
            (members left List.mem_cons_self) (rightMembers right List.mem_cons_self) different
          rw [Nat.compare_eq_gt.mpr higher] at comparison
          refine ⟨{ ordering := Ordering.gt, pseudo := false } :: decisions, ?_, ?_, ?_, ?_⟩
          · simp [compareOccurrenceAdjacentPairsAuthoritative?, comparison, computed]
          · simpa using strict
          · simpa using pseudo
          · simpa only [List.length_cons, Nat.add_sub_cancel] using congrArg Nat.succ length

theorem actual_generated_written_slot (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) (written : raw.WrittenNeighborExact)
    (cursor : CanonicalRerootCursor) (member : cursor ∈ generatedRuntimeRoots raw center) :
    ∃ position, writtenSlot? (raw.writtenNeighbors center) cursor.node.atom = some position := by
  have permutation := actual_written_permutation raw center domain written
  have distinct := permutation.nodup_iff.mpr domain.neighbors_nodup
  rw [generatedRuntimeRoots_eq raw center domain] at member
  obtain ⟨atom, inRecords, rfl⟩ := List.mem_map.mp member
  have inWritten := permutation.mem_iff.mpr inRecords
  obtain ⟨position, observed⟩ := List.mem_iff_getElem?.mp inWritten
  exact ⟨position, writtenSlot?_eq_some _ distinct position atom observed⟩

theorem actual_positions_exists (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) (roots : List CanonicalRerootCursor) :
    (∀ cursor ∈ roots, cursor ∈ generatedRuntimeRoots raw center) →
    ∃ positions, runtimePriorityPositions? raw center roots = some positions := by
  have writtenFour := (actual_written_permutation raw center domain written).length_eq.trans four
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center writtenFour
  unfold runtimePriorityPositions?
  rw [ligands]
  change (∀ cursor ∈ roots, cursor ∈ generatedRuntimeRoots raw center) →
    ∃ positions, roots.mapM (fun cursor => writtenSlot? (raw.writtenNeighbors center) cursor.node.atom) = some positions
  induction roots with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons cursor tail ih =>
      intro members
      obtain ⟨position, observed⟩ := actual_generated_written_slot raw center domain written cursor
        (members cursor List.mem_cons_self)
      obtain ⟨positions, tailComputed⟩ := ih
        (fun other member => members other (List.mem_cons.mpr (Or.inr member)))
      exact ⟨position :: positions, by simp [List.mapM_cons, observed, tailComputed]⟩

/-- The actual local runtime fact, at all budgets/states, from original records and an actual tag. -/
theorem actual_local_fact (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ positions, occurrenceFactAuthoritative? raw fuel state (canonicalCenterRoot center) =
      some (recoveredFact center positions (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions))) := by
  obtain ⟨result, computed, permutation, sorted, _⟩ := actual_generated_sort raw center domain state fuel
  have members : ∀ cursor ∈ result.1, cursor ∈ generatedRuntimeRoots raw center :=
    fun cursor member => permutation.mem_iff.mp member
  obtain ⟨positions, positionsComputed⟩ := actual_positions_exists raw center domain written four
    result.1 members
  obtain ⟨decisions, decisionsComputed, strict, pseudo, _⟩ := actual_observed_adjacent raw state fuel
    result.1 (fun cursor member => actual_root_observed raw center domain cursor (members cursor member)) sorted
  exact ⟨positions, actual_fact_of_program_bindings raw center fuel state spec parity atomObserved
    parityObserved result positions decisions _ (actual_four_frame raw center domain written four)
    computed positionsComputed decisionsComputed strict pseudo rfl
    (actual_root_observed raw center domain) (actual_root_distinct_ranks raw center domain)⟩

/-- Genuine public construction: the environment, roots, sorter, positions and all refusal checks
are derived internally. No leaf/cycle-free condition or expected result is provided. -/
theorem actual_public_fact (raw : RawMolecule) (center fuel : Nat)
    (domain : AtomicCenterDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) (only : OnlyCenterTagged raw center)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (enough : raw.atomCount + 1 ≤ fuel) :
    ∃ positions, tetrahedralOccurrenceFact? raw fuel center =
      some (recoveredPublicFact center positions (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions))) := by
  obtain ⟨positions, computed⟩ := actual_local_fact raw center domain written four spec atomObserved
    parity parityObserved [] fuel
  exact ⟨positions, public_fact_of_actual_local_fact raw fuel center only
    (prefixTree raw center 0 fuel)
    (actual_collector_complete raw center fuel domain.wellFormed domain.centerBound enough)
    positions _ computed⟩

namespace CyclicTagged

/-- This raw fixture actually carries clockwise parity on its center; both carbon/silicon
branches are ordinary-single triangles. No detached state or parser label is imported. -/
def raw : RawMolecule :=
  { atoms := [{ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise },
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .C, AtomSpec.aliphatic .C,
      AtomSpec.aliphatic .Si, AtomSpec.aliphatic .C, AtomSpec.aliphatic .C,
      AtomSpec.aliphatic .F, AtomSpec.aliphatic .Br]
    bonds := [⟨0, 1, .single⟩, ⟨0, 4, .single⟩, ⟨0, 7, .single⟩, ⟨0, 8, .single⟩,
      ⟨1, 2, .single⟩, ⟨2, 3, .single⟩, ⟨3, 1, .single⟩,
      ⟨4, 5, .single⟩, ⟨5, 6, .single⟩, ⟨6, 4, .single⟩]
    neighborOrder := [[1, 4, 7, 8], [0, 2, 3], [1, 3], [2, 1], [0, 5, 6],
      [4, 6], [5, 4], [0], [0]] }

def root (atom : Nat) : CanonicalRerootCursor :=
  { node := canonicalRoot 0 atom, previous? := some (canonicalCenterRoot 0) }

theorem actual_admissible : raw.StereochemicalAdmissible := by
  apply (stereochemicalAdmissible?_eq_true_iff raw).mp
  decide +kernel

theorem actual_domain : AtomicCenterDomain raw 0 := by
  refine ⟨actual_admissible.1.1, by decide +kernel, ?_, by decide +kernel⟩
  intro atom member
  change atom ∈ [1, 4, 7, 8] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide +kernel

theorem actual_four : (recordNeighbors raw 0).length = 4 := by decide +kernel

theorem actual_generated : generatedRuntimeRoots raw 0 = [root 1, root 4, root 7, root 8] := by
  rw [generatedRuntimeRoots_eq raw 0 actual_domain]
  rfl

theorem actual_cyclic_nonleaf : raw.atomLiesInCycle 5 1 = true ∧
    raw.atomLiesInCycle 5 4 = true ∧ (raw.incidentAtoms 1).length = 3 ∧
    (raw.incidentAtoms 4).length = 3 := by decide +kernel

theorem actual_only_center : OnlyCenterTagged raw 0 := by
  intro index spec observed tagged
  change Fin 9 at index
  fin_cases index <;> simp [raw, atomAt?, listGet?] at observed
  all_goals subst spec
  all_goals simp_all [AtomSpec.aliphatic]

theorem actual_root_observed (atom : Nat) (member : atom ∈ recordNeighbors raw 0) :
    ObservedReal raw (root atom) := by
  apply NonleafPublicOccurrenceRecovery.actual_root_observed raw 0 actual_domain
  rw [generatedRuntimeRoots_eq raw 0 actual_domain]
  exact List.mem_map.mpr ⟨atom, member, rfl⟩

theorem actual_sort (state : OccurrenceAuxState) (fuel : Nat) :
    sortOccurrencesTrackedAuthoritative? raw state fuel (generatedRuntimeRoots raw 0) =
      some ([root 8, root 4, root 7, root 1], 0) := by
  have c := actual_root_observed 1 (by decide +kernel)
  have si := actual_root_observed 4 (by decide +kernel)
  have f := actual_root_observed 7 (by decide +kernel)
  have br := actual_root_observed 8 (by decide +kernel)
  have fbr := actual_complete_comparison raw state fuel (root 7) (root 8) f br (by decide +kernel)
  have sibr := actual_complete_comparison raw state fuel (root 4) (root 8) si br (by decide +kernel)
  have sif := actual_complete_comparison raw state fuel (root 4) (root 7) si f (by decide +kernel)
  have cbr := actual_complete_comparison raw state fuel (root 1) (root 8) c br (by decide +kernel)
  have csi := actual_complete_comparison raw state fuel (root 1) (root 4) c si (by decide +kernel)
  have cf := actual_complete_comparison raw state fuel (root 1) (root 7) c f (by decide +kernel)
  change _ = some ({ ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } : OccurrenceComparison) at fbr
  change _ = some ({ ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } : OccurrenceComparison) at sibr
  change _ = some ({ ordering := Ordering.gt, pseudo := false, rule4cCarrier? := none } : OccurrenceComparison) at sif
  change _ = some ({ ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } : OccurrenceComparison) at cbr
  change _ = some ({ ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } : OccurrenceComparison) at csi
  change _ = some ({ ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } : OccurrenceComparison) at cf
  rw [actual_generated]
  simp [sortOccurrencesTrackedAuthoritative?, insertOccurrenceTrackedAuthoritative?,
    fbr, sibr, sif, cbr, csi, cf]

theorem actual_positions : runtimePriorityPositions? raw 0 [root 8, root 4, root 7, root 1] =
    some [3, 1, 2, 0] := by decide +kernel

theorem actual_local_S (state : OccurrenceAuxState) (fuel : Nat) :
    occurrenceFactAuthoritative? raw fuel state (canonicalCenterRoot 0) =
      some (recoveredFact 0 [3, 1, 2, 0] .S) := by
  obtain ⟨result, sortComputed, permutation, sorted, _⟩ :=
    actual_generated_sort raw 0 actual_domain state fuel
  have equal : result = ([root 8, root 4, root 7, root 1], 0) :=
    Option.some.inj (sortComputed.symm.trans (actual_sort state fuel))
  subst result
  have observed : ∀ cursor ∈ [root 8, root 4, root 7, root 1], ObservedReal raw cursor := by
    intro cursor member
    exact NonleafPublicOccurrenceRecovery.actual_root_observed raw 0 actual_domain cursor
      (permutation.mem_iff.mp member)
  obtain ⟨decisions, computed, strict, pseudo, _⟩ :=
    actual_observed_adjacent raw state fuel _ observed sorted
  exact actual_fact_of_program_bindings raw 0 fuel state
    { AtomSpec.aliphatic .C with tetrahedral? := some .clockwise } .clockwise rfl rfl
    ([root 8, root 4, root 7, root 1], 0) [3, 1, 2, 0] decisions .S
    (actual_four_frame raw 0 actual_domain actual_admissible.2 actual_four)
    (actual_sort state fuel) actual_positions computed strict pseudo (by decide +kernel)
    (NonleafPublicOccurrenceRecovery.actual_root_observed raw 0 actual_domain)
    (NonleafPublicOccurrenceRecovery.actual_root_distinct_ranks raw 0 actual_domain)

/-- Actual full public output at every sufficiently large budget on the cyclic/nonleaf input. -/
theorem actual_public_S (fuel : Nat) (enough : 10 ≤ fuel) :
    tetrahedralOccurrenceFact? raw fuel 0 = some (recoveredPublicFact 0 [3, 1, 2, 0] .S) :=
  public_fact_of_actual_local_fact raw fuel 0 actual_only_center (prefixTree raw 0 0 fuel)
    (actual_collector_complete raw 0 fuel actual_domain.wellFormed actual_domain.centerBound enough)
    [3, 1, 2, 0] .S (actual_local_S [] fuel)

theorem actual_environment (fuel : Nat) (enough : 10 ≤ fuel) :
    buildOccurrenceAuxStateFullyAuthoritative? raw fuel 0 = some [] :=
  actual_auxiliary_empty raw 0 fuel actual_domain.wellFormed actual_domain.centerBound
    actual_only_center enough

end CyclicTagged

end TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
