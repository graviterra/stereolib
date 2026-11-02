import TetraStereo.UniversalProof.NativeFamilyRawSupport
import TetraStereo.UniversalProof.NativeRawRecordBounds
import TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
import TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport
import TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport
import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking






















-- recordNeighbor? is re-exported from NativeFamilyRawSupport.


-- recordNeighbors is re-exported from NativeFamilyRawSupport.


/-- This is the actual runtime generator, not a surrogate list of ranked atom IDs. -/
def generatedRuntimeRoots (molecule : RawMolecule) (center : ℕ) : List CanonicalRerootCursor :=
  occurrenceLigandCursors molecule (canonicalCenterRoot center)

/-- Independent finite graph domain. No generated cursor, key, cycle-test result or sorting
conclusion occurs in its fields. Distinct source ranks imply distinct record-neighbor entries. -/
structure LeafNeighborDomain (molecule : RawMolecule) (center : ℕ) : Prop where
  wellFormed : molecule.WellFormed
  centerBound : center < molecule.atomCount
  singleEdges : (recordNeighbors molecule center).all
    (fun atom => decide (molecule.bondOrder center atom = 1)) = true
  leafNeighbors : (recordNeighbors molecule center).all
    (fun atom => decide ((molecule.incidentAtoms atom).length ≤ 1)) = true
  distinctRanks : ((recordNeighbors molecule center).map molecule.atomZAt).Nodup

theorem LeafNeighborDomain.neighbors_nodup {molecule : RawMolecule} {center : ℕ}
    (domain : LeafNeighborDomain molecule center) : (recordNeighbors molecule center).Nodup :=
  List.Nodup.of_map molecule.atomZAt domain.distinctRanks

theorem LeafNeighborDomain.single {molecule : RawMolecule} {center atom : ℕ}
    (domain : LeafNeighborDomain molecule center) (member : atom ∈ recordNeighbors molecule center) :
    molecule.bondOrder center atom = 1 :=
  of_decide_eq_true ((List.all_eq_true.mp domain.singleEdges) atom member)

theorem LeafNeighborDomain.leaf {molecule : RawMolecule} {center atom : ℕ}
    (domain : LeafNeighborDomain molecule center) (member : atom ∈ recordNeighbors molecule center) :
    (molecule.incidentAtoms atom).length ≤ 1 :=
  of_decide_eq_true ((List.all_eq_true.mp domain.leafNeighbors) atom member)

theorem LeafNeighborDomain.rank_injective {molecule : RawMolecule} {center : ℕ}
    (domain : LeafNeighborDomain molecule center) {left right : ℕ}
    (leftMember : left ∈ recordNeighbors molecule center)
    (rightMember : right ∈ recordNeighbors molecule center)
    (equal : molecule.atomZAt left = molecule.atomZAt right) : left = right :=
  (List.nodup_map_iff_inj_on domain.neighbors_nodup).mp domain.distinctRanks
    left leftMember right rightMember equal


-- recordNeighbor_bounds is re-exported from NativeRawRecordBounds.


/-- A leaf's actual graph cycle test is false at every fuel; ancestry is not used as a substitute. -/
theorem atomLiesInCycle_false_of_degree_le_one (molecule : RawMolecule) (atom fuel : ℕ)
    (degree : (molecule.incidentAtoms atom).length ≤ 1) :
    molecule.atomLiesInCycle fuel atom = false := by
  cases observed : molecule.incidentAtoms atom with
  | nil => simp [atomLiesInCycle, observed, ringPairCount]
  | cons head tail =>
      cases tail with
      | nil => simp [atomLiesInCycle, observed, ringPairCount]
      | cons second rest =>
          simp only [observed, List.length_cons] at degree
          omega

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

/-- The actual canonical generator has precisely the source record-neighbor roots, in its real
production order. Real provenance is derived from single edges and well-formed endpoints. -/
theorem canonicalChildren_centerRoot_eq (molecule : RawMolecule) (center : ℕ)
    (domain : LeafNeighborDomain molecule center) :
    molecule.canonicalChildren (canonicalCenterRoot center) =
      (recordNeighbors molecule center).map (canonicalRoot center) := by
  have seeds := unitCopies_eq_neighbors molecule center molecule.bonds (by
    intro bond member atom observed
    exact domain.single (List.mem_filterMap.mpr ⟨bond, member, observed⟩))
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
    (domain : LeafNeighborDomain molecule center) :
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

/-- A returned runtime root denotes an actual same-source atom, with actual generated ancestry and
reference frame. The source record lookup is derived from its bound. -/
theorem generated_root_meaning (molecule : RawMolecule) (center : ℕ)
    (domain : LeafNeighborDomain molecule center) (cursor : CanonicalRerootCursor)
    (member : cursor ∈ generatedRuntimeRoots molecule center) :
    cursor.node = canonicalRoot center cursor.node.atom ∧
      cursor.previous? = some (canonicalCenterRoot center) ∧
      cursor.node.atom < molecule.atomCount ∧
      ∃ spec, molecule.atomAt? cursor.node.atom = some spec ∧
        molecule.atomZAt cursor.node.atom = spec.element.atomicNumber := by
  rw [generatedRuntimeRoots_eq molecule center domain] at member
  obtain ⟨atom, inNeighbors, rfl⟩ := List.mem_map.mp member
  have bound := (recordNeighbor_bounds domain.wellFormed inNeighbors).1
  obtain ⟨spec, observed⟩ :=
    TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.atomAt?_exists_of_lt_atomCount
      molecule atom bound
  exact ⟨rfl, rfl, bound, spec, observed,
    TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.atomZAt_eq_of_atomAt?
      molecule atom spec observed⟩

/-- These are actual center-tree nodes, not detached canonical roots chosen by a caller. -/
theorem generated_root_tree (molecule : RawMolecule) (center : ℕ)
    (domain : LeafNeighborDomain molecule center) (cursor : CanonicalRerootCursor)
    (member : cursor ∈ generatedRuntimeRoots molecule center) :
    CanonicalCenterTreeNode molecule center cursor.node := by
  rw [generatedRuntimeRoots_eq molecule center domain] at member
  obtain ⟨atom, inNeighbors, rfl⟩ := List.mem_map.mp member
  apply CanonicalCenterTreeNode.child CanonicalCenterTreeNode.root
  rw [canonicalChildren_centerRoot_eq molecule center domain]
  exact List.mem_map.mpr ⟨atom, inNeighbors, rfl⟩

/-- Actual generated roots retain duplicate-free, bounded histories. This is provenance only;
physical cycle exclusion is derived separately from the source leaf condition. -/
theorem generated_root_history (molecule : RawMolecule) (center : ℕ)
    (domain : LeafNeighborDomain molecule center) (cursor : CanonicalRerootCursor)
    (member : cursor ∈ generatedRuntimeRoots molecule center) :
    cursor.node.history.Nodup ∧ ∀ atom, atom ∈ cursor.node.history → atom < molecule.atomCount := by
  have generated := generated_root_tree molecule center domain cursor member
  have real : cursor.node.provenance = CanonicalNodeProvenance.realAtom := by
    rw [(generated_root_meaning molecule center domain cursor member).1]
    rfl
  exact generated.real_history domain.centerBound domain.wellFormed real

/-- The rank domain required by checked99 is derived for each ACTUAL generated root from the
independent graph class. In particular physical leaf degree derives actual cycle false. -/
theorem generated_root_realOutsideCycle (molecule : RawMolecule) (center fuel : ℕ)
    (domain : LeafNeighborDomain molecule center) (cursor : CanonicalRerootCursor)
    (member : cursor ∈ generatedRuntimeRoots molecule center) :
    TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.RealOutsideCycle molecule fuel cursor := by
  rw [generatedRuntimeRoots_eq molecule center domain] at member
  obtain ⟨atom, inNeighbors, rfl⟩ := List.mem_map.mp member
  exact ⟨rfl, (recordNeighbor_bounds domain.wellFormed inNeighbors).1,
    atomLiesInCycle_false_of_degree_le_one molecule atom fuel (domain.leaf inNeighbors)⟩

theorem generated_roots_nodup (molecule : RawMolecule) (center : ℕ)
    (domain : LeafNeighborDomain molecule center) : (generatedRuntimeRoots molecule center).Nodup := by
  rw [generatedRuntimeRoots_eq molecule center domain]
  exact domain.neighbors_nodup.map (by
    intro first second equal
    exact congrArg (fun cursor : CanonicalRerootCursor => cursor.node.atom) equal)

theorem generated_roots_rank_injective (molecule : RawMolecule) (center : ℕ)
    (domain : LeafNeighborDomain molecule center) (left right : CanonicalRerootCursor)
    (leftMember : left ∈ generatedRuntimeRoots molecule center)
    (rightMember : right ∈ generatedRuntimeRoots molecule center)
    (equal : molecule.atomZAt left.node.atom = molecule.atomZAt right.node.atom) : left = right := by
  rw [generatedRuntimeRoots_eq molecule center domain] at leftMember rightMember
  obtain ⟨leftAtom, leftSource, rfl⟩ := List.mem_map.mp leftMember
  obtain ⟨rightAtom, rightSource, rfl⟩ := List.mem_map.mp rightMember
  have atomEqual := domain.rank_injective leftSource rightSource equal
  rw [atomEqual]

/-- Actual composed runtime callback at generated roots, expressed over recovered actual AtomSpecs.
The state is arbitrary; no callback identity or label/sort success is assumed. -/
theorem generated_compare_complete (molecule : RawMolecule) (center fuel : ℕ)
    (domain : LeafNeighborDomain molecule center) (state : OccurrenceAuxState)
    (left right : CanonicalRerootCursor)
    (leftMember : left ∈ generatedRuntimeRoots molecule center)
    (rightMember : right ∈ generatedRuntimeRoots molecule center) (different : left ≠ right) :
    ∃ leftSpec rightSpec, molecule.atomAt? left.node.atom = some leftSpec ∧
      molecule.atomAt? right.node.atom = some rightSpec ∧
      compareOccurrenceBranchesComplete? molecule state fuel left right =
        some { ordering := compare leftSpec.element.atomicNumber rightSpec.element.atomicNumber, pseudo := false } := by
  have leftDomain := generated_root_realOutsideCycle molecule center fuel domain left leftMember
  have rightDomain := generated_root_realOutsideCycle molecule center fuel domain right rightMember
  have rankDifferent : molecule.atomZAt left.node.atom ≠ molecule.atomZAt right.node.atom := by
    intro equal
    exact different (generated_roots_rank_injective molecule center domain left right leftMember rightMember equal)
  exact TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.compareOccurrenceBranchesComplete?_eq_of_rule1a_sourceBounded
    molecule state fuel left right leftDomain.1 rightDomain.1 rankDifferent
    (Or.inl leftDomain.2.2) leftDomain.2.1 rightDomain.2.1

/-- The ACTUAL authoritative runtime sorter succeeds on its generated center roots from graph
inputs alone. This is not the formal supplied-callback Fin4 rank sorter. -/
theorem generated_runtime_sort (molecule : RawMolecule) (center fuel : ℕ)
    (domain : LeafNeighborDomain molecule center) (state : OccurrenceAuxState) :
    ∃ result, sortOccurrencesTrackedAuthoritative? molecule state fuel
        (generatedRuntimeRoots molecule center) = some result ∧
      result.1.Perm (generatedRuntimeRoots molecule center) ∧
      result.1.Pairwise (TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.AtomicDesc molecule) ∧
      result.2 = 0 :=
  TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.sortOccurrencesTrackedAuthoritative?_rankDomain
    molecule state fuel (generatedRuntimeRoots molecule center)
    (generated_roots_nodup molecule center domain)
    (fun cursor member => generated_root_realOutsideCycle molecule center fuel domain cursor member)
    (fun left leftMember right rightMember equal =>
      generated_roots_rank_injective molecule center domain left right leftMember rightMember equal)

/-- A generated root of the actual materialized raw molecule is either an original source atom
with exact materialized metadata, or an actual appended ordinary H of incident order one. -/
theorem generated_expanded_source_fact (molecule : RawMolecule) (well : molecule.WellFormed)
    (center : ℕ) (domain : LeafNeighborDomain molecule.withExplicitHydrogens center)
    (cursor : CanonicalRerootCursor)
    (member : cursor ∈ generatedRuntimeRoots molecule.withExplicitHydrogens center) :
    ∃ out, molecule.withExplicitHydrogens.atomAt? cursor.node.atom = some out ∧
      ((∃ source, molecule.atomAt? cursor.node.atom = some source ∧ out = materializedAtomSpec source) ∨
        (molecule.atomCount ≤ cursor.node.atom ∧ out = AtomSpec.aliphatic Element.H ∧
          molecule.withExplicitHydrogens.incidentBondOrderSum cursor.node.atom = 1)) := by
  obtain ⟨_, _, _, out, observed, _⟩ := generated_root_meaning molecule.withExplicitHydrogens center domain cursor member
  refine ⟨out, observed, ?_⟩
  by_cases old : cursor.node.atom < molecule.atomCount
  · obtain ⟨source, sourceObserved⟩ :=
      TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.atomAt?_exists_of_lt_atomCount
        molecule cursor.node.atom old
    have transported := TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_originalAtom
      molecule well cursor.node.atom source sourceObserved
    exact Or.inl ⟨source, sourceObserved, Option.some.inj (observed.symm.trans transported)⟩
  · have lower : molecule.atomCount ≤ cursor.node.atom := Nat.le_of_not_gt old
    obtain ⟨hydrogen, incident⟩ :=
      TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_freshAtom
        molecule well cursor.node.atom out lower observed
    exact Or.inr ⟨lower, hydrogen, incident⟩

/-! Closed hand-built POSITIVE-demand runtime witness; no parser-result or descriptor claim. -/
namespace InlineHydrogenWitness

abbrev original : RawMolecule :=
  TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide

def expanded : RawMolecule := original.withExplicitHydrogens

theorem independent_domain : LeafNeighborDomain expanded 0 := by
  constructor
  · rw [wellFormed_iff_all_bondEndpointsOK]
    decide
  · decide
  · decide
  · decide
  · decide

theorem source_neighbor_records : recordNeighbors expanded 0 = [4, 1, 2, 3] := by decide

theorem actual_generated_roots : generatedRuntimeRoots expanded 0 =
    [⟨canonicalRoot 0 4, some (canonicalCenterRoot 0)⟩,
     ⟨canonicalRoot 0 1, some (canonicalCenterRoot 0)⟩,
     ⟨canonicalRoot 0 2, some (canonicalCenterRoot 0)⟩,
     ⟨canonicalRoot 0 3, some (canonicalCenterRoot 0)⟩] := by
  rw [generatedRuntimeRoots_eq expanded 0 independent_domain, source_neighbor_records]
  rfl

theorem actual_runtime_frame : occurrenceLigandFrame? expanded (canonicalCenterRoot 0) =
    some (generatedRuntimeRoots expanded 0) := by decide

theorem actual_runtime_sort (state : OccurrenceAuxState) (fuel : ℕ) :
    ∃ result, sortOccurrencesTrackedAuthoritative? expanded state fuel
        (generatedRuntimeRoots expanded 0) = some result ∧
      result.1.Perm (generatedRuntimeRoots expanded 0) ∧
      result.1.Pairwise (TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.AtomicDesc expanded) ∧
      result.2 = 0 :=
  generated_runtime_sort expanded 0 fuel independent_domain state

/-- The actual generated materialized hydrogen cursor is accepted without a supplied cycle result. -/
theorem actual_generated_hydrogen (fuel : ℕ) :
    ⟨canonicalRoot 0 4, some (canonicalCenterRoot 0)⟩ ∈ generatedRuntimeRoots expanded 0 ∧
      TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.RealOutsideCycle expanded fuel
        ⟨canonicalRoot 0 4, some (canonicalCenterRoot 0)⟩ ∧
      expanded.atomAt? 4 = some (AtomSpec.aliphatic Element.H) := by
  have member : (⟨canonicalRoot 0 4, some (canonicalCenterRoot 0)⟩ : CanonicalRerootCursor) ∈
      generatedRuntimeRoots expanded 0 := by
    rw [actual_generated_roots]
    exact List.mem_cons_self
  exact ⟨member, generated_root_realOutsideCycle expanded 0 fuel independent_domain _ member,
    TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_expansion_boundary_hydrogen⟩

end InlineHydrogenWitness

end TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
