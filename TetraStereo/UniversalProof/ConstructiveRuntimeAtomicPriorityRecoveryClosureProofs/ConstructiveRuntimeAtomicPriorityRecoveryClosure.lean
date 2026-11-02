import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.UniversalProof.ConstructiveRuntimeAtomicPriorityRecoveryClosureProofs.ConstructiveRuntimeAtomicPriorityRecoveryClosure

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
















































































/-! ## 1. General API characterisation of the occurrence-descriptor stage -/

/-- The production adjacent-comparison driver returns the empty list on an empty sorted frame. -/
theorem compareOccurrenceAdjacentPairsAuthoritative?_nil (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) :
    compareOccurrenceAdjacentPairsAuthoritative? mol state fuel [] = some [] := rfl

/-- The production adjacent-comparison driver returns the empty list on a singleton frame. -/
theorem compareOccurrenceAdjacentPairsAuthoritative?_singleton (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (cursor : CanonicalRerootCursor) :
    compareOccurrenceAdjacentPairsAuthoritative? mol state fuel [cursor] = some [] := rfl

/-- **Precise operational guard.** The production occurrence-descriptor stage requires each
actual adjacent sorted-root comparison to be non-equal. Whenever a genuine frame, a genuine tracked sort and a
genuine adjacent-comparison list are supplied, and that list is not entirely strict
(`decisions.all (fun d => d.ordering != Ordering.eq) = false`), `occurrenceFactAuthoritative?`
returns `none`: the guard `if !(decisions.all …) then none else …` fires.  No descriptor is invented
and no desired result is assumed; the strictness requirement is read off the actual production
body. -/
theorem legacyOccurrenceFactAuthoritative?_eq_none_of_adjacent_eq (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (roots sorted : List CanonicalRerootCursor) (pseudoCount : ℕ)
    (frame : occurrenceLigandFrame? mol node = some roots)
    (sortedComputed :
      sortOccurrencesTrackedAuthoritative? mol state fuel roots = some (sorted, pseudoCount))
    (decisions : List OccurrenceComparison)
    (decisionsComputed :
      compareOccurrenceAdjacentPairsAuthoritative? mol state fuel sorted = some decisions)
    (notStrict : decisions.all (fun decision => decision.ordering != Ordering.eq) = false) :
    legacyOccurrenceFactAuthoritative? mol fuel state node = none := by
  unfold legacyOccurrenceFactAuthoritative?
  cases atomObserved : mol.atomAt? node.atom with
  | none => simp
  | some spec =>
      cases parityObserved : spec.tetrahedral? with
      | none => simp [parityObserved]
      | some parity =>
          cases positionsObserved :
              (sorted.mapM (fun cursor =>
                ((mol.ligandsWithLonePair node.atom).zipIdx.find?
                  (fun entry => entry.1 == cursor.node.atom)).map Prod.snd)) with
          | none => simp [frame, sortedComputed, positionsObserved]
          | some positions =>
              simp [parityObserved, frame, sortedComputed, positionsObserved, decisionsComputed]
              simpa using notStrict

/-! ## 2. The independently specified four-ligand tied/cyclic source -/

/-- Six finite levels include the actual depth-five ring-duplicate frontier of the complete
center-rooted collector. Five levels cannot collect those leaves. This also supplies the stated
comparison and cycle-test budget; it is not unrestricted graph classification. -/
def witnessFuel : ℕ := 6

/-- The annotated tetrahedral centre atom: an ordinary aliphatic carbon carrying an explicit
`clockwise` configuration tag, so the production occurrence pipeline is actually invoked on it. -/
def centreAtom : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some TetrahedralInputParity.clockwise }

/-- An ordinary aliphatic carbon. -/
def carbonAtom : AtomSpec := AtomSpec.aliphatic Element.C

/-- The square-pyramid four-ligand source: carbon `0` bonded to the four carbons `1,2,3,4`, which
are joined in a four-cycle `1-2-3-4-1`.  Written directly from raw bond data with no supplied
comparison, ordering, key or auxiliary fact. -/
def fourLigandRing : RawMolecule where
  atoms := [centreAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single },
      { source := 0, target := 2, kind := ParsedBondKind.single },
      { source := 0, target := 3, kind := ParsedBondKind.single },
      { source := 0, target := 4, kind := ParsedBondKind.single },
      { source := 1, target := 2, kind := ParsedBondKind.single },
      { source := 2, target := 3, kind := ParsedBondKind.single },
      { source := 3, target := 4, kind := ParsedBondKind.single },
      { source := 4, target := 1, kind := ParsedBondKind.single } ]

/-- The actual generated runtime cursor for the centre's ligand `atom`: a real canonical root with
the real previous reference root, exactly the production shape. -/
def rootCursor (atom : ℕ) : CanonicalRerootCursor :=
  { node := canonicalRoot 0 atom, previous? := some (canonicalCenterRoot 0) }

/-- The four actual generated runtime cursors of the centre. -/
def roots : List CanonicalRerootCursor :=
  [rootCursor 1, rootCursor 2, rootCursor 3, rootCursor 4]

/-- Public dispatch specialization: the primitive legacy derivation is used only when the
generated-real-tree profile is unavailable. Concrete cyclic witnesses establish this below. -/
theorem occurrenceFactAuthoritative?_eq_none_of_adjacent_eq (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (roots sorted : List CanonicalRerootCursor) (pseudoCount : ℕ)
    (frame : occurrenceLigandFrame? mol node = some roots)
    (sortedComputed :
      sortOccurrencesTrackedAuthoritative? mol state fuel roots = some (sorted, pseudoCount))
    (decisions : List OccurrenceComparison)
    (decisionsComputed :
      compareOccurrenceAdjacentPairsAuthoritative? mol state fuel sorted = some decisions)
    (notStrict : decisions.all (fun decision => decision.ordering != Ordering.eq) = false)
    (profileUnavailable : FrameRuntime.profile? mol node = none) :
    occurrenceFactAuthoritative? mol fuel state node = none := by
  rw [occurrenceFactAuthoritative?_eq_legacy_of_profile_none mol fuel state node profileUnavailable]
  unfold legacyOccurrenceFactAuthoritative?
  cases atomObserved : mol.atomAt? node.atom with
  | none => simp
  | some spec =>
      cases parityObserved : spec.tetrahedral? with
      | none => simp [parityObserved]
      | some parity =>
          cases positionsObserved :
              (sorted.mapM (fun cursor =>
                ((mol.ligandsWithLonePair node.atom).zipIdx.find?
                  (fun entry => entry.1 == cursor.node.atom)).map Prod.snd)) with
          | none => simp [frame, sortedComputed, positionsObserved]
          | some positions =>
              simp [parityObserved, frame, sortedComputed, positionsObserved, decisionsComputed]
              simpa using notStrict

/-! ## 3. Structural admission of the source -/

theorem fourLigandRing_atomCount : fourLigandRing.atomCount = 5 := by decide +kernel

theorem fourLigandRing_wellFormed : fourLigandRing.WellFormed := by
  rw [wellFormed_iff_all_bondEndpointsOK]
  decide +kernel

theorem fourLigandRing_bondRecordsUnique : fourLigandRing.BondRecordsUnique :=
  (bondRecordsUnique?_eq_true_iff fourLigandRing).mp (by decide +kernel)

theorem fourLigandRing_admissible : fourLigandRing.Admissible :=
  ⟨fourLigandRing_wellFormed, fourLigandRing_bondRecordsUnique⟩

/-- The written-neighbour view is exact, so this is a genuine `StereochemicalAdmissible` raw source
with no invented or omitted ligands. -/
theorem fourLigandRing_writtenNeighborExact : fourLigandRing.WrittenNeighborExact := by
  unfold RawMolecule.WrittenNeighborExact
  decide +kernel

theorem fourLigandRing_stereochemicalAdmissible : fourLigandRing.StereochemicalAdmissible :=
  ⟨fourLigandRing_admissible, fourLigandRing_writtenNeighborExact⟩

/-! ## 4. The actual generated four-root frame and its meaning -/

/-- The actual production frame generator returns exactly the four ring-neighbour cursors. -/
theorem fourLigandRing_frame :
    occurrenceLigandFrame? fourLigandRing (canonicalCenterRoot 0) = some roots := by
  decide +kernel

/-- The centre's lone-pair-completed ligand view is exactly the four written neighbours. -/
theorem fourLigandRing_ligands : fourLigandRing.ligandsWithLonePair 0 = [1, 2, 3, 4] := by
  decide +kernel

/-- Every generated root denotes a real, in-bound, ordinary carbon at the actual materialized
specification. -/
theorem fourLigandRing_root_meaning (atom : ℕ)
    (member : atom = 1 ∨ atom = 2 ∨ atom = 3 ∨ atom = 4) :
    (rootCursor atom).node.provenance = CanonicalNodeProvenance.realAtom ∧
      (rootCursor atom).node.atom < fourLigandRing.atomCount ∧
      fourLigandRing.atomAt? (rootCursor atom).node.atom = some carbonAtom ∧
      (rootCursor atom).previous? = some (canonicalCenterRoot 0) := by
  rcases member with rfl | rfl | rfl | rfl <;>
    refine ⟨rfl, ?_, ?_, rfl⟩ <;> decide +kernel

/-- All four generated roots carry the same actual atomic number `6`: the four-root source is
genuinely atomic-number tied. -/
theorem fourLigandRing_roots_tied :
    fourLigandRing.atomZAt 1 = 6 ∧ fourLigandRing.atomZAt 2 = 6 ∧
      fourLigandRing.atomZAt 3 = 6 ∧ fourLigandRing.atomZAt 4 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- All four generated roots satisfy the actual production cycle test at the stated fuel: the four
ligands are all cyclic, not merely adjacent to a ring. -/
theorem fourLigandRing_roots_cyclic :
    fourLigandRing.atomLiesInCycle witnessFuel 1 = true ∧
      fourLigandRing.atomLiesInCycle witnessFuel 2 = true ∧
      fourLigandRing.atomLiesInCycle witnessFuel 3 = true ∧
      fourLigandRing.atomLiesInCycle witnessFuel 4 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The centre itself is cyclic at the stated fuel, so the conservative conflict gate cannot fire on
any pair of its ligand roots. -/
theorem fourLigandRing_center_cyclic :
    fourLigandRing.atomLiesInCycle witnessFuel 0 = true := by
  decide +kernel

/-! ## 5. The actual production auxiliary environment -/

/-- Actual breadth frontiers of the original canonical expansion, with no supplied tree output. -/
def canonicalFrontier : Nat → List CanonicalBranchNode
  | 0 => [canonicalCenterRoot 0]
  | level + 1 => (canonicalFrontier level).flatMap fourLigandRing.canonicalChildren

/-- The first six source-generated frontiers include every finite canonical occurrence. -/
def completeCanonicalTree : List CanonicalBranchNode :=
  (List.range 6).flatMap canonicalFrontier

/-- The nonempty final frontier consists of actual forced ring-duplicate leaves. -/
theorem fourLigandRing_finalFrontier :
    (canonicalFrontier 5).length = 16 ∧
      (canonicalFrontier 5).all (fun node => node.forcedLeaf) = true ∧
      canonicalFrontier 6 = [] := by
  decide +kernel

/-- The original five-level collector refuses on its nonempty depth-five frontier. -/
theorem fourLigandRing_collector_five_refused :
    collectCanonicalTreeAuthoritative fourLigandRing 5 [canonicalCenterRoot 0] = none := by
  decide +kernel

/-- Exhaustion propagates before annotation filtering; fuel five cannot supply even an empty
production auxiliary state for this source. -/
theorem fourLigandRing_auxState_five_refused :
    buildOccurrenceAuxStateFullyAuthoritative? fourLigandRing 5 0 = none := by
  simp [buildOccurrenceAuxStateFullyAuthoritative?, fourLigandRing_collector_five_refused]

/-- At six levels the actual collector returns the complete source-generated canonical tree. -/
theorem fourLigandRing_collector_six :
    collectCanonicalTreeAuthoritative fourLigandRing witnessFuel [canonicalCenterRoot 0] =
      some completeCanonicalTree := by
  decide +kernel

/-- No actual noncentral real node in the collected tree carries a parity annotation. -/
theorem fourLigandRing_auxiliaryFilter_empty :
    (completeCanonicalTree.filter fun node =>
      node.provenance == CanonicalNodeProvenance.realAtom && node.atom != 0 &&
        (fourLigandRing.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome)) = [] := by
  decide +kernel

/-- The actual production auxiliary environment `buildOccurrenceAuxStateFullyAuthoritative?` for the
four-ligand source is derived.  The only annotated tetrahedral atom is the centre itself, and the
builder excludes the centre, so the genuine production auxiliary data is the empty state.  No
auxiliary fact is supplied by a caller. -/
theorem fourLigandRing_auxState :
    buildOccurrenceAuxStateFullyAuthoritative? fourLigandRing witnessFuel 0 = some [] := by
  simp [buildOccurrenceAuxStateFullyAuthoritative?, fourLigandRing_collector_six,
    fourLigandRing_auxiliaryFilter_empty, sortDescBy, discoverOccurrenceAuxBatchesAuthoritative?]

/-- At the original five-level budget the public refusal is collector exhaustion, before the
local descriptor's adjacent-comparison guard can be consumed. -/
theorem fourLigandRing_public_five_refused :
    tetrahedralOccurrenceFactAuthoritative? fourLigandRing 5 0 = none := by
  simp [tetrahedralOccurrenceFactAuthoritative?, fourLigandRing_auxState_five_refused]

/-! ## 6. The actual four-root tracked sort and adjacent comparisons -/

/-- The actual production complete comparison of the `1`/`2` root pair at the empty auxiliary state
ties with zero pseudo comparison history.  This is *derived* by evaluating the production
comparator, not assumed. -/
theorem fourLigandRing_pair_12 :
    compareOccurrenceBranchesComplete? fourLigandRing ([] : OccurrenceAuxState) witnessFuel
        (rootCursor 1) (rootCursor 2) =
      some ({ ordering := Ordering.eq, pseudo := false } : OccurrenceComparison) := by
  decide +kernel

/-- The actual production complete comparison of the `2`/`3` root pair also ties. -/
theorem fourLigandRing_pair_23 :
    compareOccurrenceBranchesComplete? fourLigandRing ([] : OccurrenceAuxState) witnessFuel
        (rootCursor 2) (rootCursor 3) =
      some ({ ordering := Ordering.eq, pseudo := false } : OccurrenceComparison) := by
  decide +kernel

/-- The actual production complete comparison of the `3`/`4` root pair also ties. -/
theorem fourLigandRing_pair_34 :
    compareOccurrenceBranchesComplete? fourLigandRing ([] : OccurrenceAuxState) witnessFuel
        (rootCursor 3) (rootCursor 4) =
      some ({ ordering := Ordering.eq, pseudo := false } : OccurrenceComparison) := by
  decide +kernel




theorem fourLigandRing_sort :
    sortOccurrencesTrackedAuthoritative? fourLigandRing ([] : OccurrenceAuxState) witnessFuel roots =
      some (roots, 0) := by
  decide +kernel

/-- The actual adjacent-comparison driver on the sorted four-root frame returns three tied
decisions, so the descriptor-strictness guard is genuinely false. -/
theorem fourLigandRing_adjacent_ties :
    compareOccurrenceAdjacentPairsAuthoritative? fourLigandRing ([] : OccurrenceAuxState) witnessFuel
        roots =
      some [ { ordering := Ordering.eq, pseudo := false },
             { ordering := Ordering.eq, pseudo := false },
             { ordering := Ordering.eq, pseudo := false } ] := by
  decide +kernel

/-! ## 7. The obstruction, instantiated -/

/-- The guard value on the actual adjacent list is `false`: not every adjacent decision is strict. -/
theorem fourLigandRing_notStrict :
    (([{ ordering := Ordering.eq, pseudo := false },
        { ordering := Ordering.eq, pseudo := false },
        { ordering := Ordering.eq, pseudo := false }] : List OccurrenceComparison).all
      (fun decision => decision.ordering != Ordering.eq)) = false := by
  decide +kernel

/-- The cyclic canonical tree is outside the repaired real-tree profile. -/
theorem fourLigandRing_profile_unavailable :
    FrameRuntime.profile? fourLigandRing (canonicalCenterRoot 0) = none := by
  decide +kernel

/-- **The actual production occurrence descriptor is refused.**  The genuine four-root tied/cyclic
source has no derivable runtime descriptor at the empty production auxiliary state: the adjacent
complete comparisons are all ties, so the strictness guard fires and the descriptor is `none`. -/
theorem fourLigandRing_occurrenceFact_none :
    occurrenceFactAuthoritative? fourLigandRing witnessFuel ([] : OccurrenceAuxState)
        (canonicalCenterRoot 0) = none := by
  exact occurrenceFactAuthoritative?_eq_none_of_adjacent_eq fourLigandRing witnessFuel []
    (canonicalCenterRoot 0) roots roots 0 fourLigandRing_frame fourLigandRing_sort
    [ { ordering := Ordering.eq, pseudo := false },
      { ordering := Ordering.eq, pseudo := false },
      { ordering := Ordering.eq, pseudo := false } ] fourLigandRing_adjacent_ties
    fourLigandRing_notStrict fourLigandRing_profile_unavailable

/-- **The actual public four-ligand occurrence fact is refused.**  The composed production
`tetrahedralOccurrenceFactAuthoritative?` at the four-ligand centre returns `none`. -/
theorem fourLigandRing_occurrenceFact_none_kernel :
    tetrahedralOccurrenceFactAuthoritative? fourLigandRing witnessFuel 0 = none := by
  simp [tetrahedralOccurrenceFactAuthoritative?, fourLigandRing_auxState,
    fourLigandRing_occurrenceFact_none]

/-- **Precise actual API obstruction for the tied/cyclic four-ligand runtime assignment.**  The
four-root tracked sort succeeds and its actual auxiliary construction succeeds, but the production
four-ligand occurrence descriptor is `none`: the actual adjacent comparison guard rejects three
returned ties. This is a closed symmetric refusal witness, not a general obstruction to cyclic
assignment or a chemical nonstereogenicity conclusion. -/
theorem fourLigandRing_descriptorObstruction :
    (sortOccurrencesTrackedAuthoritative? fourLigandRing ([] : OccurrenceAuxState) witnessFuel
        roots = some (roots, 0)) ∧
      tetrahedralOccurrenceFactAuthoritative? fourLigandRing witnessFuel 0 = none ∧
      occurrenceFactAuthoritative? fourLigandRing witnessFuel ([] : OccurrenceAuxState)
        (canonicalCenterRoot 0) = none :=
  ⟨fourLigandRing_sort, fourLigandRing_occurrenceFact_none_kernel,
    fourLigandRing_occurrenceFact_none⟩

/-- Distinct operational boundaries on the same raw input: five-level auxiliary exhaustion,
six-level auxiliary success, and six-level public refusal through the actual tied decisions. -/
theorem fourLigandRing_budgetBoundary :
    buildOccurrenceAuxStateFullyAuthoritative? fourLigandRing 5 0 = none ∧
      buildOccurrenceAuxStateFullyAuthoritative? fourLigandRing witnessFuel 0 = some [] ∧
      tetrahedralOccurrenceFactAuthoritative? fourLigandRing witnessFuel 0 = none :=
  ⟨fourLigandRing_auxState_five_refused, fourLigandRing_auxState,
    fourLigandRing_occurrenceFact_none_kernel⟩

end TetraStereo.UniversalProof.ConstructiveRuntimeAtomicPriorityRecoveryClosureProofs.ConstructiveRuntimeAtomicPriorityRecoveryClosure
