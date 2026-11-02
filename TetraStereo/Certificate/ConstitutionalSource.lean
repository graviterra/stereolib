import TetraStereo.Certificate.Constitutional
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceReadiness

set_option autoImplicit false

namespace TetraStereo.Certificate.Constitutional

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource

abbrev ExactLayer := List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber)

def rootLayer (number : Nat) : ExactLayer := [([], .ofNat number)]

def childLayerFrom : Nat → List Nat → ExactLayer
  | _, [] => []
  | index, number :: rest => ([index], .ofNat number) :: childLayerFrom (index + 1) rest

def childLayer (numbers : List Nat) : ExactLayer := childLayerFrom 0 numbers

theorem exact_ofNat_self (number : Nat) :
    ExactOfficialRuleMajorKey.compareExactAtomicNumber (.ofNat number) (.ofNat number) = .eq := by
  simp [ExactOfficialRuleMajorKey.compareExactAtomicNumber, Ordering.byKey]

/-- The first-difference relation determines both directions of the actual sparse comparator. -/
theorem firstDifference_sparse_both {left right : List Nat}
    (different : FirstDifference left right) (index : Nat) :
    OfficialRuleMajorKey.compareSparseLayer ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (childLayerFrom index left) (childLayerFrom index right) = .gt ∧
    OfficialRuleMajorKey.compareSparseLayer ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (childLayerFrom index right) (childLayerFrom index left) = .lt := by
  induction left generalizing right index with
  | nil => simp [FirstDifference] at different
  | cons first rest induction =>
    cases right with
    | nil => simp [FirstDifference] at different
    | cons other others =>
      rcases different with higher | ⟨equal, later⟩
      · have forward := ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat_gt higher
        have reverse := ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat_lt higher
        constructor <;> simp [childLayerFrom, OfficialRuleMajorKey.compareSparseLayer,
          OfficialRuleMajorKey.compareSparseEntry, OfficialRuleMajorKey.compareNat,
          List.compareLex, compareLex, Ordering.byKey, flip, forward, reverse]
      · subst other
        have tail := induction later (index + 1)
        constructor
        · simpa [childLayerFrom, OfficialRuleMajorKey.compareSparseLayer,
            OfficialRuleMajorKey.compareSparseEntry, OfficialRuleMajorKey.compareNat,
            List.compareLex, compareLex, Ordering.byKey, flip, exact_ofNat_self] using tail.1
        · simpa [childLayerFrom, OfficialRuleMajorKey.compareSparseLayer,
            OfficialRuleMajorKey.compareSparseEntry, OfficialRuleMajorKey.compareNat,
            List.compareLex, compareLex, Ordering.byKey, flip, exact_ofNat_self] using tail.2

theorem prefix_layers_both (root : Nat) {left right : List Nat}
    (different : FirstDifference left right) :
    OfficialRuleMajorKey.compareSparseLayers ExactOfficialRuleMajorKey.compareExactAtomicNumber
      [rootLayer root, childLayer left] [rootLayer root, childLayer right] = .gt ∧
    OfficialRuleMajorKey.compareSparseLayers ExactOfficialRuleMajorKey.compareExactAtomicNumber
      [rootLayer root, childLayer right] [rootLayer root, childLayer left] = .lt := by
  have compared := firstDifference_sparse_both different 0
  have rootTie : OfficialRuleMajorKey.compareSparseLayer
      ExactOfficialRuleMajorKey.compareExactAtomicNumber (rootLayer root) (rootLayer root) = .eq := by
    simp [rootLayer, OfficialRuleMajorKey.compareSparseLayer, OfficialRuleMajorKey.compareSparseEntry,
      List.compareLex, compareLex, Ordering.byKey, flip, exact_ofNat_self]
  constructor <;> simp only [OfficialRuleMajorKey.compareSparseLayers, List.compareLex,
    rootTie, childLayer, compared.1, compared.2]

/-- A supplied sphere is tied to *all* actual returned children, with multiplicity, and to the
freshly projected provenance-bearing production key. No comparison or desired descriptor is a
field. The production-key computation and real-root admission remain explicit theorem inputs. -/
structure SourcePrefixRealization (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (slots : Four (Fin 4)) (observations : Four LigandPrefix) : Prop where
  roots : ∀ role, occurrenceAtomicPriority source frame (slots.get role) =
    (observations.get role).rootAtomicNumber
  children : ∀ role numbers, (observations.get role).children = some numbers →
    ((source.aromaticCanonicalRerootChildren (frame.cursorAt (slots.get role))).map
      (fun child => source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm (numbers.map DeclarativeCIP.ExactAtomicNumber.ofNat)
  projections : ∀ role numbers, (observations.get role).children = some numbers →
    ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
      ((keys.keyAt (slots.get role)).rule3.constitutional.sourceNodes) =
        [rootLayer (observations.get role).rootAtomicNumber, childLayer numbers]

/-- Adapter for four real ligands when only the middle two need a second sphere. The
structural obligations are data equalities and full child permutations, never comparator outputs. -/
theorem source_realization_two_spheres (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (slots : Four (Fin 4)) (a b c d : Nat) (bs cs : List Nat)
    (rootA : occurrenceAtomicPriority source frame slots.a = a)
    (rootB : occurrenceAtomicPriority source frame slots.b = b)
    (rootC : occurrenceAtomicPriority source frame slots.c = c)
    (rootD : occurrenceAtomicPriority source frame slots.d = d)
    (childrenB : ((source.aromaticCanonicalRerootChildren (frame.cursorAt slots.b)).map
      (fun child => source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm (bs.map DeclarativeCIP.ExactAtomicNumber.ofNat))
    (childrenC : ((source.aromaticCanonicalRerootChildren (frame.cursorAt slots.c)).map
      (fun child => source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node)).Perm (cs.map DeclarativeCIP.ExactAtomicNumber.ofNat))
    (projectionB : ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
      ((keys.keyAt slots.b).rule3.constitutional.sourceNodes) = [rootLayer b, childLayer bs])
    (projectionC : ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
      ((keys.keyAt slots.c).rule3.constitutional.sourceNodes) = [rootLayer c, childLayer cs]) :
    SourcePrefixRealization source frame keys slots
      ⟨⟨a, none⟩, ⟨b, some bs⟩, ⟨c, some cs⟩, ⟨d, none⟩⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro role
    rcases four_distinct_cover 0 1 2 3 (by decide) role with rfl | rfl | rfl | rfl
    · simpa [Four.get] using rootA
    · simpa [Four.get] using rootB
    · simpa [Four.get] using rootC
    · simpa [Four.get] using rootD
  · intro role numbers supplied
    rcases four_distinct_cover 0 1 2 3 (by decide) role with rfl | rfl | rfl | rfl
    · simp [Four.get] at supplied
    · have equal : numbers = bs := by simpa [Four.get] using supplied.symm
      subst numbers
      simpa [Four.get] using childrenB
    · have equal : numbers = cs := by simpa [Four.get] using supplied.symm
      subst numbers
      simpa [Four.get] using childrenC
    · simp [Four.get] at supplied
  · intro role numbers supplied
    rcases four_distinct_cover 0 1 2 3 (by decide) role with rfl | rfl | rfl | rfl
    · simp [Four.get] at supplied
    · have equal : numbers = bs := by simpa [Four.get] using supplied.symm
      subst numbers
      simpa [Four.get] using projectionB
    · have equal : numbers = cs := by simpa [Four.get] using supplied.symm
      subst numbers
      simpa [Four.get] using projectionC
    · simp [Four.get] at supplied

theorem SourcePrefixRealization.child_count (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (slots : Four (Fin 4)) (observations : Four LigandPrefix)
    (bound : SourcePrefixRealization source frame keys slots observations)
    (role : Fin 4) (numbers : List Nat) (supplied : (observations.get role).children = some numbers) :
    (source.aromaticCanonicalRerootChildren (frame.cursorAt (slots.get role))).length =
      numbers.length := by
  simpa only [List.length_map] using (bound.children role numbers supplied).length_eq

section Source
variable (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
variable (target : source.AromaticCanonicalOccurrence carrierFuel)
variable (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
variable (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
variable (real : OccurrenceRootsReal source frame)
variable (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
variable (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
  target view ruleFuel frame.roots = some keys)
include real computed

theorem source_atomic_callback_both (left right : Fin 4)
    (higher : occurrenceAtomicPriority source frame right <
      occurrenceAtomicPriority source frame left) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys left right =
      some { ordering := .gt, decisiveRule? := none, pseudo := false } ∧
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys right left =
      some { ordering := .lt, decisiveRule? := none, pseudo := false } := by
  have forward := occurrence_comparison_gt_of_atomic_priority source target view ruleFuel
    frame real keys computed left right higher
  have reverse := occurrence_comparison_lt_of_atomic_priority source target view ruleFuel
    frame real keys computed right left higher
  constructor <;> simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
    aromaticCanonicalRule3Through5DescriptorComparison, forward, reverse]

theorem source_atomic_callback (left right : Fin 4) (leftZ rightZ : Nat)
    (leftRoot : occurrenceAtomicPriority source frame left = leftZ)
    (rightRoot : occurrenceAtomicPriority source frame right = rightZ) (different : leftZ ≠ rightZ) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys left right =
      some { ordering := compare leftZ rightZ, decisiveRule? := none, pseudo := false } := by
  rcases Nat.lt_or_gt_of_ne different with lower | higher
  · have ordered : occurrenceAtomicPriority source frame left <
        occurrenceAtomicPriority source frame right := by simpa only [leftRoot, rightRoot] using lower
    simpa [Nat.compare_eq_lt.mpr lower] using
      (source_atomic_callback_both source target view ruleFuel frame real keys computed right left ordered).2
  · have ordered : occurrenceAtomicPriority source frame right <
        occurrenceAtomicPriority source frame left := by simpa only [leftRoot, rightRoot] using higher
    simpa [Nat.compare_eq_gt.mpr higher] using
      (source_atomic_callback_both source target view ruleFuel frame real keys computed left right ordered).1

theorem source_prefix_callback_both (slots : Four (Fin 4)) (observations : Four LigandPrefix)
    (bound : SourcePrefixRealization source frame keys slots observations)
    (left right : Fin 4) (higher : PrefixAbove (observations.get left) (observations.get right)) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys (slots.get left) (slots.get right) =
      some { ordering := .gt, decisiveRule? := none, pseudo := false } ∧
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys (slots.get right) (slots.get left) =
      some { ordering := .lt, decisiveRule? := none, pseudo := false } := by
  rcases higher with rootHigher | ⟨rootTie, childrenHigher⟩
  · apply source_atomic_callback_both source target view ruleFuel frame real keys computed
    simpa only [bound.roots] using rootHigher
  · cases leftChildren : (observations.get left).children with
    | none => simp [leftChildren] at childrenHigher
    | some leftNumbers =>
      cases rightChildren : (observations.get right).children with
      | none => simp [rightChildren] at childrenHigher
      | some rightNumbers =>
        have different : FirstDifference leftNumbers rightNumbers := by
          simpa only [leftChildren, rightChildren] using childrenHigher
        have compared := prefix_layers_both (observations.get right).rootAtomicNumber different
        have leftProjection := bound.projections left leftNumbers leftChildren
        have rightProjection := bound.projections right rightNumbers rightChildren
        rw [rootTie] at leftProjection
        have forward : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
            (keys.keyAt (slots.get left)).rule3 (keys.keyAt (slots.get right)).rule3 = .gt := by
          simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, ExactOfficialRuleMajorKey.compare,
            ExactOfficialRuleMajorKey.compareAddressedSources, Ordering.byKey, compareLex,
            leftProjection, rightProjection, compared.1]
        have reverse : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
            (keys.keyAt (slots.get right)).rule3 (keys.keyAt (slots.get left)).rule3 = .lt := by
          simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, ExactOfficialRuleMajorKey.compare,
            ExactOfficialRuleMajorKey.compareAddressedSources, Ordering.byKey, compareLex,
            leftProjection, rightProjection, compared.2]
        constructor <;> simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
          aromaticCanonicalRule3Through5DescriptorComparison,
          compareAromaticCanonicalOccurrenceRule3Through5At, forward, reverse]

end Source

def slotRank (slots : Four (Fin 4)) (slot : Fin 4) : Nat :=
  if slot = slots.a then 4 else if slot = slots.b then 3
  else if slot = slots.c then 2 else 1

theorem slot_rank_roles (slots : Four (Fin 4)) (distinct : slots.toList.Nodup) :
    slotRank slots slots.a = 4 ∧ slotRank slots slots.b = 3 ∧
      slotRank slots slots.c = 2 ∧ slotRank slots slots.d = 1 := by
  simp only [Four.toList, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, not_false_eq_true, and_true] at distinct
  rcases distinct with ⟨⟨ab, ac, ad⟩, ⟨bc, bd⟩, cd⟩
  simp [slotRank, Ne.symm ab, Ne.symm ac, Ne.symm ad, Ne.symm bc, Ne.symm bd, Ne.symm cd]

theorem slot_rank_injective (slots : Four (Fin 4)) (distinct : slots.toList.Nodup) :
    Function.Injective (slotRank slots) := by
  intro left right same
  have ranks := slot_rank_roles slots distinct
  rcases four_distinct_cover _ _ _ _ distinct left with rfl | rfl | rfl | rfl <;>
    rcases four_distinct_cover _ _ _ _ distinct right with rfl | rfl | rfl | rfl
  all_goals simp_all [ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2]

theorem slots_descending (slots : Four (Fin 4)) (distinct : slots.toList.Nodup) :
    slots.toList.Pairwise (fun left right => slotRank slots right < slotRank slots left) := by
  have ranks := slot_rank_roles slots distinct
  simp [Four.toList, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2]

section CheckedSource
variable (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
variable (target : source.AromaticCanonicalOccurrence carrierFuel)
variable (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
variable (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
variable (real : OccurrenceRootsReal source frame)
variable (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
variable (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
  target view ruleFuel frame.roots = some keys)
variable (slots : Four (Fin 4)) (distinct : slots.toList.Nodup)
variable (observations : Four LigandPrefix)
variable (bound : SourcePrefixRealization source frame keys slots observations)
variable (accepted : checkRanking observations identityCertificate = .ok identityRanking)
include real computed distinct bound accepted

/-- The common finite checker plus actual source realization derives every directed callback.
Families provide observations and physical slot identities, not twelve comparison equations. -/
theorem checked_source_callback (left right : Fin 4) (different : left ≠ right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys left right =
      strictRankComparison (slotRank slots) left right := by
  have ordered := (checkRanking_sound observations identityCertificate identityRanking accepted).2.2
  simp [ConstitutionalRanks, identityRanking, Four.toList, Four.get] at ordered
  rcases ordered with ⟨⟨ab, ac, ad⟩, ⟨bc, bd⟩, cd⟩
  have pair := source_prefix_callback_both source target view ruleFuel frame real keys computed
    slots observations bound
  have cab := pair 0 1 (by simpa [Four.get] using ab)
  have cac := pair 0 2 (by simpa [Four.get] using ac)
  have cad := pair 0 3 (by simpa [Four.get] using ad)
  have cbc := pair 1 2 (by simpa [Four.get] using bc)
  have cbd := pair 1 3 (by simpa [Four.get] using bd)
  have ccd := pair 2 3 (by simpa [Four.get] using cd)
  simp [Four.get] at cab cac cad cbc cbd ccd
  have ranks := slot_rank_roles slots distinct
  rcases four_distinct_cover _ _ _ _ distinct left with rfl | rfl | rfl | rfl <;>
    rcases four_distinct_cover _ _ _ _ distinct right with rfl | rfl | rfl | rfl
  all_goals first
  | exact (different rfl).elim
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cab.1
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cab.2
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cac.1
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cac.2
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cad.1
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cad.2
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cbc.1
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cbc.2
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cbd.1
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using cbd.2
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using ccd.1
  | simpa [strictRankComparison, ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2] using ccd.2

theorem checked_source_safe_order :
    ∃ tracked, source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      tracked.highestFirst = slots.toList ∧ tracked.pseudoComparisons = 0 ∧
      source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent keys tracked.highestFirst = true := by
  have callback := checked_source_callback source target view ruleFuel frame real keys computed
    slots distinct observations bound accepted
  obtain ⟨tracked, computedSort, permutation, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne (slotRank slots)
      (slot_rank_injective slots distinct)
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys) callback
  have higherOrdering : ∀ left right, slotRank slots right < slotRank slots left →
      (source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right).ordering = .gt := by
    intro left right higher
    have different : left ≠ right := by intro same; subst right; exact Nat.lt_irrefl _ higher
    have ordering := congrArg (fun result => result.map (fun comparison => comparison.ordering))
      (callback left right different)
    simpa [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
      strictRankComparison, Nat.compare_eq_gt.mpr higher] using ordering
  have coherent := (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
    keys tracked.highestFirst).mpr
      (descending.imp (fun {left right} higher => higherOrdering left right higher))
  have safe : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked := by
    simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?, computedSort, coherent]
  have exactOrder : tracked.highestFirst = slots.toList :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ first second => False.elim (Nat.lt_asymm first second))
      descending (slots_descending slots distinct) (permutation.trans (slots.perm_finRange distinct).symm)
  exact ⟨tracked, safe, exactOrder, zero, coherent⟩

end CheckedSource

end TetraStereo.Certificate.Constitutional
