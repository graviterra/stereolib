import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

open CertifiedLocalizedCIPInput

/-!
# Readiness at the original arbitrary occurrence

Actual returned reroot roots retain their full histories; no rootFromEdge representation is
required. Compiler readiness uses actual four-root length and validity, and the explicit
whole-source no-double restriction. Atomic comparator readiness uses real provenance/current
atoms and an independent injective rank. Source endpoint separation supplies this rank when
actual returned IDs are a permutation of the admitted drawing endpoints. No successful key
or sorting equation is assumed by the readiness existence theorem. Uniform fuel here is exactly
2 * (carrierFuel + 1); larger-fuel monotonicity, mixed evidence and policy approval are separate.
-/

private theorem canonicalExceptList_length
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (canonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel cursors keys) :
    keys.length = cursors.length :=
  match canonical with
  | .nil _ => rfl
  | .cons _ tail => by simp [canonicalExceptList_length tail]

private theorem exists_mapM_compound45_of_valid
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45Key? target view
          (2 * (carrierFuel + 1))) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ := exists_mapM_compound45_of_valid source target view cursors
        (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [List.mapM_cons, keyComputed, keysComputed]⟩

theorem exists_occurrence_production_keyFrame_of_valid_noDouble
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view (2 * (carrierFuel + 1)) roots = some keys := by
  obtain ⟨rule3Frame, rule3Computed⟩ :=
    source.exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_at_twice
      (source.aromaticCanonicalRule3SpatiallyResolved_of_noDouble noDouble carrierFuel)
      roots valid (by
        intro rawKeys rawComputed
        exact (source.mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_noDouble
          noDouble roots rawKeys rawComputed).2.2)
  have canonical :=
    (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
      (2 * (carrierFuel + 1)) roots rule3Frame).mp rule3Computed
  have rule3Length : rule3Frame.keys.length = 4 :=
    (canonicalExceptList_length canonical.2.2.2).trans rootsLength
  obtain ⟨rule45Keys, rule45Computed⟩ := exists_mapM_compound45_of_valid source
    target view roots valid
  have rule45Length : rule45Keys.length = 4 :=
    (mapM_length_eq_of_eq_some
      (source.buildAromaticCanonicalRerootCompoundRule45Key?
        target view
        (2 * (carrierFuel + 1))) roots rule45Keys rule45Computed).trans rootsLength
  refine ⟨{ rule3Frame, rule3Length, rule45Keys, rule45Length }, ?_⟩
  change source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    target view
    (2 * (carrierFuel + 1)) roots = _
  simp [buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?, rule3Computed,
    rule3Length, rule45Computed, rule45Length]


theorem exists_occurrence_production_keyFrame_of_returned_noDouble
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (returned : source.aromaticCanonicalOccurrenceLigandFrame? target = some frame.roots)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view (2 * (carrierFuel + 1)) frame.roots = some keys :=
  exists_occurrence_production_keyFrame_of_valid_noDouble source target view frame.roots
    frame.rootsLength (source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid
      target frame.roots returned) noDouble

noncomputable def occurrenceAtomicPriority (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (slot : Fin 4) : Nat := cursorAtomicPriority source (frame.cursorAt slot)

/-- Real current atoms, with arbitrary occurrence histories and reroot previous pointers. -/
def OccurrenceRootsReal (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) : Prop :=
  ∀ slot : Fin 4, ∃ atom : source.AromaticCanonicalAtom,
    (frame.cursorAt slot).occurrence.1.node.current? = some atom ∧
    (frame.cursorAt slot).occurrence.1.node.provenance = .realAtom

theorem occurrenceAtomicPriority_injective_of_source_endpoints
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (center : Nat) (drawing : Frame) (bound : SourceFrame source center drawing)
    (real : OccurrenceRootsReal source frame)
    (sameIDs : (frame.roots.map (cursorAtomID source)).Perm (drawing.endpoints.map some))
    (separated : SourceEndpointAtomicSeparation source drawing) :
    Function.Injective (occurrenceAtomicPriority source frame) := by
  intro left right priorityEqual
  obtain ⟨leftAtom, leftCurrent, _⟩ := real left
  obtain ⟨rightAtom, rightCurrent, _⟩ := real right
  have inEndpoints (slot : Fin 4) (atom : source.AromaticCanonicalAtom)
      (current : (frame.cursorAt slot).occurrence.1.node.current? = some atom) :
      atom.val ∈ drawing.endpoints := by
    have present : some atom.val ∈ frame.roots.map (cursorAtomID source) := by
      exact List.mem_map.mpr ⟨frame.cursorAt slot, List.get_mem _ _, by
        simp [cursorAtomID, current]⟩
    have presentSource := sameIDs.mem_iff.mp present
    simpa using presentSource
  have atomEqual : leftAtom = rightAtom := separated leftAtom rightAtom
    (inEndpoints left leftAtom leftCurrent) (inEndpoints right rightAtom rightCurrent)
    (by simpa [occurrenceAtomicPriority, cursorAtomicPriority, leftCurrent, rightCurrent]
      using priorityEqual)
  have distinct : (frame.roots.map (cursorAtomID source)).Nodup :=
    sameIDs.nodup_iff.mpr
      ((sourceFrame_endpoints_exactly_four_distinct source center drawing bound).2.map
        (Option.some_injective Nat))
  have idsEqual : cursorAtomID source (frame.cursorAt left) =
      cursorAtomID source (frame.cursorAt right) := by
    simp [cursorAtomID, leftCurrent, rightCurrent, atomEqual]
  have idsLength : (frame.roots.map (cursorAtomID source)).length = 4 := by
    simp [frame.rootsLength]
  have getEqual : (frame.roots.map (cursorAtomID source)).get (Fin.cast idsLength.symm left) =
      (frame.roots.map (cursorAtomID source)).get (Fin.cast idsLength.symm right) := by
    simpa [AromaticCanonicalOccurrenceFourLigandFrame.cursorAt, List.get_eq_getElem]
      using idsEqual
  have slotEqual := distinct.injective_get getEqual
  exact Fin.ext (congrArg
    (fun slot : Fin (frame.roots.map (cursorAtomID source)).length => slot.val) slotEqual)

private theorem occurrence_declarativeExceptList_forall₂
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel cursors keys) :
    List.Forall₂ (source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded fuel)
      cursors keys :=
  match derived with
  | .nil _ => .nil
  | .cons head tail => .cons head (occurrence_declarativeExceptList_forall₂ tail)

private theorem occurrence_declarativeExcept_constitutional_head
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded fuel cursor key) :
    key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] := by
  cases derived <;> rfl

theorem occurrence_keyFrame_constitutional_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view ruleFuel frame.roots = some keys) (slot : Fin 4) :
    (keys.keyAt slot).rule3.constitutional.sourceNodes.head? =
      some [([], (frame.cursorAt slot).occurrence.1.node)] := by
  have meaning := source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
    target view ruleFuel frame.roots keys computed
  have pointwise := occurrence_declarativeExceptList_forall₂ meaning.1.2.2.2
  have derived := pointwise.get (i := slot.val)
    (by rw [frame.rootsLength]; exact slot.isLt)
    (by rw [keys.rule3Length]; exact slot.isLt)
  exact occurrence_declarativeExcept_constitutional_head derived

theorem occurrence_keyFrame_exact_atomic_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (real : OccurrenceRootsReal source frame)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view ruleFuel frame.roots = some keys) (slot : Fin 4) :
    (ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
      (keys.keyAt slot).rule3.constitutional.sourceNodes).head? =
      some [([], DeclarativeCIP.ExactAtomicNumber.ofNat
        (occurrenceAtomicPriority source frame slot))] := by
  have head := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph (keys.keyAt slot).rule3.constitutional.sourceNodes
    (frame.cursorAt slot).occurrence.1.node
    (occurrence_keyFrame_constitutional_head source target view ruleFuel frame keys computed slot)
  obtain ⟨atom, current, provenance⟩ := real slot
  simpa [occurrenceAtomicPriority, cursorAtomicPriority,
    MoleculeGraph.exactOfficialRule1aObservation, current, provenance] using head

theorem occurrence_comparison_gt_of_atomic_priority
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (real : OccurrenceRootsReal source frame)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view ruleFuel
      frame.roots = some keys)
    (left right : Fin 4)
    (higher : occurrenceAtomicPriority source frame right <
      occurrenceAtomicPriority source frame left) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right =
      { ordering := .gt, pseudo := false } := by
  have rule1a := ExactOfficialRuleMajorKey.compareSparseExactRule1a_gt_of_heads_gt
    (occurrence_keyFrame_exact_atomic_head source target view ruleFuel frame real keys computed left)
    (occurrence_keyFrame_exact_atomic_head source target view ruleFuel frame real keys computed right) higher
  apply source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_gt
  apply source.compareAromaticCanonicalUncancelledRule3SpatialKeys_of_constitutional_gt
  simp [ExactOfficialRuleMajorKey.compare, ExactOfficialRuleMajorKey.compareAddressedSources,
    Ordering.byKey, compareLex, rule1a]

theorem occurrence_comparison_lt_of_atomic_priority
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (real : OccurrenceRootsReal source frame)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view ruleFuel
      frame.roots = some keys)
    (left right : Fin 4)
    (lower : occurrenceAtomicPriority source frame left <
      occurrenceAtomicPriority source frame right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right =
      { ordering := .lt, pseudo := false } := by
  have rule1a := ExactOfficialRuleMajorKey.compareSparseExactRule1a_lt_of_heads_lt
    (occurrence_keyFrame_exact_atomic_head source target view ruleFuel frame real keys computed left)
    (occurrence_keyFrame_exact_atomic_head source target view ruleFuel frame real keys computed right) lower
  have rule3 : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (keys.keyAt left).rule3 (keys.keyAt right).rule3 = Ordering.lt := by
    simp [compareAromaticCanonicalUncancelledRule3SpatialKeys,
      ExactOfficialRuleMajorKey.compare, ExactOfficialRuleMajorKey.compareAddressedSources,
      Ordering.byKey, compareLex, rule1a]
  simp [compareAromaticCanonicalOccurrenceRule3Through5At, rule3]

/-- Off-diagonal callback identity is derived from actual keys and actual source atoms. -/
theorem occurrence_callback_eq_strictRank_of_ne
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (real : OccurrenceRootsReal source frame)
    (injective : Function.Injective (occurrenceAtomicPriority source frame))
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view ruleFuel
      frame.roots = some keys)
    (left right : Fin 4) (different : left ≠ right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys left right =
      strictRankComparison (occurrenceAtomicPriority source frame)
        left right := by
  have priorityDifferent : occurrenceAtomicPriority source frame left ≠
      occurrenceAtomicPriority source frame right :=
    fun equal => different
      (injective equal)
  rcases Nat.lt_or_gt_of_ne priorityDifferent with lower | higher
  · have compared := occurrence_comparison_lt_of_atomic_priority source target view ruleFuel frame real keys computed left right lower
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
      aromaticCanonicalRule3Through5DescriptorComparison, strictRankComparison,
      compared, Nat.compare_eq_lt.mpr lower]
  · have compared := occurrence_comparison_gt_of_atomic_priority source target view ruleFuel frame real keys computed left right higher
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
      aromaticCanonicalRule3Through5DescriptorComparison, strictRankComparison,
      compared, Nat.compare_eq_gt.mpr higher]


/-- Genuine key and safe-sort construction at the original target, at uniform sufficient fuel. -/
theorem exists_occurrence_production_keys_and_safe_order
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (returned : source.aromaticCanonicalOccurrenceLigandFrame? target = some frame.roots)
    (real : OccurrenceRootsReal source frame)
    (injective : Function.Injective (occurrenceAtomicPriority source frame))
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond) :
    ∃ keys tracked,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          target view (2 * (carrierFuel + 1)) frame.roots = some keys ∧
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        occurrenceAtomicPriority source frame right < occurrenceAtomicPriority source frame left) ∧
      tracked.pseudoComparisons = 0 := by
  obtain ⟨keys, keysComputed⟩ := exists_occurrence_production_keyFrame_of_returned_noDouble
    source target view frame returned noDouble
  obtain ⟨tracked, rawComputed, perm, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
      (occurrenceAtomicPriority source frame) injective
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys)
      (occurrence_callback_eq_strictRank_of_ne source target view (2 * (carrierFuel + 1))
        frame real injective keys keysComputed)
  have coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keys tracked.highestFirst = true :=
    (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
      keys tracked.highestFirst).mpr (descending.imp (by
        intro left right higher
        rw [occurrence_comparison_gt_of_atomic_priority source target view
          (2 * (carrierFuel + 1)) frame real keys keysComputed left right higher]))
  have safeComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some tracked := by
    simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawComputed, coherent]
  exact ⟨keys, tracked, keysComputed, safeComputed, perm, descending, zero⟩

/-- Independent drawing endpoint separation supplies the generic actual rank requirement. -/
theorem exists_occurrence_production_keys_and_safe_order_of_source_endpoints
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (returned : source.aromaticCanonicalOccurrenceLigandFrame? target = some frame.roots)
    (center : Nat) (drawing : Frame) (bound : SourceFrame source center drawing)
    (real : OccurrenceRootsReal source frame)
    (sameIDs : (frame.roots.map (cursorAtomID source)).Perm (drawing.endpoints.map some))
    (separated : SourceEndpointAtomicSeparation source drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond) :
    ∃ keys tracked,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          target view (2 * (carrierFuel + 1)) frame.roots = some keys ∧
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        occurrenceAtomicPriority source frame right < occurrenceAtomicPriority source frame left) ∧
      tracked.pseudoComparisons = 0 :=
  exists_occurrence_production_keys_and_safe_order source target view frame returned real
    (occurrenceAtomicPriority_injective_of_source_endpoints
      source frame center drawing bound real sameIDs separated) noDouble

end SingleWedgeSource
end AuthoritativeChemicalInput
end TetraStereo.OneCenter
