import TetraStereo.OneCenter.AuthoritativeSingleWedgeProductionKeyReadiness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5FixedPoint
import TetraStereo.OneCenter.TrackedLocalizedLigandSortCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

open CertifiedLocalizedCIPInput

/-!
# Atomic separation in the actual production occurrence-key comparator

Drawing admission identifies every returned cursor as a real source-neighbour root. The first
constitutional sphere of its actual production key consequently observes that source atom's
atomic number. Distinct neighbour atomic numbers decide every off-diagonal comparison before
Rules 3--5 fallthrough, with no pseudoasymmetric history.

The source-domain theorem constructs both the production key frame and its safe tracked order.
Its hypotheses concern the admitted drawing, ordinary source double bonds, and independently
defined atomic separation. It does not assume successful key construction, sorting, or callback
identity. The dependency view remains explicit; no chemical admission or source approval follows.
-/

/-- Source-native first-shell separation, before any occurrence keys or sorter are constructed. -/
def SourceEndpointAtomicSeparation (source : AuthoritativeChemicalInput) (drawing : Frame) : Prop :=
  ∀ left right : source.AromaticCanonicalAtom,
    left.val ∈ drawing.endpoints → right.val ∈ drawing.endpoints →
    source.molecule.toLocalizedMoleculeGraph.atomZ left =
      source.molecule.toLocalizedMoleculeGraph.atomZ right → left = right

/-- A canonical slot refers to the actual returned cursor, without imposing source-index order. -/
noncomputable def productionCursorAt (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) (slot : Fin 4) :
    source.AromaticCanonicalRerootCursor fuel :=
  (finalOccurrenceRoots source fuel center).get
    (Fin.cast (finalOccurrenceRoots_length_of_sourceFrame source fuel center drawing bound).symm
      slot)

def cursorAtomicPriority (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) : Nat :=
  (cursor.occurrence.1.node.current?.map source.molecule.toLocalizedMoleculeGraph.atomZ).getD 0

noncomputable def productionAtomicPriority (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) (slot : Fin 4) : Nat :=
  cursorAtomicPriority source (productionCursorAt source fuel center drawing bound slot)

/-- The full node, not only its current atom ID, is a real source-neighbour edge root. -/
theorem sourceFrame_final_cursor_real_root (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    ∃ neighbor : source.AromaticCanonicalAtom, neighbor.val ∈ drawing.endpoints ∧
      cursor.occurrence.1.node = OfficialCIPNode.rootFromEdge center.1 neighbor := by
  have nodesPerm := (finalOccurrenceRoots_frames_perm source fuel center).map
    (fun frame => frame.node)
  have officialNodes : (aromaticCanonicalFinalDirectChildFrames source fuel center).map
      (fun frame => frame.node) =
      source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
        (OfficialCIPNode.root center.1) := by
    unfold aromaticCanonicalFinalDirectChildFrames
    rw [List.map_map]
    change (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      (OfficialCIPNode.root center.1)).zipIdx.map Prod.fst = _
    exact List.zipIdx_map_fst 0 _
  have inActual : cursor.occurrence.1.node ∈
      ((finalOccurrenceRoots source fuel center).map (fun child => child.occurrence.1)).map
        (fun frame => frame.node) := by
    simp only [List.mem_map]
    exact ⟨cursor.occurrence.1, ⟨cursor, present, rfl⟩, rfl⟩
  have inOfficial := nodesPerm.mem_iff.mp inActual
  rw [officialNodes, sourceFrame_official_children source center.1 drawing bound] at inOfficial
  rcases List.mem_map.mp inOfficial with ⟨neighbor, retained, nodeEq⟩
  have endpointPresent : neighbor.val ∈ drawing.endpoints :=
    of_decide_eq_true (List.mem_filter.mp retained).2
  have neighborDifferent : neighbor ≠ center.1 := by
    intro same
    exact (sourceFrame_endpoint_facts source center.1.val drawing bound
      neighbor.val endpointPresent).2.1 (congrArg Fin.val same)
  refine ⟨neighbor, endpointPresent, nodeEq.symm.trans ?_⟩
  simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
    OfficialCIPNode.root, OfficialCIPNode.rootFromEdge, neighborDifferent]

theorem productionCursorAt_real_root (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) (slot : Fin 4) :
    ∃ neighbor : source.AromaticCanonicalAtom, neighbor.val ∈ drawing.endpoints ∧
      (productionCursorAt source fuel center drawing bound slot).occurrence.1.node =
        OfficialCIPNode.rootFromEdge center.1 neighbor :=
  sourceFrame_final_cursor_real_root source fuel center drawing bound _ (List.get_mem _ _)

/-- The exact Rule-1a observation reads the actual source atom. Its zero fallback is unreachable. -/
theorem productionCursorAt_exact_atomic_observation (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) (slot : Fin 4) :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (productionCursorAt source fuel center drawing bound slot).occurrence.1.node =
      DeclarativeCIP.ExactAtomicNumber.ofNat
        (productionAtomicPriority source fuel center drawing bound slot) := by
  obtain ⟨neighbor, _present, nodeEq⟩ :=
    productionCursorAt_real_root source fuel center drawing bound slot
  simp [productionAtomicPriority, cursorAtomicPriority, nodeEq,
    OfficialCIPNode.rootFromEdge, MoleculeGraph.exactOfficialRule1aObservation]

theorem productionAtomicPriority_injective_of_source_separation
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing) :
    Function.Injective (productionAtomicPriority source fuel center drawing bound) := by
  intro left right priorityEqual
  obtain ⟨leftAtom, leftPresent, leftNode⟩ :=
    productionCursorAt_real_root source fuel center drawing bound left
  obtain ⟨rightAtom, rightPresent, rightNode⟩ :=
    productionCursorAt_real_root source fuel center drawing bound right
  have atomEqual : leftAtom = rightAtom := separated leftAtom rightAtom leftPresent rightPresent
    (by simpa [productionAtomicPriority, cursorAtomicPriority, leftNode, rightNode,
      OfficialCIPNode.rootFromEdge] using priorityEqual)
  have IDsDistinct : (finalOccurrenceRootIDs source fuel center).Nodup :=
    (sourceFrame_final_root_ids_perm source fuel center drawing bound).nodup_iff.mpr
      ((sourceFrame_endpoints_exactly_four_distinct source center.1.val drawing bound).2.map
        (Option.some_injective Nat))
  have cursorIDsEqual : cursorAtomID source
      (productionCursorAt source fuel center drawing bound left) =
      cursorAtomID source (productionCursorAt source fuel center drawing bound right) := by
    simp [cursorAtomID, leftNode, rightNode, atomEqual, OfficialCIPNode.rootFromEdge]
  have rootsLength := finalOccurrenceRoots_length_of_sourceFrame source fuel center drawing bound
  have IDsLength : (finalOccurrenceRootIDs source fuel center).length = 4 := by
    simp [finalOccurrenceRootIDs, rootsLength]
  have getEqual :
      (finalOccurrenceRootIDs source fuel center).get (Fin.cast IDsLength.symm left) =
      (finalOccurrenceRootIDs source fuel center).get (Fin.cast IDsLength.symm right) := by
    simpa [finalOccurrenceRootIDs, productionCursorAt, List.get_eq_getElem] using cursorIDsEqual
  have slotEqual := IDsDistinct.injective_get getEqual
  exact Fin.ext (congrArg
    (fun index : Fin (finalOccurrenceRootIDs source fuel center).length => index.val) slotEqual)

private theorem declarativeExceptList_forall₂
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
  | .cons head tail => .cons head (declarativeExceptList_forall₂ tail)

private theorem declarativeExcept_constitutional_head
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
      excluded fuel cursor key) :
    key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] := by
  cases derived <;> rfl

/-- Successful intermediate production compilation has the correct independently derived root
head at every canonical slot. The source-domain theorem below supplies this compilation. -/
theorem production_keyFrame_constitutional_head
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (slot : Fin 4) :
    (keys.keyAt slot).rule3.constitutional.sourceNodes.head? =
      some [([], (productionCursorAt source carrierFuel center drawing bound slot).occurrence.1.node)] := by
  have meaning := source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
    _ view ruleFuel _ keys computed
  have pointwise := declarativeExceptList_forall₂ meaning.1.2.2.2
  have rootLength := finalOccurrenceRoots_length_of_sourceFrame
    source carrierFuel center drawing bound
  have derived := pointwise.get (i := slot.val)
    (by rw [rootLength]; exact slot.isLt)
    (by rw [keys.rule3Length]; exact slot.isLt)
  exact declarativeExcept_constitutional_head derived

theorem production_keyFrame_exact_atomic_head
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (slot : Fin 4) :
    (ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
      (keys.keyAt slot).rule3.constitutional.sourceNodes).head? =
      some [([], DeclarativeCIP.ExactAtomicNumber.ofNat
        (productionAtomicPriority source carrierFuel center drawing bound slot))] := by
  have head := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph (keys.keyAt slot).rule3.constitutional.sourceNodes
    (productionCursorAt source carrierFuel center drawing bound slot).occurrence.1.node
    (production_keyFrame_constitutional_head source carrierFuel ruleFuel center view
      drawing bound keys computed slot)
  simpa only [productionCursorAt_exact_atomic_observation] using head

theorem production_comparison_gt_of_atomic_priority
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (left right : Fin 4)
    (higher : productionAtomicPriority source carrierFuel center drawing bound right <
      productionAtomicPriority source carrierFuel center drawing bound left) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right =
      { ordering := .gt, pseudo := false } := by
  have rule1a := ExactOfficialRuleMajorKey.compareSparseExactRule1a_gt_of_heads_gt
    (production_keyFrame_exact_atomic_head source carrierFuel ruleFuel center view
      drawing bound keys computed left)
    (production_keyFrame_exact_atomic_head source carrierFuel ruleFuel center view
      drawing bound keys computed right) higher
  apply source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_gt
  apply source.compareAromaticCanonicalUncancelledRule3SpatialKeys_of_constitutional_gt
  simp [ExactOfficialRuleMajorKey.compare, ExactOfficialRuleMajorKey.compareAddressedSources,
    Ordering.byKey, compareLex, rule1a]

theorem production_comparison_lt_of_atomic_priority
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (left right : Fin 4)
    (lower : productionAtomicPriority source carrierFuel center drawing bound left <
      productionAtomicPriority source carrierFuel center drawing bound right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right =
      { ordering := .lt, pseudo := false } := by
  have rule1a := ExactOfficialRuleMajorKey.compareSparseExactRule1a_lt_of_heads_lt
    (production_keyFrame_exact_atomic_head source carrierFuel ruleFuel center view
      drawing bound keys computed left)
    (production_keyFrame_exact_atomic_head source carrierFuel ruleFuel center view
      drawing bound keys computed right) lower
  have rule3 : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (keys.keyAt left).rule3 (keys.keyAt right).rule3 = Ordering.lt := by
    simp [compareAromaticCanonicalUncancelledRule3SpatialKeys,
      ExactOfficialRuleMajorKey.compare, ExactOfficialRuleMajorKey.compareAddressedSources,
      Ordering.byKey, compareLex, rule1a]
  simp [compareAromaticCanonicalOccurrenceRule3Through5At, rule3]

/-- Off-diagonal callback identity is derived from actual keys and actual source atoms. -/
theorem production_callback_eq_strictRank_of_ne
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) = some keys)
    (left right : Fin 4) (different : left ≠ right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys left right =
      strictRankComparison (productionAtomicPriority source carrierFuel center drawing bound)
        left right := by
  have priorityDifferent : productionAtomicPriority source carrierFuel center drawing bound left ≠
      productionAtomicPriority source carrierFuel center drawing bound right :=
    fun equal => different
      (productionAtomicPriority_injective_of_source_separation
        source carrierFuel center drawing bound separated equal)
  rcases Nat.lt_or_gt_of_ne priorityDifferent with lower | higher
  · have compared := production_comparison_lt_of_atomic_priority source carrierFuel ruleFuel
      center view drawing bound keys computed left right lower
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
      aromaticCanonicalRule3Through5DescriptorComparison, strictRankComparison,
      compared, Nat.compare_eq_lt.mpr lower]
  · have compared := production_comparison_gt_of_atomic_priority source carrierFuel ruleFuel
      center view drawing bound keys computed left right higher
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
      aromaticCanonicalRule3Through5DescriptorComparison, strictRankComparison,
      compared, Nat.compare_eq_gt.mpr higher]

/-- Source admission and independent first-shell separation construct the actual production
keys and the actual safe tracked sorter. Neither successful intermediate computation nor a
comparison callback equation is a premise of this source-domain theorem. -/
theorem exists_production_keys_and_safe_order_of_source_atomic_separation
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (separated : SourceEndpointAtomicSeparation source drawing) :
    ∃ keys tracked,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
          (2 * (carrierFuel + 1)) (finalOccurrenceRoots source carrierFuel center) = some keys ∧
        source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
        tracked.highestFirst.Perm (List.finRange 4) ∧
        tracked.highestFirst.Pairwise (fun left right =>
          productionAtomicPriority source carrierFuel center drawing bound right <
            productionAtomicPriority source carrierFuel center drawing bound left) ∧
        tracked.pseudoComparisons = 0 := by
  obtain ⟨keys, keysComputed⟩ := exists_production_keyFrame_of_sourceFrame_noDouble
    source carrierFuel center view drawing bound noDouble
  obtain ⟨tracked, rawComputed, perm, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
      (productionAtomicPriority source carrierFuel center drawing bound)
      (productionAtomicPriority_injective_of_source_separation
        source carrierFuel center drawing bound separated)
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys)
      (production_callback_eq_strictRank_of_ne source carrierFuel
        (2 * (carrierFuel + 1)) center view drawing bound separated keys keysComputed)
  have coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keys tracked.highestFirst = true :=
    (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
      keys tracked.highestFirst).mpr (descending.imp (by
        intro left right higher
        rw [production_comparison_gt_of_atomic_priority source carrierFuel
          (2 * (carrierFuel + 1)) center view drawing bound keys keysComputed
          left right higher]))
  have safeComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some tracked := by
    simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawComputed, coherent]
  exact ⟨keys, tracked, keysComputed, safeComputed, perm, descending, zero⟩

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeAtomicPriorityBridgeRegression

open AuthoritativeChemicalInput
open AuthoritativeChemicalInput.SingleWedgeSource
open SingleWedgeOccurrenceAlignmentRegression

theorem cfclbri_source_atomZ_injective :
    Function.Injective SingleWedgeSourceRegression.source.molecule.toLocalizedMoleculeGraph.atomZ := by
  intro left right
  fin_cases left <;> fin_cases right <;> decide +kernel

/-- Atomic separation is a fact of the actual semantic source, independently of its drawing. -/
theorem cfclbri_source_endpoint_atomic_separation (drawing : SingleWedgeSource.Frame) :
    SourceEndpointAtomicSeparation SingleWedgeSourceRegression.source drawing := by
  intro left right _leftPresent _rightPresent sameAtomicNumber
  exact cfclbri_source_atomZ_injective sameAtomicNumber

/-- An inhabited source-only production key and safe priority order at carrier zero/rule two.
This is the full occurrence-key sorter, not the separate drawing atomic-number shortcut. -/
theorem cfclbri_actual_production_safe_order_exists :
    ∃ keys tracked,
      SingleWedgeSourceRegression.source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0
            cfclbriProductionCenter)
          (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView (fun _ => none)
            (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0
              cfclbriProductionCenter))
          2 (finalOccurrenceRoots SingleWedgeSourceRegression.source 0 cfclbriProductionCenter) =
        some keys ∧
        SingleWedgeSourceRegression.source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
          keys = some tracked ∧ tracked.pseudoComparisons = 0 := by
  obtain ⟨aligned, alignedComputed⟩ := cfclbri_constructed_center_alignment 0
  have bound := (occurrenceAlignment?_sound SingleWedgeSourceRegression.source 0
    cfclbriProductionCenter aligned.1 aligned.2 alignedComputed).1
  obtain ⟨keys, tracked, keysComputed, safeComputed, _perm, _descending, zero⟩ :=
    exists_production_keys_and_safe_order_of_source_atomic_separation
      SingleWedgeSourceRegression.source 0 cfclbriProductionCenter
      (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView (fun _ => none)
        (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0
          cfclbriProductionCenter)) aligned.1 bound
      SingleWedgeProductionKeyReadinessRegression.cfclbri_no_ordinary_double_bond
      (cfclbri_source_endpoint_atomic_separation aligned.1)
  exact ⟨keys, tracked, keysComputed, safeComputed, zero⟩

end SingleWedgeAtomicPriorityBridgeRegression
end TetraStereo.OneCenter
