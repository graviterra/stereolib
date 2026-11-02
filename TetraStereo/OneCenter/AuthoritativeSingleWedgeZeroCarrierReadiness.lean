import TetraStereo.OneCenter.AuthoritativeSingleWedgeAtomicPriorityBridge

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

/-!
# Zero-carrier source readiness without a whole-source no-double restriction

At carrier fuel zero, each actual final ligand cursor has remaining depth zero and an incoming
final-center coordinate. The certified decreasing traversal budget is therefore zero, so its
reroot child list is empty. The admitted source drawing makes its incoming bond a semantic
single bond, which independently makes its Rule-3 root a structural nonunit.

These local facts construct the actual older production key frame at rule fuel two. Ordinary
double bonds elsewhere in the source are unrestricted. This is a finite carrier result, not a
claim that carrier zero captures deeper tied constitutional priorities or all chemical inputs.
The dependency view remains explicit; scientific source approval is a separate obligation.
-/

/-- Grade and incoming coordinate of every actual final cursor, at arbitrary carrier fuel. -/
theorem final_cursor_grade_and_previous (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    cursor.occurrence.1.remaining = fuel ∧ cursor.occurrence.1.address.length = 1 ∧
      cursor.previous? = some (source.aromaticCanonicalFinalOccurrence fuel center) := by
  have inActual : cursor.occurrence.1 ∈
      (finalOccurrenceRoots source fuel center).map (fun child => child.occurrence.1) :=
    List.mem_map.mpr ⟨cursor, present, rfl⟩
  have inOfficial := (finalOccurrenceRoots_frames_perm source fuel center).mem_iff.mp inActual
  rcases (mem_aromaticCanonicalFinalDirectChildFrames_iff source fuel center
    cursor.occurrence.1).mp inOfficial with ⟨child, slot, _retained, frameEq⟩
  have previous := (source.aromaticCanonicalRerootChildren_sound
    { occurrence := source.aromaticCanonicalFinalOccurrence fuel center, previous? := none }).2
      cursor present
  exact ⟨congrArg (fun frame => frame.remaining) frameEq,
    by simp [frameEq], previous⟩

/-- Arriving from the center commits a zero-carrier root to its zero outward budget. -/
theorem zero_carrier_final_cursor_budget (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 0)
    (present : cursor ∈ finalOccurrenceRoots source 0 center) :
    source.aromaticCanonicalRerootCursorBudget cursor = 0 := by
  rcases final_cursor_grade_and_previous source 0 center cursor present with
    ⟨remaining, length, previous⟩
  simp [aromaticCanonicalRerootCursorBudget, previous, aromaticCanonicalFinalOccurrence,
    remaining, length]

/-- A valid root with budget zero cannot emit a child with a smaller natural-number budget. -/
theorem zero_carrier_final_cursor_children_nil (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 0)
    (present : cursor ∈ finalOccurrenceRoots source 0 center) :
    source.aromaticCanonicalRerootChildren cursor = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro child childPresent
  have decreasing := source.aromaticCanonicalRerootChild_budget_lt cursor child
    (source.aromaticCanonicalRerootChildren cursor)
    (finalOccurrenceRoots_valid source 0 center cursor present)
    (source.aromaticCanonicalRerootChildren_sound cursor) childPresent
  rw [zero_carrier_final_cursor_budget source center cursor present] at decreasing
  exact Nat.not_lt_zero _ decreasing

/-- The admitted source bond makes each actual final root a Rule-3 structural nonunit, even
when unrelated source edges are ordinary double bonds. -/
theorem sourceFrame_final_cursor_not_rule3_edge (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge cursor.occurrence.1.node := by
  obtain ⟨neighbor, endpointPresent, nodeEq⟩ :=
    sourceFrame_final_cursor_real_root source fuel center drawing bound cursor present
  rintro ⟨_real, current, parent, currentEq, parentEq, ordinary⟩
  have currentSame : current = neighbor := by
    simpa [nodeEq, OfficialCIPNode.rootFromEdge] using currentEq.symm
  have parentSame : parent = center.1 := by
    simpa [nodeEq, OfficialCIPNode.parent?, OfficialCIPNode.rootFromEdge] using parentEq.symm
  subst current
  subst parent
  have orderTwo := ordinary.2
  rw [sourceFrame_canonical_bond_order source center.1 drawing bound neighbor.val,
    if_pos endpointPresent] at orderTwo
  omega

theorem sourceFrame_final_cursor_structural_rule3_outcome
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    source.aromaticCanonicalRule3SpatialNode? cursor.occurrence.1.node = some none :=
  source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge cursor.occurrence.1.node
    (sourceFrame_final_cursor_not_rule3_edge source fuel center drawing bound cursor present)

def zeroCarrierLeafRule3Key (source : AuthoritativeChemicalInput)
    (cursor : source.AromaticCanonicalRerootCursor 0) :
    source.AromaticCanonicalUncancelledRule3SpatialKey :=
  { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey cursor.occurrence.1.node true
    observations := [], rule3 := [] }

/-- Every actual zero-carrier final cursor compiles to its literal structural root key. -/
theorem zero_carrier_final_uncancelled_key_computed (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing)
    (cursor : source.AromaticCanonicalRerootCursor 0)
    (present : cursor ∈ finalOccurrenceRoots source 0 center) (ruleFuel : Nat) :
    source.buildAromaticCanonicalUncancelledRule3SpatialKey? ruleFuel cursor =
      some (zeroCarrierLeafRule3Key source cursor) := by
  have children := zero_carrier_final_cursor_children_nil source center cursor present
  have observed := sourceFrame_final_cursor_structural_rule3_outcome source 0 center drawing
    bound cursor present
  cases ruleFuel <;> simp [buildAromaticCanonicalUncancelledRule3SpatialKey?, children,
    observed, zeroCarrierLeafRule3Key, aromaticCanonicalRule3RootObservations,
    aromaticCanonicalRule3RootPriorities]

theorem zero_carrier_final_except_key_computed (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing)
    (cursor : source.AromaticCanonicalRerootCursor 0)
    (present : cursor ∈ finalOccurrenceRoots source 0 center)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) (ruleFuel : Nat) :
    source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded ruleFuel cursor =
      some (zeroCarrierLeafRule3Key source cursor) := by
  have children := zero_carrier_final_cursor_children_nil source center cursor present
  have observed := sourceFrame_final_cursor_structural_rule3_outcome source 0 center drawing
    bound cursor present
  have exceptObserved : source.aromaticCanonicalRule3SpatialNodeExcept?
      excluded cursor.occurrence.1.node = some none := by
    simp [aromaticCanonicalRule3SpatialNodeExcept?, observed]
  cases ruleFuel <;> simp [buildAromaticCanonicalRule3SpatialKeyExcept?, children,
    exceptObserved, zeroCarrierLeafRule3Key, aromaticCanonicalRule3RootObservations,
    aromaticCanonicalRule3RootPriorities]

private theorem mapM_eq_some_map_of_member_eq
    {Input Output : Type} (f : Input → Option Output) (g : Input → Output) :
    ∀ inputs : List Input, (∀ input ∈ inputs, f input = some (g input)) →
      inputs.mapM f = some (inputs.map g)
  | [], _ => rfl
  | input :: inputs, computed => by
      have head := computed input (by simp)
      have tail := mapM_eq_some_map_of_member_eq f g inputs
        (fun value retained => computed value (List.mem_cons_of_mem input retained))
      simp [List.mapM_cons, head, tail]

noncomputable def zeroCarrierRule3Keys (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    List source.AromaticCanonicalUncancelledRule3SpatialKey :=
  (finalOccurrenceRoots source 0 center).map (zeroCarrierLeafRule3Key source)

theorem zero_carrier_rule3_frame_units_nil (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalRule3FramePhysicalUnits (zeroCarrierRule3Keys source center) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro unit retained
  rcases (source.mem_aromaticCanonicalRule3FramePhysicalUnits_iff _ unit).mp retained with
    ⟨key, keyPresent, layer, layerPresent, _entry, _entryPresent, _identity⟩
  rcases List.mem_map.mp keyPresent with ⟨cursor, _cursorPresent, rfl⟩
  simp [zeroCarrierLeafRule3Key] at layerPresent

theorem zero_carrier_rule3_coupled_pairs_nil (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalRule3CoupledUnitPairs (zeroCarrierRule3Keys source center) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro pair retained
  have unitPresent := ((source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff _ pair).mp retained).1
  rw [zero_carrier_rule3_frame_units_nil source center] at unitPresent
  simp at unitPresent

noncomputable def zeroCarrierRule3Frame (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalRule3CanonicalKeyFrame :=
  { rawKeys := zeroCarrierRule3Keys source center
    resolution := .ordinary, excluded := [], keys := zeroCarrierRule3Keys source center }

/-- The actual common two-pass Rule-3 frame is constructed from the admitted source alone. -/
theorem zero_carrier_rule3_frame_computed (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) (ruleFuel : Nat) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? ruleFuel
      (finalOccurrenceRoots source 0 center) = some (zeroCarrierRule3Frame source center) := by
  have rawComputed : (finalOccurrenceRoots source 0 center).mapM
      (source.buildAromaticCanonicalUncancelledRule3SpatialKey? ruleFuel) =
      some (zeroCarrierRule3Keys source center) :=
    mapM_eq_some_map_of_member_eq _ _ _ (fun cursor present =>
      zero_carrier_final_uncancelled_key_computed source center drawing bound cursor present ruleFuel)
  have exceptComputed : (finalOccurrenceRoots source 0 center).mapM
      (source.buildAromaticCanonicalRule3SpatialKeyExcept? [] ruleFuel) =
      some (zeroCarrierRule3Keys source center) :=
    mapM_eq_some_map_of_member_eq _ _ _ (fun cursor present =>
      zero_carrier_final_except_key_computed source center drawing bound cursor present [] ruleFuel)
  have resolutionComputed : source.aromaticCanonicalRule3PhysicalTopologyResolution?
      (zeroCarrierRule3Keys source center) = some .ordinary := by
    simp [aromaticCanonicalRule3PhysicalTopologyResolution?,
      zero_carrier_rule3_coupled_pairs_nil]
  have excludedEmpty : source.aromaticCanonicalRule3ExcludedPhysicalUnits
      (zeroCarrierRule3Keys source center) .ordinary = [] := by
    simp [aromaticCanonicalRule3ExcludedPhysicalUnits, aromaticCanonicalRule3SharedPhysicalUnits,
      zero_carrier_rule3_frame_units_nil]
  simp [buildAromaticCanonicalRule3CanonicalKeyFrame?, rawComputed, resolutionComputed,
    excludedEmpty, exceptComputed, zeroCarrierRule3Frame]

private theorem exists_zero_mapM_compound45_of_valid
    (source : AuthoritativeChemicalInput)
    (target : source.AromaticCanonicalOccurrence 0)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor 0),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45Key? target view 2) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ := exists_zero_mapM_compound45_of_valid source target view cursors
        (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [List.mapM_cons, keyComputed, keysComputed]⟩

/-- Actual production key construction at carrier zero/rule two needs no global no-double
premise. Deeper tied-priority completeness is not asserted by this finite-carrier theorem. -/
theorem exists_zero_carrier_production_keyFrame_of_sourceFrame
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2
      (finalOccurrenceRoots source 0 center) = some keys := by
  let rule3Frame := zeroCarrierRule3Frame source center
  have rule3Computed := zero_carrier_rule3_frame_computed source center drawing bound 2
  have rootLength := finalOccurrenceRoots_length_of_sourceFrame source 0 center drawing bound
  have rule3Length : rule3Frame.keys.length = 4 := by
    simpa [rule3Frame, zeroCarrierRule3Frame, zeroCarrierRule3Keys] using rootLength
  obtain ⟨rule45Keys, rule45Computed⟩ := exists_zero_mapM_compound45_of_valid source
    (source.aromaticCanonicalFinalOccurrence 0 center) view (finalOccurrenceRoots source 0 center)
    (finalOccurrenceRoots_valid source 0 center)
  have rule45Length : rule45Keys.length = 4 :=
    (mapM_length_eq_of_eq_some
      (source.buildAromaticCanonicalRerootCompoundRule45Key?
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2)
      (finalOccurrenceRoots source 0 center) rule45Keys rule45Computed).trans rootLength
  refine ⟨{ rule3Frame, rule3Length, rule45Keys, rule45Length }, ?_⟩
  simp [buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?, rule3Frame,
    rule3Computed, rule3Length, rule45Computed, rule45Length]

/-- First-shell atomic separation additionally forces the actual safe production sorter to
succeed. Ordinary double bonds outside the depicted center remain unrestricted. -/
theorem exists_zero_carrier_production_safe_order_of_source_atomic_separation
    (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence 0 center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing) :
    ∃ keys tracked,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          (source.aromaticCanonicalFinalOccurrence 0 center) view 2
          (finalOccurrenceRoots source 0 center) = some keys ∧
        source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
        tracked.highestFirst.Perm (List.finRange 4) ∧
        tracked.highestFirst.Pairwise (fun left right =>
          productionAtomicPriority source 0 center drawing bound right <
            productionAtomicPriority source 0 center drawing bound left) ∧
        tracked.pseudoComparisons = 0 := by
  obtain ⟨keys, keysComputed⟩ := exists_zero_carrier_production_keyFrame_of_sourceFrame
    source center view drawing bound
  obtain ⟨tracked, rawComputed, perm, descending, zero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
      (productionAtomicPriority source 0 center drawing bound)
      (productionAtomicPriority_injective_of_source_separation source 0 center drawing bound separated)
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys)
      (production_callback_eq_strictRank_of_ne source 0 2 center view drawing bound separated
        keys keysComputed)
  have coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keys tracked.highestFirst = true :=
    (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
      keys tracked.highestFirst).mpr (descending.imp (by
        intro left right higher
        rw [production_comparison_gt_of_atomic_priority source 0 2 center view drawing bound
          keys keysComputed left right higher]))
  have safeComputed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some tracked := by
    simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
      aromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawComputed, coherent]
  exact ⟨keys, tracked, keysComputed, safeComputed, perm, descending, zero⟩

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeZeroCarrierReadinessRegression

open AuthoritativeChemicalInput
open AuthoritativeChemicalInput.SingleWedgeSource

/-- A literal source with an additional disconnected order-two bond. This exercises the removal
of the whole-source no-double restriction; it is not a chemical-admission certificate. -/
def remoteDoubleSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := SingleWedgeSourceRegression.molecule.atoms ++
          [SingleWedgeSourceRegression.carbon, SingleWedgeSourceRegression.carbon]
        interactions := SingleWedgeSourceRegression.molecule.interactions ++ [⟨[5, 6], .covalent 2⟩] }
    diagram? := some
      { atomPositions? := some (SingleWedgeSourceRegression.positions ++ [⟨3, 0⟩, ⟨4, 0⟩])
        bonds := SingleWedgeSourceRegression.diagram.bonds } }

theorem remote_double_source_recognized :
    (extract? remoteDoubleSource ⟨0, by decide⟩).isSome = true := by decide +kernel

theorem remote_double_source_has_ordinary_double_bond :
    remoteDoubleSource.AromaticCanonicalOrdinaryDoubleBond ⟨5, by decide⟩ ⟨6, by decide⟩ := by
  unfold AromaticCanonicalOrdinaryDoubleBond
  constructor
  · unfold AromaticCanonicalAdjacent
    decide +kernel
  · decide +kernel

theorem remote_double_source_fails_global_no_double :
    ¬ remoteDoubleSource.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro absent
  exact absent ⟨5, by decide⟩ ⟨6, by decide⟩ remote_double_source_has_ordinary_double_bond

theorem remote_double_source_center_neighbor_set :
    remoteDoubleSource.aromaticCanonicalNeighborFinset ⟨0, by decide⟩ =
      {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩} := by
  ext neighbor
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel

def remoteDoubleProductionCenter : remoteDoubleSource.AromaticCanonicalTetrahedralCenter :=
  ⟨⟨0, by decide⟩, (mem_aromaticCanonicalTetrahedralCenterSet_iff _ _).mpr ⟨by
      unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
      decide +kernel,
    by rw [remote_double_source_center_neighbor_set]; decide +kernel⟩⟩

/-- The actual key builder accepts the admitted center despite a genuine double bond elsewhere. -/
theorem remote_double_source_production_keyFrame_exists :
    ∃ keys, remoteDoubleSource.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (remoteDoubleSource.aromaticCanonicalFinalOccurrence 0 remoteDoubleProductionCenter)
      (remoteDoubleSource.aromaticCanonicalDependencyView (fun _ => none)
        (remoteDoubleSource.aromaticCanonicalFinalOccurrence 0 remoteDoubleProductionCenter))
      2 (finalOccurrenceRoots remoteDoubleSource 0 remoteDoubleProductionCenter) = some keys := by
  obtain ⟨drawing, extracted⟩ := Option.isSome_iff_exists.mp remote_double_source_recognized
  have bound : SourceFrame remoteDoubleSource remoteDoubleProductionCenter.1.val drawing :=
    (extract?_eq_some_iff remoteDoubleSource _ drawing).mp extracted
  exact exists_zero_carrier_production_keyFrame_of_sourceFrame remoteDoubleSource
    remoteDoubleProductionCenter
    (remoteDoubleSource.aromaticCanonicalDependencyView (fun _ => none)
      (remoteDoubleSource.aromaticCanonicalFinalOccurrence 0 remoteDoubleProductionCenter))
    drawing bound

end SingleWedgeZeroCarrierReadinessRegression
end TetraStereo.OneCenter
