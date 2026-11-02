import TetraStereo.OneCenter.AuthoritativeSingleWedgeSourceOccurrenceCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3FuelCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CanonicalFrameExact

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

/-!
# Constructive readiness of production occurrence keys for a source drawing

The source drawing supplies four distinct semantic single-bond neighbours. Its actual returned
production cursors therefore form a valid four-root frame, independently of carrier enumeration
order. If the whole source has no ordinary double bond, the common Rule-3 topology is resolved
and the older production Rules-1a--5 key-frame builder succeeds at the existing uniform bound.

No successful extraction, key-frame equation, root permutation, or sort is assumed. The drawing
has its independent `SourceFrame` meaning; the no-double restriction remains explicit. The
auxiliary dependency view is arbitrary, and this theorem does not certify it as a CIP model.
Priority separation, descriptor construction, scientific policy, and source approval are separate.
-/

/-- Every actual final cursor is valid, without an externally supplied root-list witness. -/
theorem finalOccurrenceRoots_valid (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    ∀ cursor ∈ finalOccurrenceRoots source fuel center,
      source.AromaticCanonicalRerootCursorValid cursor :=
  source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid
    (source.aromaticCanonicalFinalOccurrence fuel center)
    (finalOccurrenceRoots source fuel center)
    (finalOccurrenceRoots_are_returned source fuel center)

/-- Four distinct source endpoints force four actual production cursors. -/
theorem finalOccurrenceRoots_length_of_sourceFrame (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) (drawing : Frame)
    (bound : SourceFrame source center.1.val drawing) :
    (finalOccurrenceRoots source fuel center).length = 4 := by
  have endpointsLength :=
    (sourceFrame_endpoints_exactly_four_distinct source center.1.val drawing bound).1
  have lengths := (sourceFrame_final_root_ids_perm source fuel center drawing bound).length_eq
  simpa only [finalOccurrenceRootIDs, List.length_map, endpointsLength] using lengths

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

/-- Actual production key-frame success follows from source geometry and the explicit no-double
domain. This is the older `OccurrenceRule3Through5KeyFrame` used by the drawing descriptor route,
rather than the newer excluded-aware Rule-6 scheduler root-key frame. -/
theorem exists_production_keyFrame_of_sourceFrame_noDouble
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (drawing : Frame) (bound : SourceFrame source center.1.val drawing)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (finalOccurrenceRoots source carrierFuel center) = some keys := by
  let roots := finalOccurrenceRoots source carrierFuel center
  have rootsLength : roots.length = 4 :=
    finalOccurrenceRoots_length_of_sourceFrame source carrierFuel center drawing bound
  have valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor :=
    finalOccurrenceRoots_valid source carrierFuel center
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
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view roots valid
  have rule45Length : rule45Keys.length = 4 :=
    (mapM_length_eq_of_eq_some
      (source.buildAromaticCanonicalRerootCompoundRule45Key?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1))) roots rule45Keys rule45Computed).trans rootsLength
  refine ⟨{ rule3Frame, rule3Length, rule45Keys, rule45Length }, ?_⟩
  change source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
    (2 * (carrierFuel + 1)) roots = _
  simp [buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?, rule3Computed,
    rule3Length, rule45Computed, rule45Length]

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeProductionKeyReadinessRegression

open AuthoritativeChemicalInput
open AuthoritativeChemicalInput.SingleWedgeSource
open SingleWedgeOccurrenceAlignmentRegression

/-- The actual five-atom source contains no ordinary canonical double bond. -/
theorem cfclbri_no_ordinary_double_bond :
    SingleWedgeSourceRegression.source.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : SingleWedgeSourceRegression.source.molecule.aromaticCanonicalBondOrder
      left.val right.val ≠ 2 := by
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

/-- The actual production key builder succeeds at carrier zero and rule fuel two, using an
internally constructed empty dependency view. No claim that this view is a fixed point is made. -/
theorem cfclbri_production_keyFrame_exists :
    ∃ keys, SingleWedgeSourceRegression.source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0
        cfclbriProductionCenter)
      (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView (fun _ => none)
        (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0
          cfclbriProductionCenter))
      2 (finalOccurrenceRoots SingleWedgeSourceRegression.source 0
        cfclbriProductionCenter) = some keys := by
  obtain ⟨aligned, computed⟩ := cfclbri_constructed_center_alignment 0
  have bound := (occurrenceAlignment?_sound SingleWedgeSourceRegression.source 0
    cfclbriProductionCenter aligned.1 aligned.2 computed).1
  simpa using exists_production_keyFrame_of_sourceFrame_noDouble
    SingleWedgeSourceRegression.source 0 cfclbriProductionCenter
    (SingleWedgeSourceRegression.source.aromaticCanonicalDependencyView (fun _ => none)
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0
        cfclbriProductionCenter)) aligned.1 bound cfclbri_no_ordinary_double_bond

end SingleWedgeProductionKeyReadinessRegression
end TetraStereo.OneCenter
