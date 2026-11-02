import TetraStereo.OneCenter.LocalizedRankedSupportedCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Bounded

/-- Finite, computed prerequisites for finishing a tetrahedral descriptor. This records one
actual frame; it does not assert separation of every independent declarative derivation. -/
structure RankedPreparation (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) where
  callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel
  center : input.TetrahedralCenter
  centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center
  base : input.LocalizedOccurrenceFourLigandFrame fuel
  baseComputed : WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target = some base
  frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel
  frameComputed : keyFrame? input readChildren target view base = some frame
  separated : input.FullComparisonSeparated frame
  point : Fin 4 → CartesianPoint3
  pointsComputed : ∀ i, input.localizedRerootCursorSpatialPoint? (base.cursorAt i) = some (point i)
  nonzero : CartesianPoint3.orientedVolume (point 0) (point 1) (point 2) (point 3) ≠ 0

/-- Compile existing bounded keys once, check all distinct ligand comparisons and molecular
coordinates, and retain the successful data. No priority order or target label is an argument. -/
def prepareRanked? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option (RankedPreparation input readChildren target view) :=
  match centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => none
  | some center =>
    match baseComputed : WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target with
    | none => none
    | some base =>
      match frameComputed : keyFrame? input readChildren target view base with
      | none => none
      | some frame =>
        if separated : input.FullComparisonSeparated frame then
          match p0Computed : input.localizedRerootCursorSpatialPoint? (base.cursorAt 0) with
          | none => none
          | some p0 =>
            match p1Computed : input.localizedRerootCursorSpatialPoint? (base.cursorAt 1) with
            | none => none
            | some p1 =>
              match p2Computed : input.localizedRerootCursorSpatialPoint? (base.cursorAt 2) with
              | none => none
              | some p2 =>
                match p3Computed : input.localizedRerootCursorSpatialPoint? (base.cursorAt 3) with
                | none => none
                | some p3 =>
                  if nonzero : CartesianPoint3.orientedVolume p0 p1 p2 p3 ≠ 0 then
                    some
                      { callbackFree, center, centerComputed, base, baseComputed, frame,
                        frameComputed, separated, point := ![p0, p1, p2, p3], nonzero := nonzero,
                        pointsComputed := by
                          intro i
                          fin_cases i
                          · exact p0Computed
                          · exact p1Computed
                          · exact p2Computed
                          · exact p3Computed }
                  else none
        else none

private theorem mapM_points {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    (prepared : RankedPreparation input readChildren target view) (order : List (Fin 4)) :
    order.mapM (fun i => input.localizedRerootCursorSpatialPoint? (prepared.base.cursorAt i)) =
      some (order.map prepared.point) := by
  induction order with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.mapM_cons, prepared.pointsComputed i, ih, List.map_cons]
      rfl

/-- Finishing is total after finite preparation. Reuse the retained frame and points; execute
the existing tracked sorter once, retaining its actual pseudo count, then classify geometry.
The two impossible refusal branches are eliminated by the general ordering and volume proofs. -/
def RankedPreparation.finish {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    (prepared : RankedPreparation input readChildren target view) :
    Sigma fun descriptor => DescriptorCertificate input readChildren target view descriptor :=
  match trackedComputed : input.localizedNoDoubleTrackedOrderExec? prepared.frame with
  | none => False.elim (by
      obtain ⟨tracked, computed, _, _⟩ := input.trackedOrder_total_of_separated
        prepared.frame prepared.separated
      rw [trackedComputed] at computed
      cases computed)
  | some tracked =>
    have permutation : tracked.highestFirst.Perm (List.finRange 4) := by
      obtain ⟨other, computed, permutation, _⟩ := input.trackedOrder_total_of_separated
        prepared.frame prepared.separated
      have same : other = tracked := Option.some.inj (computed.symm.trans trackedComputed)
      simpa only [same] using permutation
    let evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence fuel :=
      { center := prepared.center, base := prepared.base, keys := prepared.frame, tracked,
        points := tracked.highestFirst.map prepared.point }
    match rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
    | none => False.elim (by
        obtain ⟨raw, geometry⟩ := rationalTetrahedralDescriptor_exists_of_permutation
          prepared.point tracked.highestFirst permutation prepared.nonzero
        have computed := (descriptorOfPriorityOrderedPoints?_eq_some_iff _ raw).mpr geometry
        change descriptorOfPriorityOrderedPoints? evidence.points = some raw at computed
        rw [rawComputed] at computed
        cases computed)
    | some raw =>
      ⟨classifyTetrahedralRSPseudo raw tracked.pseudoComparisons,
        { ready := prepared.callbackFree, evidence, raw, classified := rfl,
          compiled := by
            simp [spatialEvidence?, prepared.centerComputed, prepared.baseComputed,
              prepared.frameComputed, trackedComputed, mapM_points prepared tracked.highestFirst, evidence]
          geometry := (descriptorOfPriorityOrderedPoints?_eq_some_iff _ raw).mp rawComputed }⟩

/-- Total finishing returns exactly the existing bounded evaluator's label. -/
theorem RankedPreparation.finish_local {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    (prepared : RankedPreparation input readChildren target view) :
    descriptor? input readChildren target view = some prepared.finish.1 := by
  have compiled := prepared.finish.2.compiled
  have geometry := (descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).mpr prepared.finish.2.geometry
  simp [descriptor?, compiled, geometry, prepared.finish.2.classified]

/-- The original certificate constructor succeeds with the identical label. -/
theorem RankedPreparation.finish_existing {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    (prepared : RankedPreparation input readChildren target view) :
    (descriptorCertificate? input readChildren prepared.callbackFree target view).map Sigma.fst =
      some prepared.finish.1 := by
  rw [descriptorCertificate?_map_descriptor]
  exact prepared.finish_local

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Bounded

namespace TetraStereo.OneCenter.LocalizedShortCircuit
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- Automatically generated dependency support plus finite local construction prerequisites. -/
structure SupportedRankedPreparation (input : Input) (target : Occurrence input) where
  cache : Cached.RuntimeCache input
  support : DependencySupport input target
  localPreparation : Bounded.RankedPreparation input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier) target
    (input.certified.localizedDependencyView (lookup support.facts) target)

def prepareSupportedRanked? (input : Input) (target : Occurrence input) :
    Option (SupportedRankedPreparation input target) := do
  let callbackFree ← input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input)
  let cache := Cached.buildRuntimeCache input
  let support := Linear.produceDependencySupport input cache callbackFree target
  let localPreparation ← Bounded.prepareRanked? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier) callbackFree target
    (input.certified.localizedDependencyView (lookup support.facts) target)
  pure { cache, support, localPreparation }

/-- Once preparation succeeds, an accepted target certificate is always produced. -/
def SupportedRankedPreparation.finish {input : Input} {target : Occurrence input}
    (prepared : SupportedRankedPreparation input target) :
    Sigma fun descriptor => SupportedDescriptorCertificate input target descriptor :=
  let localResult := prepared.localPreparation.finish
  ⟨localResult.1, { cache := prepared.cache, support := prepared.support, localEvidence := localResult.2 }⟩

theorem SupportedRankedPreparation.finish_reference {input : Input} {target : Occurrence input}
    (prepared : SupportedRankedPreparation input target) :
    referenceState input target = some prepared.finish.1 :=
  prepared.finish.2.reference_assignment

theorem SupportedRankedPreparation.finish_accepted {input : Input} {target : Occurrence input}
    (prepared : SupportedRankedPreparation input target) :
    check (runtimeSystem input) (dependencies input) prepared.finish.2.nodes =
      some (prepared.support.facts ++ [(target, some prepared.finish.1)]) :=
  prepared.finish.2.nodes_accepted

/-- Molecular-input entry point, reusing the existing key compiler, sorter and certificate format. -/
def certifyPreparedRanked? (input : Input) (target : Occurrence input) :
    Option (Sigma fun descriptor => SupportedDescriptorCertificate input target descriptor) :=
  (prepareSupportedRanked? input target).map SupportedRankedPreparation.finish

end TetraStereo.OneCenter.LocalizedShortCircuit
