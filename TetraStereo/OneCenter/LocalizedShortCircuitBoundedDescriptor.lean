import TetraStereo.OneCenter.LocalizedShortCircuitStrictCompleteness
import TetraStereo.OneCenter.LocalizedShortCircuitWithChildren

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Bounded

/-- Compile the full comparison frame at the proved linear Rule3 bound. Compound Rule45 uses
its existing structural bound and reads the actual dependency view. -/
def keyFrame? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule3Frame ← WithChildren.buildLocalizedShortCircuitRule3FrameExec?
    input readChildren target view (2 * (carrierFuel + 1) + 2) base.cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM (WithChildren.buildLocalizedRerootCompoundRule45KeyExec?
      input readChildren target view (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    if rule45Length : rule45Keys.length = 4 then
      some { rule3Frame, rule3Length, rule45Keys, rule45Length }
    else none
  else none

def spatialEvidence? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target
  let keys ← keyFrame? input readChildren target view base
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

def descriptor? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← spatialEvidence? input readChildren target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- A certified callback-free carrier permits replacing the production Rule3 budget by the
linear bound without changing any complete key-frame result, including refusal. -/
theorem keyFrame?_eq_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (valid : ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor) :
    keyFrame? input readChildren target view base =
      input.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame? target view base := by
  have frameEq := (WithChildren.shortCircuitRule3_mutual_eq_original
    input readChildren readEq target view (2 * (carrierFuel + 1) + 2)).2 base.cursors
  have stable := input.shortCircuitRule3Frame_stable_above_linear_bound
    ready target target view view base.cursors valid (2 * (carrierFuel + 1) + 2)
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) (Nat.le_refl _)
    (shortCircuit_linear_bound_le_production carrierFuel)
  have rule45Eq : WithChildren.buildLocalizedRerootCompoundRule45KeyExec?
      input readChildren target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) =
      input.buildLocalizedRerootCompoundRule45KeyExec? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) := by
    funext cursor
    exact WithChildren.buildLocalizedRerootCompoundRule45KeyExec?_eq_original
      input readChildren readEq target view _ cursor
  simp only [keyFrame?, buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?,
    frameEq.trans stable, rule45Eq]

/-- The automatically computed four-ligand frame supplies cursor validity internally. -/
theorem spatialEvidence?_eq_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    spatialEvidence? input readChildren target view =
      input.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence? target view := by
  unfold spatialEvidence? localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?
  rw [WithChildren.localizedNoDoubleFourLigandFrameExec?_eq_original input readChildren readEq]
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some base =>
          have meaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base :=
            (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target base).mp (by
              rwa [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
                at baseComputed)
          have valid : ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor :=
            fun cursor present => input.localizedRerootChild_valid
              { occurrence := target, previous? := none } cursor base.cursors meaning.1 present
          simp [keyFrame?_eq_production input readChildren readEq ready target view base valid]

/-- The sufficient recursion bound covers the entire R/S and r/s evaluator for every
auxiliary view, rather than only the constitutionally strict class. -/
theorem descriptor?_eq_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    descriptor? input readChildren target view =
      input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view := by
  simp only [descriptor?, localizedOccurrenceShortCircuitRule3Through5Descriptor?,
    spatialEvidence?_eq_production input readChildren readEq ready target view]

/-- Local evidence produced at the smaller proved budget. Its pseudo-comparison count is retained,
so dependencies may determine either uppercase or lowercase descriptors. -/
structure DescriptorCertificate (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) where
  ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel
  evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel
  compiled : spatialEvidence? input readChildren target view = some evidence
  raw : RS
  geometry : RationalTetrahedralDescriptor evidence.points raw
  classified : descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

def descriptorCertificate? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    Option (Sigma fun descriptor => DescriptorCertificate input readChildren target view descriptor) :=
  match compiled : spatialEvidence? input readChildren target view with
  | none => none
  | some evidence =>
      match geometry : descriptorOfPriorityOrderedPoints? evidence.points with
      | none => none
      | some raw => some ⟨classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons,
          { ready, evidence, compiled, raw
            geometry := (descriptorOfPriorityOrderedPoints?_eq_some_iff evidence.points raw).mp geometry
            classified := rfl }⟩

theorem DescriptorCertificate.production
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel))}
    {target : input.LocalizedCIPOccurrence carrierFuel} {view : input.LocalizedDependencyView target}
    {descriptor : LocalizedAuxiliaryLabel}
    (certificate : DescriptorCertificate input readChildren target view descriptor)
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor) :
    input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view = some descriptor := by
  have evidenceComputed := certificate.compiled
  rw [spatialEvidence?_eq_production input readChildren readEq certificate.ready] at evidenceComputed
  have rawComputed := (descriptorOfPriorityOrderedPoints?_eq_some_iff
    certificate.evidence.points certificate.raw).mpr certificate.geometry
  simp [localizedOccurrenceShortCircuitRule3Through5Descriptor?, evidenceComputed,
    rawComputed, certificate.classified]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Bounded
