import TetraStereo.OneCenter.LocalizedExtendedShortCircuitFuelStability
import TetraStereo.OneCenter.LocalizedExtendedBaseCursorValidity
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitWithChildren
import TetraStereo.OneCenter.LocalizedExtendedTerminalLigandTieRefusal

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedBounded

/-- Compile the full comparison frame at the proved linear Rule3 bound. Compound Rule45 uses
its existing structural bound and reads the actual dependency view. -/
def keyFrame? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule3Frame ← WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
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
    (ready : input.LocalizedExtendedRule3NoCallbackCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (valid : ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor) :
    keyFrame? input readChildren target view base =
      input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? target view base := by
  have frameEq := (WithChildren.extendedShortCircuitRule3_mutual_eq_original
    input readChildren readEq target view (2 * (carrierFuel + 1) + 2)).2 base.cursors
  have stable := input.extendedShortCircuitRule3Frame_stable_above_linear_bound
    ready target view base.cursors valid (2 * (carrierFuel + 1) + 2)
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) (Nat.le_refl _)
    (localizedExtendedLinearFuel_le_production carrierFuel)
  have rule45Eq : WithChildren.buildLocalizedRerootCompoundRule45KeyExec?
      input readChildren target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) =
      input.buildLocalizedRerootCompoundRule45KeyExec? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) := by
    funext cursor
    exact WithChildren.buildLocalizedRerootCompoundRule45KeyExec?_eq_original
      input readChildren readEq target view _ cursor
  simp only [keyFrame?, buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?,
    frameEq.trans stable, rule45Eq]

/-- The automatically computed four-ligand frame supplies cursor validity internally. -/
theorem spatialEvidence?_eq_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (ready : input.LocalizedExtendedRule3NoCallbackCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    spatialEvidence? input readChildren target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence? target view := by
  unfold spatialEvidence? localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
  rw [WithChildren.localizedNoDoubleFourLigandFrameExec?_eq_original input readChildren readEq]
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some base =>
          have valid := input.localizedNoDoubleFourLigandFrameExec?_cursors_valid
            target base baseComputed
          simp [keyFrame?_eq_production input readChildren readEq ready target view base valid]

/-- The sufficient recursion bound covers the entire R/S and r/s evaluator for every
auxiliary view, rather than only the constitutionally strict class. -/
theorem descriptor?_eq_production (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (ready : input.LocalizedExtendedRule3NoCallbackCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    descriptor? input readChildren target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view := by
  simp only [descriptor?, localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?,
    spatialEvidence?_eq_production input readChildren readEq ready target view]

/-- Select the smaller proved bound from already prepared evidence. A missing certificate retains
production evaluation; it does not reject a molecular input. -/
def selectedDescriptor? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (ready? : Option (input.LocalizedExtendedRule3NoCallbackCertificate fuel))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel :=
  match ready? with
  | some _ => descriptor? input readChildren target view
  | none => WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      input readChildren target view

theorem selectedDescriptor?_eq_production (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (ready? : Option (input.LocalizedExtendedRule3NoCallbackCertificate fuel))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    selectedDescriptor? input readChildren ready? target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view := by
  cases ready? with
  | none =>
      exact WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
        input readChildren readEq target view
  | some ready => exact descriptor?_eq_production input readChildren readEq ready target view

/-- Reuse only the terminal-tie certificates proved for the extended evaluator. -/
def descriptorWithTerminalTie? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (ready? : Option (input.LocalizedExtendedRule3NoCallbackCertificate fuel))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => none
  | some _ =>
      match WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target with
      | none => none
      | some base =>
          match ExtendedTerminalTie.refusalCertificate? input readChildren target view base with
          | some _ => none
          | none => selectedDescriptor? input readChildren ready? target view

theorem descriptorWithTerminalTie?_eq_production
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (ready? : Option (input.LocalizedExtendedRule3NoCallbackCertificate fuel))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    descriptorWithTerminalTie? input readChildren ready? target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view := by
  have unchanged : selectedDescriptor? input readChildren ready? target view =
      WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        input readChildren target view :=
    (selectedDescriptor?_eq_production input readChildren readEq ready? target view).trans
      (WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
        input readChildren readEq target view).symm
  have early : descriptorWithTerminalTie? input readChildren ready? target view =
      ExtendedTerminalTie.descriptor? input readChildren target view := by
    simp only [descriptorWithTerminalTie?, ExtendedTerminalTie.descriptor?, unchanged]
    rfl
  exact early.trans ((ExtendedTerminalTie.descriptor?_eq_original input readChildren target view).trans
    (WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
      input readChildren readEq target view))

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedBounded
