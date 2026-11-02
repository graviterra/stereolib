import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Executable
import TetraStereo.OneCenter.LocalizedNoDoubleRule3Executable
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def localizedNoDoubleFourLigandFrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedOccurrenceFourLigandFrame carrierFuel) := do
  let cursors ← input.executableLocalizedRerootChildren? { occurrence := target, previous? := none }
  if length_eq : cursors.length = 4 then
    some { cursors := cursors, length_eq := length_eq }
  else none

def localizedNoDoubleTrackedOrderExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder := do
  let tracked ← sortFourLocalizedLigandsTracked (input.compareLocalizedOccurrenceRule3Through5At? frame)
  if input.localizedOccurrenceRule3Through5OrderCoherent
      frame tracked.highestFirst then some tracked else none

def localizedNoDoubleKeyFrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let descriptorFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let rule3Frame ← input.buildLocalizedNoDoubleRule3FrameExec?
    target view descriptorFuel base.cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45KeyExec? target view rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame
          rule3Length
          rule45Keys
          rule45Length }
    else none
  else none

def localizedNoDoubleSpatialEvidenceExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← input.localizedNoDoubleFourLigandFrameExec? target
  let keys ← input.localizedNoDoubleKeyFrameExec?
    target view base
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

def localizedNoDoubleDescriptorExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.localizedNoDoubleSpatialEvidenceExec?
    target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-! ## Exact equality to the full descriptor-bearing construction

Each executable wrapper below is proved extensionally equal to the original descriptor-bearing
function it replaces.  The four-ligand frame and tracked-order twins agree unconditionally (they
differ only by the total executable reroot reader).  The key-frame, spatial-evidence, and final
descriptor twins agree under the sole source hypothesis
`input.certified.input.molecule.NoLocalizedDoubleBondRecords`, where the descriptor-bearing Rule-3
frame carries no physical unit and the compound Rules-4b/4c/5 key compiler has an executable twin
proved equal by the upstream executable modules.  All equalities are equalities of `Option`, so the
rejection behaviour (`none`) is included on both sides.
-/

/-- The executable first zipper expansion agrees with the original optional expansion at every
occurrence: the executable reader is total and definitionally the same list. -/
private theorem localizedOccurrenceLigandFrame?_eq_executableLocalizedRerootChildren?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedOccurrenceLigandFrame? occurrence =
      input.executableLocalizedRerootChildren?
        { occurrence := occurrence, previous? := none } := by
  unfold localizedOccurrenceLigandFrame?
  rw [input.localizedRerootChildren?_eq_some_executable
    { occurrence := occurrence, previous? := none }]
  rw [input.executableLocalizedRerootChildren?_eq_some
    { occurrence := occurrence, previous? := none }]

/-- The executable four-ligand frame twin equals the original four-ligand frame, including the
rejection when the expansion does not have exactly four cursors. -/
theorem localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedNoDoubleFourLigandFrameExec? target =
      input.localizedOccurrenceFourLigandFrame? target := by
  unfold localizedNoDoubleFourLigandFrameExec? localizedOccurrenceFourLigandFrame?
  rw [input.localizedOccurrenceLigandFrame?_eq_executableLocalizedRerootChildren? target]

/-- The executable tracked-order twin equals the original safe tracked order under the same
cumulative key frame: the stable sort and the all-pairs coherence check are identical. -/
theorem localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    input.localizedNoDoubleTrackedOrderExec? frame =
      input.safeLocalizedOccurrenceRule3Through5TrackedOrder? frame := by
  simp only [localizedNoDoubleTrackedOrderExec?,
    safeLocalizedOccurrenceRule3Through5TrackedOrder?,
    localizedOccurrenceRule3Through5TrackedOrder?]

/-- The executable key-frame twin equals the full descriptor-bearing key frame at every target,
view, and base under the source no-localized-double-bond hypothesis.  The executable Rule-3 frame
and the executable compound Rules-4b/4c/5 key compiler are replaced by their proved-equal twins. -/
theorem localizedNoDoubleKeyFrameExec?_eq_buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    input.localizedNoDoubleKeyFrameExec? target view base =
      input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame? target view base := by
  have rule45Eq :
      (input.buildLocalizedRerootCompoundRule45KeyExec? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)) =
      (input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)) := by
    funext cursor
    exact (input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor).symm
  simp only [localizedNoDoubleKeyFrameExec?,
    buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?,
    input.buildLocalizedNoDoubleRule3FrameExec?_eq_buildLocalizedDescriptorBearingRule3Frame?
      noDouble target view,
    rule45Eq]

/-- The executable spatial-evidence twin equals the original descriptor-bearing spatial evidence
under the source no-localized-double-bond hypothesis. -/
theorem localizedNoDoubleSpatialEvidenceExec?_eq_localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedNoDoubleSpatialEvidenceExec? target view =
      input.localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence? target view := by
  simp only [localizedNoDoubleSpatialEvidenceExec?,
    localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?,
    input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target,
    input.localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?,
    input.localizedNoDoubleKeyFrameExec?_eq_buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
      noDouble target view]

/-- The executable full descriptor equals the original descriptor-bearing occurrence descriptor
under the source no-localized-double-bond hypothesis, using the same rational determinant and
pseudo-asymmetric classification. -/
theorem localizedNoDoubleDescriptorExec?_eq_localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedNoDoubleDescriptorExec? target view =
      input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? target view := by
  simp only [localizedNoDoubleDescriptorExec?,
    localizedOccurrenceDescriptorBearingRule3Through5Descriptor?,
    input.localizedNoDoubleSpatialEvidenceExec?_eq_localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?
      noDouble target view]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
