import TetraStereo.OneCenter.LocalizedExtendedShortCircuitDescriptor
import TetraStereo.OneCenter.LocalizedNoDoubleWithChildren

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WithChildren

/-! Materialized child-reader support for the short-circuit successor. The extended node evaluator handles ordinary and odd-cumulene units. The deep key traversals and Rules4a–5 use the supplied reader.
Every optional outcome is preserved under pointwise equality of readers. -/

mutual

  /-- Descriptor-bearing cumulative key. Every recursive call uses the predecessor index. -/
  def buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (readChildren : input.LocalizedRerootCursor carrierFuel →
        Option (List (input.LocalizedRerootCursor carrierFuel)))
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        input.LocalizedRerootCursor carrierFuel →
          Option input.LocalizedRerootRecursiveRule3SpatialKey
    | 0, _excluded, cursor => do
        let children ← readChildren cursor
        let observation ← input.localizedRule3StructuralNodeExec
          cursor.occurrence
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else none
    | fuel + 1, excluded, cursor => do
        let children ← readChildren cursor
        let observation ← input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target cursor.occurrence view
          (buildLocalizedExtendedShortCircuitRule3FrameExec? input readChildren target view fuel)
          excluded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM
            (buildLocalizedRerootExtendedShortCircuitRule3KeyExec? input readChildren
              target view fuel excluded)
          let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
          some
            { constitutional := OfficialRuleMajorKey.assemble
                (input.moleculeGraph.officialRuleMajorRootKey
                  cursor.occurrence.1.node false)
                (sorted.map fun child => child.constitutional)
              observations := input.localizedRule3SpatialRootObservations observation ++
                input.mergeLocalizedRerootRule3ObservationChildren sorted
              rule3 := input.localizedRule3SpatialRootPriorities observation ++
                input.mergeLocalizedRerootRule3PriorityChildren sorted }

  /-- Two-pass physical-unit frame whose raw and rebuilt keys both use the predecessor index.
  The exhaustive topology resolver must find either no coupled matching or one unique matching;
  an ambiguous frame is rejected before circular-unit cancellation is chosen. -/
  def buildLocalizedExtendedShortCircuitRule3FrameExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (readChildren : input.LocalizedRerootCursor carrierFuel →
        Option (List (input.LocalizedRerootCursor carrierFuel)))
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame
    | 0, _cursors => none
    | fuel + 1, cursors => do
        let rawKeys ← cursors.mapM
          (buildLocalizedRerootExtendedShortCircuitRule3KeyExec? input readChildren
            target view fuel [])
        let topology ← input.localizedRule3CoupledTopologyResolutionExec? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM
          (buildLocalizedRerootExtendedShortCircuitRule3KeyExec? input readChildren
            target view fuel excluded)
        some { rawKeys, coupled, excluded, keys }

end

def buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (readChildren : input.LocalizedRerootCursor carrierFuel →
        Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let descriptorFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let rule3Frame ← buildLocalizedExtendedShortCircuitRule3FrameExec? input readChildren
    target view descriptorFuel base.cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM
      (buildLocalizedRerootCompoundRule45KeyExec? input readChildren target view rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame
          rule3Length
          rule45Keys
          rule45Length }
    else none
  else none


def localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (readChildren : input.LocalizedRerootCursor carrierFuel →
        Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← localizedNoDoubleFourLigandFrameExec? input readChildren target
  let keys ← buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? input readChildren
    target view base
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }


def localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (readChildren : input.LocalizedRerootCursor carrierFuel →
        Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence? input readChildren
    target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

theorem extendedShortCircuitRule3_mutual_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel,
      (∀ excluded cursor,
        buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
          input readChildren target view fuel excluded cursor =
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel excluded cursor) ∧
      (∀ cursors,
        buildLocalizedExtendedShortCircuitRule3FrameExec? input readChildren target view fuel cursors =
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?, readEq]
      · intro cursors; rfl
  | succ fuel ih =>
      have keyEq : buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
          input readChildren target view fuel =
            input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel := by
        funext excluded cursor
        exact ih.1 excluded cursor
      have frameEq : buildLocalizedExtendedShortCircuitRule3FrameExec?
          input readChildren target view fuel =
            input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel :=
        funext ih.2
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          readEq, keyEq, frameEq]
      · intro cursors
        simp only [buildLocalizedExtendedShortCircuitRule3FrameExec?,
          CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3FrameExec?, keyEq]

theorem buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      input readChildren target view base =
        input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? target view base := by
  have rule45Eq : buildLocalizedRerootCompoundRule45KeyExec? input readChildren target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) =
      input.buildLocalizedRerootCompoundRule45KeyExec? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) := by
    funext cursor
    exact buildLocalizedRerootCompoundRule45KeyExec?_eq_original
      input readChildren readEq target view _ cursor
  simp only [buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?,
    CertifiedLocalizedCIPInput.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?,
    (extendedShortCircuitRule3_mutual_eq_original input readChildren readEq target view _).2,
    rule45Eq]

theorem localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
      input readChildren target view =
        input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence? target view := by
  simp only [localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?,
    CertifiedLocalizedCIPInput.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?,
    localizedNoDoubleFourLigandFrameExec?_eq_original input readChildren readEq,
    buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_eq_original
      input readChildren readEq]

/-- Exact optional equality, including every refusal; the optimization changes no chemistry. -/
theorem localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      input readChildren target view =
        input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view := by
  simp only [localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?,
    CertifiedLocalizedCIPInput.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?,
    localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?_eq_original
      input readChildren readEq]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WithChildren
