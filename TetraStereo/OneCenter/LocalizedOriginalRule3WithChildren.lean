import TetraStereo.OneCenter.LocalizedDescriptorBearingRule3Executable
import TetraStereo.OneCenter.LocalizedRerootChildrenCache

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalWithChildren

/-! Exact materialized-child refinement of the original eager Rule3 recursion.
The original node reader, budgets, two-pass topology and optional outcomes are preserved. -/

mutual

  /-- Descriptor-bearing cumulative key. Every recursive call uses the predecessor index. -/
  def buildLocalizedRerootDescriptorBearingRule3KeyExec?
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
        let observation ← input.localizedDescriptorBearingRule3NodeWithExec?
          target cursor.occurrence view
          (buildLocalizedDescriptorBearingRule3FrameExec? input readChildren target view fuel)
          excluded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM
            (buildLocalizedRerootDescriptorBearingRule3KeyExec? input readChildren
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
  def buildLocalizedDescriptorBearingRule3FrameExec?
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
          (buildLocalizedRerootDescriptorBearingRule3KeyExec? input readChildren
            target view fuel [])
        let topology ← input.localizedRule3CoupledTopologyResolutionExec? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM
          (buildLocalizedRerootDescriptorBearingRule3KeyExec? input readChildren
            target view fuel excluded)
        some { rawKeys, coupled, excluded, keys }

end

theorem recursive_compilers_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    (∀ excluded cursor,
      buildLocalizedRerootDescriptorBearingRule3KeyExec? input readChildren target view fuel excluded cursor =
        input.buildLocalizedRerootDescriptorBearingRule3KeyExec? target view fuel excluded cursor) ∧
    (∀ cursors,
      buildLocalizedDescriptorBearingRule3FrameExec? input readChildren target view fuel cursors =
        input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel cursors) := by
  induction fuel with
  | zero =>
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootDescriptorBearingRule3KeyExec?,
          CertifiedLocalizedCIPInput.buildLocalizedRerootDescriptorBearingRule3KeyExec?, readEq]
      · intro cursors; rfl
  | succ fuel ih =>
      have keysEq : buildLocalizedRerootDescriptorBearingRule3KeyExec? input readChildren target view fuel =
          input.buildLocalizedRerootDescriptorBearingRule3KeyExec? target view fuel :=
        funext fun excluded => funext (ih.1 excluded)
      have framesEq : buildLocalizedDescriptorBearingRule3FrameExec? input readChildren target view fuel =
          input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel := funext ih.2
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootDescriptorBearingRule3KeyExec?,
          CertifiedLocalizedCIPInput.buildLocalizedRerootDescriptorBearingRule3KeyExec?,
          readEq, keysEq, framesEq]
      · intro cursors
        simp only [buildLocalizedDescriptorBearingRule3FrameExec?,
          CertifiedLocalizedCIPInput.buildLocalizedDescriptorBearingRule3FrameExec?, keysEq]

theorem frame_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    buildLocalizedDescriptorBearingRule3FrameExec? input readChildren target view fuel cursors =
      input.buildLocalizedDescriptorBearingRule3Frame? target view fuel cursors := by
  rw [(recursive_compilers_eq input readChildren readEq target view fuel).2 cursors]
  exact input.buildLocalizedDescriptorBearingRule3FrameExec?_eq_original target view fuel cursors

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalWithChildren
