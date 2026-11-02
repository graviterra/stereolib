import TetraStereo.OneCenter.LocalizedRule3OriginalSpatialExecutable
import TetraStereo.OneCenter.LocalizedRule3CoupledTopologyExecutable
import TetraStereo.OneCenter.LocalizedRule3StructuralNodeExecutable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! Executable refinement of the entire original descriptor-bearing Rule-3 recursion.
No source-record restriction or independently supplied successful answer is assumed. -/

def localizedDescriptorBearingRule3NodeWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option input.LocalizedRule3SpatialNodeResult) := by
  exact if edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence then
      match input.localizedRule3CumulatedAxisEntryExec? occurrence with
      | none => none
      | some (.internal _ _) => some none
      | some (.ringClosure _ _) =>
          match input.localizedRule3RequiredMonocyclicEZWithExec?
              target occurrence view rule3FrameOf with
          | some result =>
              let observation :=
                input.localizedRule3RequiredMonocyclicEZObservation result
              if excluded.contains observation.physicalUnitId then some none
              else some (some observation)
          | none =>
              match input.localizedRule3CyclicAuthorityRouteExec? occurrence with
              | some (.ordinaryMonocyclicPolicy _ _ policyResult) =>
                  match policyResult.policy with
                  | .permanentlyOmit => some none
                  | .requireEZ => none
              | some (.fullyCyclicCumulene _ _ _)
              | some (.ordinaryMonocyclicPolicyGap _ _ _ _)
              | some (.ordinaryNonmonocyclic _ _)
              | none => none
      | some (.branched _ _ _ _) =>
          -- P-93.4.2.1.2/P-93.4.2.4: this is not one cumulative chain.  Analyze the
          -- oriented physical bond as its own candidate stereogenic unit.
          match input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
              target occurrence view rule3FrameOf with
          | none => none
          | some result =>
              let observation := input.localizedRule3DescriptorBearingObservation result
              if excluded.contains observation.physicalUnitId then some none
              else some (some observation)
      | some (.terminalStart _) =>
          match input.localizedRule3CumulatedEndpointCursorFrameExec?
              (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
          | none => none
          | some axis =>
              if ordinary : axis.doubleBondCount = 1 then
                match input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
                    target occurrence view rule3FrameOf with
                | none => none
                | some result =>
                    let observation := input.localizedRule3DescriptorBearingObservation result
                    if excluded.contains observation.physicalUnitId then some none
                    else some (some observation)
              else if planar : Odd axis.doubleBondCount then
                match input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
                    target occurrence view rule3FrameOf with
                | none => none
                | some result =>
                    let observation :=
                      input.localizedRule3OddCumuleneDescriptorBearingObservation result
                    if excluded.contains observation.physicalUnitId then some none
                    else some (some observation)
              else
                -- P-93.4.2.2: a nonordinary even cumulene is axial, not a planar Rule-3 unit.
                some none
    else some none

theorem localizedDescriptorBearingRule3NodeWithExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedDescriptorBearingRule3NodeWithExec? target occurrence view rule3FrameOf excluded =
      input.localizedDescriptorBearingRule3NodeWith? target occurrence view rule3FrameOf excluded := by
  unfold localizedDescriptorBearingRule3NodeWithExec? localizedDescriptorBearingRule3NodeWith?
  simp only [localizedRule3CumulatedAxisEntryExec?_eq_original,
    localizedRule3RequiredMonocyclicEZWithExec?_eq_original,
    localizedRule3CyclicAuthorityRouteExec?_eq_original,
    localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_eq_original,
    localizedRule3CumulatedEndpointCursorFrameExec?_eq_original,
    localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_eq_original]
  split
  · simp_all
    rfl
  · simp_all

mutual

  /-- Descriptor-bearing cumulative key. Every recursive call uses the predecessor index. -/
  def buildLocalizedRerootDescriptorBearingRule3KeyExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        input.LocalizedRerootCursor carrierFuel →
          Option input.LocalizedRerootRecursiveRule3SpatialKey
    | 0, _excluded, cursor => do
        let children ← input.executableLocalizedRerootChildren? cursor
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
        let children ← input.executableLocalizedRerootChildren? cursor
        let observation ← input.localizedDescriptorBearingRule3NodeWithExec?
          target cursor.occurrence view
          (input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel)
          excluded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM
            (input.buildLocalizedRerootDescriptorBearingRule3KeyExec?
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
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame
    | 0, _cursors => none
    | fuel + 1, cursors => do
        let rawKeys ← cursors.mapM
          (input.buildLocalizedRerootDescriptorBearingRule3KeyExec?
            target view fuel [])
        let topology ← input.localizedRule3CoupledTopologyResolutionExec? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM
          (input.buildLocalizedRerootDescriptorBearingRule3KeyExec?
            target view fuel excluded)
        some { rawKeys, coupled, excluded, keys }

  /-- Node reader at zero is structural; a successor delegates only to the predecessor frame. -/
  def localizedDescriptorBearingRule3NodeExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        Option (Option input.LocalizedRule3SpatialNodeResult)
    | 0, _excluded =>
        input.localizedRule3StructuralNodeExec occurrence
    | fuel + 1, excluded =>
        input.localizedDescriptorBearingRule3NodeWithExec?
          target occurrence view
          (input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel)
          excluded

end

private theorem recursive_compilers_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    (∀ excluded cursor,
      input.buildLocalizedRerootDescriptorBearingRule3KeyExec? target view fuel excluded cursor =
        input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel excluded cursor) ∧
    (∀ cursors,
      input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel cursors =
        input.buildLocalizedDescriptorBearingRule3Frame? target view fuel cursors) := by
  induction fuel with
  | zero =>
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootDescriptorBearingRule3KeyExec?,
          buildLocalizedRerootDescriptorBearingRule3Key?,
          localizedRerootChildren?_eq_some_executable, executableLocalizedRerootChildren?_eq_some,
          localizedDescriptorBearingRule3StructuralNode?_eq_localizedRule3StructuralNodeExec]
      · intro cursors; rfl
  | succ fuel ih =>
      have keysEq : input.buildLocalizedRerootDescriptorBearingRule3KeyExec? target view fuel =
          input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel :=
        funext fun excluded => funext (ih.1 excluded)
      have framesEq : input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel =
          input.buildLocalizedDescriptorBearingRule3Frame? target view fuel := funext ih.2
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootDescriptorBearingRule3KeyExec?,
          buildLocalizedRerootDescriptorBearingRule3Key?,
          localizedRerootChildren?_eq_some_executable, executableLocalizedRerootChildren?_eq_some,
          localizedDescriptorBearingRule3NodeWithExec?_eq_original, keysEq, framesEq]
      · intro cursors
        simp only [buildLocalizedDescriptorBearingRule3FrameExec?,
          buildLocalizedDescriptorBearingRule3Frame?, keysEq,
          localizedRule3CoupledTopologyResolutionExec?_eq_original]

theorem buildLocalizedRerootDescriptorBearingRule3KeyExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootDescriptorBearingRule3KeyExec? target view fuel excluded cursor =
      input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel excluded cursor :=
  (recursive_compilers_eq input target view fuel).1 excluded cursor

theorem buildLocalizedDescriptorBearingRule3FrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel cursors =
      input.buildLocalizedDescriptorBearingRule3Frame? target view fuel cursors :=
  (recursive_compilers_eq input target view fuel).2 cursors

theorem localizedDescriptorBearingRule3NodeExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedDescriptorBearingRule3NodeExec? target occurrence view fuel excluded =
      input.localizedDescriptorBearingRule3Node? target occurrence view fuel excluded := by
  cases fuel with
  | zero => exact (input.localizedDescriptorBearingRule3StructuralNode?_eq_localizedRule3StructuralNodeExec occurrence).symm
  | succ fuel =>
      have frameEq := funext (input.buildLocalizedDescriptorBearingRule3FrameExec?_eq_original
        target view fuel)
      simp only [localizedDescriptorBearingRule3NodeExec?, localizedDescriptorBearingRule3Node?,
        localizedDescriptorBearingRule3NodeWithExec?_eq_original, frameEq]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
