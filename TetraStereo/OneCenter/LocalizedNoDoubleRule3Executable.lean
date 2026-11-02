import TetraStereo.OneCenter.LocalizedNoDoubleRule3ChemicalCompleteness
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable Rule-3 key and frame twins on the no-localized-double-bond domain

`LocalizedRerootDescriptorBearingRule3Key` compiles a descriptor-bearing Rule-3 recursion in which
a genuine order-two occurrence consults a two-pass physical-unit frame and can retain a geometrical
observation.  On the source domain described by `SemanticMolecule.NoLocalizedDoubleBondRecords`
(no order-two covalent source record), every Rule-3 occurrence is a structural nonunit, so no
descriptor-bearing observation can ever be retained.

This module supplies plain executable twins:

* `buildLocalizedNoDoubleRule3KeyExec?` mirrors the descriptor-bearing fuel recursion with the node
  observation fixed to `none`, and expands each cursor through the executable
  `executableLocalizedRerootChildren?` reader.  It uses the same
  `LocalizedRerootRecursiveRule3SpatialKey`, the same `sortLocalizedRerootRecursiveRule3SpatialKeys`,
  and the same merge functions, so the constitutional component and sibling ordering are unchanged.
* `buildLocalizedNoDoubleRule3FrameExec?` is the corresponding single-pass frame: the raw pass is a
  `mapM` of the executable key with empty exclusions, and the emitted frame records `coupled := false`,
  `excluded := []`, and `keys := rawKeys`.

Both twins are proved equal to their full descriptor-bearing counterparts for every target, view,
exclusion list, fuel, and cursor, under the sole source hypothesis
`input.certified.input.molecule.NoLocalizedDoubleBondRecords`.  `none` outcomes are included: the
equalities are equalities of `Option`, so both sides refuse together.
-/

namespace CertifiedLocalizedCIPInput

/-- Executable Rule-3 key twin.  The node observation is always structural (`none`), so no
descriptor-bearing node reader, no frame callback, and no `classical` appear in the body. -/
def buildLocalizedNoDoubleRule3KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → List input.LocalizedRule3PhysicalUnitId →
      input.LocalizedRerootCursor carrierFuel →
        Option input.LocalizedRerootRecursiveRule3SpatialKey
  | 0, _excluded, cursor => do
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations none
            rule3 := input.localizedRule3SpatialRootPriorities none }
      else none
  | fuel + 1, excluded, cursor => do
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations none
            rule3 := input.localizedRule3SpatialRootPriorities none }
      else
        let childKeys ← children.mapM
          (input.buildLocalizedNoDoubleRule3KeyExec? target view fuel excluded)
        let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
        some
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := input.localizedRule3SpatialRootObservations none ++
              input.mergeLocalizedRerootRule3ObservationChildren sorted
            rule3 := input.localizedRule3SpatialRootPriorities none ++
              input.mergeLocalizedRerootRule3PriorityChildren sorted }

/-- Executable single-pass Rule-3 frame twin.  No topology resolution or second pass is needed
because no physical units can be observed on this source domain. -/
def buildLocalizedNoDoubleRule3FrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame
  | 0, _cursors => none
  | fuel + 1, cursors => do
      let rawKeys ← cursors.mapM
        (input.buildLocalizedNoDoubleRule3KeyExec? target view fuel [])
      some { rawKeys, coupled := false, excluded := [], keys := rawKeys }

/-- Executable zipper expansion agrees with the classical reader at every cursor.  This is the
single bridge to `LocalizedRerootChildrenExecutable`; the rest of this module uses it to transport
the twin recursion onto the original `localizedRerootChildren?`. -/
private theorem executableLocalizedRerootChildren?_eq_localizedRerootChildren?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.executableLocalizedRerootChildren? cursor = input.localizedRerootChildren? cursor := by
  rw [input.executableLocalizedRerootChildren?_eq_some cursor,
    input.localizedRerootChildren?_eq_some_executable cursor]

/-- The index-zero structural reader resolves to `some none` whenever no source record has order
two. -/
private theorem noDouble_structural_observation_eq_some_none
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedDescriptorBearingRule3StructuralNode? occurrence = some none := by
  classical
  have notEdge := input.localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords
    noDouble occurrence
  simp [localizedDescriptorBearingRule3StructuralNode?, notEdge]

/-- The descriptor-bearing node reader resolves to `some none` for every frame callback and every
exclusion list whenever no source record has order two. -/
private theorem noDouble_node_with_observation_eq_some_none
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedDescriptorBearingRule3NodeWith?
      target occurrence view rule3FrameOf excluded = some none := by
  classical
  have notEdge := input.localizedOccurrence_not_rule3DoubleBondEdge_of_noDoubleRecords
    noDouble occurrence
  simp [localizedDescriptorBearingRule3NodeWith?, notEdge]

/-- The executable key twin equals the full descriptor-bearing key at every fuel, exclusion list,
and cursor, including `none` outcomes. -/
theorem buildLocalizedNoDoubleRule3KeyExec?_eq_buildLocalizedRerootDescriptorBearingRule3Key?
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor,
      input.buildLocalizedNoDoubleRule3KeyExec? target view fuel excluded cursor =
        input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel excluded cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor
      have childrenEq : input.executableLocalizedRerootChildren? cursor =
          input.localizedRerootChildren? cursor :=
        executableLocalizedRerootChildren?_eq_localizedRerootChildren? input cursor
      have structuralObs := noDouble_structural_observation_eq_some_none
        input noDouble cursor.occurrence
      simp [buildLocalizedNoDoubleRule3KeyExec?,
        buildLocalizedRerootDescriptorBearingRule3Key?, childrenEq, structuralObs]
  | succ fuel ih =>
      intro excluded cursor
      have childrenEq : input.executableLocalizedRerootChildren? cursor =
          input.localizedRerootChildren? cursor :=
        executableLocalizedRerootChildren?_eq_localizedRerootChildren? input cursor
      have nodeWithObs := noDouble_node_with_observation_eq_some_none
        input noDouble target cursor.occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) excluded
      have childEq : input.buildLocalizedNoDoubleRule3KeyExec? target view fuel excluded =
          input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel excluded := by
        funext child
        exact ih excluded child
      simp [buildLocalizedNoDoubleRule3KeyExec?,
        buildLocalizedRerootDescriptorBearingRule3Key?, childrenEq, nodeWithObs, childEq]

/-- No coupled matching can survive when the raw frame carries no physical units. -/
private theorem localizedRule3CoupledPerfectMatchings_eq_nil_of_framePhysicalUnits_nil
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (empty : input.localizedRule3FramePhysicalUnits keys = []) :
    input.localizedRule3CoupledPerfectMatchings keys = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro matching present
  have derived := (input.mem_localizedRule3CoupledPerfectMatchings_iff keys matching).mp present
  exact (by simpa [empty] using derived.1)

/-- No shared physical unit survives when the raw frame carries no physical units. -/
private theorem localizedRule3SharedPhysicalUnits_eq_nil_of_framePhysicalUnits_nil
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (empty : input.localizedRule3FramePhysicalUnits keys = []) :
    input.localizedRule3SharedPhysicalUnits keys = [] := by
  have flatMapNil : (keys.flatMap input.localizedRule3PhysicalUnitIds).eraseDups = [] := by
    simpa [localizedRule3FramePhysicalUnits] using empty
  simp [localizedRule3SharedPhysicalUnits, flatMapNil]

/-- The executable frame twin equals the full two-pass descriptor-bearing frame at every fuel and
cursor list, including `none` outcomes. -/
theorem buildLocalizedNoDoubleRule3FrameExec?_eq_buildLocalizedDescriptorBearingRule3Frame?
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursors,
      input.buildLocalizedNoDoubleRule3FrameExec? target view fuel cursors =
        input.buildLocalizedDescriptorBearingRule3Frame? target view fuel cursors := by
  intro fuel
  cases fuel with
  | zero =>
      intro cursors
      simp [buildLocalizedNoDoubleRule3FrameExec?, buildLocalizedDescriptorBearingRule3Frame?]
  | succ fuel =>
      intro cursors
      have keyEq : input.buildLocalizedNoDoubleRule3KeyExec? target view fuel [] =
          input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel [] := by
        funext cursor
        exact input.buildLocalizedNoDoubleRule3KeyExec?_eq_buildLocalizedRerootDescriptorBearingRule3Key?
          noDouble target view fuel [] cursor
      have rawEq : cursors.mapM
            (input.buildLocalizedNoDoubleRule3KeyExec? target view fuel []) =
          cursors.mapM
            (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel []) := by
        rw [keyEq]
      cases rawComputed : cursors.mapM
          (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel []) with
      | none =>
          simp [buildLocalizedNoDoubleRule3FrameExec?,
            buildLocalizedDescriptorBearingRule3Frame?, rawEq, rawComputed]
      | some rawKeys =>
          have frameUnitsNil := input.localizedRule3FramePhysicalUnits_nil_of_noDoubleRecords
            noDouble target view fuel cursors rawKeys rawComputed
          have matchingsNil :=
            localizedRule3CoupledPerfectMatchings_eq_nil_of_framePhysicalUnits_nil
              input rawKeys frameUnitsNil
          have topologyOrd : input.localizedRule3CoupledTopologyResolution? rawKeys =
              some .ordinary := by
            simp [localizedRule3CoupledTopologyResolution?, matchingsNil]
          have sharedNil :=
            localizedRule3SharedPhysicalUnits_eq_nil_of_framePhysicalUnits_nil
              input rawKeys frameUnitsNil
          have excludedEq : input.localizedRule3CoupledExcludedPhysicalUnits rawKeys .ordinary =
              [] := by
            simpa using sharedNil
          have execEq : input.buildLocalizedNoDoubleRule3FrameExec?
                target view (fuel + 1) cursors =
              some { rawKeys := rawKeys, coupled := false, excluded := [], keys := rawKeys } := by
            simp [buildLocalizedNoDoubleRule3FrameExec?, rawEq, rawComputed]
          have fullEq : input.buildLocalizedDescriptorBearingRule3Frame?
                target view (fuel + 1) cursors =
              some { rawKeys := rawKeys, coupled := false, excluded := [], keys := rawKeys } := by
            simp [buildLocalizedDescriptorBearingRule3Frame?,
              LocalizedRule3CoupledTopologyResolution.isCoupled, rawComputed, topologyOrd,
              excludedEq]
          exact execEq.trans fullEq.symm

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
