import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3PhysicalTopology

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Two-pass source-canonical Rule-3 frame

The first pass discovers every physical unit in all ligand trees and resolves the exhaustive
four-key coupled topology.  The second pass recompiles every ligand under one common exclusion
set.  Hence no pairwise comparison can choose a different circular-cancellation policy.
-/

/-- Resolve one node while cancelling a physical identity selected by the common frame policy. -/
noncomputable def aromaticCanonicalRule3SpatialNodeExcept?
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option (Option source.AromaticCanonicalRule3SpatialNodeResult) :=
  match source.aromaticCanonicalRule3SpatialNode? node with
  | none => none
  | some none => some none
  | some (some result) =>
      if excluded.contains result.physicalUnitId then some none
      else some (some result)

inductive DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialNodeResult → Prop
  | structuralNonunit
      (notUnit : ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node) :
      source.DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
        excluded node none
  | excludedUnit {result : source.AromaticCanonicalRule3SpatialNodeResult}
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNode node result)
      (excludedIdentity : result.physicalUnitId ∈ excluded) :
      source.DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
        excluded node none
  | retainedGeometry {result : source.AromaticCanonicalRule3SpatialNodeResult}
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNode node result)
      (freshIdentity : result.physicalUnitId ∉ excluded) :
      source.DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
        excluded node (some result)

theorem aromaticCanonicalRule3SpatialNodeExcept?_sound
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult)
    (computed : source.aromaticCanonicalRule3SpatialNodeExcept? excluded node =
      some outcome) :
    source.DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
      excluded node outcome := by
  unfold aromaticCanonicalRule3SpatialNodeExcept? at computed
  cases originalComputed : source.aromaticCanonicalRule3SpatialNode? node with
  | none => simp [originalComputed] at computed
  | some original =>
      cases original with
      | none =>
          simp [originalComputed] at computed
          subst outcome
          exact .structuralNonunit
            (source.aromaticCanonicalRule3SpatialNode?_eq_some_none_implies_not_edge
              node originalComputed)
      | some result =>
          by_cases isExcluded : result.physicalUnitId ∈ excluded
          · simp [originalComputed, isExcluded] at computed
            subst outcome
            exact .excludedUnit
              (source.aromaticCanonicalRule3SpatialNode?_sound
                node result originalComputed) isExcluded
          · simp [originalComputed, isExcluded] at computed
            subst outcome
            exact .retainedGeometry
              (source.aromaticCanonicalRule3SpatialNode?_sound
                node result originalComputed) isExcluded

/-- Recompile one occurrence branch with a fixed physical-unit exclusion set. -/
noncomputable def buildAromaticCanonicalRule3SpatialKeyExcept?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalUncancelledRule3SpatialKey
  | 0, cursor => do
      let children := source.aromaticCanonicalRerootChildren cursor
      let observation ← source.aromaticCanonicalRule3SpatialNodeExcept?
        excluded cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }
      else none
  | fuel + 1, cursor => do
      let children := source.aromaticCanonicalRerootChildren cursor
      let observation ← source.aromaticCanonicalRule3SpatialNodeExcept?
        excluded cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }
      else
        let childKeys ← children.mapM
          (source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded fuel)
        let compare := source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        let sorted := sortAromaticCanonicalUncancelledRule3SpatialKeys compare childKeys
        some
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := source.aromaticCanonicalRule3RootObservations observation ++
              mergeAromaticCanonicalRule3ObservationChildren sorted
            rule3 := source.aromaticCanonicalRule3RootPriorities observation ++
              mergeAromaticCanonicalRule3PriorityChildren sorted }

mutual

inductive DeclarativeAromaticCanonicalRule3SpatialKeyExcept
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Prop
  | zeroLeaf {cursor children observation}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = [])
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
        excluded cursor.occurrence.1.node observation) :
      source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded 0 cursor
        { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
            cursor.occurrence.1.node true
          observations := source.aromaticCanonicalRule3RootObservations observation
          rule3 := source.aromaticCanonicalRule3RootPriorities observation }
  | successorLeaf {fuel cursor children observation}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = [])
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
        excluded cursor.occurrence.1.node observation) :
      source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
        excluded (fuel + 1) cursor
        { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
            cursor.occurrence.1.node true
          observations := source.aromaticCanonicalRule3RootObservations observation
          rule3 := source.aromaticCanonicalRule3RootPriorities observation }
  | successorBranch {fuel cursor children observation childKeys sorted}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (nonterminal : children ≠ [])
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
        excluded cursor.occurrence.1.node observation)
      (childrenDerived :
        source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
          excluded fuel children childKeys)
      (permutation : sorted.Perm childKeys)
      (descending : AromaticCanonicalUncancelledRule3SpatialKeysDescending
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys sorted) :
      source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
        excluded (fuel + 1) cursor
        { constitutional := ExactOfficialRuleMajorKey.assemble
            (MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node false)
            (sorted.map fun child => child.constitutional)
          observations := source.aromaticCanonicalRule3RootObservations observation ++
            mergeAromaticCanonicalRule3ObservationChildren sorted
          rule3 := source.aromaticCanonicalRule3RootPriorities observation ++
            mergeAromaticCanonicalRule3PriorityChildren sorted }

inductive DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
      List source.AromaticCanonicalUncancelledRule3SpatialKey → Prop
  | nil (fuel : Nat) :
      source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
        excluded fuel [] []
  | cons {fuel cursor cursors key keys}
      (head : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
        excluded fuel cursor key)
      (tail : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
        excluded fuel cursors keys) :
      source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
        excluded fuel (cursor :: cursors) (key :: keys)

end

private theorem mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (sound : ∀ (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalUncancelledRule3SpatialKey),
      source.buildAromaticCanonicalRule3SpatialKeyExcept?
        excluded fuel cursor = some key →
      source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
        excluded fuel cursor key) :
    ∀ (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey),
      cursors.mapM (source.buildAromaticCanonicalRule3SpatialKeyExcept?
        excluded fuel) = some keys →
      source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
        excluded fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact .nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalRule3SpatialKeyExcept?
          excluded fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact .cons (sound cursor head headComputed)
                (mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_sound
                  source excluded sound cursors tail tailComputed)

theorem buildAromaticCanonicalRule3SpatialKeyExcept?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalUncancelledRule3SpatialKey),
      source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded fuel cursor = some key →
      source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
        excluded fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalRule3SpatialKeyExcept? at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      cases observationComputed : source.aromaticCanonicalRule3SpatialNodeExcept?
          excluded cursor.occurrence.1.node with
      | none => simp [observationComputed] at computed
      | some observation =>
          by_cases terminal : children = []
          · simp [children, observationComputed, terminal] at computed
            subst key
            exact .zeroLeaf
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
              (source.aromaticCanonicalRule3SpatialNodeExcept?_sound
                excluded cursor.occurrence.1.node observation observationComputed)
          · simp [children, observationComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalRule3SpatialKeyExcept? at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      cases observationComputed : source.aromaticCanonicalRule3SpatialNodeExcept?
          excluded cursor.occurrence.1.node with
      | none => simp [observationComputed] at computed
      | some observation =>
          by_cases terminal : children = []
          · simp [children, observationComputed, terminal] at computed
            subst key
            exact .successorLeaf
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
              (source.aromaticCanonicalRule3SpatialNodeExcept?_sound
                excluded cursor.occurrence.1.node observation observationComputed)
          · cases childKeysComputed : children.mapM
                (source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded fuel) with
            | none =>
                simp [children, observationComputed, terminal,
                  childKeysComputed] at computed
            | some childKeys =>
                let compare :=
                  source.compareAromaticCanonicalUncancelledRule3SpatialKeys
                let sorted :=
                  sortAromaticCanonicalUncancelledRule3SpatialKeys compare childKeys
                simp [children, observationComputed, terminal, childKeysComputed] at computed
                subst key
                letI : Std.TransCmp compare :=
                  source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
                exact .successorBranch
                  (source.aromaticCanonicalRerootChildren_sound cursor) terminal
                  (source.aromaticCanonicalRule3SpatialNodeExcept?_sound
                    excluded cursor.occurrence.1.node observation observationComputed)
                  (mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_sound
                    source excluded
                    (source.buildAromaticCanonicalRule3SpatialKeyExcept?_sound
                      excluded fuel)
                    children childKeys childKeysComputed)
                  (sortAromaticCanonicalUncancelledRule3SpatialKeys_perm
                    compare childKeys)
                  (sortAromaticCanonicalUncancelledRule3SpatialKeys_descending
                    compare childKeys)

/-- Two-pass physical-unit-aware result for one fixed ligand frame. -/
structure AromaticCanonicalRule3CanonicalKeyFrame
    (source : AuthoritativeChemicalInput) where
  rawKeys : List source.AromaticCanonicalUncancelledRule3SpatialKey
  resolution : source.AromaticCanonicalRule3PhysicalTopologyResolution
  excluded : List source.AromaticCanonicalRule3PhysicalUnitId
  keys : List source.AromaticCanonicalUncancelledRule3SpatialKey

noncomputable def buildAromaticCanonicalRule3CanonicalKeyFrame?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option source.AromaticCanonicalRule3CanonicalKeyFrame := do
  let rawKeys ← cursors.mapM
    (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel)
  let resolution ← source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys
  let excluded := source.aromaticCanonicalRule3ExcludedPhysicalUnits rawKeys resolution
  let keys ← cursors.mapM
    (source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded fuel)
  some { rawKeys, resolution, excluded, keys }

private theorem mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_sound_for_frame
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : cursors.mapM
      (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) = some keys) :
    source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
      fuel cursors keys := by
  induction cursors generalizing keys with
  | nil =>
      simp at computed
      subst keys
      exact .nil fuel
  | cons cursor cursors ih =>
      rw [List.mapM_cons] at computed
      cases headComputed :
          source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact .cons
                (source.buildAromaticCanonicalUncancelledRule3SpatialKey?_sound
                  fuel cursor head headComputed)
                (ih tail tailComputed)

def DeclarativeAromaticCanonicalRule3CanonicalKeyFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame) : Prop :=
  source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
      fuel cursors frame.rawKeys ∧
    source.DeclarativeAromaticCanonicalRule3PhysicalTopologyResolution
      frame.rawKeys frame.resolution ∧
    frame.excluded = source.aromaticCanonicalRule3ExcludedPhysicalUnits
      frame.rawKeys frame.resolution ∧
    source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      frame.excluded fuel cursors frame.keys

theorem buildAromaticCanonicalRule3CanonicalKeyFrame?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      fuel cursors = some frame) :
    source.DeclarativeAromaticCanonicalRule3CanonicalKeyFrame
      fuel cursors frame := by
  unfold buildAromaticCanonicalRule3CanonicalKeyFrame? at computed
  cases rawComputed : cursors.mapM
      (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) with
  | none => simp [rawComputed] at computed
  | some rawKeys =>
      cases resolutionComputed :
          source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys with
      | none => simp [rawComputed, resolutionComputed] at computed
      | some resolution =>
          let excluded :=
            source.aromaticCanonicalRule3ExcludedPhysicalUnits rawKeys resolution
          cases keysComputed : cursors.mapM
              (source.buildAromaticCanonicalRule3SpatialKeyExcept?
                excluded fuel) with
          | none =>
              simp [rawComputed, resolutionComputed, excluded,
                keysComputed] at computed
          | some keys =>
              simp [rawComputed, resolutionComputed, excluded,
                keysComputed] at computed
              subst frame
              exact ⟨
                source.mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_sound_for_frame
                  cursors rawKeys rawComputed,
                source.aromaticCanonicalRule3PhysicalTopologyResolution?_sound
                  rawKeys resolution resolutionComputed,
                rfl,
                mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_sound
                  source excluded
                  (source.buildAromaticCanonicalRule3SpatialKeyExcept?_sound
                    excluded fuel)
                  cursors keys keysComputed⟩

def AromaticCanonicalRule3CanonicalKeyFrame.keyAt
    {source : AuthoritativeChemicalInput}
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (index : Fin frame.keys.length) :
    source.AromaticCanonicalUncancelledRule3SpatialKey :=
  frame.keys.get index

noncomputable def compareAromaticCanonicalRule3CanonicalKeyFrameAt
    (source : AuthoritativeChemicalInput)
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame) :
    Fin frame.keys.length → Fin frame.keys.length → Ordering :=
  Ordering.byKey frame.keyAt
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys

theorem compareAromaticCanonicalRule3CanonicalKeyFrameAt_transCmp
    (source : AuthoritativeChemicalInput)
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame) :
    Std.TransCmp (source.compareAromaticCanonicalRule3CanonicalKeyFrameAt frame) := by
  letI : Std.TransCmp source.compareAromaticCanonicalUncancelledRule3SpatialKeys :=
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
  unfold compareAromaticCanonicalRule3CanonicalKeyFrameAt
  infer_instance

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
