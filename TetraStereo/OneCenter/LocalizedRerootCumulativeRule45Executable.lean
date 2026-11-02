import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable cumulative Rules-4a--5 keys over occurrence reroot cursors

`buildLocalizedRerootCumulativeRule45Key?` is `noncomputable` only because each reroot step consults
the fail-closed carrier-membership scan of `localizedRerootChildren?`.  The observation language, the
cumulative node vector, the lawful descending sibling sort and the slot/rank merges are themselves
computable.

This module recompiles the same cumulative key over the executable reroot child enumerator.  The
definition is a plain `def` mirroring the proof-facing compiler line for line, replacing the child
enumeration and the recursive self-call; every key component is retained, including `labels` and the
hierarchy-rank-addressed `rankedLabels` that P-92.5.2.1(b) reads.  No stage, target, view, fuel or
cursor is restricted.

The executable twin computes exactly the proof-facing key at every fuel and cursor, so all of the
proof-facing properties transfer: soundness against the independent recursive derivation, completion
of the constitutional component, and its alignment with fresh observations from its source nodes.
-/

namespace CertifiedLocalizedCIPInput

/-- Plain twin of `buildLocalizedRerootCumulativeRule45Key?` over the executable reroot child
enumerator.  Fail-closed exhaustion is preserved: a nonterminal cursor at zero fuel is refused, and a
child refused by the executable compiler refuses its parent. -/
def buildLocalizedRerootCumulativeRule45KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        let label := input.localizedDependencyLabel target view cursor
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else none
  | fuel + 1, cursor => do
      let children ← input.executableLocalizedRerootChildren? cursor
      let label := input.localizedDependencyLabel target view cursor
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else
        let childKeys ← children.mapM
          (input.buildLocalizedRerootCumulativeRule45KeyExec? stage target view fuel)
        let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
        some
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }

/-- The executable reroot child enumeration returns exactly the proof-facing expansion at every
cursor: the executable option is its total child list, which is precisely the `some` value that the
fail-closed enumeration proves itself equal to.  Both compilers therefore agree as soon as their
identical continuations are compared. -/
theorem executableLocalizedRerootChildren?_eq_localizedRerootChildren
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.executableLocalizedRerootChildren? cursor =
      input.localizedRerootChildren? cursor :=
  (input.executableLocalizedRerootChildren?_eq_some cursor).trans
    (input.localizedRerootChildren?_eq_some_executable cursor).symm

/-- The executable twin computes exactly the proof-facing cumulative key, for every stage, target,
restricted state view, fuel and cursor. -/
theorem buildLocalizedRerootCumulativeRule45KeyExec?_eq_build
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCumulativeRule45KeyExec? stage target view fuel cursor =
        input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor
  | 0, cursor => by
      have childrenIdentified : input.executableLocalizedRerootChildren? cursor =
          some (input.executableLocalizedRerootChildren cursor) :=
        (input.executableLocalizedRerootChildren?_eq_localizedRerootChildren cursor).trans
          (input.localizedRerootChildren?_eq_some_executable cursor)
      unfold buildLocalizedRerootCumulativeRule45KeyExec?
        buildLocalizedRerootCumulativeRule45Key?
      rw [childrenIdentified, input.localizedRerootChildren?_eq_some_executable cursor]
  | fuel + 1, cursor => by
      have childrenIdentified : input.executableLocalizedRerootChildren? cursor =
          some (input.executableLocalizedRerootChildren cursor) :=
        (input.executableLocalizedRerootChildren?_eq_localizedRerootChildren cursor).trans
          (input.localizedRerootChildren?_eq_some_executable cursor)
      have mappedChildren : ∀ children : List (input.LocalizedRerootCursor carrierFuel),
          children.mapM
              (input.buildLocalizedRerootCumulativeRule45KeyExec? stage target view fuel) =
            children.mapM
              (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel) := by
        intro children
        induction children with
        | nil => rfl
        | cons head tail tailInduction =>
            rw [List.mapM_cons, List.mapM_cons,
              input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build
                stage target view fuel head,
              tailInduction]
      unfold buildLocalizedRerootCumulativeRule45KeyExec?
        buildLocalizedRerootCumulativeRule45Key?
      rw [childrenIdentified, input.localizedRerootChildren?_eq_some_executable cursor]
      simp [mappedChildren]

/-- Every successful executable cumulative compilation carries the independent recursive
derivation. -/
theorem buildLocalizedRerootCumulativeRule45KeyExec?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyExec?
      stage target view fuel cursor = some key) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key := by
  rw [input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build stage target view] at computed
  exact input.buildLocalizedRerootCumulativeRule45Key?_sound
    stage target view fuel cursor key computed

/-- The constitutional component of every successful executable cumulative key is complete. -/
theorem buildLocalizedRerootCumulativeRule45KeyExec?_constitutional_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyExec?
      stage target view fuel cursor = some key) :
    key.constitutional.complete = true := by
  rw [input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build stage target view] at computed
  exact input.buildLocalizedRerootCumulativeRule45Key?_constitutional_complete
    stage target view fuel cursor key computed

/-- The constitutional component of every successful executable cumulative key is a fresh exact
projection of its provenance-bearing source nodes. -/
theorem buildLocalizedRerootCumulativeRule45KeyExec?_constitutional_sourceAligned
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyExec?
      stage target view fuel cursor = some key) :
    OfficialRuleMajorKey.SourceAligned input.moleculeGraph key.constitutional := by
  rw [input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build stage target view] at computed
  exact input.buildLocalizedRerootCumulativeRule45Key?_constitutional_sourceAligned
    stage target view fuel cursor key computed

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
