import TetraStereo.OneCenter.LocalizedRealizedTreePhysicalDistance
import TetraStereo.OneCenter.LocalizedPhysicalNearestRule4bReference
import TetraStereo.OneCenter.Rule1bSourceProfileFidelity
import TetraStereo.OneCenter.DeclarativeCIPConstitutional
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-!
# Physical observations of the actual outer digraph

This module supplies the positive, actual-to-physical observation bridge for the single-bond
acyclic localized domain.  It does not change the runtime, does not construct any new tree or
key, and does not assume agreement between a desired key, a reader or a comparator.

The exact source profile is the `Hanson2018` proposed totalization
(`Rule1bSourceProfile.hanson2018Proposed`): a real atom node observes its own sphere, a
multiple-bond duplicate observes the sphere of the atom it is attached to, a ring-closure
duplicate observes the sphere of the represented atom, and a phantom observes its own sphere.
Only the real-atom row is used here, and it is the shared "own sphere" row.

The main results are:

* `carrierOccurrence_rule1bRootDistance_eq_physical_dist` — for **any** actual carrier
  occurrence of the bounded localized enumeration (in particular the upward rerooted cursor of
  the actual outward walk), the stored `rule1bRootDistance` of its node is exactly the physical
  graph distance from the occurrence's declared original root to the observed current atom.
  The original root is the occurrence root; the occurrence address is not substituted for any
  reroot-relative position.
* `positionRecordedObservations_eq_outerRootPhysical` — at every position of an actual realized
  decorated tree, the three comparison-visible recorded observations
  `(atomicNumber, rule1bDistance, isotopeMass)` are the independently stated physical tuple
  `(atomZ v, dist outerRoot v, atomMass v)`, where `v` is the physical atom of the position and
  `outerRoot` is the original outer-digraph root preserved by every actual child step.
* `positionNode_rule1bDistance_eq_one_add_length_of_originalRoot` — for the final
  original-root arms only (the incoming occurrence is the empty-address outer root and the
  realized tree starts at the outward cursor whose address has length one), the physical root
  distance is `1 + p.val.length`.
* `declarative_observations_eq_position_observations_of_originalRoot` — the same
  original-root arms agree with the independent declarative CIP observations
  `DeclarativeCIP.nodeAtomicNumber`, `DeclarativeCIP.nodeRule1bRootDistance` (whose real-node
  value is `position.length + 1`) and `DeclarativeCIP.nodeAtomicMass`.
* `position_hanson2018Observation_eq_positionRule1bDistance` — alignment of the realized
  position's Rule-1b distance with the source-profile observation at source kind `realAtom`,
  for arbitrary `SphereData` whose own sphere is the physical outer-root distance.  The
  duplicate-only fields `attachedSphere` and `representedSphere` are not filled from runtime
  data and remain arbitrary.

The remaining work is the hierarchy-ordering join: this module returns the physical observation
values with no ordering, sorting or first-difference claim.  In particular `sortedChildren` in
`LocalizedCumulativeTreeRealizes` is a permutation witness only; it proves no sorting.
-/

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}









/-- **The Rule-1b root distance of an actual carrier occurrence is its address length.**

Real provenance is derived from the single-bond acyclic carrier, and the history length is the
address length plus one, so the node depth is exactly the address length. -/
theorem carrierOccurrence_rule1bRootDistance_eq_address_length
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.rule1bRootDistance = occurrence.1.address.length := by
  have real := input.carrierOccurrence_provenance_real singleBonded acyclic occurrence
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have rooted : input.DeclarativeLocalizedOccurrenceSubtree occurrence.1.root []
      (fuel + 1) (OfficialCIPNode.root occurrence.1.root) occurrence.1 := derived
  have aligned : (OfficialCIPNode.root occurrence.1.root).history.length =
      (([] : List Nat).length) + 1 := by
    simp [OfficialCIPNode.root]
  have historyLen : occurrence.1.node.history.length =
      occurrence.1.address.length + 1 :=
    input.declarativeLocalizedOccurrenceSubtree_history_length rooted aligned
  have depthEq : occurrence.1.node.rule1bRootDistance = occurrence.1.node.depth := by
    simp only [OfficialCIPNode.rule1bRootDistance, real]
  rw [depthEq]
  simp only [OfficialCIPNode.depth]
  omega

/-- **Exact positive observation lemma for any actual carrier occurrence.**

For an actual occurrence of the bounded localized enumeration and any observed current atom of
its node, the stored Rule-1b root distance is the physical graph distance from the occurrence's
declared original root to that atom.  The root is the occurrence root, so this covers the upward
rerooted cursor of the actual outward walk as well as the final original-root occurrence; no
reroot-relative address length is substituted for the physical distance. -/
theorem carrierOccurrence_rule1bRootDistance_eq_physical_dist
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel)
    {current : input.Atom} (observed : occurrence.1.node.current? = some current) :
    occurrence.1.node.rule1bRootDistance =
      input.moleculeGraph.underlyingSimpleGraph.dist occurrence.1.root current := by
  rw [carrierOccurrence_rule1bRootDistance_eq_address_length singleBonded acyclic occurrence,
    ← carrierOccurrence_dist_eq_address_length singleBonded acyclic occurrence observed]

/-- **Cursor form of the exact positive observation lemma.**

Every cursor of the actual reroot walk (including every upward rerooted cursor) carries an
occurrence root, and its Rule-1b distance is the physical distance from that root to the
observed current atom. -/
theorem cursor_rule1bRootDistance_eq_physical_dist
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (cursor : input.LocalizedRerootCursor fuel)
    {current : input.Atom} (observed : cursor.occurrence.1.node.current? = some current) :
    cursor.occurrence.1.node.rule1bRootDistance =
      input.moleculeGraph.underlyingSimpleGraph.dist cursor.occurrence.1.root current :=
  carrierOccurrence_rule1bRootDistance_eq_physical_dist singleBonded acyclic
    cursor.occurrence observed








/-- A realized decorated tree stores exactly its source occurrence's Rule-1b root distance. -/
theorem localizedRootTree_rule1bDistance_eq_source
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    tree.rule1bDistance = tree.source.occurrence.1.node.rule1bRootDistance := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize => rfl

/-- The Rule-1b distance at a position is its source occurrence's Rule-1b root distance. -/
theorem positionNode_rule1bDistance_eq_source
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).rule1bDistance =
      (positionSource p).occurrence.1.node.rule1bRootDistance :=
  localizedRootTree_rule1bDistance_eq_source
    (realizes_of_subtree realizes (positionNode_spec p))

/-- **Physical Rule-1b distance at every realized position.**

The position's recorded distance is the actual physical distance from the root of the position's
own source occurrence to the position atom.  This deliberately uses the occurrence root, not the
slot path length `p.val.length`, which is reroot-relative and generally differs from the distance
to the original outer root. -/
theorem positionNode_rule1bDistance_eq_physical_dist
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).rule1bDistance =
      input.moleculeGraph.underlyingSimpleGraph.dist
        (positionSource p).occurrence.1.root (positionAtom singleBonded acyclic p) := by
  rw [positionNode_rule1bDistance_eq_source realizes p]
  exact carrierOccurrence_rule1bRootDistance_eq_physical_dist singleBonded acyclic
    (positionSource p).occurrence (positionAtom_spec singleBonded acyclic p)

/-- Every actual subtree step of a realized tree keeps the occurrence root of its source. -/
theorem subtreeAt?_source_occurrence_root_eq
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) :
    node.source.occurrence.1.root = tree.source.occurrence.1.root := by
  induction path generalizing tree with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      cases lookup
      rfl
  | cons slot rest inductionHypothesis =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      exact (inductionHypothesis (realizes_of_child realizes childLookup)
        restLookup).trans (child_root_of_child realizes childLookup)

/-- **The occurrence root of a position is the original outer root.**

Every actual child step preserves the occurrence root, so the root carried by any position source
is the root of the realized tree, i.e. the declared original outer-digraph root. -/
theorem positionSource_occurrence_root_eq
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionSource p).occurrence.1.root = tree.source.occurrence.1.root :=
  subtreeAt?_source_occurrence_root_eq realizes (positionNode_spec p)

/-- **Physical Rule-1b distance from the original outer root at every realized position.** -/
theorem positionNode_rule1bDistance_eq_outerRoot_dist
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).rule1bDistance =
      input.moleculeGraph.underlyingSimpleGraph.dist tree.source.occurrence.1.root
        (positionAtom singleBonded acyclic p) := by
  rw [positionNode_rule1bDistance_eq_physical_dist singleBonded acyclic realizes p,
    positionSource_occurrence_root_eq realizes p]

/-- The three comparison-visible observations recorded at a realized position. -/
def positionRecordedObservations {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : Nat × Nat × Nat :=
  ((positionNode p).atomicNumber, (positionNode p).rule1bDistance, (positionNode p).isotopeMass)

/-- The independently stated physical tuple at a realized position, read from the position's own
source occurrence root. -/
noncomputable def positionPhysicalObservations
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : Nat × Nat × Nat :=
  (input.moleculeGraph.atomZ (positionAtom singleBonded acyclic p),
    input.moleculeGraph.underlyingSimpleGraph.dist
      (positionSource p).occurrence.1.root (positionAtom singleBonded acyclic p),
    input.moleculeGraph.atomMass (positionAtom singleBonded acyclic p))

/-- The independently stated physical tuple at a realized position, read from the original outer
root of the realized tree. -/
noncomputable def positionOuterRootPhysicalObservations
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : Nat × Nat × Nat :=
  (input.moleculeGraph.atomZ (positionAtom singleBonded acyclic p),
    input.moleculeGraph.underlyingSimpleGraph.dist tree.source.occurrence.1.root
      (positionAtom singleBonded acyclic p),
    input.moleculeGraph.atomMass (positionAtom singleBonded acyclic p))

/-- **The three comparison-visible observations equal the physical tuple.**

Atomic number is read by Rule 1a, the Rule-1b distance by the positive observation lemma, and
isotope mass by Rule 2; all three values are graph values at the physical position atom, with no
production key used as a definition. -/
theorem positionRecordedObservations_eq_physical
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    positionRecordedObservations p = positionPhysicalObservations singleBonded acyclic p := by
  dsimp [positionRecordedObservations, positionPhysicalObservations]
  exact Prod.ext (positionAtomicNumber_eq_atomZ singleBonded acyclic realizes p)
    (Prod.ext (positionNode_rule1bDistance_eq_physical_dist singleBonded acyclic realizes p)
      (positionIsotopeMass_eq_atomMass singleBonded acyclic realizes p))

/-- The two physical readings agree: the position's source root is the tree's outer root. -/
theorem positionPhysicalObservations_eq_outerRoot
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    positionPhysicalObservations singleBonded acyclic p =
      positionOuterRootPhysicalObservations singleBonded acyclic p := by
  dsimp [positionPhysicalObservations, positionOuterRootPhysicalObservations]
  rw [positionSource_occurrence_root_eq realizes p]

/-- **The three comparison-visible observations equal the physical tuple at the outer root.** -/
theorem positionRecordedObservations_eq_outerRootPhysical
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    positionRecordedObservations p =
      positionOuterRootPhysicalObservations singleBonded acyclic p :=
  (positionRecordedObservations_eq_physical singleBonded acyclic realizes p).trans
    (positionPhysicalObservations_eq_outerRoot singleBonded acyclic realizes p)

/-! ## The final original-root arms

An original-root arm is characterized by the actual incoming occurrence having the empty address
(the outer root frame) and the realized tree starting at its outward cursor.  Then the cursor
address length is one, and the branch-depth theorem
`positionSource_address_length_of_previous` gives `1 + p.val.length`.  This is the only place
where `p.val.length` enters, and it enters as a derived physical distance, not as an assumption.
-/

/-- The outward cursor above the empty-address outer root has address length one. -/
theorem rerootCursor_address_length_eq_one_of_previous_root
    {startCursor : input.LocalizedRerootCursor carrierFuel}
    (valid : input.LocalizedRerootCursorValid startCursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : startCursor.previous? = some previous)
    (previousRoot : previous.1.address = []) :
    startCursor.occurrence.1.address.length = 1 := by
  have neighbor : startCursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) previous.1 := by
    have v := valid
    unfold LocalizedRerootCursorValid at v
    rw [previousEq] at v
    change startCursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) previous.1 at v
    exact v
  have adjacent := ((input.mem_localizedRerootNeighborFrames_iff previous.1
    startCursor.occurrence.1).mp neighbor).2
  obtain ⟨_sameRoot, parent | child⟩ := adjacent
  · have h := parent.1
    rw [previousRoot] at h
    simp only [List.length_nil] at h
    omega
  · have h := child.1
    rw [previousRoot] at h
    simpa using h.symm

/-- **Branch depth for an original-root arm.**  The address length at any position is
`1 + p.val.length`. -/
theorem positionSource_address_length_eq_one_add_length_of_originalRoot
    {startCursor : input.LocalizedRerootCursor carrierFuel}
    (valid : input.LocalizedRerootCursorValid startCursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : startCursor.previous? = some previous)
    (previousRoot : previous.1.address = [])
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (sourceEq : tree.source = startCursor)
    (p : Position tree) :
    (positionSource p).occurrence.1.address.length = 1 + p.val.length := by
  have startLength := rerootCursor_address_length_eq_one_of_previous_root
    (carrierFuel := carrierFuel) valid previous previousEq previousRoot
  have previousShorter : previous.1.address.length <
      startCursor.occurrence.1.address.length := by
    rw [previousRoot, startLength]
    simp
  have relative := LocalizedCumulativeDecoratedTree.positionSource_address_length_of_previous
    (input := input) (carrierFuel := carrierFuel) (read := read)
    (startCursor := startCursor) valid previous previousEq previousShorter realizes sourceEq p
  rw [startLength] at relative
  exact relative

/-- **The realized physical Rule-1b distance of an original-root arm is `1 + p.val.length`.** -/
theorem positionNode_rule1bDistance_eq_one_add_length_of_originalRoot
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {startCursor : input.LocalizedRerootCursor carrierFuel}
    (valid : input.LocalizedRerootCursorValid startCursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : startCursor.previous? = some previous)
    (previousRoot : previous.1.address = [])
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (sourceEq : tree.source = startCursor)
    (p : Position tree) :
    (positionNode p).rule1bDistance = 1 + p.val.length := by
  have sourceLen := positionSource_address_length_eq_one_add_length_of_originalRoot
    (carrierFuel := carrierFuel) (read := read) valid previous previousEq previousRoot
    realizes sourceEq p
  have carrierLen := carrierOccurrence_rule1bRootDistance_eq_address_length singleBonded acyclic
    (positionSource p).occurrence
  rw [positionNode_rule1bDistance_eq_source realizes p, carrierLen, sourceLen]

/-- **The original-root physical distance is `1 + p.val.length`.** -/
theorem positionNode_physical_dist_eq_one_add_length_of_originalRoot
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {startCursor : input.LocalizedRerootCursor carrierFuel}
    (valid : input.LocalizedRerootCursorValid startCursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : startCursor.previous? = some previous)
    (previousRoot : previous.1.address = [])
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (sourceEq : tree.source = startCursor)
    (p : Position tree) :
    input.moleculeGraph.underlyingSimpleGraph.dist tree.source.occurrence.1.root
        (positionAtom singleBonded acyclic p) = 1 + p.val.length := by
  rw [← positionNode_rule1bDistance_eq_outerRoot_dist singleBonded acyclic realizes p,
    positionNode_rule1bDistance_eq_one_add_length_of_originalRoot singleBonded acyclic
      valid previous previousEq previousRoot realizes sourceEq p]

/-! ## Alignment with the independent declarative CIP observations -/

/-- Rule 1a at a real declarative node is the physical atomic number. -/
theorem declarative_nodeAtomicNumber_real (atom : input.Atom) :
    DeclarativeCIP.nodeAtomicNumber input.moleculeGraph
        (some ⟨some atom, DeclarativeCIP.NodeProvenance.realAtom⟩) =
      input.moleculeGraph.atomZ atom := rfl

/-- Rule 2 at a real declarative node is the physical isotope mass. -/
theorem declarative_nodeAtomicMass_real (atom : input.Atom) :
    DeclarativeCIP.nodeAtomicMass input.moleculeGraph
        (some ⟨some atom, DeclarativeCIP.NodeProvenance.realAtom⟩) =
      input.moleculeGraph.atomMass atom := rfl

/-- The declarative total Rule-1b distance at a real node is the positional sphere
`position.length + 1`. -/
theorem declarative_nodeRule1bRootDistance_real (position : List Nat) (atom : input.Atom) :
    DeclarativeCIP.nodeRule1bRootDistance position
        (some ⟨some atom, DeclarativeCIP.NodeProvenance.realAtom⟩) =
      position.length + 1 := rfl

/-- **Declarative observations agree with the recorded observations of an original-root arm.** -/
theorem declarative_observations_eq_position_observations_of_originalRoot
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {startCursor : input.LocalizedRerootCursor carrierFuel}
    (valid : input.LocalizedRerootCursorValid startCursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : startCursor.previous? = some previous)
    (previousRoot : previous.1.address = [])
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (sourceEq : tree.source = startCursor)
    (p : Position tree) :
    DeclarativeCIP.nodeAtomicNumber input.moleculeGraph
        (some ⟨some (positionAtom singleBonded acyclic p),
          DeclarativeCIP.NodeProvenance.realAtom⟩) =
        (positionNode p).atomicNumber ∧
      DeclarativeCIP.nodeRule1bRootDistance p.val
        (some ⟨some (positionAtom singleBonded acyclic p),
          DeclarativeCIP.NodeProvenance.realAtom⟩) =
        (positionNode p).rule1bDistance ∧
      DeclarativeCIP.nodeAtomicMass input.moleculeGraph
        (some ⟨some (positionAtom singleBonded acyclic p),
          DeclarativeCIP.NodeProvenance.realAtom⟩) =
        (positionNode p).isotopeMass := by
  have numberEq : DeclarativeCIP.nodeAtomicNumber input.moleculeGraph
      (some ⟨some (positionAtom singleBonded acyclic p),
        DeclarativeCIP.NodeProvenance.realAtom⟩) =
      (positionNode p).atomicNumber := by
    rw [declarative_nodeAtomicNumber_real]
    exact (positionAtomicNumber_eq_atomZ singleBonded acyclic realizes p).symm
  have distanceEq : DeclarativeCIP.nodeRule1bRootDistance p.val
      (some ⟨some (positionAtom singleBonded acyclic p),
        DeclarativeCIP.NodeProvenance.realAtom⟩) =
      (positionNode p).rule1bDistance := by
    rw [declarative_nodeRule1bRootDistance_real,
      positionNode_rule1bDistance_eq_one_add_length_of_originalRoot singleBonded acyclic
        valid previous previousEq previousRoot realizes sourceEq p]
    exact Nat.add_comm _ _
  have massEq : DeclarativeCIP.nodeAtomicMass input.moleculeGraph
      (some ⟨some (positionAtom singleBonded acyclic p),
        DeclarativeCIP.NodeProvenance.realAtom⟩) =
      (positionNode p).isotopeMass := by
    rw [declarative_nodeAtomicMass_real]
    exact (positionIsotopeMass_eq_atomMass singleBonded acyclic realizes p).symm
  exact ⟨numberEq, distanceEq, massEq⟩

/-- **The declarative Rule-1b distance of an original-root arm is the outer-root physical
distance.** -/
theorem declarative_nodeRule1bRootDistance_eq_outerRoot_dist_of_originalRoot
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {startCursor : input.LocalizedRerootCursor carrierFuel}
    (valid : input.LocalizedRerootCursorValid startCursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : startCursor.previous? = some previous)
    (previousRoot : previous.1.address = [])
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (sourceEq : tree.source = startCursor)
    (p : Position tree) :
    DeclarativeCIP.nodeRule1bRootDistance p.val
        (some ⟨some (positionAtom singleBonded acyclic p),
          DeclarativeCIP.NodeProvenance.realAtom⟩) =
      input.moleculeGraph.underlyingSimpleGraph.dist tree.source.occurrence.1.root
        (positionAtom singleBonded acyclic p) := by
  rw [declarative_nodeRule1bRootDistance_real]
  rw [show p.val.length + 1 = 1 + p.val.length from Nat.add_comm _ _]
  rw [← positionNode_physical_dist_eq_one_add_length_of_originalRoot singleBonded acyclic
    valid previous previousEq previousRoot realizes sourceEq p]

/-! ## Source-profile observation alignment (Hanson2018 proposed totalization)

The profile observation at source kind `realAtom` is the node's own sphere.  We quantify the
`SphereData` fields arbitrarily and identify only `ownSphere` with the physical outer-root
distance; the duplicate-only fields are not read at a real node and are not filled from any
runtime value. -/

/-- Actual carrier occurrences have source kind `realAtom`. -/
theorem carrierOccurrence_sourceKind_eq_realAtom
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    Rule1bSourceProfile.Official.sourceKind occurrence.1.node.provenance =
      Rule1bSourceProfile.NodeKind.realAtom := by
  rw [input.carrierOccurrence_provenance_real singleBonded acyclic occurrence]
  rfl

/-- **Carrier-level alignment with the Hanson2018 proposed observation.**

For an actual carrier occurrence, the proposed source observation of its provenance kind equals
the stored Rule-1b root distance whenever the data's own sphere is the physical outer-root
distance.  The attached and represented spheres are arbitrary. -/
theorem carrierOccurrence_hanson2018Observation_eq_rule1bRootDistance
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel)
    {current : input.Atom} (observed : occurrence.1.node.current? = some current)
    (data : Rule1bSourceProfile.SphereData)
    (ownSphereEq : data.ownSphere =
      input.moleculeGraph.underlyingSimpleGraph.dist occurrence.1.root current) :
    Rule1bSourceProfile.hanson2018Observation
        (Rule1bSourceProfile.Official.sourceKind occurrence.1.node.provenance) data =
      occurrence.1.node.rule1bRootDistance := by
  rw [carrierOccurrence_sourceKind_eq_realAtom singleBonded acyclic occurrence,
    Rule1bSourceProfile.hanson2018Observation_realAtom, ownSphereEq,
    ← carrierOccurrence_rule1bRootDistance_eq_physical_dist singleBonded acyclic
      occurrence observed]

/-- **Position-level alignment with the Hanson2018 proposed observation.**

At every realized position, source kind `realAtom` observes its own sphere, which is the
physical outer-root distance.  The duplicate-only sphere fields are irrelevant and arbitrary. -/
theorem position_hanson2018Observation_eq_positionRule1bDistance
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree)
    (data : Rule1bSourceProfile.SphereData)
    (ownSphereEq : data.ownSphere =
      input.moleculeGraph.underlyingSimpleGraph.dist tree.source.occurrence.1.root
        (positionAtom singleBonded acyclic p)) :
    Rule1bSourceProfile.hanson2018Observation Rule1bSourceProfile.NodeKind.realAtom data =
      (positionNode p).rule1bDistance := by
  rw [Rule1bSourceProfile.hanson2018Observation_realAtom, ownSphereEq,
    ← positionNode_rule1bDistance_eq_outerRoot_dist singleBonded acyclic realizes p]

/-- **The selected `hanson2018Proposed` profile observation equals the realized position's
Rule-1b distance.** -/
theorem position_observation_hanson2018Proposed_eq_positionRule1bDistance
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree)
    (data : Rule1bSourceProfile.SphereData)
    (ownSphereEq : data.ownSphere =
      input.moleculeGraph.underlyingSimpleGraph.dist tree.source.occurrence.1.root
        (positionAtom singleBonded acyclic p)) :
    Rule1bSourceProfile.observation Rule1bSourceProfile.SourceProfile.hanson2018Proposed
        Rule1bSourceProfile.NodeKind.realAtom data =
      (positionNode p).rule1bDistance := by
  change Rule1bSourceProfile.hanson2018Observation Rule1bSourceProfile.NodeKind.realAtom data =
    (positionNode p).rule1bDistance
  exact position_hanson2018Observation_eq_positionRule1bDistance singleBonded acyclic
    realizes p data ownSphereEq

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.carrierOccurrence_rule1bRootDistance_eq_address_length
assert_kernel_only TetraStereo.OneCenter.carrierOccurrence_rule1bRootDistance_eq_physical_dist
assert_kernel_only TetraStereo.OneCenter.cursor_rule1bRootDistance_eq_physical_dist
assert_kernel_only TetraStereo.OneCenter.localizedRootTree_rule1bDistance_eq_source
assert_kernel_only TetraStereo.OneCenter.positionNode_rule1bDistance_eq_source
assert_kernel_only TetraStereo.OneCenter.positionNode_rule1bDistance_eq_physical_dist
assert_kernel_only TetraStereo.OneCenter.subtreeAt?_source_occurrence_root_eq
assert_kernel_only TetraStereo.OneCenter.positionSource_occurrence_root_eq
assert_kernel_only TetraStereo.OneCenter.positionNode_rule1bDistance_eq_outerRoot_dist
assert_kernel_only TetraStereo.OneCenter.positionRecordedObservations
assert_kernel_only TetraStereo.OneCenter.positionPhysicalObservations
assert_kernel_only TetraStereo.OneCenter.positionOuterRootPhysicalObservations
assert_kernel_only TetraStereo.OneCenter.positionRecordedObservations_eq_physical
assert_kernel_only TetraStereo.OneCenter.positionPhysicalObservations_eq_outerRoot
assert_kernel_only TetraStereo.OneCenter.positionRecordedObservations_eq_outerRootPhysical
assert_kernel_only TetraStereo.OneCenter.rerootCursor_address_length_eq_one_of_previous_root
assert_kernel_only TetraStereo.OneCenter.positionSource_address_length_eq_one_add_length_of_originalRoot
assert_kernel_only TetraStereo.OneCenter.positionNode_rule1bDistance_eq_one_add_length_of_originalRoot
assert_kernel_only TetraStereo.OneCenter.positionNode_physical_dist_eq_one_add_length_of_originalRoot
assert_kernel_only TetraStereo.OneCenter.declarative_nodeAtomicNumber_real
assert_kernel_only TetraStereo.OneCenter.declarative_nodeAtomicMass_real
assert_kernel_only TetraStereo.OneCenter.declarative_nodeRule1bRootDistance_real
assert_kernel_only TetraStereo.OneCenter.declarative_observations_eq_position_observations_of_originalRoot
assert_kernel_only TetraStereo.OneCenter.declarative_nodeRule1bRootDistance_eq_outerRoot_dist_of_originalRoot
assert_kernel_only TetraStereo.OneCenter.carrierOccurrence_sourceKind_eq_realAtom
assert_kernel_only TetraStereo.OneCenter.carrierOccurrence_hanson2018Observation_eq_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.position_hanson2018Observation_eq_positionRule1bDistance
assert_kernel_only TetraStereo.OneCenter.position_observation_hanson2018Proposed_eq_positionRule1bDistance

end TetraStereo.OneCenter
