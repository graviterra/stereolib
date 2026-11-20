import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution
import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal
import TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Generated prepared snapshots read through an independent candidate source map

This module closes the connection between the actual generated prepared-context snapshot and an
independently defined candidate source-state reader on certified detected occurrence units.

The candidate reader identifies the raw canonical query by its certified occurrence history and
real provenance, and asks
whether that node is a strict canonical descendant of the supplied raw source within the source
budget.  It never inspects the generated state, the prepared recursion, or any supplied
source/query equality.  Its optional descriptor argument is arbitrary; only the realization
theorem instantiates it with the actual prepared descriptor.

The main theorem states that the raw-state descriptor map of the actual generated snapshot is
exactly this candidate map, pointwise on every detected occurrence.  The proof uses the exact
source budget and the converse emission theorem for strict descendants: stored labels are exactly
the recursive descriptors at the derived residual depth, and a missing label means that the
recursive descriptor itself refuses.  Consequently absence needs no desired-label premise.

The final results record the termination-facing congruence: on the supported domain of a strictly
deeper source, the candidate map agrees with the parent map at the correspondingly decreased
budget, and the candidate map depends only on the candidate values at strictly deeper supported
occurrences.

Scope: this is an exact snapshot/reader connection.  It does not assert IUPAC faithfulness of the
generated labels, chemical correctness of the prepared recursion, or completion of the surrounding
retained-context construction.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingPreparedContextRecursion
  (MarkContext PreparedStep childrenUnder factsOfStep descriptorOfStep preparedFacts
   preparedDescriptor? rawStepPrepared?)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointPreparedLabelExecution
  (snapshot_source_budget snapshot_contains generated_label_eq_descriptor residual_depth_lt)
open LocalizedMarkedTerminalReferenceScope (Descends StrictDescendant descendant_reached)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)
open LocalizedMarkedGeneratedFactUniqueness (factOf_key)
open LocalizedMarkedRetainedStateReader
  (rawOccurrenceKey rawStateFact? rawStateDescriptorMap factDescriptor factLabel)
open LocalizedMarkedTerminalGaugeRefusal (generated_eq_of_key)
open LocalizedGenericMarkedRecalculation (Geometry factOf)
open AuthoritativeCIPMoleculeCursorRanking (CanonicalCenterTreeNode)

abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## The descriptor bridge

`rawStateDescriptorMap` reads the `R`/`S`/`r`/`s` descriptor coordinate of a stored fact.  The
prepared recursion produces a `LocalizedTetrahedralRSPseudoDescriptor`, whose four constructors are
exactly those four letters.  This bridge is a pure projection and has no dependency on any runtime
state. -/

/-- The four-letter descriptor carried by a localized tetrahedral pseudo-descriptor. -/
def localizedDescriptor : LocalizedTetrahedralRSPseudoDescriptor → Descriptor
  | .chiral RS.R => .R
  | .chiral RS.S => .S
  | .pseudoasymmetric .r => .r
  | .pseudoasymmetric .s => .s

/-- Reading a generated fact as a raw descriptor is the same as projecting its label. -/
theorem factDescriptor_factOf (node : Node)
    (label : LocalizedTetrahedralRSPseudoDescriptor) :
    factDescriptor (factOf node label) = localizedDescriptor label := by
  cases label with
  | chiral raw => cases raw <;> rfl
  | pseudoasymmetric pseudo => cases pseudo <;> rfl

/-- The projected descriptor is always tetrahedral. -/
theorem localizedDescriptor_isTetrahedral (label : LocalizedTetrahedralRSPseudoDescriptor) :
    (localizedDescriptor label).IsTetrahedral := by
  cases label with
  | chiral raw => cases raw <;> trivial
  | pseudoasymmetric pseudo => cases pseudo <;> trivial

/-- The localized descriptor round-trips through the stored-label projection. -/
theorem localizedDescriptor_toLocalizedLabel (label : LocalizedTetrahedralRSPseudoDescriptor) :
    (localizedDescriptor label).toLocalizedLabel = some label := by
  cases label with
  | chiral raw => cases raw <;> rfl
  | pseudoasymmetric pseudo => cases pseudo <;> rfl

/-! ## Molecular support of a candidate query

A detected occurrence unit determines the raw occurrence key
`((root :: path).reverse).map Fin.val` with real provenance.  A raw canonical node supports that
unit at a source and budget when its full canonical occurrence key is exactly that molecular key,
it is a strict canonical descendant of the source, and its history fits the remaining source
budget.  This is the complete query domain of `childrenUnder`: no path-length approximation and no
divergent branch is included. -/

/-- A raw canonical node carries exactly one certified occurrence at a source within budget. -/
def SupportedNode {n : Nat} (mol : RawMolecule) (depth : Nat) (source : Node)
    (unit : OccurrenceUnit (Fin n)) (node : Node) : Prop :=
  canonicalOccurrenceKey node = rawOccurrenceKey unit ∧
    StrictDescendant mol source node ∧
    node.history.length ≤ depth + source.history.length

/-- The total reader domain: a detected molecular occurrence with at least one supported raw node. -/
def Supported (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat)
    (source : Node) (unit : OccurrenceUnit input.Atom) : Prop :=
  IsDetectedCenter input.moleculeGraph unit.atom ∧
    ∃ node, SupportedNode mol depth source unit node

/-- A supported node retains the exact molecular history of its occurrence unit. -/
theorem SupportedNode.history {n : Nat} {mol : RawMolecule} {depth : Nat} {source : Node}
    {unit : OccurrenceUnit (Fin n)} {node : Node}
    (supported : SupportedNode mol depth source unit node) :
    node.history = ((unit.root :: unit.path).reverse).map Fin.val := by
  have history := congrArg CanonicalOccurrenceKey.history supported.1
  simpa only [canonicalOccurrenceKey, rawOccurrenceKey] using history

/-- A supported node has real provenance, because the molecular key has real provenance. -/
theorem SupportedNode.provenance {n : Nat} {mol : RawMolecule} {depth : Nat} {source : Node}
    {unit : OccurrenceUnit (Fin n)} {node : Node}
    (supported : SupportedNode mol depth source unit node) :
    node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom := by
  have provenance := congrArg CanonicalOccurrenceKey.provenance supported.1
  simpa only [canonicalOccurrenceKey, rawOccurrenceKey] using provenance

/-- A strict descendant of a reached source lies in one canonical center tree. -/
theorem exists_canonicalTreeNode_of_strictDescendant (mol : RawMolecule) {source target : Node}
    (sourceReached : Reached mol source) (path : StrictDescendant mol source target) :
    ∃ center, CanonicalCenterTreeNode mol center target := by
  obtain ⟨child, edge, rest⟩ := path
  have targetReached : Reached mol target :=
    descendant_reached (reached_child mol source child sourceReached edge) rest
  obtain ⟨center, valid, targetPath⟩ := targetReached
  exact ⟨center, generated_of_reachedFrom mol center target targetPath⟩

/-- Two supported nodes for the same molecular occurrence are the same canonical node.  This is
the key uniqueness already proved for generated center trees, applied to the reached strict
descendants of the common source. -/
theorem supportedNode_eq {n : Nat} {mol : RawMolecule} {depth : Nat} {source : Node}
    {unit : OccurrenceUnit (Fin n)} {left right : Node}
    (sourceReached : Reached mol source)
    (leftSupported : SupportedNode mol depth source unit left)
    (rightSupported : SupportedNode mol depth source unit right) :
    left = right := by
  have keys : canonicalOccurrenceKey left = canonicalOccurrenceKey right :=
    leftSupported.1.trans rightSupported.1.symm
  obtain ⟨leftCenter, leftTree⟩ :=
    exists_canonicalTreeNode_of_strictDescendant mol sourceReached leftSupported.2.1
  obtain ⟨rightCenter, rightTree⟩ :=
    exists_canonicalTreeNode_of_strictDescendant mol sourceReached rightSupported.2.1
  exact generated_eq_of_key leftTree rightTree keys

/-! ## The independent candidate reader

The reader uses only the occurrence unit, the source (through its canonical descendant relation and
history budget), and an arbitrary candidate function on raw canonical nodes.  It contains no
generated state, no prepared recursion, no runtime assumptions, and no supplied source/query
equality.  Its witness is chosen classically; `supportedNode_eq` proves the chosen value is unique
and hence independent of the choice. -/

/-- The candidate source reader at one occurrence unit. -/
noncomputable def candidateSourceReader (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (unit : OccurrenceUnit input.Atom) : Option Descriptor := by
  classical
  exact
    if h : Supported input mol depth source unit then
      (candidate (depth + source.history.length - (Classical.choose h.2).history.length)
        (Classical.choose h.2)).map localizedDescriptor
    else none

/-- The candidate source map on all detected occurrence units. -/
noncomputable def candidateSourceMap (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor) :
    DescriptorMap (DetectedOccurrence input.moleculeGraph) :=
  fun unit => candidateSourceReader input mol depth source candidate unit.1

/-- The candidate reader at any one supplied supported node. -/
theorem candidateSourceReader_eq_of_supported
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (unit : OccurrenceUnit input.Atom) (node : Node)
    (sourceReached : Reached mol source)
    (detected : IsDetectedCenter input.moleculeGraph unit.atom)
    (supported : SupportedNode mol depth source unit node) :
    candidateSourceReader input mol depth source candidate unit =
      (candidate (depth + source.history.length - node.history.length) node).map
        localizedDescriptor := by
  classical
  have witness : ∃ node, SupportedNode mol depth source unit node := ⟨node, supported⟩
  have total : Supported input mol depth source unit := ⟨detected, witness⟩
  unfold candidateSourceReader
  rw [dif_pos total]
  have chosen : Classical.choose total.2 = node :=
    supportedNode_eq sourceReached (Classical.choose_spec total.2) supported
  rw [chosen]

/-- The candidate reader refuses when the molecular unit is not detected. -/
theorem candidateSourceReader_eq_none_of_not_detected
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (unit : OccurrenceUnit input.Atom)
    (notDetected : ¬ IsDetectedCenter input.moleculeGraph unit.atom) :
    candidateSourceReader input mol depth source candidate unit = none := by
  classical
  have notSupported : ¬ Supported input mol depth source unit := fun supported => notDetected supported.1
  unfold candidateSourceReader
  rw [dif_neg notSupported]

/-- The candidate reader refuses when no raw canonical source node supports the unit. -/
theorem candidateSourceReader_eq_none_of_no_node
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (unit : OccurrenceUnit input.Atom)
    (noNode : ¬ ∃ node, SupportedNode mol depth source unit node) :
    candidateSourceReader input mol depth source candidate unit = none := by
  classical
  have notSupported : ¬ Supported input mol depth source unit := fun supported => noNode supported.2
  unfold candidateSourceReader
  rw [dif_neg notSupported]

/-- The candidate map refuses at a detected unit with no supported raw node. -/
theorem candidateSourceMap_eq_none_of_no_node
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (unit : DetectedOccurrence input.moleculeGraph)
    (noNode : ¬ ∃ node, SupportedNode mol depth source unit.1 node) :
    candidateSourceMap input mol depth source candidate unit = none := by
  unfold candidateSourceMap
  exact candidateSourceReader_eq_none_of_no_node input mol depth source candidate unit.1 noNode

/-- Outside the canonical source domain the map is empty: if no raw node with the molecular key is
a strict canonical descendant of the source, the reader yields `none`. -/
theorem candidateSourceMap_eq_none_of_no_canonicalOccurrence
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (unit : DetectedOccurrence input.moleculeGraph)
    (noOccurrence : ∀ node, canonicalOccurrenceKey node = rawOccurrenceKey unit.1 →
      ¬ StrictDescendant mol source node) :
    candidateSourceMap input mol depth source candidate unit = none := by
  apply candidateSourceMap_eq_none_of_no_node
  intro supported
  obtain ⟨node, key, path, _⟩ := supported
  exact noOccurrence node key path

/-- Outside the residual source budget the map is empty. -/
theorem candidateSourceMap_eq_none_of_inadequate
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (unit : DetectedOccurrence input.moleculeGraph)
    (inadequate : ∀ node, canonicalOccurrenceKey node = rawOccurrenceKey unit.1 →
      StrictDescendant mol source node → depth + source.history.length < node.history.length) :
    candidateSourceMap input mol depth source candidate unit = none := by
  apply candidateSourceMap_eq_none_of_no_node
  intro supported
  obtain ⟨node, key, path, budget⟩ := supported
  exact Nat.not_lt_of_ge budget (inadequate node key path)

/-- Every value of the candidate source map is tetrahedral. -/
theorem candidateSourceMap_tetrahedral
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat) (source : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (unit : DetectedOccurrence input.moleculeGraph) (value : Descriptor)
    (observed : candidateSourceMap input mol depth source candidate unit = some value) :
    value.IsTetrahedral := by
  classical
  unfold candidateSourceMap at observed
  unfold candidateSourceReader at observed
  by_cases supported : Supported input mol depth source unit.1
  · rw [dif_pos supported] at observed
    obtain ⟨label, _, rfl⟩ := Option.map_eq_some_iff.1 observed
    exact localizedDescriptor_isTetrahedral label
  · rw [dif_neg supported] at observed
    cases observed

/-! ## Realization by the actual prepared recursion

Only from this point on does the actual prepared descriptor appear.  It is supplied as an argument
to the already-defined reader, never inspected by the reader definition.  The candidate keeps the
full ordered reference list and the original geometry; `preparedDescriptor?` itself regenerates the
mirror geometry and its child state, so the realization covers the separately regenerated mirrored
branch without adding a second geometry parameter to the reader. -/

/-- The actual prepared descriptor as a candidate function on raw canonical nodes. -/
noncomputable def preparedCandidate (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (geom : Geometry) (references : List input.Atom) :
    Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor :=
  fun residual node =>
    preparedDescriptor? mol (jointOperations input mol) residual geom []
      (references.map Fin.val) node

/-- If a fact with the molecular key is present, the raw lookup is present.  The converse is
immediate from the definition of `find?`; together they give the exact absence criterion used in
the realization proof. -/
theorem exists_rawStateFact?_of_mem {n : Nat} (state : OccurrenceAuxState)
    (unit : OccurrenceUnit (Fin n)) (fact : OccurrenceAuxFact)
    (member : fact ∈ state) (key : fact.key = rawOccurrenceKey unit) :
    ∃ found, rawStateFact? state unit = some found := by
  cases lookup : rawStateFact? state unit with
  | some found => exact ⟨found, rfl⟩
  | none =>
      have lookup' : state.find? (fun candidate => candidate.key == rawOccurrenceKey unit) = none := by
        simpa only [rawStateFact?] using lookup
      have impossible := (List.find?_eq_none.mp lookup') fact member
      exact (impossible (beq_iff_eq.mpr key)).elim

/-- Pointwise label form of the generated snapshot at a supported query, exactly as supplied by
`generated_label_eq_descriptor`. -/
theorem candidateSourceReader_toLocalizedLabel_eq_generated_factAt
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (source : Node) (references : List input.Atom)
    (sourceReached : Reached mol source) (unit : OccurrenceUnit input.Atom) (node : Node)
    (detected : IsDetectedCenter input.moleculeGraph unit.atom)
    (supported : SupportedNode mol depth source unit node) :
    (candidateSourceReader input mol depth source (preparedCandidate input mol geom references)
        unit).bind Descriptor.toLocalizedLabel =
      ((generated input mol depth geom source references).factAt? node).map factLabel := by
  classical
  rw [candidateSourceReader_eq_of_supported input mol depth source
    (preparedCandidate input mol geom references) unit node sourceReached detected supported]
  have mapped : (Option.map localizedDescriptor
        (preparedCandidate input mol geom references
          (depth + source.history.length - node.history.length) node)).bind
        Descriptor.toLocalizedLabel =
      preparedCandidate input mol geom references
        (depth + source.history.length - node.history.length) node := by
    cases preparedCandidate input mol geom references
        (depth + source.history.length - node.history.length) node with
    | none => rfl
    | some label => simp [localizedDescriptor_toLocalizedLabel]
  rw [mapped]
  exact (generated_label_eq_descriptor input mol depth geom source node references sourceReached
    supported.2.1 supported.2.2).symm

/-- **Exact snapshot/reader equality.**  The raw descriptor map of the actual generated prepared
snapshot is the independent candidate source map, pointwise on every detected occurrence.  The
candidate supplied in the realization is the actual prepared recursion at the residual depth derived
from each supported query, with the full ordered reference list and the original geometry; the
generated snapshot itself and all of its runtime state are absent from the candidate reader
definition. -/
theorem rawStateDescriptorMap_generated_eq_candidateSourceMap
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (source : Node) (references : List input.Atom)
    (sourceReached : Reached mol source) :
    rawStateDescriptorMap input (generated input mol depth geom source references) =
      candidateSourceMap input mol depth source (preparedCandidate input mol geom references) := by
  classical
  funext unit
  simp only [rawStateDescriptorMap, candidateSourceMap]
  cases observed : rawStateFact? (generated input mol depth geom source references) unit.1 with
  | none =>
      simp only [Option.map_none]
      by_cases supported : Supported input mol depth source unit.1
      · obtain ⟨node, nodeSupported⟩ := supported.2
        rw [candidateSourceReader_eq_of_supported input mol depth source
          (preparedCandidate input mol geom references) unit.1 node sourceReached supported.1
          nodeSupported]
        cases computed : preparedCandidate input mol geom references
            (depth + source.history.length - node.history.length) node with
        | none => rfl
        | some label =>
            exfalso
            have computedStep : descriptorOfStep (rawStepPrepared? (jointOperations input mol))
                mol (depth + source.history.length - node.history.length) geom []
                (references.map Fin.val) node = some label := by
              simpa only [preparedCandidate, preparedDescriptor?] using computed
            have member := snapshot_contains (rawStepPrepared? (jointOperations input mol))
              mol depth geom [] source node (references.map Fin.val)
              nodeSupported.2.1 nodeSupported.2.2 label computedStep
            have member' : factOf node label ∈ generated input mol depth geom source references := by
              simpa only [generated, preparedFacts] using member
            have keyEq : (factOf node label).key = rawOccurrenceKey unit.1 := by
              simpa only [factOf_key] using nodeSupported.1
            obtain ⟨found, foundEq⟩ := exists_rawStateFact?_of_mem
              (generated input mol depth geom source references) unit.1
              (factOf node label) member' keyEq
            rw [observed] at foundEq
            cases foundEq
      · have noNode : ¬ ∃ node, SupportedNode mol depth source unit.1 node := by
          intro supportedNodes
          exact supported ⟨unit.2, supportedNodes⟩
        simp [candidateSourceReader_eq_none_of_no_node input mol depth source
          (preparedCandidate input mol geom references) unit.1 noNode]
  | some fact =>
      have lookup : (generated input mol depth geom source references).find?
          (fun found => found.key == rawOccurrenceKey unit.1) = some fact := by
        simpa only [rawStateFact?] using observed
      have member : fact ∈ generated input mol depth geom source references :=
        List.mem_of_find?_eq_some lookup
      have keyEq : fact.key = rawOccurrenceKey unit.1 := by
        simpa only [beq_iff_eq] using List.find?_some lookup
      obtain ⟨target, label, remaining, path, budget, computed, factValue⟩ :=
        snapshot_source_budget (rawStepPrepared? (jointOperations input mol)) mol depth geom []
          source (references.map Fin.val) fact
          (by simpa only [generated, preparedFacts] using member)
      have targetKey : canonicalOccurrenceKey target = rawOccurrenceKey unit.1 := by
        simpa only [factValue, factOf_key] using keyEq
      have adequate : target.history.length ≤ depth + source.history.length := by omega
      have targetSupported : SupportedNode mol depth source unit.1 target :=
        ⟨targetKey, path, adequate⟩
      rw [candidateSourceReader_eq_of_supported input mol depth source
        (preparedCandidate input mol geom references) unit.1 target sourceReached unit.2
        targetSupported]
      have residualEq : remaining = depth + source.history.length - target.history.length := by
        omega
      have candidateComputed : preparedCandidate input mol geom references
          (depth + source.history.length - target.history.length) target = some label := by
        rw [← residualEq]
        simpa only [preparedCandidate, preparedDescriptor?] using computed
      rw [factValue, candidateComputed]
      simp [factDescriptor_factOf]

/-! ## Termination-facing congruence

The candidate map only reads candidate values at strict canonical descendants of its source.  On the
supported domain of a strictly deeper source, its value is exactly the parent map's value with the
budget decreased by the length difference; that decreased budget is strictly smaller than the parent
budget.  Thus a future well-founded recursion may replace generated facts on the deeper supported
occurrences by the independently indexed candidate values. -/

/-- Strict canonical descent is transitive. -/
theorem strictDescendant_trans (mol : RawMolecule) {first middle last : Node}
    (firstPath : StrictDescendant mol first middle)
    (secondPath : StrictDescendant mol middle last) :
    StrictDescendant mol first last := by
  obtain ⟨child, edge, rest⟩ := firstPath
  obtain ⟨child', edge', rest'⟩ := secondPath
  exact ⟨child, edge, (rest.tail edge').trans rest'⟩

/-- The candidate map depends only on candidate values at strictly deeper supported occurrences. -/
theorem candidateSourceMap_congr_of_agree
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat) (source : Node)
    (candidate₁ candidate₂ : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (sourceReached : Reached mol source)
    (agreement : ∀ residual node, StrictDescendant mol source node →
      node.history.length ≤ depth + source.history.length →
      candidate₁ residual node = candidate₂ residual node) :
    candidateSourceMap input mol depth source candidate₁ =
      candidateSourceMap input mol depth source candidate₂ := by
  classical
  funext unit
  unfold candidateSourceMap
  by_cases supported : Supported input mol depth source unit.1
  · obtain ⟨node, nodeSupported⟩ := supported.2
    rw [candidateSourceReader_eq_of_supported input mol depth source candidate₁ unit.1 node
          sourceReached supported.1 nodeSupported,
        candidateSourceReader_eq_of_supported input mol depth source candidate₂ unit.1 node
          sourceReached supported.1 nodeSupported]
    simp [agreement (depth + source.history.length - node.history.length) node
          nodeSupported.2.1 nodeSupported.2.2]
  · simp [candidateSourceReader_eq_none_of_no_node input mol depth source candidate₁ unit.1
          (fun nodes => supported ⟨unit.2, nodes⟩),
        candidateSourceReader_eq_none_of_no_node input mol depth source candidate₂ unit.1
          (fun nodes => supported ⟨unit.2, nodes⟩)]

/-- On the supported domain of a strictly deeper source, the candidate map is the parent candidate
map at the same residual depth.  The parent budget is `depth + source.length - deeper.length`, which
is strictly below `depth` because `deeper` is a strict canonical descendant. -/
theorem candidateSourceMap_strictDescendant_eq
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (source deeper : Node)
    (candidate : Nat → Node → Option LocalizedTetrahedralRSPseudoDescriptor)
    (sourceReached : Reached mol source)
    (path : StrictDescendant mol source deeper)
    (adequate : deeper.history.length ≤ depth + source.history.length)
    (unit : DetectedOccurrence input.moleculeGraph)
    (supportedDeeper : Supported input mol
      (depth + source.history.length - deeper.history.length) deeper unit.1) :
    candidateSourceMap input mol
        (depth + source.history.length - deeper.history.length) deeper candidate unit =
      candidateSourceMap input mol depth source candidate unit := by
  classical
  have deeperReached : Reached mol deeper := by
    obtain ⟨child, edge, rest⟩ := path
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  obtain ⟨node, nodeSupported⟩ := supportedDeeper.2
  have nodePath : StrictDescendant mol source node :=
    strictDescendant_trans mol path nodeSupported.2.1
  have nodeBudget : node.history.length ≤ depth + source.history.length := by
    have deeperBudget := nodeSupported.2.2
    omega
  have nodeSupportedSource : SupportedNode mol depth source unit.1 node :=
    ⟨nodeSupported.1, nodePath, nodeBudget⟩
  unfold candidateSourceMap
  rw [candidateSourceReader_eq_of_supported input mol
        (depth + source.history.length - deeper.history.length) deeper candidate unit.1 node
        deeperReached unit.2 nodeSupported,
      candidateSourceReader_eq_of_supported input mol depth source candidate unit.1 node
        sourceReached unit.2 nodeSupportedSource]
  have residual : (depth + source.history.length - deeper.history.length) +
        deeper.history.length - node.history.length =
      depth + source.history.length - node.history.length := by omega
  simp [residual]

/-- The decreased budget at a strictly deeper supported source is strictly smaller than the parent
budget.  This is the measure consumed by the termination argument. -/
theorem candidateSourceMap_strictDescendant_depth_lt
    (mol : RawMolecule) (depth : Nat) {source deeper : Node}
    (path : StrictDescendant mol source deeper)
    (adequate : deeper.history.length ≤ depth + source.history.length) :
    depth + source.history.length - deeper.history.length < depth :=
  residual_depth_lt depth path adequate

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.factDescriptor_factOf
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.localizedDescriptor_isTetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.localizedDescriptor_toLocalizedLabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.SupportedNode.history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.SupportedNode.provenance
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.exists_canonicalTreeNode_of_strictDescendant
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.supportedNode_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceReader_eq_of_supported
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceReader_eq_none_of_not_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceReader_eq_none_of_no_node
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceMap_eq_none_of_no_node
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceMap_eq_none_of_no_canonicalOccurrence
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceMap_eq_none_of_inadequate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceMap_tetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.exists_rawStateFact?_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceReader_toLocalizedLabel_eq_generated_factAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.rawStateDescriptorMap_generated_eq_candidateSourceMap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.strictDescendant_trans
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceMap_congr_of_agree
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceMap_strictDescendant_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceMap_strictDescendant_depth_lt

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback.candidateSourceMap
  [TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.generated,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedFacts,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor?,
   TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateDescriptorMap,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
