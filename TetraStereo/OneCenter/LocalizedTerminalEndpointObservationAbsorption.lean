import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial
import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedRule3DoubleBondEdgeDecidable

set_option autoImplicit false

/-!
# Terminal reference pairs and nonstereogenic endpoint observations

This module supplies an *independent*, executable terminal-reference check for one endpoint of a
physical double bond, together with its soundness against the production short-circuit endpoint
selector and the accepted descriptor-bearing absorption theorem.

The check does **not** inspect the opposite endpoint's keys, frame, or callback.  It starts from
the actual endpoint cursor, performs the same occurrence-local reference lookup as production,
and then verifies, on the two real reference cursors:

* the executable cut-neighbourhood expansion is exactly `some []` (a genuine source leaf);
* the cursor is a structural nonunit (`¬ LocalizedOccurrenceHasRule3DoubleBondEdge`);
* the two root nodes carry the same official atom label (element and isotope mass);
* the two root nodes carry the same Rule-1b root distance; and
* the two *actually compiled* compound Rules-4b--5 keys compare equal.

Under those assumptions the Rule-3 keys of both leaves are canonical root keys, so their
constitutional and Rule-3 comparisons both tie; the Rule-4b--5 tie is checked rather than assumed.
The resulting endpoint priority is therefore `.nonstereogenic` for the real production selector
`localizedRule3ShortCircuitEndpointPriorityExec?` using the production extended frame callback.

The bridge to geometry is the accepted absorption theorem
`localizedRule3DescriptorBearingSpatialUnit?_of_left_nonstereogenic`: an arbitrary opposite
endpoint frame, with an arbitrary opposite priority, forces no additional coordinate demand once
the left endpoint is tied.  Consequently the geometry is `.nonstereogenic` independently of the
opposite endpoint's frame, and the existing short-circuit spatial observation exposes exactly that
geometry.

Nothing here claims universal CIP coverage or chemical realizability.  The two leaves are required
to be terminal and nonunit with equal constitutional root observations; the compound Rules-4b--5
tie is an executive check of compiled keys, not a claim that the dependency view is irrelevant.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalEndpointObservation

open TetraStereo.OneCenter

/-- The bind of a `some` value in the `Option` monad is definitionally the applied continuation.
Stated for the `Bind.bind` produced by `do`-blocks (rather than primitive `Option.bind`); the two
are definitionally equal, so the proof is `rfl`. -/
private theorem option_some_bind_apply {α β : Type} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-! ## The terminal Rules-1a--3 key -/

/-- Exact Rules-1a--3 key of a terminal structural nonunit: the canonical root key together with the
empty root observation and empty root priority layers. -/
def terminalRule3Key (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.LocalizedRerootRecursiveRule3SpatialKey :=
  { constitutional :=
      input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
    observations := input.localizedRule3SpatialRootObservations none
    rule3 := input.localizedRule3SpatialRootPriorities none }

/-- The production extended short-circuit key compiler returns the canonical terminal key at every
budget and every excluded physical-unit set, for a genuine terminal structural nonunit. -/
theorem terminalRule3Key_computed (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (nonunit : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence)
    (budget : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view budget excluded cursor = some (terminalRule3Key input cursor) := by
  cases budget with
  | zero =>
      simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?, terminal,
        (input.localizedRule3StructuralNodeExec_eq_some_none_iff cursor.occurrence).mpr
          nonunit, terminalRule3Key]
  | succ budget =>
      simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?, terminal,
        localizedRule3ExtendedShortCircuitNodeWithExec?, localizedRule3OddRouteCertificate?,
        localizedRule3ShortCircuitNodeWithExec?, localizedRule3OrdinaryRouteCertificate?,
        localizedDescriptorBearingRule3NodeWithExec?, nonunit, terminalRule3Key]

/-! ## Constitutional equality of two terminal roots -/

/-- Equal official atom labels and equal Rule-1b root distances make two canonical root keys
constitutionally equal.  `sourceNodes` and `complete` are ignored by the comparator. -/
theorem officialRuleMajorRootKey_compare_eq_of_label_distance
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (labelEq : input.moleculeGraph.officialNodeAtomLabel first.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel second.occurrence.1.node)
    (distanceEq : first.occurrence.1.node.rule1bRootDistance =
      second.occurrence.1.node.rule1bRootDistance) :
    OfficialRuleMajorKey.compare
      (input.moleculeGraph.officialRuleMajorRootKey first.occurrence.1.node true)
      (input.moleculeGraph.officialRuleMajorRootKey second.occurrence.1.node true) =
        Ordering.eq := by
  rw [officialRuleMajorKey_compare_eq_iff]
  exact ⟨by simp [labelEq], by simp [distanceEq], by simp [labelEq]⟩

/-- Two terminal keys with equal root labels and distances compare equal under the cumulative
Rules-1a--3 comparator.  Both Rule-3 projections are the empty root-priority list. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_terminalRule3Key_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (labelEq : input.moleculeGraph.officialNodeAtomLabel first.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel second.occurrence.1.node)
    (distanceEq : first.occurrence.1.node.rule1bRootDistance =
      second.occurrence.1.node.rule1bRootDistance) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (terminalRule3Key input first) (terminalRule3Key input second) = Ordering.eq := by
  rw [input.compareLocalizedRerootRecursiveRule3SpatialKeys_of_constitutional_eq _ _
    (officialRuleMajorRootKey_compare_eq_of_label_distance input first second labelEq distanceEq)]
  rw [compareSparseLayers_compareNat_eq_iff]
  rfl

/-- The plain first-sphere root comparator ties on two cursors with equal root label. -/
theorem compareLocalizedRerootCursorConstitutionalRoot_eq_of_label
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (labelEq : input.moleculeGraph.officialNodeAtomLabel first.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel second.occurrence.1.node) :
    input.compareLocalizedRerootCursorConstitutionalRoot first second = Ordering.eq := by
  simp [compareLocalizedRerootCursorConstitutionalRoot,
    localizedRerootCursorRootAtomicNumber, labelEq]

/-- The executable complete constitutional compiler returns the canonical root key for a terminal
cursor at every budget. -/
theorem buildLocalizedRerootRuleMajorKeyExec?_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some []) :
    ∀ budget,
      input.buildLocalizedRerootRuleMajorKeyExec? budget cursor =
        some (input.moleculeGraph.officialRuleMajorRootKey
          cursor.occurrence.1.node true)
  | 0 => by
      simp [buildLocalizedRerootRuleMajorKeyExec?, terminal]
  | budget + 1 => by
      simp [buildLocalizedRerootRuleMajorKeyExec?, terminal]

/-- Two terminal cursors with equal root labels and distances tie under the executable complete
constitutional comparison, so the short-circuit selector reaches its deferred frame branch. -/
theorem compareLocalizedConstitutionalCursors?_terminal_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (firstTerminal : input.executableLocalizedRerootChildren? first = some [])
    (secondTerminal : input.executableLocalizedRerootChildren? second = some [])
    (labelEq : input.moleculeGraph.officialNodeAtomLabel first.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel second.occurrence.1.node)
    (distanceEq : first.occurrence.1.node.rule1bRootDistance =
      second.occurrence.1.node.rule1bRootDistance) :
    input.compareLocalizedConstitutionalCursors? first second = some Ordering.eq := by
  simp [compareLocalizedConstitutionalCursors?,
    buildLocalizedRerootRuleMajorKeyExec?_terminal input first firstTerminal,
    buildLocalizedRerootRuleMajorKeyExec?_terminal input second secondTerminal,
    officialRuleMajorRootKey_compare_eq_of_label_distance input first second labelEq distanceEq]

/-! ## Two-terminal frame keys -/

/-- The production two-pass extended Rule-3 frame, run on exactly two terminal cursors, retains
exactly their canonical terminal keys in the rebuilt pass.  The coupled-topology resolution and the
excluded physical-unit set are arbitrary: a terminal key does not depend on either. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_two_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel budget : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (first second : input.LocalizedRerootCursor carrierFuel)
    (firstTerminal : input.executableLocalizedRerootChildren? first = some [])
    (secondTerminal : input.executableLocalizedRerootChildren? second = some [])
    (firstNonunit : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge first.occurrence)
    (secondNonunit : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge second.occurrence)
    (positive : 0 < budget)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view budget [first, second] = some frame) :
    frame.keys = [terminalRule3Key input first, terminalRule3Key input second] := by
  cases budget with
  | zero => omega
  | succ fuel =>
      unfold buildLocalizedExtendedShortCircuitRule3FrameExec? at computed
      simp only [List.mapM_cons, List.mapM_nil, Option.pure_def,
        option_some_bind_apply,
        terminalRule3Key_computed input target view first firstTerminal firstNonunit fuel [],
        terminalRule3Key_computed input target view second secondTerminal secondNonunit fuel []]
        at computed
      try dsimp only at computed
      cases topologyComputed :
          input.localizedRule3CoupledTopologyResolutionExec?
            [terminalRule3Key input first, terminalRule3Key input second] with
      | none => simp [topologyComputed] at computed
      | some resolution =>
          simp only [topologyComputed,
            option_some_bind_apply,
            terminalRule3Key_computed input target view first firstTerminal firstNonunit fuel
              (input.localizedRule3CoupledExcludedPhysicalUnits
                [terminalRule3Key input first, terminalRule3Key input second] resolution),
            terminalRule3Key_computed input target view second secondTerminal secondNonunit fuel
              (input.localizedRule3CoupledExcludedPhysicalUnits
                [terminalRule3Key input first, terminalRule3Key input second] resolution)]
            at computed
          try dsimp only at computed
          have hframe : frame =
              { rawKeys := [terminalRule3Key input first, terminalRule3Key input second]
                coupled := resolution.isCoupled
                excluded := input.localizedRule3CoupledExcludedPhysicalUnits
                  [terminalRule3Key input first, terminalRule3Key input second] resolution
                keys := [terminalRule3Key input first, terminalRule3Key input second] } := by
            simpa using computed.symm
          rw [hframe]

/-! ## The executable terminal-reference check -/

/-- Independently specified data and verified computations for one endpoint.  Every field is either
an actual computation of the production executable reference/key machinery or a decidable
observation of the two real terminal source nodes.  No field asserts that the endpoint is already
nonstereogenic. -/
structure TerminalReferencePair (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) where
  first : input.Atom
  second : input.Atom
  candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second]
  firstCursor : input.LocalizedRerootCursor carrierFuel
  secondCursor : input.LocalizedRerootCursor carrierFuel
  firstComputed : input.localizedRule3ReferenceCursorExec? endpointCursor first = some firstCursor
  secondComputed : input.localizedRule3ReferenceCursorExec? endpointCursor second = some secondCursor
  firstChildren : input.executableLocalizedRerootChildren? firstCursor = some []
  secondChildren : input.executableLocalizedRerootChildren? secondCursor = some []
  firstNonunit : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge firstCursor.occurrence
  secondNonunit : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge secondCursor.occurrence
  labelEq : input.moleculeGraph.officialNodeAtomLabel firstCursor.occurrence.1.node =
    input.moleculeGraph.officialNodeAtomLabel secondCursor.occurrence.1.node
  distanceEq : firstCursor.occurrence.1.node.rule1bRootDistance =
    secondCursor.occurrence.1.node.rule1bRootDistance
  firstRule45 : input.LocalizedRerootCompoundRule45Key
  secondRule45 : input.LocalizedRerootCompoundRule45Key
  firstRule45Computed : input.buildLocalizedRerootCompoundRule45KeyExec? target view
    (localizedOccurrenceRerootEvaluationFuel carrierFuel) firstCursor = some firstRule45
  secondRule45Computed : input.buildLocalizedRerootCompoundRule45KeyExec? target view
    (localizedOccurrenceRerootEvaluationFuel carrierFuel) secondCursor = some secondRule45
  rule45Tied : input.compareLocalizedRerootCompoundRule45Keys firstRule45 secondRule45 =
    Ordering.eq
  frame : input.LocalizedRule3CanonicalKeyFrame
  frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) [firstCursor, secondCursor] =
      some frame

/-- Run the full terminal-reference check.  The candidates, reference lookups, terminal
children, nonunit decisions, root observations, compound Rules-4b--5 compilations, their comparison
and the production two-terminal frame computation are all actually performed. -/
def terminalReferencePair? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    Option (TerminalReferencePair input target view endpoint partner endpointCursor) :=
  match candidates : input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] =>
      match firstComputed : input.localizedRule3ReferenceCursorExec? endpointCursor first with
      | none => none
      | some firstCursor =>
          match secondComputed : input.localizedRule3ReferenceCursorExec?
              endpointCursor second with
          | none => none
          | some secondCursor =>
              match firstChildren : input.executableLocalizedRerootChildren? firstCursor with
              | some [] =>
                  match secondChildren : input.executableLocalizedRerootChildren? secondCursor with
                  | some [] =>
                      if firstNonunit :
                          ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge
                              firstCursor.occurrence then
                        if secondNonunit :
                            ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge
                                secondCursor.occurrence then
                          if labelEq :
                              input.moleculeGraph.officialNodeAtomLabel
                                  firstCursor.occurrence.1.node =
                                input.moleculeGraph.officialNodeAtomLabel
                                  secondCursor.occurrence.1.node then
                            if distanceEq :
                                firstCursor.occurrence.1.node.rule1bRootDistance =
                                  secondCursor.occurrence.1.node.rule1bRootDistance then
                              match firstRule45Computed :
                                  input.buildLocalizedRerootCompoundRule45KeyExec?
                                    target view
                                    (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                                    firstCursor with
                              | none => none
                              | some firstRule45 =>
                                  match secondRule45Computed :
                                      input.buildLocalizedRerootCompoundRule45KeyExec?
                                        target view
                                        (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                                        secondCursor with
                                  | none => none
                                  | some secondRule45 =>
                                      if rule45Tied :
                                          input.compareLocalizedRerootCompoundRule45Keys
                                            firstRule45 secondRule45 = Ordering.eq then
                                        match frameComputed :
                                            input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                                              target view
                                              (localizedDescriptorBearingRule3EvaluationFuel
                                                carrierFuel)
                                              [firstCursor, secondCursor] with
                                        | none => none
                                        | some frame =>
                                            some
                                              { first := first
                                                second := second
                                                candidates := candidates
                                                firstCursor := firstCursor
                                                secondCursor := secondCursor
                                                firstComputed := firstComputed
                                                secondComputed := secondComputed
                                                firstChildren := firstChildren
                                                secondChildren := secondChildren
                                                firstNonunit := firstNonunit
                                                secondNonunit := secondNonunit
                                                labelEq := labelEq
                                                distanceEq := distanceEq
                                                firstRule45 := firstRule45
                                                secondRule45 := secondRule45
                                                firstRule45Computed := firstRule45Computed
                                                secondRule45Computed := secondRule45Computed
                                                rule45Tied := rule45Tied
                                                frame := frame
                                                frameComputed := frameComputed }
                                      else none
                            else none
                          else none
                        else none
                      else none
                  | _ => none
              | _ => none
  | _ => none

/-! ## Soundness of the check -/

/-- The endpoint key frame synthesized from a certificate: the two actual candidates, each with
its canonical terminal Rule-3 key and its actually compiled compound Rules-4b--5 key. -/
def TerminalReferencePair.endpointFrame {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor) :
    input.LocalizedRule3EndpointKeyFrame :=
  { first := certificate.first
    second := certificate.second
    firstKey :=
      { rule3 := terminalRule3Key input certificate.firstCursor
        rule45 := certificate.firstRule45 }
    secondKey :=
      { rule3 := terminalRule3Key input certificate.secondCursor
        rule45 := certificate.secondRule45 } }

/-- The inert short-circuit result certified by a terminal reference pair. -/
def TerminalReferencePair.shortCircuitEndpoint
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor) :
    input.LocalizedRule3ShortCircuitEndpointResult :=
  { priority := .nonstereogenic, firstCandidate := certificate.first }

/-- The cumulative Rules-1a--5 comparison of the certified endpoint keys ties: the Rules-1a--3
comparison is forced by the terminal root observations, and the Rules-4b--5 comparison is the
compiled-key equality carried by the certificate. -/
theorem TerminalReferencePair.compareKeys_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor) :
    input.compareLocalizedOccurrenceRule3Through5Keys
      certificate.endpointFrame.firstKey
      certificate.endpointFrame.secondKey = Ordering.eq := by
  unfold compareLocalizedOccurrenceRule3Through5Keys
  rw [compareLex_eq_eq]
  refine ⟨?_, ?_⟩
  · simpa [Ordering.byKey, TerminalReferencePair.endpointFrame] using
      compareLocalizedRerootRecursiveRule3SpatialKeys_terminalRule3Key_eq input
        certificate.firstCursor certificate.secondCursor
        certificate.labelEq certificate.distanceEq
  · simpa [Ordering.byKey, TerminalReferencePair.endpointFrame] using certificate.rule45Tied

/-- The certified endpoint frame's complete endpoint priority is `.nonstereogenic`.  This is
derived from the comparison, not assumed. -/
theorem TerminalReferencePair.endpointPriority_eq_nonstereogenic
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor) :
    input.localizedRule3EndpointPriority certificate.endpointFrame = .nonstereogenic := by
  rw [input.localizedRule3EndpointPriority_eq_nonstereogenic_iff]
  exact certificate.compareKeys_eq

/-- The production executable endpoint compiler, invoked with the production extended Rule-3
frame callback, compiles the two certified terminal references to exactly the certified endpoint
frame.  No opposite-endpoint data is consulted. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_terminalPair
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec? target view
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
      endpoint partner endpointCursor =
    some
      { firstCursor := certificate.firstCursor
        secondCursor := certificate.secondCursor
        rule3Frame := certificate.frame
        endpointFrame := certificate.endpointFrame } := by
  have positive : 0 < localizedDescriptorBearingRule3EvaluationFuel carrierFuel := by
    unfold localizedDescriptorBearingRule3EvaluationFuel
    have spanPositive : 0 < 2 * (carrierFuel + 1) + 1 := by omega
    exact Nat.mul_pos spanPositive spanPositive
  have frameKeys : certificate.frame.keys =
      [terminalRule3Key input certificate.firstCursor,
       terminalRule3Key input certificate.secondCursor] :=
    buildLocalizedExtendedShortCircuitRule3FrameExec?_two_terminal input target view
      certificate.firstCursor certificate.secondCursor certificate.firstChildren
      certificate.secondChildren certificate.firstNonunit certificate.secondNonunit
      positive certificate.frame certificate.frameComputed
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
  rw [certificate.candidates]
  dsimp only
  rw [certificate.firstComputed, option_some_bind_apply,
      certificate.secondComputed, option_some_bind_apply, certificate.frameComputed,
      option_some_bind_apply]
  try dsimp only
  rw [frameKeys]
  try dsimp only
  rw [certificate.firstRule45Computed, option_some_bind_apply,
      certificate.secondRule45Computed, option_some_bind_apply]
  rfl

/-- **Main selector soundness.**  A successful terminal-reference check makes the real executable
short-circuit endpoint selector return `.nonstereogenic` with the certified first candidate.  The
certificate independently establishes the tie; the selector's own result is then recomputed. -/
theorem TerminalReferencePair.shortCircuitEndpointPriority_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor) :
    input.localizedRule3ShortCircuitEndpointPriorityExec? target view
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
      endpoint partner endpointCursor =
    some certificate.shortCircuitEndpoint := by
  have rootTied : input.compareLocalizedRerootCursorConstitutionalRoot
      certificate.firstCursor certificate.secondCursor = Ordering.eq :=
    compareLocalizedRerootCursorConstitutionalRoot_eq_of_label input
      certificate.firstCursor certificate.secondCursor certificate.labelEq
  have constitutionalTied : input.compareLocalizedConstitutionalCursors?
      certificate.firstCursor certificate.secondCursor = some Ordering.eq :=
    compareLocalizedConstitutionalCursors?_terminal_eq input
      certificate.firstCursor certificate.secondCursor certificate.firstChildren
      certificate.secondChildren certificate.labelEq certificate.distanceEq
  have priorityTied : input.localizedRule3EndpointPriority certificate.endpointFrame =
      .nonstereogenic := certificate.endpointPriority_eq_nonstereogenic
  unfold localizedRule3ShortCircuitEndpointPriorityExec?
  rw [certificate.candidates]
  dsimp only
  rw [certificate.firstComputed, option_some_bind_apply,
      certificate.secondComputed, option_some_bind_apply]
  rw [rootTied]
  dsimp only
  rw [constitutionalTied]
  try dsimp only
  rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_terminalPair certificate,
      option_some_bind_apply]
  try dsimp only
  rw [priorityTied]
  rfl

/-! ## Absorption into geometry and the observation projection -/

/-- The accepted descriptor-bearing absorption theorem, applied to the certified endpoint frame and
an *arbitrary* opposite endpoint frame: on a physical double bond the left endpoint's proved tie
forces unit geometry `.nonstereogenic` without consulting the opposite priority or its coordinates. -/
theorem TerminalReferencePair.descriptorBearingSpatialUnit?_of_endpoint
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor)
    (rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (doubleBond : input.moleculeGraph.bond endpoint partner = 2) :
    input.localizedRule3DescriptorBearingSpatialUnit?
        endpoint partner certificate.endpointFrame rightFrame =
      some
        { leftPriority := .nonstereogenic
          rightPriority := input.localizedRule3EndpointPriority rightFrame
          geometry := .nonstereogenic } :=
  input.localizedRule3DescriptorBearingSpatialUnit?_of_left_nonstereogenic
    endpoint partner certificate.endpointFrame rightFrame doubleBond
    certificate.endpointPriority_eq_nonstereogenic

/-- The minimal short-circuit spatial unit computed from the certified endpoint and an *arbitrary*
opposite endpoint result: its core geometry is `.nonstereogenic`. -/
theorem TerminalReferencePair.shortCircuitSpatialUnit?_of_endpoint
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor)
    (rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (doubleBond : input.moleculeGraph.bond endpoint partner = 2) :
    ∃ unit,
      input.localizedRule3ShortCircuitSpatialUnit?
          endpoint partner certificate.shortCircuitEndpoint rightEndpoint = some unit ∧
        unit.core.geometry = OfficialRule3Geometry.nonstereogenic := by
  let core : input.LocalizedRule3DescriptorBearingSpatialUnitResult :=
    { leftPriority := .nonstereogenic
      rightPriority := rightEndpoint.priority
      geometry := OfficialRule3Geometry.nonstereogenic }
  have coreComputed : input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
      endpoint partner .nonstereogenic rightEndpoint.priority = some core := by
    simp [localizedRule3DescriptorBearingSpatialUnitOfPriorities?, doubleBond, core]
  exact
    ⟨{ left := certificate.shortCircuitEndpoint
       right := rightEndpoint
       core := core },
     input.localizedRule3ShortCircuitSpatialUnit?_eq_some_of_priorities endpoint partner
       certificate.shortCircuitEndpoint rightEndpoint core coreComputed,
     rfl⟩

/-- The existing short-circuit observation projection exposes the projected unit geometry
unchanged.  Hence any occurrence result carrying a nonstereogenic unit core also carries a
nonstereogenic observable geometry, independently of how the opposite endpoint was computed. -/
theorem localizedRule3ShortCircuitSpatialObservation_geometry_of_core
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (coreNonstereogenic :
      result.unit.core.geometry = OfficialRule3Geometry.nonstereogenic) :
    (input.localizedRule3ShortCircuitSpatialObservation result).unit.geometry =
      OfficialRule3Geometry.nonstereogenic :=
  (localizedRule3ShortCircuitSpatialObservation_geometry input result).trans
    coreNonstereogenic

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalEndpointObservation
